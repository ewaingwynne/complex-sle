/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.PathStatMeas
public import ComplexSLE.Internal.Stationary.PathStatMarkov
public import ComplexSLE.Internal.Polar.PolarRestartSigma
public import ComplexSLE.Internal.Polar.PolarSigmaTop

/-!
# The path observable after time `s` and the restart at `σ_z(s)` (M7/A4c)

For an adapted driver `hU`, a point `z` and `s ≥ 0`, the *path observable*
`pathObsAt hU z s ω = Ξ_s(ω)` is

  `(e^{2iθ̂_s(z)}, (θ̂_{s+r}(z) - θ̂_s(z))_{r ≥ 0}, (log |f̂_{s+r}(z)| - log |f̂_s(z)|)_{r ≥ 0})`

as an element of `ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)`, and `pathObs hU s (ω, u) = pathObsAt hU e^{iu} s ω`.

* `polarInc_restart` (deterministic): if `v` is the restarted and rescaled driver at `σ_z(t̃)`
  (`sigmaRestartDriver`), the polar increments of `(v, z')` with `z' = e^{iθ̂_{t̃}(z)}`
  (`restartPoint`) are the increments of the polar data of `(U, z)` after `t̃`;
* `pathObsAt_eq_obsC`: if `σ_z` is defined on `[0, ∞)` for the path `ω`, then
  `Ξ_s(ω) = obsC (CPath.scale ρ⁻¹ (postPath hU σ_z(s) ω), θ̂_s(z)(ω))`, `ρ = |f̂_s(z)|`;
* `lintegral_pathObsAt` (strong Markov step): for `z ≠ 0` and measurable `F`,
  `E F(Ξ_s) = E ∫ F(obsC (w, θ̂_s(z))) dΛ(w)`, `Λ` = law of the driver on `CPath`.

Uses the classical input `strongMarkov_sleDriver`, proved in-project (through
`lintegral_comp_scale_postPath`).
-/

@[expose] public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter Complex

namespace ComplexSLE.Internal

open Polar

/-! ### The path observable -/

section Obs

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-- **The path observable** `Ξ_s(ω)` of the chain started at `z`:
`(e^{2iθ̂_s(z)}, (θ̂_{s+r}(z) - θ̂_s(z))_r, (log |f̂_{s+r}(z)| - log |f̂_s(z)|)_r)`. -/
noncomputable def pathObsAt (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) (s : ℝ≥0) (ω : Ω) :
    ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) :=
  (Complex.exp (2 * Complex.I * (thetaHat hU z s ω : ℝ)),
    fun r => thetaHat hU z (s + r) ω - thetaHat hU z s ω,
    fun r => Real.log ‖fHat hU z (s + r) ω‖ - Real.log ‖fHat hU z s ω‖)

/-- The path observable at the random point `e^{iu}` on `Ω × ℝ`. -/
noncomputable def pathObs (hU : IsSLEDriverAdapted a b c U P ℱ) (s : ℝ≥0) (q : Ω × ℝ) :
    ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) :=
  pathObsAt hU (unitPt q.2) s q.1

theorem measurable_pathObs (hU : IsSLEDriverAdapted a b c U P ℱ) (s : ℝ≥0) :
    Measurable (pathObs hU s) := by
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · have := measurable_thetaHat_unit hU s
    change Measurable fun q : Ω × ℝ =>
      Complex.exp (2 * Complex.I * (thetaHat hU (unitPt q.2) s q.1 : ℝ))
    fun_prop
  · refine measurable_pi_iff.2 fun r => ?_
    exact (measurable_thetaHat_unit hU (s + r)).sub (measurable_thetaHat_unit hU s)
  · refine measurable_pi_iff.2 fun r => ?_
    exact (measurable_log_norm_fHat_unit hU (s + r)).sub (measurable_log_norm_fHat_unit hU s)

end Obs

/-! ### The deterministic restart identity for `polarInc` -/

section Deterministic

variable {U : ℝ≥0 → ℂ}

/-- **Polar increments of the restarted chain.** If `v` is the restarted and rescaled driver at
`σ_z(t̃)`, with `σ_z` defined on `[t̃, ∞)`, the polar increments of `(v, z')`,
`z' = e^{iθ̂_{t̃}(z)}`, are the increments after `t̃` of the polar data of `(U, z)`. -/
theorem polarInc_restart (hU : Continuous U) {z : ℂ} {tt : ℝ} (ht : tt ∈ sigmaDom U hU z)
    (hall : ∀ r : ℝ≥0, tt + r ∈ sigmaDom U hU z) (v : CPath)
    (hv : v.1 = sigmaRestartDriver U hU z tt) :
    polarInc v (restartPoint U hU z tt) =
      (fun r : ℝ≥0 => argPath U hU z (sigmaTime U hU z (tt + r)) -
          argPath U hU z (sigmaTime U hU z tt),
        fun r : ℝ≥0 => Real.log ‖fPath U hU z (sigmaTime U hU z (tt + r))‖ -
          Real.log ‖fPath U hU z (sigmaTime U hU z tt)‖) := by
  obtain ⟨w, hw⟩ := v
  simp only at hv
  subst hv
  have hdom : ∀ r : ℝ≥0, (r : ℝ) ∈ sigmaDom (sigmaRestartDriver U hU z tt) hw
      (restartPoint U hU z tt) := fun r =>
    (mem_sigmaDom_restart_sigma ht).2 ⟨r.coe_nonneg, hall r⟩
  have hz0 : (0 : ℝ) ∈ lifeSet (sigmaRestartDriver U hU z tt) (restartPoint U hU z tt) := by
    have := sigmaTime_mem_lifeSet hw (hdom 0)
    exact mem_lifeSet_of_le this le_rfl this.1
  have hθ : ∀ r : ℝ≥0,
      thetaC r ⟨sigmaRestartDriver U hU z tt, hw⟩ (restartPoint U hU z tt) -
        thetaC 0 ⟨sigmaRestartDriver U hU z tt, hw⟩ (restartPoint U hU z tt) =
      argPath U hU z (sigmaTime U hU z (tt + r)) - argPath U hU z (sigmaTime U hU z tt) := by
    intro r
    have e1 := thetaC_of_mem (v := ⟨sigmaRestartDriver U hU z tt, hw⟩)
      (z := restartPoint U hU z tt) (hdom r)
    have e0 := thetaC_of_mem (v := ⟨sigmaRestartDriver U hU z tt, hw⟩)
      (z := restartPoint U hU z tt) (hdom 0)
    rw [e1, e0]
    have s0 := sigmaTime_zero hw hz0
    simp only [NNReal.coe_zero] at e0 ⊢
    change argPath (sigmaRestartDriver U hU z tt) hw (restartPoint U hU z tt)
        (sigmaTime (sigmaRestartDriver U hU z tt) hw (restartPoint U hU z tt) r) -
      argPath (sigmaRestartDriver U hU z tt) hw (restartPoint U hU z tt)
        (sigmaTime (sigmaRestartDriver U hU z tt) hw (restartPoint U hU z tt) 0) = _
    rw [s0]
    exact restart_argPath ht (hdom r)
  have hl : ∀ r : ℝ≥0, logfC r ⟨sigmaRestartDriver U hU z tt, hw⟩ (restartPoint U hU z tt) =
      Real.log ‖fPath U hU z (sigmaTime U hU z (tt + r))‖ -
        Real.log ‖fPath U hU z (sigmaTime U hU z tt)‖ := by
    intro r
    rw [logfC_of_mem (v := ⟨sigmaRestartDriver U hU z tt, hw⟩) (z := restartPoint U hU z tt)
      (hdom r)]
    exact restart_log_norm ht (hdom r)
  unfold polarInc
  congr 1
  · funext r; exact hθ r
  · funext r; exact hl r

end Deterministic

/-! ### The path observable as a function of the rescaled post-`σ_z(s)` driver -/

section Identification

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-- The rescaled post-`σ_z(s)` path is the restarted driver `sigmaRestartDriver`. -/
theorem scale_postPath_eq (hU : IsSLEDriverAdapted a b c U P ℱ) {z : ℂ} {s : ℝ≥0} {ω : Ω}
    (hmem : (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z) :
    (CPath.scale (‖fHat hU z s ω‖₊)⁻¹ (postPath hU (sigmaTop hU z s) ω)).1 =
      sigmaRestartDriver (fun r => U r ω) (hU.cont ω) z (s : ℝ) := by
  have hsT := sigmaTop_of_mem hU hmem
  have hρ : ‖fHat hU z s ω‖₊ =
      restartScale (fun r => U r ω) (hU.cont ω) z (s : ℝ) := by
    rw [fHat_of_mem hU hmem]; rfl
  have hpos : 0 < ‖fHat hU z s ω‖₊ := by rw [hρ]; exact restartScale_pos hmem
  funext s'
  simp only [CPath.scale, postPath, CPath.ofDriver, postDriver]
  rw [hsT, sigmaRestartDriver_apply, ← hρ]
  have hT : ((((sigmaTime (fun r => U r ω) (hU.cont ω) z s).toNNReal : ℝ≥0) :
      WithTop ℝ≥0)).untopA = restartTime (fun r => U r ω) (hU.cont ω) z (s : ℝ) := rfl
  rw [hT]
  have h1 : s' / (‖fHat hU z s ω‖₊)⁻¹ ^ 2 = ‖fHat hU z s ω‖₊ ^ 2 * s' := by
    rw [inv_pow, div_inv_eq_mul, mul_comm]
  rw [h1, add_comm]
  have h2 : (((‖fHat hU z s ω‖₊)⁻¹ : ℝ≥0) : ℂ) = ((‖fHat hU z s ω‖₊ : ℝ≥0) : ℂ)⁻¹ := by
    rw [show (((‖fHat hU z s ω‖₊)⁻¹ : ℝ≥0) : ℂ) =
      ((((‖fHat hU z s ω‖₊)⁻¹ : ℝ≥0) : ℝ) : ℂ) from rfl, NNReal.coe_inv, Complex.ofReal_inv]
  rw [h2]

/-- **The path observable is the observable of the rescaled post-`σ_z(s)` driver.** If `σ_z` is
defined on `[0, ∞)` for the path `ω`, then
`Ξ_s(ω) = obsC (CPath.scale |f̂_s|⁻¹ (post-σ_z(s) path), θ̂_s(z))`. -/
theorem pathObsAt_eq_obsC (hU : IsSLEDriverAdapted a b c U P ℱ) {z : ℂ} {s : ℝ≥0} {ω : Ω}
    (hall : sigmaDom (fun r => U r ω) (hU.cont ω) z = Ici 0) :
    pathObsAt hU z s ω =
      obsC (CPath.scale (‖fHat hU z s ω‖₊)⁻¹ (postPath hU (sigmaTop hU z s) ω),
        thetaHat hU z s ω) := by
  have hmemr : ∀ r : ℝ≥0, (r : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z := fun r => by
    rw [hall]; exact r.coe_nonneg
  have hmem := hmemr s
  have hall' : ∀ r : ℝ≥0, (s : ℝ) + r ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z := fun r => by
    rw [hall]; exact add_nonneg s.coe_nonneg r.coe_nonneg
  have hv := scale_postPath_eq hU (z := z) hmem
  have hpt : unitPt (thetaHat hU z s ω) =
      restartPoint (fun r => U r ω) (hU.cont ω) z (s : ℝ) := by
    rw [restartPoint_eq_exp hmem, thetaHat_of_mem hU hmem]
    rfl
  have hinc := polarInc_restart (hU.cont ω) hmem hall'
    (CPath.scale (‖fHat hU z s ω‖₊)⁻¹ (postPath hU (sigmaTop hU z s) ω)) hv
  unfold obsC pathObsAt
  rw [hpt]
  simp only
  rw [hinc]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext r
    have h2 : ((s + r : ℝ≥0) : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z := hmemr _
    simp only [thetaHat_of_mem hU hmem, thetaHat_of_mem hU h2, NNReal.coe_add]
  · funext r
    have h2 : ((s + r : ℝ≥0) : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z := hmemr _
    simp only [fHat_of_mem hU hmem, fHat_of_mem hU h2, NNReal.coe_add]

end Identification

/-! ### The strong Markov step for the path observable -/

section Markov

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-- **Strong Markov step for the path observable.** For `z ≠ 0` and measurable
`F : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞`,
`E F(Ξ_s) = E ∫ F(obsC (w, θ̂_s(z))) dΛ(w)`, where `Λ` is the law of the driver on `CPath`. -/
theorem lintegral_pathObsAt [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ)
    (ha : 0 < a) (hc : c ^ 2 ≤ a * b) {z : ℂ} (hz : z ≠ 0) (s : ℝ≥0)
    {F : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (pathObsAt hU z s ω) ∂P =
      ∫⁻ ω, ∫⁻ w, F (obsC (w, thetaHat hU z s ω)) ∂(P.map (CPath.ofDriver U hU.cont)) ∂P := by
  have hgood := ae_sigmaDom_eq_Ici hU z ha hc hz
  have hτ := isStoppingTime_sigmaTop hU z s
  have hfin : ∀ᵐ ω ∂P, sigmaTop hU z s ω ≠ ⊤ := by
    filter_upwards [hgood] with ω hω
    have hmem : (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z := by
      rw [hω]; exact s.coe_nonneg
    rw [sigmaTop_of_mem hU hmem]
    exact WithTop.coe_ne_top
  have hX : Measurable[hτ.measurableSpace]
      (fun ω => (‖fHat hU z s ω‖₊, thetaHat hU z s ω)) := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_nnnorm.comp (measurable_fHat hU (z := z) s)
    · exact ((isStronglyProgressive_thetaHat hU (z := z)).stronglyAdapted s).measurable
  have hρ : ∀ᵐ ω ∂P, 0 < (‖fHat hU z s ω‖₊, thetaHat hU z s ω).1 := by
    filter_upwards [hgood] with ω hω
    have hmem : (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z := by
      rw [hω]; exact s.coe_nonneg
    change 0 < ‖fHat hU z s ω‖₊
    rw [fHat_of_mem hU hmem]
    exact nnnorm_pos.2 (fPath_sigmaTime_ne_zero (hU.cont ω) hmem)
  have hFm : Measurable fun q : CPath × ℝ => F (obsC q) := hF.comp (measurable_obsC hU)
  have key := lintegral_comp_scale_postPath hU hτ hfin hX hρ hFm
  rw [← key]
  refine lintegral_congr_ae ?_
  filter_upwards [hgood] with ω hω
  rw [pathObsAt_eq_obsC hU hω]

end Markov

end ComplexSLE.Internal

end
