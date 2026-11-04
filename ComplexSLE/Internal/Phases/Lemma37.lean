/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.Lemma37Meas
public import ComplexSLE.Internal.Phases.ErgodicMean
public import ComplexSLE.Internal.Stationary.PathStat

/-!
# Lemma 3.9 (`lem-computation`) in the form Proposition 3.2(b) consumes (M7/E1)

`paper.tex:L1506-1548`. Let `a, b > 0`, `c² ≤ ab`, `hU : IsSLEDriverAdapted a b c U P ℱ`, `p` an
admissible density, `ν = admissibleMeasure p`, and work on `μ = P ⊗ ν` with the random point
`𝐳 = e^{iu}`, `u ∼ ν`. For fixed `t̃, s̃ ≥ 0` put `σ = σ_𝐳`, `t = σ(t̃)`, `t + s = σ(s̃ + t̃)`; the
future hull is `L_{t,s+t} = leftHull (r ↦ U(r + t) - U t) s` (the hull of the concatenation
property (2.3)). The theorem proved is the equality in law of real random variables under `μ`

  `dist(f_t(𝐳), L_{t,s+t}) / |f_t(𝐳)|  =_d  dist(𝐳, L_{σ(s̃)})`,

`lemma_3_9`; the expectation form is `integral_comp_lemma_3_9`.
The two random variables are `futureDistRatioRV` and `hullDistRV` (`futureDistRatio`, `hullDist` of
`Lemma37Hull.lean`, evaluated at the path `ω ↦ U · ω` and the point `e^{iu}`). Both are a.e. equal
to measurable functions (`aemeasurable_futureDistRatioRV`, `aemeasurable_hullDistRV`), so the
equality of the image measures is the equality of laws. Off the almost sure event that `σ_𝐳` is
defined on `[0, ∞)` (Remark 2.12) they carry the project's junk convention, which does not affect
the laws.

**The source states a stronger joint law.** Lemma 3.9 asserts the equality in law of the pair
`(f_t(𝐳)/|f_t(𝐳)|, L_{t,s+t}/|f_t(𝐳)|) =_d (𝐳, L_{σ(s̃)})`. In the available one-time
stationarity (`InvarianceStationary.lean`) only `e^{2iθ̂}` (not `e^{iθ̂}`) is stationary, because
the driver law is only known to be symmetric under `U ↦ -U`. What the later argument uses (Step 2 of
the proof of `lem-converse-w-o-upgrade`, `paper.tex:L1690`) is only the displayed consequence for
the distance, and the distance is invariant under the simultaneous negation
`(direction, hull) ↦ (-direction, -hull)` (`hullDistC_neg`, from `leftHull_neg` and `sigmaTime_neg`;
`map_neg_eq`, from `IsSLEDriver.neg`). The proof therefore applies the strong Markov property at
`σ_𝐳(t̃)` and the stationarity of `e^{2iθ̂_t̃}` to a `π`-periodic function of the direction, exactly
as in `PathStat.lean`; the stronger joint statement is not claimed.

## Proof

* **Pathwise restart** (`futureDistRatio_eq_hullDist_restart`, `Lemma37Hull.lean`, the scaling
  calculation of the source). With `T = σ_𝐳(t̃)`, `r = |f_T(𝐳)|`, `V = r⁻¹ (U_{T + r² ·} - U_T)` the
  rescaled post-`T` driver and `𝐳' = f_T(𝐳)/r = e^{iθ̂_t̃}`, the left side equals
  `dist(𝐳', L^V_{σ^V_{𝐳'}(s̃)})` (`futureDistRatio_eq_hullDistC_scale_postPath`).
* **Strong Markov step** (`lintegral_futureDistRatio`, classical input `strongMarkov_sleDriver`
  through `lintegral_comp_scale_postPath`): for fixed `u`, `E G(left side) = E H_G(θ̂_t̃)`, where
  `H_G(β) = ∫ G(dist(e^{iβ}, L_{σ(s̃)}(w))) dΛ(w)` and `Λ` is the driver law.
* **Periodicity** (`obsKernelH_add_pi`): `H_G(β + π) = H_G(β)`, by `hullDistC_neg` and `-U =_d U`.
* **Stationarity** (`lintegral_comp_thetaHat_of_periodic`): the law of `e^{2iθ̂_t̃}` under `μ` is
  that of `e^{2iu}`, so `E_μ H_G(θ̂_t̃) = ∫ H_G dν`.
* **The right side** (`lintegral_hullDistRV`): `E_μ G(dist(𝐳, L_{σ(s̃)})) = ∫ H_G dν` by Fubini.

Uses the classical inputs `strongMarkov_sleDriver`, `ito_formula` and
`timeChange_isContLocalMartingale`, all proved in-project (`Internal/ExternalProofs/`).
-/

@[expose] public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter Complex Metric

namespace ComplexSLE.Internal

open Polar

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-! ### The two random variables -/

/-- The left side of Lemma 3.9 at the random point `e^{iu}`:
`dist(f_t(𝐳), L_{t,s+t}) / |f_t(𝐳)|` with `t = σ(t̃)`, `t + s = σ(s̃ + t̃)`. -/
noncomputable def futureDistRatioRV (hU : IsSLEDriverAdapted a b c U P ℱ) (tt ss : ℝ≥0)
    (q : Ω × ℝ) : ℝ :=
  futureDistRatio (fun r => U r q.1) (hU.cont q.1) (unitPt q.2) tt ss

/-- The right side of Lemma 3.9 at the random point `e^{iu}`: `dist(𝐳, L_{σ(s̃)})`. -/
noncomputable def hullDistRV (hU : IsSLEDriverAdapted a b c U P ℱ) (ss : ℝ≥0) (q : Ω × ℝ) : ℝ :=
  hullDist (fun r => U r q.1) (hU.cont q.1) (unitPt q.2) ss

/-! ### The kernel `H_G` -/

/-- `H_G(β) = ∫ G(dist(e^{iβ}, L_{σ(s̃)}(w))) dΛ(w)`. -/
noncomputable def hullKernelH (Λ : Measure CPath) (ss : ℝ≥0) (G : ℝ → ℝ≥0∞) (β : ℝ) : ℝ≥0∞ :=
  ∫⁻ w, G (hullDistC ss w (unitPt β)) ∂Λ

theorem measurable_hullKernelH (hU : IsSLEDriverAdapted a b c U P ℱ) (Λ : Measure CPath)
    [SFinite Λ] (ss : ℝ≥0) {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    Measurable (hullKernelH Λ ss G) := by
  have h : Measurable fun p : CPath × ℝ => G (hullDistC ss p.1 (unitPt p.2)) :=
    hG.comp (measurable_hullDistC_unit hU ss)
  exact h.lintegral_prod_left'

/-- **`π`-periodicity of `H_G`** (`hullDistC_neg` and `-U =_d U`). -/
theorem obsKernelH_add_pi (hU : IsSLEDriverAdapted a b c U P ℱ) [IsProbabilityMeasure P]
    (ss : ℝ≥0) {G : ℝ → ℝ≥0∞} (hG : Measurable G) (β : ℝ) :
    hullKernelH (driverLaw hU) ss G (β + π) = hullKernelH (driverLaw hU) ss G β := by
  have hUm : ∀ t, Measurable (U t) := fun t => hU.adapted.measurable
  have hFβ : Measurable fun w : CPath => G (hullDistC ss w (unitPt β)) := by
    have h1 := (measurable_hullDistC_unit hU ss).comp
      (measurable_id.prodMk (measurable_const (a := β)))
    exact hG.comp h1
  have e1 : ∫⁻ w, G (hullDistC ss w (unitPt (β + π))) ∂(driverLaw hU) =
      ∫⁻ w, G (hullDistC ss (CPath.neg w) (unitPt β)) ∂(driverLaw hU) := by
    refine lintegral_congr fun w => ?_
    rw [hullDistC_neg, unitPt_add_pi]
  have e2 : ∫⁻ w, G (hullDistC ss (CPath.neg w) (unitPt β)) ∂(driverLaw hU) =
      ∫⁻ w, G (hullDistC ss w (unitPt β)) ∂((driverLaw hU).map CPath.neg) :=
    (lintegral_map hFβ CPath.measurable_neg).symm
  have e3 : ∫⁻ w, G (hullDistC ss w (unitPt β)) ∂((driverLaw hU).map CPath.neg) =
      ∫⁻ w, G (hullDistC ss w (unitPt β)) ∂(driverLaw hU) := by
    rw [driverLaw, map_neg_eq hU.toIsSLEDriver hU.cont hUm]
  unfold hullKernelH
  rw [e1, e2, e3]

theorem hullKernelH_periodic (hU : IsSLEDriverAdapted a b c U P ℱ) [IsProbabilityMeasure P]
    (ss : ℝ≥0) {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    Function.Periodic (hullKernelH (driverLaw hU) ss G) π :=
  fun β => obsKernelH_add_pi hU ss hG β

/-! ### Stationarity of `E H(θ̂_s)` for `π`-periodic `H` -/

/-- **Stationarity of the expectation of `H(θ̂_s)` for a measurable `π`-periodic `H`**, from the
one-time stationarity of `e^{2iθ̂_s}`. -/
theorem lintegral_comp_thetaHat_of_periodic [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (s : ℝ≥0) {H : ℝ → ℝ≥0∞}
    (hHm : Measurable H) (hper : Function.Periodic H π) :
    ∫⁻ q, H (thetaHat hU (unitPt q.2) s q.1) ∂(P.prod (admissibleMeasure p)) =
      ∫⁻ u, H u ∂(admissibleMeasure p) := by
  set H' : ℂ → ℝ≥0∞ := fun w => H (Complex.arg w / 2) with hH'def
  have hH'm : Measurable H' := hHm.comp (Complex.measurable_arg.div_const 2)
  have hexp : ∀ β : ℝ, H β = H' (Complex.exp (2 * Complex.I * (β : ℂ))) := fun β =>
    periodic_eq_comp_exp hper β
  have hlaw := map_exp_thetaHat_prod_eq_admissible hU ha hb hc hp s
  have hY : Measurable fun q : Ω × ℝ =>
      Complex.exp (2 * Complex.I * (thetaHat hU (unitPt q.2) s q.1 : ℝ)) := by
    have := measurable_thetaHat_unit hU s
    fun_prop
  have hZ : Measurable fun u : ℝ => Complex.exp (2 * Complex.I * (u : ℂ)) := by fun_prop
  calc ∫⁻ q, H (thetaHat hU (unitPt q.2) s q.1) ∂(P.prod (admissibleMeasure p))
      = ∫⁻ q, H' (Complex.exp (2 * Complex.I * (thetaHat hU (unitPt q.2) s q.1 : ℝ)))
        ∂(P.prod (admissibleMeasure p)) := by simp only [hexp]
    _ = ∫⁻ w, H' w ∂((P.prod (admissibleMeasure p)).map fun q : Ω × ℝ =>
          Complex.exp (2 * Complex.I * (thetaHat hU (unitPt q.2) s q.1 : ℝ))) :=
        (lintegral_map hH'm hY).symm
    _ = ∫⁻ w, H' w ∂((admissibleMeasure p).map fun u : ℝ =>
          Complex.exp (2 * Complex.I * (u : ℂ))) := by rw [hlaw]
    _ = ∫⁻ u, H' (Complex.exp (2 * Complex.I * (u : ℂ))) ∂(admissibleMeasure p) :=
        lintegral_map hH'm hZ
    _ = ∫⁻ u, H u ∂(admissibleMeasure p) := by simp only [hexp]

/-! ### The pathwise restart identity on the path space -/

/-- **The left side is the hull distance of the rescaled post-`σ_z(t̃)` driver.** If `σ_z` is
defined on `[0, ∞)` for the path `ω`, then
`dist(f_t(z), L_{t,s+t}) / |f_t(z)| = dist(z', L^V_{σ^V_{z'}(s̃)})` with `V` the rescaled
post-`σ_z(t̃)` path and `z' = e^{iθ̂_t̃}`. -/
theorem futureDistRatio_eq_hullDistC_scale_postPath (hU : IsSLEDriverAdapted a b c U P ℱ) {z : ℂ}
    {tt ss : ℝ≥0} {ω : Ω} (hall : sigmaDom (fun r => U r ω) (hU.cont ω) z = Ici 0) :
    futureDistRatio (fun r => U r ω) (hU.cont ω) z tt ss =
      hullDistC ss (CPath.scale (‖fHat hU z tt ω‖₊)⁻¹ (postPath hU (sigmaTop hU z tt) ω))
        (unitPt (thetaHat hU z tt ω)) := by
  have hmem : (tt : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z := by
    rw [hall]; exact tt.coe_nonneg
  have hts : (ss : ℝ) + tt ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z := by
    rw [hall]; exact add_nonneg ss.coe_nonneg tt.coe_nonneg
  have hts' : (tt : ℝ) + ss ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z := by
    rwa [add_comm]
  have hv := scale_postPath_eq hU (z := z) hmem
  have hpt : unitPt (thetaHat hU z tt ω) =
      restartPoint (fun r => U r ω) (hU.cont ω) z (tt : ℝ) := by
    rw [restartPoint_eq_exp hmem, thetaHat_of_mem hU hmem]
    rfl
  have hvc : CPath.scale (‖fHat hU z tt ω‖₊)⁻¹ (postPath hU (sigmaTop hU z tt) ω) =
      ⟨sigmaRestartDriver (fun r => U r ω) (hU.cont ω) z (tt : ℝ),
        sigmaRestartDriver_continuous (hU.cont ω) z (tt : ℝ)⟩ := Subtype.ext hv
  rw [hvc, hpt, futureDistRatio_eq_hullDist_restart (hU.cont ω) hmem hts]
  have hdom : (ss : ℝ) ∈ sigmaDom (sigmaRestartDriver (fun r => U r ω) (hU.cont ω) z (tt : ℝ))
      (sigmaRestartDriver_continuous (hU.cont ω) z (tt : ℝ))
      (restartPoint (fun r => U r ω) (hU.cont ω) z (tt : ℝ)) :=
    (mem_sigmaDom_restart_sigma hmem).2 ⟨ss.coe_nonneg, hts'⟩
  exact (hullDistC_of_mem (v := ⟨sigmaRestartDriver (fun r => U r ω) (hU.cont ω) z (tt : ℝ),
    sigmaRestartDriver_continuous (hU.cont ω) z (tt : ℝ)⟩) hdom).symm

/-! ### The strong Markov step -/

/-- **Strong Markov step for the left side of Lemma 3.9.** For `z ≠ 0` and measurable
`G : ℝ → ℝ≥0∞`: `E G(left side) = E H_G(θ̂_t̃(z))` with `H_G` the kernel over the driver law. -/
theorem lintegral_futureDistRatio [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ)
    (ha : 0 < a) (hc : c ^ 2 ≤ a * b) {z : ℂ} (hz : z ≠ 0) (tt ss : ℝ≥0) {G : ℝ → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ ω, G (futureDistRatio (fun r => U r ω) (hU.cont ω) z tt ss) ∂P =
      ∫⁻ ω, hullKernelH (driverLaw hU) ss G (thetaHat hU z tt ω) ∂P := by
  have hgood := ae_sigmaDom_eq_Ici hU z ha hc hz
  have hτ := isStoppingTime_sigmaTop hU z tt
  have hfin : ∀ᵐ ω ∂P, sigmaTop hU z tt ω ≠ ⊤ := by
    filter_upwards [hgood] with ω hω
    have hmem : (tt : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z := by
      rw [hω]; exact tt.coe_nonneg
    rw [sigmaTop_of_mem hU hmem]
    exact WithTop.coe_ne_top
  have hX : Measurable[hτ.measurableSpace]
      (fun ω => (‖fHat hU z tt ω‖₊, thetaHat hU z tt ω)) := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_nnnorm.comp (measurable_fHat hU (z := z) tt)
    · exact ((isStronglyProgressive_thetaHat hU (z := z)).stronglyAdapted tt).measurable
  have hρ : ∀ᵐ ω ∂P, 0 < (‖fHat hU z tt ω‖₊, thetaHat hU z tt ω).1 := by
    filter_upwards [hgood] with ω hω
    have hmem : (tt : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z := by
      rw [hω]; exact tt.coe_nonneg
    change 0 < ‖fHat hU z tt ω‖₊
    rw [fHat_of_mem hU hmem]
    exact nnnorm_pos.2 (fPath_sigmaTime_ne_zero (hU.cont ω) hmem)
  have hFm : Measurable fun q : CPath × ℝ => G (hullDistC ss q.1 (unitPt q.2)) :=
    hG.comp (measurable_hullDistC_unit hU ss)
  have key := lintegral_comp_scale_postPath hU hτ hfin hX hρ hFm
  refine Eq.trans ?_ (key.trans ?_)
  · refine lintegral_congr_ae ?_
    filter_upwards [hgood] with ω hω
    rw [futureDistRatio_eq_hullDistC_scale_postPath hU hω]
  · rfl

/-! ### Measurability of the path-space representatives along the driver -/

theorem measurable_hullDistC_ofDriver (hU : IsSLEDriverAdapted a b c U P ℱ) (ss : ℝ≥0) :
    Measurable fun q : Ω × ℝ => hullDistC ss (CPath.ofDriver U hU.cont q.1) (unitPt q.2) := by
  have hUm : ∀ t, Measurable (U t) := fun t => hU.adapted.measurable
  have hι := CPath.measurable_ofDriver hU.cont hUm
  have h := (measurable_hullDistC_unit hU ss).comp ((hι.comp measurable_fst).prodMk measurable_snd)
  simp only [Function.comp_def] at h
  exact h

theorem measurable_futureDistRatioC_ofDriver (hU : IsSLEDriverAdapted a b c U P ℱ)
    (tt ss : ℝ≥0) :
    Measurable fun q : Ω × ℝ =>
      futureDistRatioC tt ss (CPath.ofDriver U hU.cont q.1) (unitPt q.2) := by
  have hUm : ∀ t, Measurable (U t) := fun t => hU.adapted.measurable
  have hι := CPath.measurable_ofDriver hU.cont hUm
  have h := (measurable_futureDistRatioC_unit hU tt ss).comp
    ((hι.comp measurable_fst).prodMk measurable_snd)
  simp only [Function.comp_def] at h
  exact h

/-! ### The right side -/

/-- **The right side of Lemma 3.9 under `P ⊗ ν`.** `E_{P ⊗ ν} G(dist(𝐳, L_{σ(s̃)})) = ∫ H_G dν`. -/
theorem lintegral_hullDistRV [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ)
    (ha : 0 < a) (hc : c ^ 2 ≤ a * b) {ν : Measure ℝ} [SFinite ν] (ss : ℝ≥0) {G : ℝ → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ q, G (hullDistRV hU ss q) ∂(P.prod ν) =
      ∫⁻ u, hullKernelH (driverLaw hU) ss G u ∂ν := by
  have hUm : ∀ t, Measurable (U t) := fun t => hU.adapted.measurable
  have hι := CPath.measurable_ofDriver hU.cont hUm
  have hFm : Measurable fun q : CPath × ℝ => G (hullDistC ss q.1 (unitPt q.2)) :=
    hG.comp (measurable_hullDistC_unit hU ss)
  have hmq : Measurable fun q : Ω × ℝ =>
      G (hullDistC ss (CPath.ofDriver U hU.cont q.1) (unitPt q.2)) :=
    hG.comp (measurable_hullDistC_ofDriver hU ss)
  have hgood := ae_mem_goodSet hU ha hc (ν := ν)
  have h1 : ∫⁻ q, G (hullDistRV hU ss q) ∂(P.prod ν) =
      ∫⁻ q, G (hullDistC ss (CPath.ofDriver U hU.cont q.1) (unitPt q.2)) ∂(P.prod ν) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hgood] with q hq
    have hmem := mem_sigmaDom_of_mem_goodSet hU hq ss
    have := hullDistC_of_mem (v := CPath.ofDriver U hU.cont q.1) hmem
    exact congrArg G this.symm
  have h2 := lintegral_prod_symm (μ := P) (ν := ν) _ hmq.aemeasurable
  rw [h1, h2]
  refine lintegral_congr fun u => ?_
  have hFu : Measurable fun w : CPath => G (hullDistC ss w (unitPt u)) := by
    have h4 := (measurable_hullDistC_unit hU ss).comp
      (measurable_id.prodMk (measurable_const (a := u)))
    exact hG.comp h4
  have h3 := lintegral_map hFu hι (μ := P)
  exact h3.symm

/-! ### The left side under `P ⊗ ν` -/

theorem aemeasurable_futureDistRatioRV [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hc : c ^ 2 ≤ a * b) {ν : Measure ℝ}
    [SFinite ν] (tt ss : ℝ≥0) : AEMeasurable (futureDistRatioRV hU tt ss) (P.prod ν) := by
  have hUm : ∀ t, Measurable (U t) := fun t => hU.adapted.measurable
  have hι := CPath.measurable_ofDriver hU.cont hUm
  have hm := measurable_futureDistRatioC_ofDriver hU tt ss
  refine hm.aemeasurable.congr ?_
  filter_upwards [ae_mem_goodSet hU ha hc (ν := ν)] with q hq
  have h1 := mem_sigmaDom_of_mem_goodSet hU hq tt
  have h2 := mem_sigmaDom_of_mem_goodSet hU hq (ss + tt)
  rw [NNReal.coe_add] at h2
  exact (futureDistRatio_eq_C (v := CPath.ofDriver U hU.cont q.1) h1 h2).symm

theorem aemeasurable_hullDistRV [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hc : c ^ 2 ≤ a * b) {ν : Measure ℝ}
    [SFinite ν] (ss : ℝ≥0) : AEMeasurable (hullDistRV hU ss) (P.prod ν) := by
  have hUm : ∀ t, Measurable (U t) := fun t => hU.adapted.measurable
  have hι := CPath.measurable_ofDriver hU.cont hUm
  have hm := measurable_hullDistC_ofDriver hU ss
  refine hm.aemeasurable.congr ?_
  filter_upwards [ae_mem_goodSet hU ha hc (ν := ν)] with q hq
  have hmem := mem_sigmaDom_of_mem_goodSet hU hq ss
  simp only [hullDistRV]
  rw [hullDistC_of_mem (v := CPath.ofDriver U hU.cont q.1) hmem]
  rfl

/-- **The left side of Lemma 3.9 under `P ⊗ ν`** (strong Markov step, periodicity and
stationarity of `e^{2iθ̂_t̃}`): `E_{P ⊗ ν} G(left side) = ∫ H_G dν`. -/
theorem lintegral_futureDistRatioRV [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (tt ss : ℝ≥0) {G : ℝ → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ q, G (futureDistRatioRV hU tt ss q) ∂(P.prod (admissibleMeasure p)) =
      ∫⁻ u, hullKernelH (driverLaw hU) ss G u ∂(admissibleMeasure p) := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  have : IsProbabilityMeasure (driverLaw hU) := isProbabilityMeasure_driverLaw hU
  have hHm := measurable_hullKernelH hU (driverLaw hU) ss hG
  have hGm : Measurable fun q : Ω × ℝ =>
      hullKernelH (driverLaw hU) ss G (thetaHat hU (unitPt q.2) tt q.1) :=
    hHm.comp (measurable_thetaHat_unit hU tt)
  have hae := aemeasurable_futureDistRatioRV hU ha hc (ν := admissibleMeasure p) tt ss
  have e1 := lintegral_prod_symm (μ := P) (ν := admissibleMeasure p)
    (fun q : Ω × ℝ => G (futureDistRatioRV hU tt ss q)) (hG.comp_aemeasurable hae)
  have e2 := lintegral_prod_symm (μ := P) (ν := admissibleMeasure p)
    (fun q : Ω × ℝ => hullKernelH (driverLaw hU) ss G (thetaHat hU (unitPt q.2) tt q.1))
    hGm.aemeasurable
  rw [← lintegral_comp_thetaHat_of_periodic hU ha hb hc hp tt hHm
    (hullKernelH_periodic hU ss hG), e1, e2]
  refine lintegral_congr fun u => ?_
  exact lintegral_futureDistRatio hU ha hc (unitPt_ne_zero u) tt ss hG

/-! ### Lemma 3.9 -/

/-- **Lemma 3.9 (`lem-computation`), in the form Proposition 3.2(b) consumes.** On `P ⊗ ν`,
`ν = admissibleMeasure p`, with the random point `𝐳 = e^{iu}`, for fixed `t̃, s̃ ≥ 0`
(`t = σ_𝐳(t̃)`, `t + s = σ_𝐳(s̃ + t̃)`),
`dist(f_t(𝐳), L_{t,s+t}) / |f_t(𝐳)|  =_d  dist(𝐳, L_{σ_𝐳(s̃)})`. -/
theorem lemma_3_9 [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (tt ss : ℝ≥0) :
    (P.prod (admissibleMeasure p)).map (futureDistRatioRV hU tt ss) =
      (P.prod (admissibleMeasure p)).map (hullDistRV hU ss) := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  refine Measure.ext_of_lintegral _ fun G hG => ?_
  rw [lintegral_map' hG.aemeasurable (aemeasurable_futureDistRatioRV hU ha hc tt ss),
    lintegral_map' hG.aemeasurable (aemeasurable_hullDistRV hU ha hc ss),
    lintegral_futureDistRatioRV hU ha hb hc hp tt ss hG,
    lintegral_hullDistRV hU ha hc ss hG]

/-- **Lemma 3.9, expectation form** (Bochner integral): for every Borel
`φ : ℝ → ℝ`, `E φ(left side) = E φ(right side)` under `P ⊗ ν` (both sides are the integral of `φ`
against the common law; if `φ` is not integrable for that law both sides are `0`). -/
theorem integral_comp_lemma_3_9 [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (tt ss : ℝ≥0) {φ : ℝ → ℝ}
    (hφ : Measurable φ) :
    ∫ q, φ (futureDistRatioRV hU tt ss q) ∂(P.prod (admissibleMeasure p)) =
      ∫ q, φ (hullDistRV hU ss q) ∂(P.prod (admissibleMeasure p)) := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  rw [← integral_map (aemeasurable_futureDistRatioRV hU ha hc tt ss) hφ.aestronglyMeasurable,
    ← integral_map (aemeasurable_hullDistRV hU ha hc ss) hφ.aestronglyMeasurable,
    lemma_3_9 hU ha hb hc hp tt ss]

end ComplexSLE.Internal

end
