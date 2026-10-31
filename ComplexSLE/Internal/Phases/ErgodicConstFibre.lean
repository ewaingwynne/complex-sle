/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.ErgodicConstRegen

/-!
# The 0-1 law for the Birkhoff limit at one starting point (M7/A5b, regeneration step)

Source: paper.tex:L1361-1372 (`step:sde-limit-deterministic`, `step:sde-regeneration`). For an
adapted driver `hU` and a point `z`, given regeneration data `D k : RegenDatum hU z k` for every
`k` (`ErgodicConstRegen.lean`) and a measurable `L` with `log |f̂_s(z)| / s → L` a.s.:

* `lintegral_mul_comp_scale_postPath`: the strong Markov step with an extra `ℱ_τ`-measurable
  weight `G` (companion of `lintegral_comp_scale_postPath`);
* `limFunctional`, `measurable_limFunctional`, `limFunctional_eq_of_tendsto`,
  `limFunctional_pathObsAt`: the limit functional `limsup_n ℓ(n)/n` of the path observable, which
  recovers `L` from the observable after any time `s₀`;
* `lintegral_mul_comp_limit` (regeneration step): for every `ℱ_{S}`-measurable weight `G` and
  measurable `ψ`, `E[G ψ(L)] = E[G] · ∫ ψ(limFunctional (obsC (w, 0))) dΛ(w)` — the conditional
  law of `L` given `ℱ_S` is the fixed law `Λ`-image, independent of the past (the state at `τ`
  is `e^{2iθ̂_τ} = 1`, and the kernel `obsKernel` depends on the state only through `e^{2iβ}`);
* `fibre_law_and_const`: the law of `L` is `(Λ).map (limFunctional ∘ obsC (·, 0))` and `L` is a.s.
  constant (the limit is independent of the pasts `ℱ_{S_n} ∋ log |f̂_n|` and is their limit).

Uses the EXTERNAL `strongMarkov_sleDriver` (through the strong Markov step).
-/

@[expose] public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal

open Polar

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-! ### The strong Markov step with an `ℱ_τ`-measurable weight -/

/-- **The strong Markov step with a random `ℱ_τ`-measurable rescaling and weight** (integral
form): `E[G F(ρ⁻¹-scaled post-τ path, β)] = E[G ∫ F(w, β) dΛ(w)]`. -/
theorem lintegral_mul_comp_scale_postPath (hU : IsSLEDriverAdapted a b c U P ℱ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤)
    {X : Ω → ℝ≥0 × ℝ} (hX : Measurable[hτ.measurableSpace] X) (hρ : ∀ᵐ ω ∂P, 0 < (X ω).1)
    {G : Ω → ℝ≥0∞} (hG : Measurable[hτ.measurableSpace] G)
    {F : CPath × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, G ω * F (CPath.scale (X ω).1⁻¹ (postPath hU τ ω), (X ω).2) ∂P =
      ∫⁻ ω, G ω * ∫⁻ w, F (w, (X ω).2) ∂(P.map (CPath.ofDriver U hU.cont)) ∂P := by
  have : IsProbabilityMeasure P := hU.toIsSLEDriver.isProbabilityMeasure
  obtain ⟨hVd, hind, -⟩ := External.strongMarkov_sleDriver hU τ hτ hfin
  have hUm : ∀ t, Measurable (U t) := fun t => hU.adapted.measurable
  have hVm : ∀ s, Measurable (postDriver U τ s) := measurable_postDriver hU hτ
  have hW : Measurable (postPath hU τ) := measurable_postPath hU hτ
  have hXm : Measurable X := hX.mono hτ.measurableSpace_le le_rfl
  have hGm : Measurable G := hG.mono hτ.measurableSpace_le le_rfl
  have hXG : Measurable[hτ.measurableSpace] (fun ω => (X ω, G ω)) := hX.prodMk hG
  have hXGm : Measurable (fun ω => (X ω, G ω)) := hXm.prodMk hGm
  -- the law of the post-`τ` path is the law of the driver
  have hlawW : P.map (postPath hU τ) = P.map (CPath.ofDriver U hU.cont) :=
    map_ofDriver_eq hVd hU.toIsSLEDriver (continuous_postDriver hU τ) hU.cont hVm hUm
  -- independence of the post-`τ` path and `(X, G)`
  have hindep : IndepFun (postPath hU τ) (fun ω => (X ω, G ω)) P := by
    have e : MeasurableSpace.comap (postPath hU τ) inferInstance =
        ⨆ s : ℝ≥0, MeasurableSpace.comap
          (fun ω => U ((τ ω).untopA + s) ω - U (τ ω).untopA ω) inferInstance := by
      change MeasurableSpace.comap (postPath hU τ)
        (MeasurableSpace.comap Subtype.val MeasurableSpace.pi) = _
      rw [MeasurableSpace.comap_comp, MeasurableSpace.pi, MeasurableSpace.comap_iSup]
      refine iSup_congr fun s => ?_
      rw [MeasurableSpace.comap_comp]
      rfl
    have hXGle : MeasurableSpace.comap (fun ω => (X ω, G ω)) inferInstance ≤
        hτ.measurableSpace := hXG.comap_le
    exact indep_of_indep_of_le_right (e ▸ hind) hXGle
  have hjoint : P.map (fun ω => (postPath hU τ ω, (X ω, G ω))) =
      (P.map (CPath.ofDriver U hU.cont)).prod (P.map fun ω => (X ω, G ω)) := by
    have := (indepFun_iff_map_prod_eq_prod_map_map hW.aemeasurable hXGm.aemeasurable).1 hindep
    rwa [hlawW] at this
  have hFm : Measurable fun p : CPath × ((ℝ≥0 × ℝ) × ℝ≥0∞) =>
      p.2.2 * F (CPath.scale p.2.1.1⁻¹ p.1, p.2.1.2) := by
    refine (measurable_snd.comp measurable_snd).mul ?_
    exact hF.comp ((CPath.measurable_scale.comp
      (((measurable_fst.comp (measurable_fst.comp measurable_snd)).inv).prodMk
        measurable_fst)).prodMk
      (measurable_snd.comp (measurable_fst.comp measurable_snd)))
  have hKm : Measurable fun y : (ℝ≥0 × ℝ) × ℝ≥0∞ =>
      y.2 * ∫⁻ w, F (w, y.1.2) ∂(P.map (CPath.ofDriver U hU.cont)) := by
    refine measurable_snd.mul ?_
    exact Measurable.lintegral_prod_left' (f := fun p : CPath × ((ℝ≥0 × ℝ) × ℝ≥0∞) =>
      F (p.1, p.2.1.2))
      (hF.comp (measurable_fst.prodMk (measurable_snd.comp (measurable_fst.comp measurable_snd))))
  calc ∫⁻ ω, G ω * F (CPath.scale (X ω).1⁻¹ (postPath hU τ ω), (X ω).2) ∂P
      = ∫⁻ p, p.2.2 * F (CPath.scale p.2.1.1⁻¹ p.1, p.2.1.2)
          ∂(P.map fun ω => (postPath hU τ ω, (X ω, G ω))) := by
        rw [lintegral_map hFm (hW.prodMk hXGm)]
    _ = ∫⁻ p, p.2.2 * F (CPath.scale p.2.1.1⁻¹ p.1, p.2.1.2)
          ∂((P.map (CPath.ofDriver U hU.cont)).prod (P.map fun ω => (X ω, G ω))) := by
        rw [hjoint]
    _ = ∫⁻ y, ∫⁻ w, y.2 * F (CPath.scale y.1.1⁻¹ w, y.1.2)
          ∂(P.map (CPath.ofDriver U hU.cont)) ∂(P.map fun ω => (X ω, G ω)) :=
        lintegral_prod_symm _ hFm.aemeasurable
    _ = ∫⁻ y, y.2 * ∫⁻ w, F (w, y.1.2) ∂(P.map (CPath.ofDriver U hU.cont))
          ∂(P.map fun ω => (X ω, G ω)) := by
        refine lintegral_congr_ae ?_
        have hpos : ∀ᵐ y ∂(P.map fun ω => (X ω, G ω)), 0 < y.1.1 :=
          (ae_map_iff hXGm.aemeasurable (measurableSet_lt measurable_const
            (measurable_fst.comp measurable_fst))).2 hρ
        filter_upwards [hpos] with y hy
        have hr : 0 < y.1.1⁻¹ := inv_pos.2 hy
        have hsc := map_scale_eq hU.toIsSLEDriver hU.cont hUm hr
        have hFy : Measurable fun w : CPath => F (w, y.1.2) :=
          hF.comp (measurable_id.prodMk measurable_const)
        rw [lintegral_const_mul y.2 (f := fun w : CPath => F (CPath.scale y.1.1⁻¹ w, y.1.2))
          (hF.comp ((CPath.measurable_scale_const _).prodMk measurable_const))]
        congr 1
        calc ∫⁻ w, F (CPath.scale y.1.1⁻¹ w, y.1.2) ∂(P.map (CPath.ofDriver U hU.cont))
            = ∫⁻ w', F (w', y.1.2)
                ∂((P.map (CPath.ofDriver U hU.cont)).map (CPath.scale y.1.1⁻¹)) :=
              (lintegral_map hFy (CPath.measurable_scale_const _)).symm
          _ = ∫⁻ w, F (w, y.1.2) ∂(P.map (CPath.ofDriver U hU.cont)) := by rw [hsc]
    _ = ∫⁻ ω, G ω * ∫⁻ w, F (w, (X ω).2) ∂(P.map (CPath.ofDriver U hU.cont)) ∂P := by
        rw [lintegral_map hKm hXGm]

/-! ### The limit functional of the path observable -/

/-- The limit functional `ξ = (x, θ, ℓ) ↦ limsup_n ℓ(n)/n` of a path observable. -/
noncomputable def limFunctional (ξ : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) : ℝ :=
  limsup (fun n : ℕ => ξ.2.2 (n : ℝ≥0) / (n : ℝ)) atTop

theorem measurable_limFunctional : Measurable limFunctional :=
  Measurable.limsup fun n =>
    ((measurable_pi_apply (n : ℝ≥0)).comp (measurable_snd.comp measurable_snd)).div_const _

theorem limFunctional_eq_of_tendsto {ξ : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)} {l : ℝ}
    (h : Tendsto (fun n : ℕ => ξ.2.2 (n : ℝ≥0) / (n : ℝ)) atTop (𝓝 l)) :
    limFunctional ξ = l :=
  h.limsup_eq

section Pathwise

variable (hU : IsSLEDriverAdapted a b c U P ℱ) {z : ℂ} {ω : Ω} {l : ℝ}

/-- If `log |f̂_s(z)| / s → l` as `s → ∞`, then the limit functional of the path observable after
any time `s₀` is `l`: `(Y_{s₀ + n} - Y_{s₀}) / n → l`. -/
theorem limFunctional_pathObsAt
    (h : Tendsto (fun s : ℝ≥0 => Real.log ‖fHat hU z s ω‖ / (s : ℝ)) atTop (𝓝 l))
    (s₀ : ℝ≥0) : limFunctional (pathObsAt hU z s₀ ω) = l := by
  refine limFunctional_eq_of_tendsto ?_
  have hn : Tendsto (fun n : ℕ => s₀ + (n : ℝ≥0)) atTop atTop :=
    tendsto_atTop_mono (fun n => le_add_self) tendsto_natCast_atTop_atTop
  have h1 := h.comp hn
  have h2 : Tendsto (fun n : ℕ => ((s₀ + (n : ℝ≥0) : ℝ≥0) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (s₀ : ℝ)).add_const 1
    simp only [zero_add] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    push_cast
    field_simp
  have h3 : Tendsto (fun n : ℕ => Real.log ‖fHat hU z s₀ ω‖ / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have h4 := (h1.mul h2).sub h3
  simp only [mul_one, sub_zero] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < ((s₀ + (n : ℝ≥0) : ℝ≥0) : ℝ) := by
    push_cast
    positivity
  simp only [Function.comp, pathObsAt]
  field_simp

end Pathwise

/-! ### The regeneration step -/

section Regeneration

variable [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ) {z : ℂ} {k : ℕ}

/-- **The regeneration step** (paper.tex:L1368-1372). Let `D` be a regeneration datum at level
`k` and `L` the a.s. real-time limit of `log |f̂_s(z)| / s`. For every `ℱ_S`-measurable weight `G`
(`S = D.S`) and every measurable `ψ`,
`E[G ψ(L)] = E[G] · ∫ ψ(limFunctional (obsC (w, 0))) dΛ(w)`: `L` is independent of `ℱ_S` and has
the fixed law of `limFunctional (obsC (w, 0))`, `w ∼ Λ`, `Λ` the law of the driver. -/
theorem lintegral_mul_comp_limit (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (D : RegenDatum hU z k)
    {L : Ω → ℝ}
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun s : ℝ≥0 => Real.log ‖fHat hU z s ω‖ / (s : ℝ)) atTop
      (𝓝 (L ω)))
    {G : Ω → ℝ≥0∞} (hG : Measurable[D.hS.measurableSpace] G) {ψ : ℝ → ℝ≥0∞}
    (hψ : Measurable ψ) :
    ∫⁻ ω, G ω * ψ (L ω) ∂P =
      (∫⁻ ω, G ω ∂P) * ∫⁻ w, ψ (limFunctional (obsC (w, 0))) ∂(driverLaw hU) := by
  set F : CPath × ℝ → ℝ≥0∞ := fun q => ψ (limFunctional (obsC q)) with hFdef
  have hFm : Measurable F := hψ.comp (measurable_limFunctional.comp (measurable_obsC hU))
  set X : Ω → ℝ≥0 × ℝ := fun ω => (‖fHat hU z (D.τ ω) ω‖₊, thetaHat hU z (D.τ ω) ω) with hXdef
  have step1 : ∫⁻ ω, G ω * ψ (L ω) ∂P =
      ∫⁻ ω, G ω * F (CPath.scale (X ω).1⁻¹ (postPath hU D.S ω), (X ω).2) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hlim, D.hobs] with ω h1 h2
    congr 1
    simp only [hFdef, hXdef]
    rw [← h2, limFunctional_pathObsAt hU h1 (D.τ ω)]
  have step2 := lintegral_mul_comp_scale_postPath hU D.hS D.hfin D.hX D.hpos hG hFm
  -- the kernel
  set K : ℝ → ℝ≥0∞ := obsKernel (driverLaw hU) (fun ξ => ψ (limFunctional ξ)) with hKdef
  have hKF : ∀ β : ℝ, ∫⁻ w, F (w, β) ∂(P.map (CPath.ofDriver U hU.cont)) = K β := fun β => rfl
  have hper : Function.Periodic K π :=
    obsKernel_periodic hU ha hc (hψ.comp measurable_limFunctional)
  have hK0 : ∀ᵐ ω ∂P, K (thetaHat hU z (D.τ ω) ω) = K 0 := by
    filter_upwards [D.hstate] with ω hω
    rw [periodic_eq_comp_exp hper, hω, Complex.arg_one, zero_div]
  have hGm : Measurable G := hG.mono D.hS.measurableSpace_le le_rfl
  rw [step1, step2]
  simp only [hKF]
  calc ∫⁻ ω, G ω * K (X ω).2 ∂P = ∫⁻ ω, G ω * K 0 ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hK0] with ω hω
        simp only [hXdef]
        rw [hω]
    _ = (∫⁻ ω, G ω ∂P) * K 0 := lintegral_mul_const _ hGm

end Regeneration

/-! ### The fibre law and the 0-1 law -/

section ZeroOne

variable [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ) {z : ℂ}

/-- A bounded measurable function with `E[f²] = E[f]²` is a.s. constant. -/
theorem ae_const_of_integral_sq_eq {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ ω, |f ω| ≤ C) (h : ∫ ω, f ω ^ 2 ∂P = (∫ ω, f ω ∂P) ^ 2) :
    ∃ c₀ : ℝ, ∀ᵐ ω ∂P, f ω = c₀ := by
  have hmem : MemLp f 2 P :=
    MemLp.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using hC ω)
  have hvar : variance f P = 0 := by
    rw [variance_eq_sub hmem]
    simpa [Pi.pow_apply] using sub_eq_zero.2 h
  exact ⟨_, ae_eq_integral_of_variance_eq_zero hmem hvar⟩

/-- **The fibre law and the 0-1 law** (paper.tex:L1361-1372, `step:sde-limit-deterministic`).
Given regeneration data at every level `k` and a measurable a.s. real-time limit `L` of
`log |f̂_s(z)| / s`, the law of `L` is the image of the driver law `Λ` under
`w ↦ limFunctional (obsC (w, 0))` (independent of `z`), and `L` is a.s. constant. -/
theorem fibre_law_and_const (ha : 0 < a) (hc : c ^ 2 ≤ a * b)
    (D : ∀ k : ℕ, RegenDatum hU z k) {L : Ω → ℝ} (hL : Measurable L)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun s : ℝ≥0 => Real.log ‖fHat hU z s ω‖ / (s : ℝ)) atTop
      (𝓝 (L ω))) :
    P.map L = (driverLaw hU).map (fun w : CPath => limFunctional (obsC (w, 0))) ∧
      ∃ c₀ : ℝ, ∀ᵐ ω ∂P, L ω = c₀ := by
  have hΛm : Measurable fun w : CPath => limFunctional (obsC (w, 0)) :=
    measurable_limFunctional.comp ((measurable_obsC hU).comp
      (measurable_id.prodMk measurable_const))
  refine ⟨?_, ?_⟩
  · refine Measure.ext_of_lintegral _ fun ψ hψ => ?_
    rw [lintegral_map hψ hL, lintegral_map hψ hΛm]
    have := lintegral_mul_comp_limit hU ha hc (D 0) hlim (G := fun _ => 1) measurable_const hψ
    simpa using this
  -- the constancy
  set φ : ℝ → ℝ := fun x => Real.arctan x + π / 2 with hφdef
  have hφc : Continuous φ := Real.continuous_arctan.add continuous_const
  have hφpos : ∀ x, 0 ≤ φ x := fun x => by
    have := Real.neg_pi_div_two_lt_arctan x
    simp only [hφdef]; linarith
  have hφle : ∀ x, φ x ≤ π := fun x => by
    have := Real.arctan_lt_pi_div_two x
    simp only [hφdef]; linarith
  set Ψ : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (φ x) with hΨdef
  have hΨc : Continuous Ψ := ENNReal.continuous_ofReal.comp hφc
  have hΨm : Measurable Ψ := hΨc.measurable
  have hΨle : ∀ x, Ψ x ≤ ENNReal.ofReal π := fun x => ENNReal.ofReal_le_ofReal (hφle x)
  set κ : ℝ≥0∞ := ∫⁻ w, Ψ (limFunctional (obsC (w, 0))) ∂(driverLaw hU) with hκdef
  have hκ : ∫⁻ ω, Ψ (L ω) ∂P = κ := by
    have := lintegral_mul_comp_limit hU ha hc (D 0) hlim (G := fun _ => 1) measurable_const hΨm
    simpa using this
  have hκfin : κ ≠ ∞ := by
    rw [← hκ]
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun ω => hΨle (L ω)) ?_)
    simp
  -- the weights
  set G : ℕ → Ω → ℝ≥0∞ := fun n ω => Ψ (Real.log ‖fHat hU z (n : ℝ≥0) ω‖ / (n : ℝ)) with hGdef
  have hGmeas : ∀ n, Measurable[(D n).hS.measurableSpace] (G n) := fun n =>
    hΨm.comp (((D n).hpast n le_rfl).div_const _)
  have hGm : ∀ n, Measurable (G n) := fun n =>
    (hGmeas n).mono (D n).hS.measurableSpace_le le_rfl
  have hGle : ∀ n ω, G n ω ≤ ENNReal.ofReal π := fun n ω => hΨle _
  have hG : ∀ n, ∫⁻ ω, G n ω * Ψ (L ω) ∂P = (∫⁻ ω, G n ω ∂P) * κ := fun n =>
    lintegral_mul_comp_limit hU ha hc (D n) hlim (hGmeas n) hΨm
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun n => G n ω) atTop (𝓝 (Ψ (L ω))) := by
    filter_upwards [hlim] with ω hω
    have h1 := hω.comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => Real.log ‖fHat hU z (n : ℝ≥0) ω‖ / (n : ℝ)) atTop
        (𝓝 (L ω)) := by
      refine h1.congr fun n => ?_
      simp
    exact (hΨc.tendsto _).comp h2
  have hfinπ : ∫⁻ _ : Ω, ENNReal.ofReal π ∂P ≠ ∞ := by simp
  have hT2 : Tendsto (fun n => ∫⁻ ω, G n ω ∂P) atTop (𝓝 (∫⁻ ω, Ψ (L ω) ∂P)) :=
    tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal π) hGm
      (fun n => Eventually.of_forall (hGle n)) hfinπ hconv
  have hfin2 : ∫⁻ _ : Ω, ENNReal.ofReal π * ENNReal.ofReal π ∂P ≠ ∞ := by
    rw [lintegral_const, measure_univ, mul_one]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hT1 : Tendsto (fun n => ∫⁻ ω, G n ω * Ψ (L ω) ∂P) atTop
      (𝓝 (∫⁻ ω, Ψ (L ω) * Ψ (L ω) ∂P)) :=
    tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal π * ENNReal.ofReal π)
      (fun n => (hGm n).mul (hΨm.comp hL))
      (fun n => Eventually.of_forall fun ω => mul_le_mul' (hGle n ω) (hΨle _)) hfin2
      (hconv.mono fun ω hω => ENNReal.Tendsto.mul_const hω (Or.inr ENNReal.ofReal_ne_top))
  have hT2' : Tendsto (fun n => (∫⁻ ω, G n ω ∂P) * κ) atTop
      (𝓝 ((∫⁻ ω, Ψ (L ω) ∂P) * κ)) := ENNReal.Tendsto.mul_const hT2 (Or.inr hκfin)
  have hsq : ∫⁻ ω, Ψ (L ω) * Ψ (L ω) ∂P = κ * κ := by
    have := tendsto_nhds_unique (hT1.congr hG) hT2'
    rwa [hκ] at this
  -- to real integrals
  set f : Ω → ℝ := fun ω => φ (L ω) with hfdef
  have hfm : Measurable f := hφc.measurable.comp hL
  have hfnn : ∀ ω, 0 ≤ f ω := fun ω => hφpos _
  have hfint : Integrable f P :=
    Integrable.of_bound hfm.aestronglyMeasurable π (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hfnn ω)]; exact hφle _)
  have hf2int : Integrable (fun ω => f ω ^ 2) P :=
    Integrable.of_bound (hfm.pow_const 2).aestronglyMeasurable (π ^ 2)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (hfnn ω) (hφle _) 2)
  have e1 : ENNReal.ofReal (∫ ω, f ω ∂P) = κ := by
    rw [ofReal_integral_eq_lintegral_ofReal hfint (Eventually.of_forall hfnn), ← hκ]
  have e2 : ENNReal.ofReal (∫ ω, f ω ^ 2 ∂P) = κ * κ := by
    rw [ofReal_integral_eq_lintegral_ofReal hf2int (Eventually.of_forall fun ω => sq_nonneg _),
      ← hsq]
    refine lintegral_congr fun ω => ?_
    rw [sq, ENNReal.ofReal_mul (hfnn ω)]
  have h3 : ∫ ω, f ω ^ 2 ∂P = (∫ ω, f ω ∂P) ^ 2 := by
    have hm0 : 0 ≤ ∫ ω, f ω ∂P := integral_nonneg hfnn
    have h4 : ENNReal.ofReal (∫ ω, f ω ^ 2 ∂P) = ENNReal.ofReal ((∫ ω, f ω ∂P) ^ 2) := by
      rw [e2, sq, ENNReal.ofReal_mul hm0, e1]
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun ω => sq_nonneg _)
      (sq_nonneg _)).1 h4
  obtain ⟨c₁, hc₁⟩ := ae_const_of_integral_sq_eq hfm (C := π)
    (fun ω => by rw [abs_of_nonneg (hfnn ω)]; exact hφle _) h3
  refine ⟨Real.tan (c₁ - π / 2), ?_⟩
  filter_upwards [hc₁] with ω hω
  have : Real.arctan (L ω) = c₁ - π / 2 := by
    simp only [hfdef, hφdef] at hω
    linarith
  rw [← this, Real.tan_arctan]

end ZeroOne

end ComplexSLE.Internal

end
