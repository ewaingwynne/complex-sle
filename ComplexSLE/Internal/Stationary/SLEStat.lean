/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.SLEStatLaw

/-!
# One-time stationarity of `θ̂(𝐳)` on the product space (M7/A4a)

For `a, b > 0`, `c² ≤ ab`, an adapted driver `hU : IsSLEDriverAdapted a b c U P ℱ`, an admissible
density `p` and `ν = p(u) 1_{[0,2π]}(u) du` (`admissibleMeasure p`), for every `s ≥ 0` the random
point `(ω, u) ↦ θ̂_s(e^{iu})(ω)` on `(Ω × ℝ, P ⊗ ν)` satisfies

* `map_addCircle_thetaHat_prod_eq`: `θ̂_s mod π` has the law of `u mod π` under `ν`
  (as measures on `AddCircle π`);
* `map_exp_thetaHat_prod_eq`: `e^{2iθ̂_s(e^{iu})}` has the law of `u ↦ e^{2iu}` under `ν`
  (as measures on `ℂ`).

Proof: for a continuous `π`-periodic `f`, Fubini gives
`E_{P⊗ν} f(θ̂_s(e^{iu})) = ∫ (∫ f(θ̂_s(e^{iu})) dP) dν(u)`. For fixed `u`, `θ̂(e^{iu})` is a
solution of `dX = µ(X) dt + β(X) dB` started a.s. at `[u]_{2π}` (`ae_thetaHat_zero`), so the inner
integral is `T_s f([u]_{2π}) = T_s f(u)` by the representation clause and `π`-periodicity of
`T_s f`; and
`∫ T_s f dν = ∫ f dν` (`integral_kernelOp_admissibleMeasure`). The laws then agree by the
trigonometric-polynomial density argument (`map_addCircle_eq_of_forall_integral_eq`).

The point `e^{iu}` is `Polar.unitPt u`. The transition kernel and its Markov property are the
explicit hypothesis `MarkovOneDimFor (µ) β` (resp. `MarkovOneDim`), the statement of the EXTERNAL (R29)
external `markov_oneDim` (`ComplexSLE/External/MarkovOneDim.lean`); it is neither
imported nor postulated. Modulo that hypothesis the results consume the externals
`hormander_oneDim`, `ito_formula` and `timeChange_isContLocalMartingale`, so are `PROVED_REL`.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set Function Real

namespace ComplexSLE.Internal

open Polar

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- For a fixed starting point `e^{iu}`, `E f(θ̂_s(e^{iu})) = T_s f([u]_{2π})`. -/
theorem integral_comp_thetaHat_eq_kernelOp [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {β : ℝ → ℝ} (hβsq : ∀ u, β u ^ 2 = 2 * diffusionD a b c u) {p' : ℝ≥0 → ℝ → ℝ → ℝ}
    (K : IsDiffusionKernel (mu a b c) β p') (s : ℝ≥0) {f : ℝ → ℝ} (hf : Continuous f) (u : ℝ) :
    ∫ ω, f (thetaHat hU (unitPt u) s ω) ∂P =
      kernelOp p' s f (toIcoMod Real.two_pi_pos 0 u) := by
  have hX := isDiffusionSolution_thetaHat_of_sq hU ha hb hc hβsq u
  exact K.integral_comp_eq_kernelOp hX (ae_thetaHat_zero hU ha hc u) s hf.measurable

/-- **Fubini step.** For a diffusion kernel `p'` of `(µ, β)` and a continuous `π`-periodic `f`,
`E_{P⊗ν} f(θ̂_s(e^{iu})) = ∫ f dν`. -/
theorem integral_comp_thetaHat_prod [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ 2 β) (hβsq : ∀ u, β u ^ 2 = 2 * diffusionD a b c u)
    {p' : ℝ≥0 → ℝ → ℝ → ℝ} (K : IsDiffusionKernel (mu a b c) β p')
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (s : ℝ≥0) {f : ℝ → ℝ} (hf : Continuous f)
    (hfper : Periodic f π) :
    ∫ q, f (thetaHat hU (unitPt q.2) s q.1) ∂(P.prod (admissibleMeasure p)) =
      ∫ u, f u ∂(admissibleMeasure p) := by
  have := isProbabilityMeasure_admissibleMeasure hp
  obtain ⟨C, hC⟩ := hfper.exists_bound pi_ne_zero hf
  have hFper : Periodic (kernelOp p' s f) π := by
    rcases eq_or_ne s 0 with rfl | hs
    · simpa using hfper
    · have hs' := pos_iff_ne_zero.mpr hs
      rw [kernelOp_of_pos hs']
      exact periodic_integral_mul_transition (K.equivariant s hs') hfper
  have hint : Integrable (fun q : Ω × ℝ => f (thetaHat hU (unitPt q.2) s q.1))
      (P.prod (admissibleMeasure p)) :=
    (integrable_const C).mono'
      (hf.measurable.comp (measurable_thetaHat_unit hU s)).aestronglyMeasurable
      (Eventually.of_forall fun q => by simpa [Real.norm_eq_abs] using hC _)
  rw [integral_prod_symm _ hint]
  have h1 : ∀ u : ℝ, ∫ ω, f (thetaHat hU (unitPt u) s ω) ∂P = kernelOp p' s f u := fun u => by
    rw [integral_comp_thetaHat_eq_kernelOp hU ha hb hc hβsq K s hf u]
    have hd : toIcoMod Real.two_pi_pos 0 u =
        u + ((-2 * toIcoDiv Real.two_pi_pos 0 u : ℤ) : ℝ) * π := by
      have := toIcoMod_sub_self Real.two_pi_pos 0 u
      rw [zsmul_eq_mul] at this
      push_cast at this ⊢
      linarith
    rw [hd]
    exact (hFper.int_mul _) u
  simp only [h1]
  exact integral_kernelOp_admissibleMeasure K hp hβ hβsq s hf hfper

/-- **One-time stationarity of `θ̂` on the product space, mod `π`, for a diffusion kernel.** -/
theorem map_addCircle_thetaHat_prod_eq_of_kernel [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ 2 β) (hβsq : ∀ u, β u ^ 2 = 2 * diffusionD a b c u)
    {p' : ℝ≥0 → ℝ → ℝ → ℝ} (K : IsDiffusionKernel (mu a b c) β p')
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (s : ℝ≥0) :
    (P.prod (admissibleMeasure p)).map
        (fun q : Ω × ℝ => ((thetaHat hU (unitPt q.2) s q.1 : ℝ) : AddCircle π)) =
      (admissibleMeasure p).map ((↑) : ℝ → AddCircle π) := by
  have := isProbabilityMeasure_admissibleMeasure hp
  have h := map_addCircle_eq_of_forall_integral_eq (P := P.prod (admissibleMeasure p))
    (Y := fun q : Ω × ℝ => thetaHat hU (unitPt q.2) s q.1) (Z := Prod.snd)
    (measurable_thetaHat_unit hU s) measurable_snd fun f hf hfper => by
      rw [integral_comp_thetaHat_prod hU ha hb hc hβ hβsq K hp s hf.continuous hfper,
        ← integral_map measurable_snd.aemeasurable hf.continuous.aestronglyMeasurable,
        Measure.map_snd_prod]
      simp
  rw [h, show (fun q : Ω × ℝ => ((q.2 : ℝ) : AddCircle π)) =
      ((↑) : ℝ → AddCircle π) ∘ Prod.snd from rfl,
    ← Measure.map_map measurable_coe_addCircle measurable_snd, Measure.map_snd_prod]
  simp

/-- **One-time stationarity of `θ̂` on the product space, `e^{2iθ̂}`, for a diffusion kernel.** -/
theorem map_exp_thetaHat_prod_eq_of_kernel [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ 2 β) (hβsq : ∀ u, β u ^ 2 = 2 * diffusionD a b c u)
    {p' : ℝ≥0 → ℝ → ℝ → ℝ} (K : IsDiffusionKernel (mu a b c) β p')
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (s : ℝ≥0) :
    (P.prod (admissibleMeasure p)).map
        (fun q : Ω × ℝ => Complex.exp (2 * Complex.I * (thetaHat hU (unitPt q.2) s q.1 : ℝ))) =
      (admissibleMeasure p).map (fun u : ℝ => Complex.exp (2 * Complex.I * u)) := by
  have := isProbabilityMeasure_admissibleMeasure hp
  have h := map_exp_eq_of_forall_integral_eq (P := P.prod (admissibleMeasure p))
    (Y := fun q : Ω × ℝ => thetaHat hU (unitPt q.2) s q.1) (Z := Prod.snd)
    (measurable_thetaHat_unit hU s) measurable_snd fun f hf hfper => by
      rw [integral_comp_thetaHat_prod hU ha hb hc hβ hβsq K hp s hf.continuous hfper,
        ← integral_map measurable_snd.aemeasurable hf.continuous.aestronglyMeasurable,
        Measure.map_snd_prod]
      simp
  have hm : Measurable fun u : ℝ => Complex.exp (2 * Complex.I * u) := by fun_prop
  rw [h, show (fun q : Ω × ℝ => Complex.exp (2 * Complex.I * (q.2 : ℝ))) =
      (fun u : ℝ => Complex.exp (2 * Complex.I * u)) ∘ Prod.snd from rfl,
    ← Measure.map_map hm measurable_snd, Measure.map_snd_prod]
  simp

/-! ### The diffusion coefficient `β` and the headline statements -/

/-- A smooth `β` with `β² = 2D` satisfying the Hörmander condition (A.1) for `α = µ`:
`√(2D)` when `c² < ab`, and `√a sin u - (c/√a) cos u` when `c² = ab`. -/
theorem exists_beta (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b) :
    ∃ β : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) β ∧ (∀ u, β u ^ 2 = 2 * diffusionD a b c u) ∧
      ∀ u, β u ≠ 0 ∨ deriv β u * mu a b c u ≠ 0 := by
  rcases hc.lt_or_eq with h | h
  · exact ⟨fun u => √(2 * diffusionD a b c u), contDiff_sqrt_two_mul_diffusionD ha hb h,
      sq_sqrt_two_mul_diffusionD ha hb hc, hormander_sqrt_two_mul_diffusionD ha hb h⟩
  · exact ⟨betaCrit a c, contDiff_betaCrit a c, sq_betaCrit ha h, hormander_betaCrit ha hb h⟩

/-- **One-time stationarity of `θ̂` on the product space, mod `π`**, given the conclusions of the
EXTERNAL `markov_oneDim` (R29) for `(µ, β)`. For `s ≥ 0`, under `P ⊗ ν` with
`ν = p(u) 1_{[0,2π]}(u) du`, the law of `θ̂_s(e^{iu}) mod π` is the law of `u mod π`. -/
theorem map_addCircle_thetaHat_prod_eq [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β) (hβsq : ∀ u, β u ^ 2 = 2 * diffusionD a b c u)
    (hH : ∀ u, β u ≠ 0 ∨ deriv β u * mu a b c u ≠ 0) (hMO : MarkovOneDimFor (mu a b c) β)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (s : ℝ≥0) :
    (P.prod (admissibleMeasure p)).map
        (fun q : Ω × ℝ => ((thetaHat hU (unitPt q.2) s q.1 : ℝ) : AddCircle π)) =
      (admissibleMeasure p).map ((↑) : ℝ → AddCircle π) := by
  obtain ⟨p', K⟩ := exists_isDiffusionKernel hU ha hb hc hβ hβsq hH hMO
  exact map_addCircle_thetaHat_prod_eq_of_kernel hU ha hb hc
    (hβ.of_le (WithTop.coe_le_coe.mpr le_top)) hβsq K hp s

/-- **One-time stationarity of `θ̂` on the product space, `e^{2iθ̂}`**, given the conclusions of the
EXTERNAL `markov_oneDim` (R29) for `(µ, β)`: under `P ⊗ ν`, `e^{2iθ̂_s(e^{iu})}` has the law of
`u ↦ e^{2iu}` under `ν`. -/
theorem map_exp_thetaHat_prod_eq [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β) (hβsq : ∀ u, β u ^ 2 = 2 * diffusionD a b c u)
    (hH : ∀ u, β u ≠ 0 ∨ deriv β u * mu a b c u ≠ 0) (hMO : MarkovOneDimFor (mu a b c) β)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (s : ℝ≥0) :
    (P.prod (admissibleMeasure p)).map
        (fun q : Ω × ℝ => Complex.exp (2 * Complex.I * (thetaHat hU (unitPt q.2) s q.1 : ℝ))) =
      (admissibleMeasure p).map (fun u : ℝ => Complex.exp (2 * Complex.I * u)) := by
  obtain ⟨p', K⟩ := exists_isDiffusionKernel hU ha hb hc hβ hβsq hH hMO
  exact map_exp_thetaHat_prod_eq_of_kernel hU ha hb hc
    (hβ.of_le (WithTop.coe_le_coe.mpr le_top)) hβsq K hp s

/-- **A4a, headline (mod `π`).** With the EXTERNAL `markov_oneDim` (R29) as the hypothesis
`hMO : MarkovOneDim`, for every `s ≥ 0`, `θ̂_s(e^{iu}) mod π` under `P ⊗ ν` has the law of
`u mod π` under `ν = p(u) 1_{[0,2π]}(u) du`. -/
theorem map_addCircle_thetaHat_prod_eq_of_markovOneDim [IsProbabilityMeasure P]
    (hMO : MarkovOneDim) (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b)
    (hc : c ^ 2 ≤ a * b) {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (s : ℝ≥0) :
    (P.prod (admissibleMeasure p)).map
        (fun q : Ω × ℝ => ((thetaHat hU (unitPt q.2) s q.1 : ℝ) : AddCircle π)) =
      (admissibleMeasure p).map ((↑) : ℝ → AddCircle π) := by
  obtain ⟨β, hβ, hβsq, hH⟩ := exists_beta ha hb hc
  exact map_addCircle_thetaHat_prod_eq hU ha hb hc hβ hβsq hH
    (hMO (mu a b c) β (contDiff_mu a b c) hβ (mu_periodic a b c)
      (fun u => sq_periodic_of_sq_eq_two_mul_diffusionD hβsq u) hH) hp s

/-- **A4a, headline (`e^{2iθ̂}`).** With the EXTERNAL `markov_oneDim` (R29) as the hypothesis
`hMO : MarkovOneDim`, for every `s ≥ 0`, the law of `(ω, u) ↦ e^{2iθ̂_s(e^{iu})(ω)}` under `P ⊗ ν`
equals the law of `u ↦ e^{2iu}` under `ν = p(u) 1_{[0,2π]}(u) du`. -/
theorem map_exp_thetaHat_prod_eq_of_markovOneDim [IsProbabilityMeasure P]
    (hMO : MarkovOneDim) (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b)
    (hc : c ^ 2 ≤ a * b) {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (s : ℝ≥0) :
    (P.prod (admissibleMeasure p)).map
        (fun q : Ω × ℝ => Complex.exp (2 * Complex.I * (thetaHat hU (unitPt q.2) s q.1 : ℝ))) =
      (admissibleMeasure p).map (fun u : ℝ => Complex.exp (2 * Complex.I * u)) := by
  obtain ⟨β, hβ, hβsq, hH⟩ := exists_beta ha hb hc
  exact map_exp_thetaHat_prod_eq hU ha hb hc hβ hβsq hH
    (hMO (mu a b c) β (contDiff_mu a b c) hβ (mu_periodic a b c)
      (fun u => sq_periodic_of_sq_eq_two_mul_diffusionD hβsq u) hH) hp s

end ComplexSLE.Internal

end
