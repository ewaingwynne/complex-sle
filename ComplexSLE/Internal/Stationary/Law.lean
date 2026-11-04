/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# From periodic test functions to the law of `X_t mod π` and of `e^{2iX_t}`

`step:kol-process-stationarity` (one-time marginals): if `E f(Y) = E f(Z)` for every `C²`
`π`-periodic `f : ℝ → ℝ`, then `Y` and `Z` have the same law modulo `π` (as random variables in
`AddCircle π`), hence `e^{2iY}` and `e^{2iZ}` have the same law in `ℂ`. The extension from `C²`
periodic test functions to all bounded continuous functions on the circle goes through the density
of trigonometric polynomials (`span_fourier_closure_eq_top`), the real and imaginary parts of
`fourier n` being `cos (2nu)` and `sin (2nu)`.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set Function Real

namespace ComplexSLE.Internal

/-- `0 < π`, as a `Fact` (needed by the measure-space structure on `AddCircle π`). -/
instance fact_pi_pos : Fact (0 < π) := ⟨pi_pos⟩

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- The quotient map `ℝ → AddCircle π` is continuous. -/
theorem continuous_coe_addCircle : Continuous ((↑) : ℝ → AddCircle π) :=
  continuous_quotient_mk'

/-- The quotient map `ℝ → AddCircle π` is measurable. -/
theorem measurable_coe_addCircle : Measurable ((↑) : ℝ → AddCircle π) :=
  continuous_coe_addCircle.measurable

/-- Two real random variables whose expectations agree on every `C²` `π`-periodic test function
have the same law modulo `π`. -/
theorem map_addCircle_eq_of_forall_integral_eq {Y Z : Ω → ℝ} (hY : Measurable Y)
    (hZ : Measurable Z)
    (h : ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → Periodic f π → ∫ ω, f (Y ω) ∂P = ∫ ω, f (Z ω) ∂P) :
    P.map (fun ω => ((Y ω : ℝ) : AddCircle π)) = P.map (fun ω => ((Z ω : ℝ) : AddCircle π)) := by
  have hmk := measurable_coe_addCircle
  -- the complex functionals `q ↦ E q(W mod π)`
  set Λ : (Ω → ℝ) → C(AddCircle π, ℂ) → ℂ := fun W q => ∫ ω, q (W ω : AddCircle π) ∂P with hΛ
  have hint : ∀ W : Ω → ℝ, Measurable W → ∀ q : C(AddCircle π, ℂ),
      Integrable (fun ω => q (W ω : AddCircle π)) P := fun W hW q =>
    (integrable_const (μ := P) ‖q‖).mono'
      (q.continuous.measurable.comp (hmk.comp hW)).aestronglyMeasurable
      (Eventually.of_forall fun ω => q.norm_coe_le_norm _)
  have hΛcont : ∀ W : Ω → ℝ, Measurable W → Continuous (Λ W) := by
    intro W hW
    refine (LipschitzWith.of_dist_le' (K := 1) fun q₁ q₂ => ?_).continuous
    simp only [hΛ, dist_eq_norm, one_mul]
    rw [← integral_sub (hint W hW q₁) (hint W hW q₂)]
    have := norm_integral_le_of_norm_le_const (μ := P)
      (Eventually.of_forall fun ω => (q₁ - q₂).norm_coe_le_norm (W ω : AddCircle π))
    simpa using this
  -- agreement on the Fourier monomials
  have hexp : ∀ (n : ℤ) (x : ℝ), (fourier n (x : AddCircle π) : ℂ) =
      (Real.cos (2 * n * x) : ℂ) + (Real.sin (2 * n * x) : ℂ) * Complex.I := by
    intro n x
    rw [fourier_coe_apply]
    have : (2 * (π : ℂ) * Complex.I * n * x / π : ℂ) = ((2 * n * x : ℝ) : ℂ) * Complex.I := by
      have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
      push_cast
      field_simp
    rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hkey : ∀ (n : ℤ) (W : Ω → ℝ), Measurable W → Λ W (fourier n) =
      ((∫ ω, Real.cos (2 * n * W ω) ∂P : ℝ) : ℂ) +
        ((∫ ω, Real.sin (2 * n * W ω) ∂P : ℝ) : ℂ) * Complex.I := by
    intro n W hW
    have hcm : Measurable fun ω => Real.cos (2 * n * W ω) := by fun_prop
    have hsm : Measurable fun ω => Real.sin (2 * n * W ω) := by fun_prop
    have hc : Integrable (fun ω => Real.cos (2 * n * W ω)) P :=
      (integrable_const (μ := P) 1).mono' hcm.aestronglyMeasurable
        (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using Real.abs_cos_le_one _)
    have hs : Integrable (fun ω => Real.sin (2 * n * W ω)) P :=
      (integrable_const (μ := P) 1).mono' hsm.aestronglyMeasurable
        (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using Real.abs_sin_le_one _)
    have e1 : ∫ ω, ((Real.cos (2 * n * W ω) : ℝ) : ℂ) ∂P =
        ((∫ ω, Real.cos (2 * n * W ω) ∂P : ℝ) : ℂ) := integral_ofReal
    have e2 : ∫ ω, ((Real.sin (2 * n * W ω) : ℝ) : ℂ) ∂P =
        ((∫ ω, Real.sin (2 * n * W ω) ∂P : ℝ) : ℂ) := integral_ofReal
    simp only [hΛ, hexp]
    rw [integral_add hc.ofReal (hs.ofReal.mul_const _), integral_mul_const, e1, e2]
  have hmono : ∀ n : ℤ, Λ Y (fourier n) = Λ Z (fourier n) := by
    intro n
    have hcos : ∫ ω, Real.cos (2 * n * Y ω) ∂P = ∫ ω, Real.cos (2 * n * Z ω) ∂P :=
      h (fun x => Real.cos (2 * n * x)) (by fun_prop) fun x => by
        simp only
        rw [show 2 * (n : ℝ) * (x + π) = 2 * n * x + n * (2 * π) by ring,
          Real.cos_add_int_mul_two_pi]
    have hsin : ∫ ω, Real.sin (2 * n * Y ω) ∂P = ∫ ω, Real.sin (2 * n * Z ω) ∂P :=
      h (fun x => Real.sin (2 * n * x)) (by fun_prop) fun x => by
        simp only
        rw [show 2 * (n : ℝ) * (x + π) = 2 * n * x + n * (2 * π) by ring,
          Real.sin_add_int_mul_two_pi]
    rw [hkey n Y hY, hkey n Z hZ, hcos, hsin]
  -- agreement on trigonometric polynomials
  have hspan : ∀ q ∈ Submodule.span ℂ (range (@fourier π)), Λ Y q = Λ Z q := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨n, rfl⟩ := hq
      exact hmono n
    | zero => simp [hΛ]
    | add q₁ q₂ _ _ h₁ h₂ =>
      simp only [hΛ, ContinuousMap.add_apply] at h₁ h₂ ⊢
      rw [integral_add (hint Y hY q₁) (hint Y hY q₂), integral_add (hint Z hZ q₁) (hint Z hZ q₂),
        h₁, h₂]
    | smul a q _ hq =>
      simp only [hΛ, ContinuousMap.smul_apply, smul_eq_mul] at hq ⊢
      rw [integral_const_mul, integral_const_mul, hq]
  -- by density, agreement on all continuous functions
  have hdense : Dense (Submodule.span ℂ (range (@fourier π)) : Set C(AddCircle π, ℂ)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr span_fourier_closure_eq_top
  have hΛeq : Λ Y = Λ Z :=
    Continuous.ext_on hdense (hΛcont Y hY) (hΛcont Z hZ) fun q hq => hspan q hq
  -- conclude for the laws
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun g => ?_
  rw [integral_map (φ := fun ω => ((Y ω : ℝ) : AddCircle π)) (hmk.comp hY).aemeasurable
      g.continuous.aestronglyMeasurable,
    integral_map (φ := fun ω => ((Z ω : ℝ) : AddCircle π)) (hmk.comp hZ).aemeasurable
      g.continuous.aestronglyMeasurable]
  let q : C(AddCircle π, ℂ) := ⟨fun x => (g x : ℂ), Complex.continuous_ofReal.comp g.continuous⟩
  have hq := congrFun hΛeq q
  simp only [hΛ, q, ContinuousMap.coe_mk] at hq
  exact_mod_cast hq

/-! ### The map `e^{2iu}` on `ℝ ⧸ πℤ` -/

/-- `u ↦ e^{2iu}` is `π`-periodic. -/
theorem periodic_exp_two_mul_I : Periodic (fun u : ℝ => Complex.exp (2 * Complex.I * u)) π := by
  intro u
  simp only
  rw [show (2 * Complex.I * ((u + π : ℝ) : ℂ)) = 2 * Complex.I * u + 2 * π * Complex.I by
    push_cast; ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- `e^{2iu}` as a function on the circle `ℝ ⧸ πℤ`. -/
@[expose] noncomputable def expTwoI : AddCircle π → ℂ := periodic_exp_two_mul_I.lift

theorem continuous_expTwoI : Continuous expTwoI :=
  Continuous.quotient_liftOn' (by fun_prop) _

/-- Two real random variables whose expectations agree on every `C²` `π`-periodic test function
give `e^{2iY}` and `e^{2iZ}` the same law in `ℂ`. -/
theorem map_exp_eq_of_forall_integral_eq {Y Z : Ω → ℝ} (hY : Measurable Y) (hZ : Measurable Z)
    (h : ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → Periodic f π → ∫ ω, f (Y ω) ∂P = ∫ ω, f (Z ω) ∂P) :
    P.map (fun ω => Complex.exp (2 * Complex.I * Y ω)) =
      P.map (fun ω => Complex.exp (2 * Complex.I * Z ω)) := by
  have hmk := measurable_coe_addCircle
  have hm := continuous_expTwoI.measurable
  have e1 : (fun ω => Complex.exp (2 * Complex.I * Y ω)) =
      expTwoI ∘ fun ω => ((Y ω : ℝ) : AddCircle π) := rfl
  have e2 : (fun ω => Complex.exp (2 * Complex.I * Z ω)) =
      expTwoI ∘ fun ω => ((Z ω : ℝ) : AddCircle π) := rfl
  rw [e1, e2, ← Measure.map_map (f := fun ω => ((Y ω : ℝ) : AddCircle π)) hm (hmk.comp hY),
    ← Measure.map_map (f := fun ω => ((Z ω : ℝ) : AddCircle π)) hm (hmk.comp hZ),
    map_addCircle_eq_of_forall_integral_eq hY hZ h]

end ComplexSLE.Internal

end
