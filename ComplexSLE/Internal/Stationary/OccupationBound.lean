/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.OccupationMeasure
public import ComplexSLE.Internal.Stationary.OccupationPeriodic
public import ComplexSLE.Internal.Stationary.OccupationNullSets
public import ComplexSLE.Internal.Stationary.ThetaSemigroupDynkin

/-!
# The occupation estimate (M10-R5a): `θ̂` spends no time in a null set where `β² > 0`

Let `X` be an everywhere-continuous solution of the martingale problem for `(µ, β)`, `β` continuous
and `β² = 2D` (`0 < a`, `0 < b`, `c² ≤ ab`), and `ρ = occupation X P T`.

* `exists_integral_mul_sq_le` (**Dynkin bound**): there is `K ≥ 0` with
  `∫ ψ β² dρ ≤ K ∫₀^π ψ` for every continuous `π`-periodic `ψ ≥ 0`. Proof: take `g` periodic `C²`
  with `g'' = ψ - M/π` (`exists_periodic_contDiff_two_second_deriv`); then
  `ψ β² = 2 L g - 2 g' µ + (M/π) β²` and `|∫ L g dρ| ≤ 2‖g‖` by Dynkin's formula against `ρ`.
* `occupation_inter_ne_zero_eq_zero`: `ρ (N ∩ {β² ≠ 0}) = 0` for Lebesgue-null `N`
  (`measure_inter_ne_zero_eq_zero`).

The only classical input is `External.ito_formula` (through `ItoReal.lean`).
-/

public section

open scoped NNReal ENNReal Topology Real
open MeasureTheory ProbabilityTheory Filter Set Function

namespace ComplexSLE.Internal

section Bound

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ≥0 mΩ} {a b c : ℝ} {β : ℝ → ℝ} {X : ℝ≥0 → Ω → ℝ}

theorem integrable_of_abs_le {ρ : Measure ℝ} [IsFiniteMeasure ρ] {f : ℝ → ℝ} (hf : Continuous f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f ρ :=
  (integrable_const C).mono' hf.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)

theorem abs_integral_le_mul_of_abs_le {ρ : Measure ℝ} [IsFiniteMeasure ρ] {f : ℝ → ℝ} {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) : |∫ x, f x ∂ρ| ≤ C * ρ.real univ := by
  have := norm_integral_le_of_norm_le_const (μ := ρ) (f := f) (C := C)
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)
  simpa [Real.norm_eq_abs] using this

/-- **The Dynkin bound.** -/
theorem exists_integral_mul_sq_le (hX : IsDiffusionSolution ℱ (mu a b c) β X P)
    (hXc : ∀ ω, Continuous fun t => X t ω) (hβc : Continuous β)
    (hβsq : ∀ v, β v ^ 2 = 2 * diffusionD a b c v) (T : ℝ≥0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ : ℝ → ℝ, Continuous ψ → Periodic ψ π → (∀ x, 0 ≤ ψ x) →
      ∫ x, ψ x * β x ^ 2 ∂(occupation X P T) ≤ K * ∫ s in (0 : ℝ)..π, ψ s := by
  have hXm : ∀ t, Measurable (X t) := IsDiffusionSolution.measurable hX
  set ρ := occupation X P T with hρ
  have hρT : ρ.real univ = T := real_occupation_univ hXc hXm T
  obtain ⟨CM, hCM⟩ := exists_abs_le_of_periodic (continuous_mu a b c) (mu_periodic a b c)
  have hβ2per : Periodic (fun v => β v ^ 2) π := fun v =>
    sq_periodic_of_sq_eq_two_mul_diffusionD hβsq v
  obtain ⟨CB, hCB⟩ := exists_abs_le_of_periodic (hβc.pow 2) hβ2per
  have hCM0 : 0 ≤ CM := (abs_nonneg _).trans (hCM 0)
  have hCB0 : 0 ≤ CB := (abs_nonneg _).trans (hCB 0)
  refine ⟨16 * π + 8 * CM * T + CB * T / π, by positivity, fun ψ hψ hper hnn => ?_⟩
  set M := ∫ s in (0 : ℝ)..π, ψ s with hM
  have hM0 : 0 ≤ M := intervalIntegral.integral_nonneg Real.pi_pos.le fun t _ => hnn t
  obtain ⟨g, hg, hgper, hg2, hg1b, hg0b⟩ := exists_periodic_contDiff_two_second_deriv hψ hper hnn
  rw [← hM] at hg2 hg1b hg0b
  have hLc : Continuous (generator (mu a b c) β g) :=
    continuous_generator (continuous_mu a b c) hβc hg
  obtain ⟨CL, hCL⟩ := exists_abs_le_of_periodic hLc (periodic_generator_mu hβsq hgper)
  have hdyn := abs_integral_generator_occupation_le hX hXc (continuous_mu a b c) hβc hg hg0b hCL T
  have hg'c : Continuous (deriv g) := hg.continuous_deriv one_le_two
  -- the pointwise identity
  have hid : ∀ x, ψ x * β x ^ 2 = 2 * generator (mu a b c) β g x - 2 * (deriv g x * mu a b c x) +
      (M / π) * β x ^ 2 := fun x => by
    unfold generator
    rw [hg2 x]
    ring
  have i1 : Integrable (generator (mu a b c) β g) ρ := integrable_of_abs_le hLc hCL
  have hgμ : Continuous fun x => deriv g x * mu a b c x := hg'c.mul (continuous_mu a b c)
  have b2 : ∀ x, |deriv g x * mu a b c x| ≤ 4 * M * CM := fun x => by
    rw [abs_mul]
    exact mul_le_mul (hg1b x) (hCM x) (abs_nonneg _) (by positivity)
  have i2 : Integrable (fun x => deriv g x * mu a b c x) ρ := integrable_of_abs_le hgμ b2
  have i3 : Integrable (fun x => β x ^ 2) ρ := integrable_of_abs_le (hβc.pow 2) hCB
  have hsplit : ∫ x, (2 * generator (mu a b c) β g x - 2 * (deriv g x * mu a b c x) +
      (M / π) * β x ^ 2) ∂ρ = 2 * ∫ x, generator (mu a b c) β g x ∂ρ -
      2 * ∫ x, deriv g x * mu a b c x ∂ρ + (M / π) * ∫ x, β x ^ 2 ∂ρ := by
    have h12 : Integrable (fun x => 2 * generator (mu a b c) β g x -
        2 * (deriv g x * mu a b c x)) ρ := (i1.const_mul 2).sub (i2.const_mul 2)
    rw [integral_add h12 (i3.const_mul _), integral_sub (i1.const_mul 2) (i2.const_mul 2),
      integral_const_mul, integral_const_mul, integral_const_mul]
  have hint : ∫ x, ψ x * β x ^ 2 ∂ρ = 2 * ∫ x, generator (mu a b c) β g x ∂ρ -
      2 * ∫ x, deriv g x * mu a b c x ∂ρ + (M / π) * ∫ x, β x ^ 2 ∂ρ := by
    rw [← hsplit]
    exact integral_congr_ae (Eventually.of_forall hid)
  have e2 := abs_integral_le_mul_of_abs_le (ρ := ρ) b2
  have e3 := abs_integral_le_mul_of_abs_le (ρ := ρ) hCB
  rw [hρT] at e2 e3
  have hπ := Real.pi_pos
  have h1 : ∫ x, generator (mu a b c) β g x ∂ρ ≤ 2 * (4 * π * M) := (le_abs_self _).trans hdyn
  have h2 : -∫ x, deriv g x * mu a b c x ∂ρ ≤ 4 * M * CM * T := (neg_le_abs _).trans e2
  have h3 : (M / π) * ∫ x, β x ^ 2 ∂ρ ≤ (M / π) * (CB * T) :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans e3) (by positivity)
  have h4 : (M / π) * (CB * T) = CB * T / π * M := by ring
  rw [hint]
  nlinarith

/-- **The occupation of null sets.** `θ̂` (or any solution `X`) spends no time, in the sense of the
occupation measure, in `N ∩ {β² ≠ 0}` for a Lebesgue-null set `N`. -/
theorem occupation_inter_ne_zero_eq_zero (hX : IsDiffusionSolution ℱ (mu a b c) β X P)
    (hXc : ∀ ω, Continuous fun t => X t ω) (hβc : Continuous β)
    (hβsq : ∀ v, β v ^ 2 = 2 * diffusionD a b c v) (T : ℝ≥0) {N : Set ℝ} (hN : volume N = 0) :
    occupation X P T (N ∩ {x | β x ^ 2 ≠ 0}) = 0 := by
  obtain ⟨K, hK0, hK⟩ := exists_integral_mul_sq_le hX hXc hβc hβsq T
  have hβ2per : Periodic (fun v => β v ^ 2) π := fun v =>
    sq_periodic_of_sq_eq_two_mul_diffusionD hβsq v
  obtain ⟨CB, hCB⟩ := exists_abs_le_of_periodic (hβc.pow 2) hβ2per
  exact measure_inter_ne_zero_eq_zero inferInstance (hβc.pow 2) (fun x => sq_nonneg _)
    (B := CB) (fun x => (le_abs_self _).trans (hCB x)) hK0 hK hN

end Bound

end ComplexSLE.Internal

end
