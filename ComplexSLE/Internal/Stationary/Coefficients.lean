/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Density.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Lemma 2.14: the diffusion coefficient of the one-noise SDE for `θ̂`

The deterministic coefficient facts used when Lemma A.1 is applied to `θ̂` with `α = µ` and
`β² = 2D` (paper.tex:L986-993, `step:D-structure`, `step:stat-apply-kolmogorov-noncritical`,
`step:stat-apply-kolmogorov-critical`):

* noncritical case `c² < ab`: `β = √(2D)` is smooth, `β² = 2D`, and `β` never vanishes, so the
  Hörmander condition (A.1) holds trivially;
* critical case `c² = ab`: `β(u) = √a sin u - (c/√a) cos u` (the paper's `√a sin u ∓ √b cos u`
  for `c = ±√(ab)`) is smooth with `β² = 2D`, and at every zero of `β` one has
  `β'(u) µ(u) ≠ 0` (indeed `µ(u) = -4c/(a+b)` there), so (A.1) holds.

Together with `mu_periodic` and `diffusionD_periodic` these are exactly the coefficient
hypotheses of `External.hormander_oneDim` and of `IsAdmissibleDensity.isKolmogorovDensity`.
-/

public section

open Real
open scoped ContDiff

namespace ComplexSLE.Internal

variable {a b c : ℝ}

/-! ### Noncritical case: `β = √(2D)` -/

theorem contDiff_sqrt_two_mul_diffusionD (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 < a * b) :
    ContDiff ℝ ∞ fun u => √(2 * diffusionD a b c u) :=
  (contDiff_const.mul (contDiff_diffusionD a b c)).sqrt fun u => by
    have := diffusionD_pos ha hb hc u; positivity

theorem sq_sqrt_two_mul_diffusionD (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b) (u : ℝ) :
    √(2 * diffusionD a b c u) ^ 2 = 2 * diffusionD a b c u :=
  Real.sq_sqrt (by have := diffusionD_nonneg ha hb hc u; positivity)

theorem sqrt_two_mul_diffusionD_ne_zero (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 < a * b) (u : ℝ) :
    √(2 * diffusionD a b c u) ≠ 0 :=
  (Real.sqrt_pos.mpr (by have := diffusionD_pos ha hb hc u; positivity)).ne'

/-- The Hörmander condition (A.1) in the noncritical case: `β = √(2D)` never vanishes. -/
theorem hormander_sqrt_two_mul_diffusionD (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 < a * b) (u : ℝ) :
    √(2 * diffusionD a b c u) ≠ 0 ∨
      deriv (fun u => √(2 * diffusionD a b c u)) u * mu a b c u ≠ 0 :=
  Or.inl (sqrt_two_mul_diffusionD_ne_zero ha hb hc u)

/-- `β² = 2D` is `π`-periodic (for any `β` with `β² = 2D`). -/
theorem sq_periodic_of_sq_eq_two_mul_diffusionD {β : ℝ → ℝ}
    (hβ : ∀ u, β u ^ 2 = 2 * diffusionD a b c u) (u : ℝ) : β (u + π) ^ 2 = β u ^ 2 := by
  rw [hβ, hβ, diffusionD_periodic a b c u]

/-! ### Critical case `c² = ab`: `β(u) = √a sin u - (c/√a) cos u` -/

/-- The diffusion coefficient of (2.31): `√a sin u ∓ √b cos u` for `c = ±√(ab)`, written as
`√a sin u - (c/√a) cos u` (note `c/√a = ±√b` when `c² = ab`). -/
@[expose] noncomputable def betaCrit (a c : ℝ) (u : ℝ) : ℝ := √a * sin u - c / √a * cos u

theorem contDiff_betaCrit (a c : ℝ) : ContDiff ℝ ∞ (betaCrit a c) := by
  unfold betaCrit; fun_prop

theorem hasDerivAt_betaCrit (a c u : ℝ) :
    HasDerivAt (betaCrit a c) (√a * cos u + c / √a * sin u) u := by
  have h := ((hasDerivAt_sin u).const_mul (√a)).sub ((hasDerivAt_cos u).const_mul (c / √a))
  have e : √a * cos u + c / √a * sin u = √a * cos u - c / √a * -sin u := by ring
  rw [e]
  exact h

theorem deriv_betaCrit (a c u : ℝ) : deriv (betaCrit a c) u = √a * cos u + c / √a * sin u :=
  (hasDerivAt_betaCrit a c u).deriv

/-- `β² = 2D` in the critical case (`step:D-structure`). -/
theorem sq_betaCrit (ha : 0 < a) (hc : c ^ 2 = a * b) (u : ℝ) :
    betaCrit a c u ^ 2 = 2 * diffusionD a b c u := by
  have hsa : √a ^ 2 = a := Real.sq_sqrt ha.le
  have hsa0 : √a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have e : c / √a * √a = c := div_mul_cancel₀ c hsa0
  have e2 : (c / √a) ^ 2 = b := by
    rw [div_pow, hsa, hc, mul_div_cancel_left₀ b ha.ne']
  unfold betaCrit diffusionD
  linear_combination sin u ^ 2 * hsa - 2 * sin u * cos u * e + cos u ^ 2 * e2

/-- At a zero of `β`, `a sin u = c cos u`. -/
theorem a_mul_sin_eq_of_betaCrit_eq_zero (ha : 0 < a) {u : ℝ} (h0 : betaCrit a c u = 0) :
    a * sin u = c * cos u := by
  have hsa : √a ^ 2 = a := Real.sq_sqrt ha.le
  have hsa0 : √a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have e : c / √a * √a = c := div_mul_cancel₀ c hsa0
  unfold betaCrit at h0
  linear_combination √a * h0 - sin u * hsa + cos u * e

/-- At a zero of `β` (critical case), `(a + b) cos² u = a`. -/
theorem cos_sq_of_betaCrit_eq_zero (ha : 0 < a) (hc : c ^ 2 = a * b) {u : ℝ}
    (h0 : betaCrit a c u = 0) : (a + b) * cos u ^ 2 = a := by
  have h1 := a_mul_sin_eq_of_betaCrit_eq_zero ha h0
  have hsc := sin_sq_add_cos_sq u
  have h : a * (a * sin u ^ 2 - b * cos u ^ 2) = 0 := by
    linear_combination (a * sin u + c * cos u) * h1 + cos u ^ 2 * hc
  have h' : a * sin u ^ 2 - b * cos u ^ 2 = 0 :=
    (mul_eq_zero.mp h).resolve_left ha.ne'
  linear_combination a * hsc - h'

/-- At a zero of `β` (critical case), `(a + b) sin u cos u = c`. -/
theorem sin_mul_cos_of_betaCrit_eq_zero (ha : 0 < a) (hc : c ^ 2 = a * b) {u : ℝ}
    (h0 : betaCrit a c u = 0) : (a + b) * (sin u * cos u) = c := by
  have h1 := a_mul_sin_eq_of_betaCrit_eq_zero ha h0
  have h2 := cos_sq_of_betaCrit_eq_zero ha hc h0
  have h : a * ((a + b) * (sin u * cos u) - c) = 0 := by
    linear_combination (a + b) * cos u * h1 + c * h2
  linear_combination (mul_eq_zero.mp h).resolve_left ha.ne'

/-- At a zero of `β`, `µ(u) = -4c/(a+b)` (paper.tex:L993: `µ β' = ∓4√(ab/(a+b))` there). -/
theorem mu_eq_of_betaCrit_eq_zero (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a * b) {u : ℝ}
    (h0 : betaCrit a c u = 0) : mu a b c u = -4 * c / (a + b) := by
  have hab : a + b ≠ 0 := by positivity
  have h2 := cos_sq_of_betaCrit_eq_zero ha hc h0
  have h3 := sin_mul_cos_of_betaCrit_eq_zero ha hc h0
  rw [eq_div_iff hab, mu, Real.sin_two_mul, Real.cos_two_mul]
  linear_combination (-(4 - a + b)) * h3 - 2 * c * h2

/-- At a zero of `β` (critical case), `β'(u) ≠ 0`. -/
theorem deriv_betaCrit_ne_zero_of_eq_zero (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a * b) {u : ℝ}
    (h0 : betaCrit a c u = 0) : deriv (betaCrit a c) u ≠ 0 := by
  rw [deriv_betaCrit]
  intro hzero
  have hsa : √a ^ 2 = a := Real.sq_sqrt ha.le
  have hsa0 : √a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have e : c / √a * √a = c := div_mul_cancel₀ c hsa0
  have h4 : a * cos u + c * sin u = 0 := by
    linear_combination √a * hzero - cos u * hsa - sin u * e
  have h2 := cos_sq_of_betaCrit_eq_zero ha hc h0
  have h3 := sin_mul_cos_of_betaCrit_eq_zero ha hc h0
  have h5 : a * (a + b) = 0 := by
    linear_combination -a * h2 - c * h3 + (a + b) * cos u * h4 - hc
  exact (mul_pos ha (by positivity)).ne' h5

/-- The Hörmander condition (A.1) in the critical case `c² = ab`
(`step:stat-apply-kolmogorov-critical`). -/
theorem hormander_betaCrit (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a * b) (u : ℝ) :
    betaCrit a c u ≠ 0 ∨ deriv (betaCrit a c) u * mu a b c u ≠ 0 := by
  by_cases h0 : betaCrit a c u = 0
  · right
    have hc0 : c ≠ 0 := by
      rintro rfl
      have := mul_pos ha hb
      rw [zero_pow two_ne_zero] at hc
      linarith
    have hab : a + b ≠ 0 := by positivity
    refine mul_ne_zero (deriv_betaCrit_ne_zero_of_eq_zero ha hb hc h0) ?_
    rw [mu_eq_of_betaCrit_eq_zero ha hb hc h0]
    exact div_ne_zero (by intro h; apply hc0; linarith) hab
  · exact Or.inl h0

end ComplexSLE.Internal

end
