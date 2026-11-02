/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.Coefficients
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# The critical case `c² = ab`: the zero lattice of `D` (M10-R5a, part A)

For `0 < a`, `0 < b` and `c² = ab` the diffusion coefficient `D` of (1.10) is a multiple of
`sin²(u - x₀)`: with `β = betaCrit a c = √a sin u - (c/√a) cos u` one has `β u = R sin (u - x₀)`
(`R = √(a + c²/a) > 0`, `x₀ = arctan (c/a)`), and `D = β²/2`. Hence

* `exists_diffusionD_eq_mul_sin_sq`: `D(u) = (R²/2) sin²(u - x₀)` and `µ(x₀) ≠ 0`;
* `exists_zero_lattice_diffusionD`: `D` vanishes exactly on the lattice `x₀ + πℤ`, with
  `D''(x₀) > 0` (a double zero) and `µ(x₀) ≠ 0`.

These are the deterministic coefficient facts used by the occupation estimates
(`Occupation*.lean`): no time is spent at the zero lattice because of the drift `µ(x₀) ≠ 0`.
-/

public section

open Real

namespace ComplexSLE.Internal

variable {a b c : ℝ}

/-- In the critical case `β u = R sin (u - x₀)` for some `R > 0` (`R = √a √(1 + (c/a)²)`,
`x₀ = arctan (c/a)`). -/
theorem exists_betaCrit_eq_mul_sin (ha : 0 < a) :
    ∃ R x₀ : ℝ, 0 < R ∧ ∀ u, betaCrit a c u = R * sin (u - x₀) := by
  have hsa : √a ^ 2 = a := Real.sq_sqrt ha.le
  have hsa0 : 0 < √a := Real.sqrt_pos.mpr ha
  have e : c / √a = √a * (c / a) := by
    field_simp
    linear_combination (-c) * hsa
  have hs0 : 0 < √(1 + (c / a) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  refine ⟨√a * √(1 + (c / a) ^ 2), arctan (c / a), by positivity, fun u => ?_⟩
  rw [sin_sub, Real.sin_arctan, Real.cos_arctan]
  unfold betaCrit
  rw [e]
  generalize √(1 + (c / a) ^ 2) = s at hs0 ⊢
  generalize c / a = t
  field_simp

theorem hasDerivAt_mul_sin_sq_sub (k x₀ u : ℝ) :
    HasDerivAt (fun v => k * sin (v - x₀) ^ 2) (k * (2 * sin (u - x₀) * cos (u - x₀))) u := by
  have h := (((hasDerivAt_id u).sub_const x₀).sin.pow 2).const_mul k
  refine h.congr_deriv ?_
  simp only [id]
  norm_num

theorem hasDerivAt_mul_sin_cos_sub (k x₀ u : ℝ) :
    HasDerivAt (fun v => k * (2 * sin (v - x₀) * cos (v - x₀)))
      (k * (2 * (cos (u - x₀) ^ 2 - sin (u - x₀) ^ 2))) u := by
  have h := ((((hasDerivAt_id u).sub_const x₀).sin.const_mul 2).mul
    ((hasDerivAt_id u).sub_const x₀).cos).const_mul k
  refine h.congr_deriv ?_
  simp only [id]
  ring

/-- **`D` is a multiple of `sin²(u - x₀)` in the critical case.** For `0 < a`, `0 < b`, `c² = ab`
there are `R > 0` and `x₀` with `D(u) = (R²/2) sin²(u - x₀)` for all `u` (`β = R sin (· - x₀)`
and `D = β²/2`), and the drift `µ` does not vanish at `x₀`. -/
theorem exists_diffusionD_eq_mul_sin_sq (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a * b) :
    ∃ R x₀ : ℝ, 0 < R ∧ (∀ u, diffusionD a b c u = R ^ 2 / 2 * sin (u - x₀) ^ 2) ∧
      mu a b c x₀ ≠ 0 := by
  obtain ⟨R, x₀, hR, hβ⟩ := exists_betaCrit_eq_mul_sin (c := c) ha
  refine ⟨R, x₀, hR, fun v => ?_, ?_⟩
  · have := sq_betaCrit ha hc v (b := b)
    rw [hβ] at this
    linarith [mul_pow R (sin (v - x₀)) 2]
  · have h0 : betaCrit a c x₀ = 0 := by rw [hβ]; simp
    rw [mu_eq_of_betaCrit_eq_zero ha hb hc h0]
    have hc0 : c ≠ 0 := by
      rintro rfl
      have := mul_pos ha hb
      rw [zero_pow two_ne_zero] at hc
      linarith
    exact div_ne_zero (by intro h; apply hc0; linarith) (by positivity)

/-- **The zero lattice of `D` in the critical case.** For `0 < a`, `0 < b`, `c² = ab`, the
diffusion coefficient `D` vanishes exactly on `x₀ + πℤ`, has a nondegenerate double zero at `x₀`,
and the drift `µ` does not vanish at `x₀` (hence, by `π`-periodicity, at any zero of `D`). -/
theorem exists_zero_lattice_diffusionD (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a * b) :
    ∃ x₀ : ℝ, (∀ u, diffusionD a b c u = 0 ↔ ∃ n : ℤ, u = x₀ + n * π) ∧
      0 < deriv (deriv (diffusionD a b c)) x₀ ∧ mu a b c x₀ ≠ 0 := by
  obtain ⟨R, x₀, hR, hD, hμ⟩ := exists_diffusionD_eq_mul_sin_sq ha hb hc
  have hD' : diffusionD a b c = fun v => R ^ 2 / 2 * sin (v - x₀) ^ 2 := funext hD
  refine ⟨x₀, fun u => ?_, ?_, hμ⟩
  · rw [hD]
    simp only [mul_eq_zero, pow_eq_zero_iff two_ne_zero, div_eq_zero_iff, OfNat.ofNat_ne_zero,
      or_false, hR.ne', false_or, Real.sin_eq_zero_iff]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by linarith⟩
  · have h1 : deriv (diffusionD a b c) =
        fun v => R ^ 2 / 2 * (2 * sin (v - x₀) * cos (v - x₀)) := by
      rw [hD']; funext v
      exact (hasDerivAt_mul_sin_sq_sub _ _ v).deriv
    rw [h1, (hasDerivAt_mul_sin_cos_sub (R ^ 2 / 2) x₀ x₀).deriv]
    simp only [sub_self, sin_zero, cos_zero]
    positivity

end ComplexSLE.Internal

end
