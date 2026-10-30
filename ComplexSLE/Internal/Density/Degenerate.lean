/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Density.Basic
public import ComplexSLE.Internal.Density.SingularODE
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Admissible densities, Case 2: `c² = ab`

For `c = √(ab) > 0` the diffusion coefficient is `D(u) = ((a+b)/2) sin²(u - x)` with
`x = arctan √(b/a)`, so `D` vanishes exactly on `x + πℤ`, `D'(x) = 0` and
`µ(x) = -4c/(a+b) < 0` (paper.tex:L1082-1105, (2.32)). We verify the hypotheses of the
abstract singular construction `SingularData.exists_solution` and normalise. The case
`c = -√(ab)` follows by the symmetry `u ↦ -u` (`IsAdmissibleDensity.neg_c`, ruling R19: the
degenerate point is then `-x`, i.e. `tan(-x) = sgn(c) √(b/a)`).
-/

public section

open Set Filter Topology MeasureTheory intervalIntegral Function Real
open scoped ContDiff

namespace ComplexSLE.Internal

variable {a b c : ℝ}

/-- **Lemma 2.13, Case 2** with `c = √(ab) > 0`. -/
theorem exists_admissibleDensity_of_sq_eq_of_pos (ha : 0 < a) (hb : 0 < b) (hcab : c ^ 2 = a * b)
    (hc0 : 0 < c) : ∃ p, IsAdmissibleDensity a b c p := by
  have hab : 0 < a + b := by linarith
  have hab0 : a + b ≠ 0 := hab.ne'
  -- square roots
  set A : ℝ := √a with hAdef
  set B : ℝ := √b with hBdef
  set R : ℝ := √(a + b) with hRdef
  have hA : A ^ 2 = a := sq_sqrt ha.le
  have hB : B ^ 2 = b := sq_sqrt hb.le
  have hR : R ^ 2 = a + b := sq_sqrt hab.le
  have hApos : 0 < A := sqrt_pos.2 ha
  have hBpos : 0 < B := sqrt_pos.2 hb
  have hRpos : 0 < R := sqrt_pos.2 hab
  have hc : c = A * B := by
    rw [hAdef, hBdef, ← sqrt_mul ha.le, ← hcab, sqrt_sq hc0.le]
  -- the degenerate point `x = arctan (B / A)`
  set x : ℝ := arctan (B / A) with hxdef
  have hsq : √(1 + (B / A) ^ 2) = R / A := by
    have h1 : 1 + (B / A) ^ 2 = (a + b) / a := by
      rw [div_pow, hB, hA]; field_simp
    rw [h1, sqrt_div hab.le]
  have hcosx : cos x = A / R := by
    rw [hxdef, cos_arctan, hsq, one_div_div]
  have hsinx : sin x = B / R := by
    rw [hxdef, sin_arctan, hsq]
    field_simp
  have hRc : R * cos x = A := by rw [hcosx]; field_simp
  have hRs : R * sin x = B := by rw [hsinx]; field_simp
  -- the formula `D u = (a+b)/2 · sin²(u - x)`
  have hDform : ∀ u, diffusionD a b c u = (a + b) / 2 * sin (u - x) ^ 2 := by
    intro u
    have hE : R * sin (u - x) = A * sin u - B * cos u := by
      rw [sin_sub]
      linear_combination (sin u) * hRc - (cos u) * hRs
    have hD : diffusionD a b c u = (A * sin u - B * cos u) ^ 2 / 2 := by
      simp only [diffusionD]
      linear_combination (-(sin u) ^ 2 / 2) * hA + (-(cos u) ^ 2 / 2) * hB +
        (-(cos u * sin u)) * hc
    rw [hD, ← hE]
    linear_combination (sin (u - x) ^ 2 / 2) * hR
  -- the value `µ x = -4c/(a+b)`
  have hs2 : sin (2 * x) = 2 * c / (a + b) := by
    rw [eq_div_iff hab0, sin_two_mul]
    linear_combination (-2 * sin x * cos x) * hR + (2 * R * cos x) * hRs + (2 * B) * hRc +
      (-2) * hc
  have hc2 : cos (2 * x) = (a - b) / (a + b) := by
    rw [eq_div_iff hab0, cos_two_mul']
    linear_combination (-(cos x ^ 2 - sin x ^ 2)) * hR + (R * cos x + A) * hRc -
      (R * sin x + B) * hRs + hA - hB
  have hμx : mu a b c x = -4 * c / (a + b) := by
    simp only [mu]
    rw [hs2, hc2]
    field_simp
    ring
  have hμx_neg : mu a b c x < 0 := by
    rw [hμx]
    exact div_neg_of_neg_of_pos (by linarith) hab
  -- derivative of `D`
  have hDderiv : ∀ u, HasDerivAt (diffusionD a b c) ((a + b) * sin (u - x) * cos (u - x)) u := by
    intro u
    have hDfun : diffusionD a b c = fun u => (a + b) / 2 * sin (u - x) ^ 2 := funext hDform
    have h := ((((hasDerivAt_id' u).sub_const x).sin).pow 2).const_mul ((a + b) / 2)
    rw [hDfun]
    convert h using 1
    simp
    ring
  have hD'x : deriv (diffusionD a b c) x = 0 := by
    rw [(hDderiv x).deriv, sub_self, sin_zero]
    ring
  -- continuity of `µ` near `x` and `x + π`
  have hμcont : Continuous (mu a b c) := continuous_mu a b c
  have hμy : mu a b c (x + π) = mu a b c x := mu_periodic a b c x
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.continuousAt_iff.1 (hμcont.continuousAt (x := x))
    (-mu a b c x / 2) (by linarith)
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuousAt_iff.1 (hμcont.continuousAt (x := x + π))
    (-mu a b c x / 2) (by linarith)
  have hμ_near_x : ∀ u, dist u x < δ₀ → mu a b c u ≤ mu a b c x / 2 := by
    intro u hu
    have := hδ₀' hu
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.2]
  have hμ_near_y : ∀ u, dist u (x + π) < δ₁ → mu a b c u ≤ mu a b c x / 2 := by
    intro u hu
    have := hδ₁' hu
    rw [Real.dist_eq, abs_lt, hμy] at this
    linarith [this.2]
  -- the key comparison
  set κ : ℝ := -mu a b c x / (a + b) with hκdef
  have hκ : 0 < κ := div_pos (by linarith) hab
  have hcomp : ∀ u t, 0 < t → mu a b c u ≤ mu a b c x / 2 → 0 < diffusionD a b c u →
      diffusionD a b c u ≤ (a + b) / 2 * t ^ 2 → mu a b c u / diffusionD a b c u ≤ -κ / t ^ 2 := by
    intro u t ht hμu hDu hDle
    rw [div_le_div_iff₀ hDu (pow_pos ht 2)]
    have e : -κ * diffusionD a b c u = mu a b c x * diffusionD a b c u / (a + b) := by
      rw [hκdef]; ring
    rw [e, le_div_iff₀ hab]
    have h1 : mu a b c u * t ^ 2 ≤ mu a b c x / 2 * t ^ 2 :=
      mul_le_mul_of_nonneg_right hμu (sq_nonneg _)
    have h2 : mu a b c x * ((a + b) / 2 * t ^ 2) ≤ mu a b c x * diffusionD a b c u :=
      mul_le_mul_of_nonpos_left hDle hμx_neg.le
    have h3 := mul_le_mul_of_nonneg_right h1 hab.le
    linarith
  -- the singular data
  have hdata : SingularData (mu a b c) (diffusionD a b c) x π :=
    { T_pos := pi_pos
      D_smooth := contDiff_diffusionD a b c
      μ_smooth := contDiff_mu a b c
      D_per := diffusionD_periodic a b c
      μ_per := mu_periodic a b c
      D_pos := by
        intro u hu
        rw [hDform]
        have : 0 < sin (u - x) := sin_pos_of_pos_of_lt_pi (by linarith [hu.1]) (by linarith [hu.2])
        positivity
      D_x := by rw [hDform, sub_self, sin_zero]; ring
      D'_x := hD'x
      μ_x := hμx_neg
      bound := by
        refine ⟨κ, hκ, min (min δ₀ δ₁) π, lt_min (lt_min hδ₀ hδ₁) pi_pos, ?_, ?_⟩
        · intro u hu
          have hδle : min (min δ₀ δ₁) π ≤ δ₀ := (min_le_left _ _).trans (min_le_left _ _)
          have hπle : min (min δ₀ δ₁) π ≤ π := min_le_right _ _
          have ht : 0 < u - x := sub_pos.2 hu.1
          have hμu : mu a b c u ≤ mu a b c x / 2 := hμ_near_x u (by
            rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hu.1, hu.2])
          have hDu : 0 < diffusionD a b c u := by
            rw [hDform]
            have : 0 < sin (u - x) :=
              sin_pos_of_pos_of_lt_pi ht (by linarith [hu.2])
            positivity
          have hDle : diffusionD a b c u ≤ (a + b) / 2 * (u - x) ^ 2 := by
            rw [hDform]
            exact mul_le_mul_of_nonneg_left sin_sq_le_sq (by positivity)
          exact hcomp u (u - x) ht hμu hDu hDle
        · intro u hu
          have hδle : min (min δ₀ δ₁) π ≤ δ₁ := (min_le_left _ _).trans (min_le_right _ _)
          have hπle : min (min δ₀ δ₁) π ≤ π := min_le_right _ _
          have ht : 0 < x + π - u := sub_pos.2 hu.2
          have hμu : mu a b c u ≤ mu a b c x / 2 := hμ_near_y u (by
            rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hu.1, hu.2])
          have hsin : sin (u - x) = sin (x + π - u) := by
            rw [show u - x = π - (x + π - u) by ring, sin_pi_sub]
          have hDu : 0 < diffusionD a b c u := by
            rw [hDform, hsin]
            have : 0 < sin (x + π - u) :=
              sin_pos_of_pos_of_lt_pi ht (by linarith [hu.1])
            positivity
          have hDle : diffusionD a b c u ≤ (a + b) / 2 * (x + π - u) ^ 2 := by
            rw [hDform, hsin]
            exact mul_le_mul_of_nonneg_left sin_sq_le_sq (by positivity)
          exact hcomp u (x + π - u) ht hμu hDu hDle
      D_low := by
        refine ⟨(a + b) / 2 * (2 / π) ^ 2, by positivity, π / 2, by positivity, ?_⟩
        intro u hu
        have ht : 0 < x + π - u := sub_pos.2 hu.2
        have ht' : x + π - u ≤ π / 2 := by linarith [hu.1]
        have hsin : sin (u - x) = sin (x + π - u) := by
          rw [show u - x = π - (x + π - u) by ring, sin_pi_sub]
        rw [hDform, hsin, mul_assoc, ← mul_pow]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (by positivity) (mul_le_sin ht.le ht') 2 }
  obtain ⟨p, hp_cont, hp_nonneg, hp_per, hp_pos, hp_smooth, hDp⟩ := hdata.exists_solution
  have pre : IsPreDensity a b c p x 1 :=
    { continuous := hp_cont
      nonneg := hp_nonneg
      periodic := hp_per
      integral_pos := Infrastructure.Periodic.integral_two_mul_pos pi_pos hp_per hp_cont hp_pos
      contDiffOn := hp_smooth
      hasDerivAt := hDp }
  exact pre.exists_isAdmissibleDensity

/-- **Lemma 2.13, Case 2** (`c² = ab`): an admissible density exists. -/
theorem exists_admissibleDensity_of_sq_eq (ha : 0 < a) (hb : 0 < b) (hcab : c ^ 2 = a * b) :
    ∃ p, IsAdmissibleDensity a b c p := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h] at hcab
    nlinarith [mul_pos ha hb]
  rcases hc0.lt_or_gt with hneg | hpos
  · obtain ⟨p, hp⟩ := exists_admissibleDensity_of_sq_eq_of_pos ha hb (c := -c)
      (by rw [neg_sq]; exact hcab) (by linarith)
    have := IsAdmissibleDensity.neg_c hp
    rw [neg_neg] at this
    exact ⟨_, this⟩
  · exact exists_admissibleDensity_of_sq_eq_of_pos ha hb hcab hpos

end ComplexSLE.Internal

end
