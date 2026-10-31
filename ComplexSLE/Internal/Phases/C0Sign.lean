/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.C0Density

/-!
# The case `c = 0`: the sign of `∫₀^{2π} cos(2u) p(u) du`

Deterministic part of Lemma 3.11 (`lem-c0-phases`, paper.tex:L1824-1910), the claim
`eqn-c0-phase-show`: `∫₀^{2π} cos(2u) p(u) du > 0` for the density (3.30), hence for every
admissible density for `c = 0`.

The explicit density depends on `u` only through `cos 2u`: `c0Shape a b u = c0F a b (cos 2u)` with
`c0F a b t = (a + b + (b - a) t)^{4/(b-a)}` (`a ≠ b`) or `exp ((2/a)(1 + t))` (`a = b`). The three
cases `a < b`, `a > b`, `a = b` of the source are exactly the three cases of the strict inequality
`c0F a b (-t) < c0F a b t` for `0 < t ≤ 1` (`eqn-cos-reflect`). The reduction to `[0, π/4]` uses
`π`-periodicity, the symmetry `u ↦ π - u`, and the reflection `u ↦ π/2 - u` across `π/4`
(`integral_pos_of_symm`).
-/

@[expose] public section

open Set Filter Topology MeasureTheory intervalIntegral Function Real

namespace ComplexSLE.Internal

variable {a b : ℝ}

/-! ### Reduction to `[0, π/4]` -/

/-- A continuous `π`-periodic `f` with `f (π - u) = f u` whose reflection sum
`f u + f (π/2 - u)` is positive on `(0, π/4)` has positive integral over `[0, 2π]`. -/
theorem integral_pos_of_symm {f : ℝ → ℝ} (hcont : Continuous f) (hper : Periodic f π)
    (hsym : ∀ u, f (π - u) = f u) (hpos : ∀ u ∈ Ioo 0 (π / 4), 0 < f u + f (π / 2 - u)) :
    0 < ∫ u in (0)..(2 * π), f u := by
  have hint : ∀ x y, IntervalIntegrable f volume x y := hcont.intervalIntegrable
  have hrefl : Continuous fun u => f (π / 2 - u) := by fun_prop
  -- `∫₀^{2π} = 2 ∫₀^π` by periodicity
  have h1 : ∫ u in (0)..(2 * π), f u = 2 * ∫ u in (0)..π, f u := by
    rw [← integral_add_adjacent_intervals (hint 0 π) (hint π (2 * π))]
    have : ∫ u in π..(2 * π), f u = ∫ u in (0)..π, f u := by
      have := hper.intervalIntegral_add_eq π 0
      rw [two_mul]
      simpa using this
    rw [this]; ring
  -- `∫₀^π = 2 ∫₀^{π/2}` by the symmetry `u ↦ π - u`
  have h2 : ∫ u in (0)..π, f u = 2 * ∫ u in (0)..(π / 2), f u := by
    rw [← integral_add_adjacent_intervals (hint 0 (π / 2)) (hint (π / 2) π)]
    have : ∫ u in (π / 2)..π, f u = ∫ u in (0)..(π / 2), f u := by
      have h := intervalIntegral.integral_comp_sub_left f (a := 0) (b := π / 2) π
      simp only [hsym] at h
      rw [h]
      congr 1 <;> ring
    rw [this]; ring
  -- `∫₀^{π/2} = ∫₀^{π/4} (f u + f (π/2 - u))` by the reflection across `π/4`
  have h3 : ∫ u in (0)..(π / 2), f u = ∫ u in (0)..(π / 4), (f u + f (π / 2 - u)) := by
    rw [intervalIntegral.integral_add (hint 0 (π / 4))
      (hrefl.intervalIntegrable 0 (π / 4)),
      ← integral_add_adjacent_intervals (hint 0 (π / 4)) (hint (π / 4) (π / 2))]
    congr 1
    have h := intervalIntegral.integral_comp_sub_left f (a := 0) (b := π / 4) (π / 2)
    rw [h]
    congr 1 <;> ring
  have h4 : 0 < ∫ u in (0)..(π / 4), (f u + f (π / 2 - u)) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      ((hcont.add hrefl).intervalIntegrable 0 (π / 4))
      hpos (by positivity)
  rw [h1, h2, h3]
  linarith

/-! ### The monotone profile -/

/-- The density (3.30) as a function of `t = cos 2u`. -/
noncomputable def c0F (a b t : ℝ) : ℝ :=
  if a = b then exp (2 / a * (1 + t)) else (a + b + (b - a) * t) ^ (4 / (b - a))

theorem c0Shape_eq_c0F (a b u : ℝ) : c0Shape a b u = c0F a b (cos (2 * u)) := by
  unfold c0Shape c0F
  split_ifs
  · congr 1
    rw [cos_two_mul]
    ring
  · rfl

/-- `eqn-cos-reflect` and the three-case comparison of the source: `c0F a b (-t) < c0F a b t`
for `0 < t ≤ 1`. -/
theorem c0F_neg_lt (ha : 0 < a) (hb : 0 < b) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    c0F a b (-t) < c0F a b t := by
  unfold c0F
  by_cases hab : a = b
  · simp only [hab, ite_true]
    subst hab
    apply exp_lt_exp.2
    have : 0 < 2 / a := by positivity
    nlinarith
  · simp only [hab, ite_false]
    have hpos : 0 < a + b + (b - a) * t := base_pos_of_mem_Icc ha hb (by linarith) ht1
    have hneg : 0 < a + b + (b - a) * -t :=
      base_pos_of_mem_Icc ha hb (by linarith) (by linarith)
    rcases lt_or_gt_of_ne hab with h | h
    · -- `a < b`: positive exponent, increasing base
      have hba : 0 < b - a := sub_pos.2 h
      apply rpow_lt_rpow hneg.le _ (by positivity)
      nlinarith [mul_pos hba ht]
    · -- `a > b`: negative exponent, decreasing base
      have hba : b - a < 0 := sub_neg.2 h
      apply rpow_lt_rpow_of_neg hpos _ (div_neg_of_pos_of_neg (by norm_num) hba)
      nlinarith [mul_pos (neg_pos.2 hba) ht]

/-! ### The integral -/

/-- `∫₀^{2π} cos(2u) · c0Shape a b u du > 0` (`eqn-c0-phase-show` for the explicit density). -/
theorem integral_cos_mul_c0Shape_pos (ha : 0 < a) (hb : 0 < b) :
    0 < ∫ u in (0)..(2 * π), cos (2 * u) * c0Shape a b u := by
  have hcont : Continuous fun u => cos (2 * u) * c0Shape a b u :=
    (by fun_prop : Continuous fun u : ℝ => cos (2 * u)).mul (continuous_c0Shape ha hb)
  refine integral_pos_of_symm hcont ?_ ?_ ?_
  · intro u
    simp only [c0Shape_periodic a b u]
    rw [show 2 * (u + π) = 2 * u + 2 * π by ring, cos_add_two_pi]
  · intro u
    simp only [c0Shape_eq_c0F]
    rw [show 2 * (π - u) = 2 * π - 2 * u by ring, cos_two_pi_sub]
  · intro u hu
    obtain ⟨hu0, hu1⟩ := hu
    simp only [c0Shape_eq_c0F]
    have h2 : 2 * (π / 2 - u) = π - 2 * u := by ring
    rw [h2, cos_pi_sub]
    have hc : 0 < cos (2 * u) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have hc1 : cos (2 * u) ≤ 1 := cos_le_one _
    have := c0F_neg_lt ha hb hc hc1
    nlinarith

/-- **Lemma 3.11, `eqn-c0-phase-show`**: for `a, b > 0` and every admissible density `p` for
`c = 0`, `∫₀^{2π} cos(2u) p(u) du > 0`. -/
theorem integral_cos_mul_pos (ha : 0 < a) (hb : 0 < b) {p : ℝ → ℝ}
    (hp : IsAdmissibleDensity a b 0 p) : 0 < ∫ u in (0)..(2 * π), cos (2 * u) * p u := by
  rw [IsAdmissibleDensity.eq_c0Shape_div ha hb hp]
  have : (fun u => cos (2 * u) * (c0Shape a b u / ∫ v in (0)..(2 * π), c0Shape a b v)) =
      fun u => (cos (2 * u) * c0Shape a b u) / ∫ v in (0)..(2 * π), c0Shape a b v := by
    funext u; ring
  simp only [this]
  rw [intervalIntegral.integral_div]
  exact div_pos (integral_cos_mul_c0Shape_pos ha hb) (integral_c0Shape_pos ha hb)

end ComplexSLE.Internal

end
