/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.LeftRightNhds

/-!
# L'Hôpital's rule, `∞/∞` form, at a left-sided limit

Mathlib only provides the `0/0` forms of L'Hôpital's rule. We prove the one-sided `∞/∞` form
needed for the degenerate admissible density: if `g → +∞` as `u ↑ b` and `f'/g' → l`, then
`f/g → l`. The proof is the classical Cauchy mean value argument.
-/

public section

open Set Filter Topology

namespace ComplexSLE.Infrastructure

/-- **L'Hôpital's rule** (`∞/∞` form) at the right endpoint of an interval, approached from
the left. Only the denominator is required to diverge. -/
theorem lhopital_atTop_left_on_Ioo {a b l : ℝ} {f f' g g' : ℝ → ℝ} (hab : a < b)
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Ioo a b, g' x ≠ 0) (hgb : Tendsto g (𝓝[<] b) atTop)
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[<] b) (𝓝 l)) :
    Tendsto (fun x => f x / g x) (𝓝[<] b) (𝓝 l) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  -- a point `c` beyond which the derivative ratio is within `ε/2` of `l`
  have h1 : ∀ᶠ x in 𝓝[<] b, dist (f' x / g' x) l < ε / 2 :=
    (Metric.tendsto_nhds.1 hdiv) _ hε2
  obtain ⟨c, hc, hcb, hcIoo⟩ : ∃ c, a < c ∧ c < b ∧
      ∀ x ∈ Ioo c b, dist (f' x / g' x) l < ε / 2 := by
    have h2 : ∀ᶠ x in 𝓝[<] b, x ∈ Ioo a b := Ioo_mem_nhdsLT hab
    obtain ⟨c, hc, hcs⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 (h1.and h2)
    have hc' : c < b := hc
    have hmax : max a c < b := max_lt hab hc'
    refine ⟨(max a c + b) / 2, by linarith [le_max_left a c], by linarith, fun x hx => ?_⟩
    exact (hcs ⟨by linarith [hx.1, le_max_right a c], hx.2⟩).1
  set r0 : ℝ := |l| + ε / 2 with hr0
  set M : ℝ := |f c| + r0 * |g c| with hM
  have hM0 : 0 ≤ M := by positivity
  have h3 : ∀ᶠ x in 𝓝[<] b, M / (ε / 2) + 1 ≤ g x := hgb.eventually_ge_atTop _
  have h4 : ∀ᶠ x in 𝓝[<] b, x ∈ Ioo c b := Ioo_mem_nhdsLT hcb
  filter_upwards [h3, h4] with u hgu hu
  have hgu_pos : 0 < g u := by
    have : 0 ≤ M / (ε / 2) := by positivity
    linarith
  -- Cauchy mean value theorem on `[c, u]`
  have hsub : Ioo c u ⊆ Ioo a b := Ioo_subset_Ioo hc.le hu.2.le
  have hsub' : Icc c u ⊆ Ioo a b := Icc_subset_Ioo hc hu.2
  obtain ⟨ξ, hξ, hξeq⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f f' hu.1
    (HasDerivAt.continuousOn fun x hx => hff' x (hsub' hx)) (fun x hx => hff' x (hsub hx)) g g'
    (HasDerivAt.continuousOn fun x hx => hgg' x (hsub' hx)) (fun x hx => hgg' x (hsub hx))
  have hξab : ξ ∈ Ioo a b := hsub hξ
  have hξcb : ξ ∈ Ioo c b := ⟨hξ.1, hξ.2.trans hu.2⟩
  have hg'ξ : g' ξ ≠ 0 := hg' ξ hξab
  set r : ℝ := f' ξ / g' ξ with hr
  have hrl : |r - l| < ε / 2 := by simpa [Real.dist_eq] using hcIoo ξ hξcb
  have hkey : f u = f c + r * (g u - g c) := by
    have : f u - f c = r * (g u - g c) := by
      rw [hr, div_mul_eq_mul_div, eq_div_iff hg'ξ]
      linear_combination -hξeq
    linarith
  have hrabs : |r| ≤ r0 := by
    rw [hr0]
    have := abs_sub_abs_le_abs_sub r l
    linarith
  have hnum : |f c - r * g c| ≤ M := by
    rw [hM]
    calc |f c - r * g c| ≤ |f c| + |r * g c| := abs_sub _ _
      _ = |f c| + |r| * |g c| := by rw [abs_mul]
      _ ≤ |f c| + r0 * |g c| := by gcongr
  have hdecomp : f u / g u - l = (f c - r * g c) / g u + (r - l) := by
    rw [hkey]; field_simp; ring
  have hfrac : |(f c - r * g c) / g u| < ε / 2 := by
    rw [abs_div, abs_of_pos hgu_pos, div_lt_iff₀ hgu_pos]
    calc |f c - r * g c| ≤ M := hnum
      _ = ε / 2 * (M / (ε / 2)) := by field_simp
      _ < ε / 2 * g u := by
        apply mul_lt_mul_of_pos_left _ hε2
        linarith
  rw [Real.dist_eq, hdecomp]
  calc |(f c - r * g c) / g u + (r - l)| ≤ |(f c - r * g c) / g u| + |r - l| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hfrac hrl
    _ = ε := by ring

end ComplexSLE.Infrastructure

end
