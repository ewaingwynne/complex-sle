/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.PeriodicODE.DoubleZeroTaylor
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Algebra.Ring.Periodic

/-!
# Local data of `D / α` at a double zero of `D`

For `D` with a nondegenerate double zero at `0` and `α 0 > 0`, near `0`:
`α ≥ α 0 / 2`, `D ≥ c₁ y² > 0` for `y ≠ 0`, `α / D ≥ c / y²`, and the derivative of `D / α`
is `≥ -1/2`.
-/

public section

open Set Filter Topology Function

namespace ComplexSLE.Infrastructure

/-- The derivative `(D' α - D α') / α²` of `D / α`. -/
@[expose] noncomputable def ratioDeriv (α D : ℝ → ℝ) (u : ℝ) : ℝ :=
  (deriv D u * α u - D u * deriv α u) / α u ^ 2

theorem hasDerivAt_ratio {α D : ℝ → ℝ} (hα : Differentiable ℝ α) (hD : Differentiable ℝ D)
    {u : ℝ} (hu : α u ≠ 0) : HasDerivAt (fun u => D u / α u) (ratioDeriv α D u) u :=
  (hD u).hasDerivAt.div (hα u).hasDerivAt hu

/-- The derivative of a `T`-periodic function is `T`-periodic. -/
theorem periodic_deriv {f : ℝ → ℝ} {T : ℝ} (hf : Periodic f T) : Periodic (deriv f) T :=
  fun u => by
    have := deriv_comp_add_const (f := f) (a := T) (x := u)
    have h : (fun x => f (x + T)) = f := funext hf
    rw [h] at this
    exact this.symm

theorem exists_local_data {α D : ℝ → ℝ} (hα : ContDiff ℝ 1 α) (hD : ContDiff ℝ 2 D)
    (hDz : D 0 = 0) (hD1 : deriv D 0 = 0) (hD2 : 0 < deriv (deriv D) 0) (hα0 : 0 < α 0) :
    ∃ δ > 0, ∃ c > 0, ∀ y ∈ Icc (-δ) δ, α 0 / 2 ≤ α y ∧ -(1 / 2) ≤ ratioDeriv α D y ∧
      (y ≠ 0 → 0 < D y ∧ c / y ^ 2 ≤ α y / D y) := by
  obtain ⟨δ₁, hδ₁, c₁, C₁, hc₁, hC₁, hDb⟩ := exists_sq_bounds hD hDz hD1 hD2
  obtain ⟨hDd, hDd2, -⟩ := contDiff_two_deriv_facts hD
  have hαc : Continuous α := hα.continuous
  have hαd' : Continuous (deriv α) := hα.continuous_deriv le_rfl
  have hrat : ContinuousAt (ratioDeriv α D) 0 := by
    unfold ratioDeriv
    refine ContinuousAt.div (ContinuousAt.sub (ContinuousAt.mul hDd2.continuous.continuousAt
      hαc.continuousAt) (ContinuousAt.mul hDd.continuous.continuousAt hαd'.continuousAt))
      (ContinuousAt.pow hαc.continuousAt 2) (by positivity)
  have hrat0 : ratioDeriv α D 0 = 0 := by simp [ratioDeriv, hDz, hD1]
  have hev : ∀ᶠ y in 𝓝 (0 : ℝ), α 0 / 2 < α y ∧ -(1 / 2) < ratioDeriv α D y := by
    refine Filter.Eventually.and (hαc.continuousAt.eventually (lt_mem_nhds (by linarith))) ?_
    exact hrat.eventually (lt_mem_nhds (by rw [hrat0]; norm_num))
  obtain ⟨δ₂, hδ₂, hP⟩ := exists_Icc_of_eventually_nhds_zero hev
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, α 0 / 2 / C₁, by positivity, fun y hy => ?_⟩
  have hy₁ : y ∈ Icc (-δ₁) δ₁ := ⟨hy.1.trans' (neg_le_neg (min_le_left _ _)),
    hy.2.trans (min_le_left _ _)⟩
  have hy₂ : y ∈ Icc (-δ₂) δ₂ := ⟨hy.1.trans' (neg_le_neg (min_le_right _ _)),
    hy.2.trans (min_le_right _ _)⟩
  refine ⟨(hP y hy₂).1.le, (hP y hy₂).2.le, fun hy0 => ?_⟩
  have hypos : 0 < y ^ 2 := by positivity
  have hDy : 0 < D y := lt_of_lt_of_le (by positivity) (hDb y hy₁).1
  refine ⟨hDy, ?_⟩
  have h1 : α 0 / 2 / (C₁ * y ^ 2) ≤ α y / D y :=
    div_le_div₀ (by linarith [(hP y hy₂).1]) (hP y hy₂).1.le hDy (hDb y hy₁).2
  rwa [div_div]

end ComplexSLE.Infrastructure

end
