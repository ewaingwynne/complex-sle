/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Algebra.Field.Periodic
public import Mathlib.Topology.Order.Compact

/-!
# Maximum principle for periodic functions

A `C²` function `g` on `ℝ` with a `T`-periodic generator `α g' + D g''` (`D ≥ 0`) that is a
constant `C` has `C = 0`. At a maximum point `g' = 0` and `g'' ≤ 0`, so `C ≤ 0`; applying this
to `-g` gives `C ≥ 0`.
-/

public section

open Set Filter Topology Function
open scoped ContDiff

namespace ComplexSLE.Infrastructure

/-- A continuous `T`-periodic function attains its maximum. -/
theorem Periodic.exists_forall_le_of_continuous {g : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hg : Continuous g) (hper : Periodic g T) : ∃ x, ∀ y, g y ≤ g x := by
  obtain ⟨x, -, hx⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hT.le) hg.continuousOn
  refine ⟨x, fun y => ?_⟩
  obtain ⟨z, hz, hyz⟩ := hper.exists_mem_Ico₀ hT y
  rw [hyz]
  exact hx ⟨hz.1, hz.2.le⟩

/-- At a local maximum of a `C²` function the second derivative is nonpositive. -/
theorem deriv_deriv_nonpos_of_isLocalMax {g : ℝ → ℝ} {x : ℝ} (hg : ContDiff ℝ 2 g)
    (hmax : IsLocalMax g x) : deriv (deriv g) x ≤ 0 := by
  by_contra hpos'
  have hpos : 0 < deriv (deriv g) x := not_le.1 hpos'
  have hd : deriv g x = 0 := hmax.deriv_eq_zero
  have hmin : IsLocalMin g x :=
    isLocalMin_of_deriv_deriv_pos hpos hd hg.continuous.continuousAt
  have hconst : g =ᶠ[𝓝 x] fun _ => g x := by
    filter_upwards [hmax, hmin] with y h1 h2 using le_antisymm h1 h2
  have h1 : deriv g =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    simpa using hconst.deriv
  have h2 : deriv (deriv g) x = deriv (fun _ : ℝ => (0 : ℝ)) x := h1.deriv_eq
  rw [h2] at hpos
  simp at hpos

/-- If the generator of a periodic `C²` function is constant, the constant is `≤ 0`. -/
theorem le_zero_of_periodic_generator_eq_const {α D g : ℝ → ℝ} {T C : ℝ} (hT : 0 < T)
    (hD : ∀ u, 0 ≤ D u) (hg : ContDiff ℝ 2 g) (hgper : Periodic g T)
    (h : ∀ u, α u * deriv g u + D u * deriv (deriv g) u = C) : C ≤ 0 := by
  obtain ⟨x, hx⟩ := Periodic.exists_forall_le_of_continuous hT hg.continuous hgper
  have hmax : IsLocalMax g x := Filter.Eventually.of_forall hx
  have hd : deriv g x = 0 := hmax.deriv_eq_zero
  have h2 := deriv_deriv_nonpos_of_isLocalMax hg hmax
  rw [← h x, hd, mul_zero, zero_add]
  exact mul_nonpos_of_nonneg_of_nonpos (hD x) h2

/-- Maximum principle: a `C²` periodic `g` whose generator `α g' + D g''` (`D ≥ 0`) is a constant
`C` has `C = 0`. -/
theorem eq_zero_of_periodic_generator_eq_const {α D g : ℝ → ℝ} {T C : ℝ} (hT : 0 < T)
    (hD : ∀ u, 0 ≤ D u) (hg : ContDiff ℝ 2 g) (hgper : Function.Periodic g T)
    (h : ∀ u, α u * deriv g u + D u * deriv (deriv g) u = C) : C = 0 := by
  refine le_antisymm (le_zero_of_periodic_generator_eq_const hT hD hg hgper h) ?_
  have hneg : ∀ u, α u * deriv (fun x => -g x) u + D u * deriv (deriv (fun x => -g x)) u = -C := by
    intro u
    have e1 : deriv (fun x => -g x) = fun x => -deriv g x := funext fun x => deriv.fun_neg
    simp only [e1, deriv.fun_neg]
    have := h u
    linarith
  have hnegper : Periodic (fun x => -g x) T := fun x => by simp only [hgper x]
  have := le_zero_of_periodic_generator_eq_const hT hD hg.neg hnegper hneg
  linarith

end ComplexSLE.Infrastructure

end
