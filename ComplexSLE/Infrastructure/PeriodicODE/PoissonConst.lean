/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.PeriodicODE.PoissonMax
public import ComplexSLE.Infrastructure.Primitive
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The periodic Poisson equation from first-order periodic solutions

If `h` is a `C¹` `T`-periodic solution of `D h' + α h = f` with `∫₀ᵀ h = 0`, then the primitive
`g = ∫₀ˣ h` is a `C²` periodic solution of `α g' + D g'' = f`.

Given periodic `C¹` solutions `h₁` of `D h' + α h = 1` and `hr` of `D h' + α h = r`, the mean of
`h₁` is nonzero by the maximum principle (`PoissonMax`), and `h = hr - C h₁` with
`C = ∫ hr / ∫ h₁` has mean zero. This gives the periodic Poisson equation
`α g' + D g'' = r - C`.
-/

public section

open Set Filter Topology MeasureTheory intervalIntegral Function
open scoped ContDiff

namespace ComplexSLE.Infrastructure

/-- The primitive `x ↦ ∫₀ˣ h` of a continuous mean-zero `T`-periodic function is `T`-periodic. -/
theorem periodic_integral_of_integral_eq_zero {h : ℝ → ℝ} {T : ℝ} (hc : Continuous h)
    (hper : Periodic h T) (h0 : ∫ u in (0)..T, h u = 0) :
    Periodic (fun x => ∫ u in (0)..x, h u) T := by
  intro x
  have := hper.intervalIntegral_add_eq_add 0 x (fun _ _ => hc.intervalIntegrable _ _)
  simp only [zero_add] at this
  simp only [this, h0, add_zero]

/-- The primitive `x ↦ ∫₀ˣ h` of a `C¹` function is `C²`, with derivative `h`. -/
theorem contDiff_two_integral_of_contDiff_one {h : ℝ → ℝ} (hc : ContDiff ℝ 1 h) :
    ContDiff ℝ 2 (fun x => ∫ u in (0)..x, h u) := by
  have hd : ∀ x, HasDerivAt (fun x => ∫ u in (0)..x, h u) (h x) x := fun x =>
    hasDerivAt_integral_of_continuous hc.continuous 0 x
  have hderiv : deriv (fun x => ∫ u in (0)..x, h u) = h := funext fun x => (hd x).deriv
  have h2 : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
  rw [h2, contDiff_succ_iff_deriv]
  refine ⟨fun x => (hd x).differentiableAt, by simp, ?_⟩
  rw [hderiv]
  exact hc

/-- A `C¹` periodic mean-zero solution of `D h' + α h = f` is the derivative of a `C²` periodic
solution of `α g' + D g'' = f`. -/
theorem exists_periodic_poisson_of_mean_zero {α D f h : ℝ → ℝ} {T : ℝ} (hc : ContDiff ℝ 1 h)
    (hper : Periodic h T) (h0 : ∫ u in (0)..T, h u = 0)
    (heq : ∀ u, D u * deriv h u + α u * h u = f u) :
    ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ Periodic g T ∧
      ∀ u, α u * deriv g u + D u * deriv (deriv g) u = f u := by
  refine ⟨fun x => ∫ u in (0)..x, h u, contDiff_two_integral_of_contDiff_one hc,
    periodic_integral_of_integral_eq_zero hc.continuous hper h0, fun u => ?_⟩
  have hderiv : deriv (fun x => ∫ u in (0)..x, h u) = h :=
    funext fun x => (hasDerivAt_integral_of_continuous hc.continuous 0 x).deriv
  rw [hderiv, ← heq u]
  ring

/-- From periodic `C¹` solutions of `D h' + α h = r` and of `D h' + α h = 1` to the periodic
Poisson equation `α g' + D g'' = r - C`. -/
theorem exists_periodic_poisson_of_solutions {α D r h₁ hr : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hD : ∀ u, 0 ≤ D u) (h₁c : ContDiff ℝ 1 h₁) (h₁per : Function.Periodic h₁ T)
    (h₁eq : ∀ u, D u * deriv h₁ u + α u * h₁ u = 1) (hrc : ContDiff ℝ 1 hr)
    (hrper : Function.Periodic hr T) (hreq : ∀ u, D u * deriv hr u + α u * hr u = r u) :
    ∃ C : ℝ, ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ Function.Periodic g T ∧
      ∀ u, α u * deriv g u + D u * deriv (deriv g) u = r u - C := by
  have hI : ∫ u in (0)..T, h₁ u ≠ 0 := by
    intro h0
    obtain ⟨g, hgc, hgper, hg⟩ :=
      exists_periodic_poisson_of_mean_zero (f := fun _ => (1 : ℝ)) h₁c h₁per h0 h₁eq
    exact one_ne_zero (eq_zero_of_periodic_generator_eq_const hT hD hgc hgper hg)
  set C : ℝ := (∫ u in (0)..T, hr u) / ∫ u in (0)..T, h₁ u with hC
  have hhc : ContDiff ℝ 1 (fun u => hr u - C * h₁ u) := hrc.sub (contDiff_const.mul h₁c)
  have hhper : Periodic (fun u => hr u - C * h₁ u) T := fun u => by
    simp only [hrper u, h₁per u]
  have hmean : ∫ u in (0)..T, (hr u - C * h₁ u) = 0 := by
    have hi1 : IntervalIntegrable hr volume 0 T := hrc.continuous.intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun u => C * h₁ u) volume 0 T :=
      (continuous_const.mul h₁c.continuous).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul, hC,
      div_mul_cancel₀ _ hI, sub_self]
  have hderiv : ∀ u, deriv (fun u => hr u - C * h₁ u) u = deriv hr u - C * deriv h₁ u := by
    intro u
    have h1 : DifferentiableAt ℝ hr u := (hrc.differentiable (by norm_num)) u
    have h2 : DifferentiableAt ℝ h₁ u := (h₁c.differentiable (by norm_num)) u
    exact (h1.hasDerivAt.sub (h2.hasDerivAt.const_mul C)).deriv
  obtain ⟨g, hgc, hgper, hg⟩ := exists_periodic_poisson_of_mean_zero (α := α) (D := D)
    (f := fun u => r u - C) hhc hhper hmean (fun u => by
      rw [hderiv u, ← hreq u]
      have := h₁eq u
      linear_combination (-C) * this)
  exact ⟨C, g, hgc, hgper, hg⟩

end ComplexSLE.Infrastructure

end
