/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Smoothness of primitives

Small calculus facts: a function whose derivative is `C^∞` (on an open set, or globally) is
`C^∞`; primitives `u ↦ ∫ₐᵘ g` of continuous functions are differentiable with derivative `g`.
-/

public section

open Set Filter Topology MeasureTheory intervalIntegral
open scoped ContDiff

namespace ComplexSLE.Infrastructure

/-- A function with a `C^∞` derivative on an open set is `C^∞` there. -/
theorem contDiffOn_infty_of_hasDerivAt {F g : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hF : ∀ u ∈ s, HasDerivAt F (g u) u) (hg : ContDiffOn ℝ ∞ g s) : ContDiffOn ℝ ∞ F s := by
  rw [contDiffOn_infty_iff_deriv_of_isOpen hs]
  refine ⟨fun u hu => (hF u hu).differentiableAt.differentiableWithinAt, ?_⟩
  exact hg.congr fun u hu => (hF u hu).deriv

/-- A function with a `C^∞` derivative is `C^∞`. -/
theorem contDiff_infty_of_hasDerivAt {F g : ℝ → ℝ} (hF : ∀ u, HasDerivAt F (g u) u)
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ F := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun u => (hF u).differentiableAt, ?_⟩
  have : deriv F = g := funext fun u => (hF u).deriv
  rw [this]; exact hg

/-- Derivative of a primitive of a continuous function. -/
theorem hasDerivAt_integral_of_continuous {g : ℝ → ℝ} (hg : Continuous g) (a u : ℝ) :
    HasDerivAt (fun v => ∫ s in a..v, g s) (g u) u :=
  (hg.integral_hasStrictDerivAt a u).hasDerivAt

/-- A primitive of a `C^∞` function is `C^∞`. -/
theorem contDiff_integral_of_contDiff {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (a : ℝ) :
    ContDiff ℝ ∞ (fun v => ∫ s in a..v, g s) :=
  contDiff_infty_of_hasDerivAt (hasDerivAt_integral_of_continuous hg.continuous a) hg

/-- Derivative of `u ↦ ∫ₐᵘ g` at a point of an open set on which `g` is continuous, provided
`g` is interval integrable between `a` and `u`. -/
theorem hasDerivAt_integral_right_of_continuousOn {g : ℝ → ℝ} {s : Set ℝ} {a u : ℝ}
    (hs : IsOpen s) (hg : ContinuousOn g s) (hu : u ∈ s)
    (hint : IntervalIntegrable g volume a u) :
    HasDerivAt (fun v => ∫ t in a..v, g t) (g u) u :=
  integral_hasDerivAt_right hint (hg.stronglyMeasurableAtFilter hs u hu)
    (hg.continuousAt (hs.mem_nhds hu))

end ComplexSLE.Infrastructure

end
