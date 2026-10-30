/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.Nu
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The integral (I)
-/

@[expose] public section

open Real


namespace ComplexSLE

/-- The integral (I) `= ∫₀^{2π} ν(u) p(u) du` of Theorem 1.8 (paper.tex:L440). -/
noncomputable def integralI (a b c : ℝ) (p : ℝ → ℝ) : ℝ :=
  ∫ u in (0)..(2 * π), nu a b c u * p u

end ComplexSLE

end
