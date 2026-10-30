/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.Nu
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The integral (II)
-/

@[expose] public section

open Real


namespace ComplexSLE

/-- The integral (II) `= ∫₀^{2π} (ν(u) + 2 cos 2u) p(u) du` of Theorem 1.8
(paper.tex:L441). -/
noncomputable def integralII (a b c : ℝ) (p : ℝ → ℝ) : ℝ :=
  ∫ u in (0)..(2 * π), (nu a b c u + 2 * cos (2 * u)) * p u

end ComplexSLE

end
