/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The drift µ
-/

@[expose] public section

open Real


namespace ComplexSLE

/-- `µ(u) = -(2 - a/2 + b/2) sin 2u - c cos 2u` (1.10), paper.tex:L424. -/
noncomputable def mu (a b c : ℝ) (u : ℝ) : ℝ :=
  -(2 - a / 2 + b / 2) * sin (2 * u) - c * cos (2 * u)

end ComplexSLE

end
