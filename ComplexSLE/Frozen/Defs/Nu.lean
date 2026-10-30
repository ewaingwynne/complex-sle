/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The drift ν
-/

@[expose] public section

open Real


namespace ComplexSLE

/-- `ν(u) = (2 - a/2 + b/2) cos 2u - c sin 2u` (1.10), paper.tex:L425. -/
noncomputable def nu (a b c : ℝ) (u : ℝ) : ℝ :=
  (2 - a / 2 + b / 2) * cos (2 * u) - c * sin (2 * u)

end ComplexSLE

end
