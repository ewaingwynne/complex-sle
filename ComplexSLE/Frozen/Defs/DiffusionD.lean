/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The diffusion coefficient D
-/

@[expose] public section

open Real


namespace ComplexSLE

/-- `D(u) = (a/2) sin² u + (b/2) cos² u - c cos u sin u` (1.10), paper.tex:L426. -/
noncomputable def diffusionD (a b c : ℝ) (u : ℝ) : ℝ :=
  a / 2 * sin u ^ 2 + b / 2 * cos u ^ 2 - c * cos u * sin u

end ComplexSLE

end
