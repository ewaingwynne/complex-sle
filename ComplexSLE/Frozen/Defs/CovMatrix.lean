/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Basic.Real.Basic

/-!
# The covariance matrix
-/

@[expose] public section


namespace ComplexSLE

/-- The covariance matrix `Σ = [[a, c], [c, b]]` (paper.tex:L304-306). -/
def covMatrix (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, c; c, b]

end ComplexSLE

end
