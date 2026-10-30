/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.AbsorbingTime

/-!
# The left hull
-/

@[expose] public section

open scoped NNReal

namespace ComplexSLE

/-- The left hull `L_t = {z : T_z ≤ t}` (Def 1.2, paper.tex:L271-277). -/
def leftHull (U : ℝ≥0 → ℂ) (t : ℝ≥0) : Set ℂ :=
  {z | absorbingTime U z ≤ t}

end ComplexSLE

end
