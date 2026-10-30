/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.LoewnerWellDefined
public import ComplexSLE.Frozen.Defs.LeftHull

/-!
# The Loewner map
-/

@[expose] public section

open scoped NNReal ENNReal

namespace ComplexSLE

/-- The Loewner map `g_t : ℂ ∖ L_t → ℂ` (Def 1.1, paper.tex:L251-263): `g_t(z)` is the value at
time `t` of the solution of `ġ = 2/(g - U)`, `g_0 = z`, on `[0, T_z)`. This is unique choice:
by `loewner_wellDefined` every solution on `[0, T_z)` has the same value at `t < T_z`. -/
noncomputable def loewnerMap (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0)
    (z : ↥(leftHull U t)ᶜ) : ℂ :=
  Classical.choose (loewner_wellDefined U hU z).1 t

end ComplexSLE

end
