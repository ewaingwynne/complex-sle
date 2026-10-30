/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.LeftHull
import ComplexSLE.Internal.Reflection_LeftHull

/-!
# Reflection property (2.2) for left hulls
-/

public section

open scoped NNReal ComplexConjugate

namespace ComplexSLE

/-- **Reflection property (2.2), left hulls** (paper.tex:L553-557):
`L^{U*}_t = (L^U_t)*` and `L^{-U}_t = -L^U_t`. -/
theorem reflection_leftHull (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) :
    leftHull (fun s => conj (U s)) t = conj '' leftHull U t ∧
      leftHull (fun s => -U s) t = Neg.neg '' leftHull U t :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ComplexSLE.Internal.reflection_leftHull U hU t
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE

end
-- FROZEN_ANCHOR_SUFFIX_END
