/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.RightHull
import ComplexSLE.Internal.Reflection_RightHull

/-!
# Reflection property (2.2) for right hulls
-/

public section

open scoped NNReal ComplexConjugate

namespace ComplexSLE

/-- **Reflection property (2.2), right hulls** (paper.tex:L553-557, "the same is true with right
hulls"): `R_t^{U*} = (R_t^U)*` and `R_t^{-U} = -R_t^U`. -/
theorem reflection_rightHull (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) :
    rightHull (fun s => conj (U s)) (by fun_prop) t = conj '' rightHull U hU t ∧
      rightHull (fun s => -U s) (by fun_prop) t = Neg.neg '' rightHull U hU t :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE

end
-- FROZEN_ANCHOR_SUFFIX_END
