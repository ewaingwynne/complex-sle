/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.RightHull
import ComplexSLE.Internal.Lemma_2_4_RightHull

/-!
# Lemma 2.4 (connectedness of right hulls)
-/

public section

open scoped NNReal ComplexConjugate

namespace ComplexSLE

/-- **Lemma 2.4, right hulls** (paper.tex:L658-666): for continuous `U`, each `R_t` is connected. -/
theorem lemma_2_4_rightHull (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) :
    IsConnected (rightHull U hU t) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE

end
-- FROZEN_ANCHOR_SUFFIX_END
