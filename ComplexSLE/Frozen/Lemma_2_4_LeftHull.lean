/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.LeftHull
import ComplexSLE.Internal.Lemma_2_4_LeftHull

/-!
# Lemma 2.4 (left hulls are connected)
-/

public section

open scoped NNReal

namespace ComplexSLE

/-- **Lemma 2.4, left hulls** (paper.tex:L658-666): for continuous `U`, each `L_t` is
connected (in particular nonempty). -/
theorem lemma_2_4_leftHull (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) :
    IsConnected (leftHull U t) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE

end
-- FROZEN_ANCHOR_SUFFIX_END
