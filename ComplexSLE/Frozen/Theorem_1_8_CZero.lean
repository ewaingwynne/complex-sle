/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.IsThinPhase
public import ComplexSLE.Frozen.Defs.IsSwallowingPhase
public import ComplexSLE.Frozen.Defs.IsHittingPhase
import ComplexSLE.Internal.Theorem_1_8_CZero

/-!
# Theorem 1.8 (the case c = 0)
-/

public section


namespace ComplexSLE

/-- **Theorem 1.8, the case `c = 0`** (paper.tex:L450). -/
theorem theorem_1_8_c_zero (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a - b ≤ 4 → IsThinPhase a b 0) ∧
    (4 < a - b → a - b < 8 → IsSwallowingPhase a b 0) ∧
    (8 ≤ a - b → IsHittingPhase a b 0) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE

end
-- FROZEN_ANCHOR_SUFFIX_END
