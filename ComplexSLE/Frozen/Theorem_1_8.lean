/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.IsThinPhase
public import ComplexSLE.Frozen.Defs.IsSwallowingPhase
public import ComplexSLE.Frozen.Defs.IsHittingPhase
public import ComplexSLE.Frozen.Defs.IsDensePhase
public import ComplexSLE.Frozen.Defs.IsAdmissibleDensity
public import ComplexSLE.Frozen.Defs.IntegralI
public import ComplexSLE.Frozen.Defs.IntegralII
import ComplexSLE.Internal.Theorem_1_8

/-!
# Theorem 1.8 (phases of SLE_Σ)
-/

public section


namespace ComplexSLE

/-- **Theorem 1.8** (paper.tex:L437-449). For `a, b > 0`, `c² ≤ ab`, and every density `p`
admissible in the sense of Lemma 2.14, the signs of (I) and (II) determine the phase. -/
theorem theorem_1_8 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (p : ℝ → ℝ) (hp : IsAdmissibleDensity a b c p) :
    (0 ≤ integralI a b c p → 0 < integralII a b c p → IsThinPhase a b c) ∧
    (integralI a b c p < 0 → 0 < integralII a b c p → IsSwallowingPhase a b c) ∧
    (integralI a b c p < 0 → integralII a b c p < 0 → IsHittingPhase a b c) ∧
    (0 ≤ integralI a b c p → integralII a b c p < 0 → IsDensePhase a b c) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ComplexSLE.Internal.theorem_1_8 a b c ha hb hc p hp
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE

end
-- FROZEN_ANCHOR_SUFFIX_END
