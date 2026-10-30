/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.IsAdmissibleDensity
import ComplexSLE.Internal.Lemma_2_13_Exists

/-!
# Lemma 2.13 (existence of an admissible density)
-/

public section


namespace ComplexSLE

/-- **Lemma 2.13, existence part** (paper.tex:L941-955; rulings R5, R7).
For `a, b > 0` and `c² ≤ ab`, there is a density satisfying the hypotheses of Lemma 2.14. -/
theorem exists_admissibleDensity (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b) :
    ∃ p, IsAdmissibleDensity a b c p :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE

end
-- FROZEN_ANCHOR_SUFFIX_END
