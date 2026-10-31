/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsThinPhase
public import ComplexSLE.Frozen.Defs.IsSwallowingPhase
public import ComplexSLE.Frozen.Defs.IsHittingPhase
import ComplexSLE.Frozen.Theorem_1_8
import ComplexSLE.Frozen.Lemma_2_13_Exists
import ComplexSLE.Internal.Phases.C0Integrals
import ComplexSLE.Internal.Phases.C0Bdy

/-!
# Provider for `ComplexSLE.theorem_1_8_c_zero`

Implementation module for the frozen anchor `ComplexSLE/Frozen/Theorem_1_8_CZero.lean`. The anchor
is SEALED. The proof is paper.tex:L1930-1932 ("combine Propositions 3.1 and 3.2 with Lemmas 3.11
and 3.12"): fix an admissible density `p` for `(a, b, 0)` (sealed `exists_admissibleDensity`,
Lemma 2.13), read off the signs of `(I)` and `(II)` from the explicit `c = 0` evaluation
(`c0_integral_signs`, `Internal/Phases/C0Integrals.lean`, Lemma 3.11), and apply the sealed
`theorem_1_8`. At `a - b = 8`, where `(II) = 0`, the hitting phase is Lemma 3.12 (`lemma_3_12`,
`Internal/Phases/C0Bdy.lean`).
-/

public section

namespace ComplexSLE.Internal

theorem theorem_1_8_c_zero (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a - b ≤ 4 → IsThinPhase a b 0) ∧
    (4 < a - b → a - b < 8 → IsSwallowingPhase a b 0) ∧
    (8 ≤ a - b → IsHittingPhase a b 0) := by
  have hc : (0 : ℝ) ^ 2 ≤ a * b := by rw [zero_pow two_ne_zero]; exact (mul_pos ha hb).le
  obtain ⟨p, hp⟩ := _root_.ComplexSLE.exists_admissibleDensity a b 0 ha hb hc
  obtain ⟨hthin, hswal, hhit, -⟩ := _root_.ComplexSLE.theorem_1_8 a b 0 ha hb hc p hp
  obtain ⟨s1, s2, s3, -⟩ := c0_integral_signs ha hb hp
  refine ⟨fun h => hthin (s1 h).1 (s1 h).2, fun h h' => hswal (s2 h h').1 (s2 h h').2,
    fun h => ?_⟩
  rcases h.lt_or_eq with h | h
  · exact hhit (s3 h).1 (s3 h).2
  · exact lemma_3_12 a b ha hb h.symm

end ComplexSLE.Internal

end
