/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsSLEDriver
public import ComplexSLE.Frozen.Defs.LeftHull
public import ComplexSLE.Frozen.Defs.DisconnectsFromInfinity
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import ComplexSLE.Internal.Disconnect.Thm110B
import ComplexSLE.Internal.Disconnect.Lemma41

/-!
# Provider for `ComplexSLE.theorem_1_10_b`

Implementation module for the frozen anchor `ComplexSLE/Frozen/Theorem_1_10_B.lean`. The anchor
is SEALED. The proof is paper.tex:L2220-2224: `theorem_1_10_b_of_lemma41`
(`Internal/Disconnect/Thm110B*.lean`: the probability that `L_s` disconnects a ball does not depend
on `s` by scaling, Blumenthal's 0-1 law gives arbitrarily small such times a.s., and hulls are
monotone) applied to Lemma 4.1 (`lemma_4_1`, `Internal/Disconnect/Lemma41*.lean`).
-/

public section

open scoped NNReal ENNReal
open MeasureTheory

namespace ComplexSLE.Internal

theorem theorem_1_10_b (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ℝ≥0 → Ω → ℂ) (hU : IsSLEDriver a b c U P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      (interior {w | DisconnectsFromInfinity (leftHull (U · ω) t) {w}}).Nonempty :=
  theorem_1_10_b_of_lemma41 a b c ha hb hc
    (fun Ω' _ P' _ U' hU' => lemma_4_1 a b c ha hb hc Ω' P' U' hU') Ω P U hU

end ComplexSLE.Internal

end
