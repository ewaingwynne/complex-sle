/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsSLEDriver
public import ComplexSLE.Frozen.Defs.LeftHull
public import ComplexSLE.Frozen.Defs.DisconnectsFromInfinity
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import ComplexSLE.Internal.Disconnect.Thm110A
import ComplexSLE.Internal.Disconnect.Lemma41

/-!
# Provider for `ComplexSLE.theorem_1_10_a`

Implementation module for the frozen anchor `ComplexSLE/Frozen/Theorem_1_10_A.lean`. The anchor
is SEALED. The proof is paper.tex:L2199-2217: `theorem_1_10_a_of_lemma41`
(`Internal/Disconnect/Thm110A*.lean`, the upgrade from a positive-probability disconnection to
every `z`, with the R27 hitting lemma in place of Girsanov) applied to Lemma 4.1 (`lemma_4_1`,
`Internal/Disconnect/Lemma41*.lean`, with the R20 construction).
-/

public section

open scoped NNReal ENNReal
open MeasureTheory

namespace ComplexSLE.Internal

theorem theorem_1_10_a (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ℝ≥0 → Ω → ℂ) (hU : IsSLEDriver a b c U P) (z : ℂ) (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, ∃ t : ℝ≥0, 0 < t ∧ z ∉ leftHull (U · ω) t ∧
      DisconnectsFromInfinity (leftHull (U · ω) t) {z} :=
  theorem_1_10_a_of_lemma41 a b c ha hb hc
    (fun Ω' _ P' _ U' hU' => lemma_4_1 a b c ha hb hc Ω' P' U' hU') Ω P U hU z hz

end ComplexSLE.Internal

end
