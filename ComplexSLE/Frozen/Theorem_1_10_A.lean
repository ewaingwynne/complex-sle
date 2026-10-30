/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.IsSLEDriver
public import ComplexSLE.Frozen.Defs.LeftHull
public import ComplexSLE.Frozen.Defs.DisconnectsFromInfinity
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import ComplexSLE.Internal.Theorem_1_10_A

/-!
# Theorem 1.10(a)
-/

public section

open MeasureTheory

open scoped NNReal ENNReal

namespace ComplexSLE

/-- **Theorem 1.10(a)** (paper.tex:L502-507). For each `z ≠ 0`, a.s. some `L_t` disconnects
`z` from `∞` without containing it. -/
theorem theorem_1_10_a (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ℝ≥0 → Ω → ℂ) (hU : IsSLEDriver a b c U P) (z : ℂ) (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, ∃ t : ℝ≥0, 0 < t ∧ z ∉ leftHull (U · ω) t ∧
      DisconnectsFromInfinity (leftHull (U · ω) t) {z} :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE

end
-- FROZEN_ANCHOR_SUFFIX_END
