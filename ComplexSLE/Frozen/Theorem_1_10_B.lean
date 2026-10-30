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
import ComplexSLE.Internal.Theorem_1_10_B

/-!
# Theorem 1.10(b)
-/

public section

open MeasureTheory

open scoped NNReal ENNReal

namespace ComplexSLE

/-- **Theorem 1.10(b)** (paper.tex:L502-509). A.s., for every `t > 0`, the set of points
disconnected from `∞` by `L_t` has nonempty interior. -/
theorem theorem_1_10_b (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ℝ≥0 → Ω → ℂ) (hU : IsSLEDriver a b c U P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      (interior {w | DisconnectsFromInfinity (leftHull (U · ω) t) {w}}).Nonempty :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE

end
-- FROZEN_ANCHOR_SUFFIX_END
