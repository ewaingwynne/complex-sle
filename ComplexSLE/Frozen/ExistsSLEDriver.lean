/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.IsSLEDriver
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import ComplexSLE.Internal.ExistsSLEDriver

/-!
# Existence of the SLE_Σ driver
-/

public section

open MeasureTheory

open scoped NNReal

namespace ComplexSLE

/-- **Existence of the SLE_Σ driver.** For `a, b > 0` and `c² ≤ ab` there is a probability
space carrying a complex Brownian motion with covariance `Σ`. The paper takes this for granted;
it guarantees that the probabilistic roots below are not vacuous. -/
theorem exists_sleDriver (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (U : ℝ≥0 → Ω → ℂ), IsSLEDriver a b c U P :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE

end
-- FROZEN_ANCHOR_SUFFIX_END
