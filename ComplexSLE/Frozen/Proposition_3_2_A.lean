/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.IsSLEDriver
public import ComplexSLE.Frozen.Defs.AbsorbingTime
public import ComplexSLE.Frozen.Defs.IsAdmissibleDensity
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import ComplexSLE.Frozen.Defs.IntegralII
public import ComplexSLE.Frozen.Defs.LeftHull
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import ComplexSLE.Internal.Proposition_3_2_A

/-!
# Proposition 3.2(a)
-/

public section

open MeasureTheory Metric

open scoped NNReal ENNReal

namespace ComplexSLE

/-- **Proposition 3.2(a)** (paper.tex:L1276-1281): a.s. `lim_{t → T_z⁻} dist(z, L_t) = 0`. -/
theorem proposition_3_2_a (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (p : ℝ → ℝ) (hp : IsAdmissibleDensity a b c p) (hII : integralII a b c p < 0)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ℝ≥0 → Ω → ℂ) (hU : IsSLEDriver a b c U P) (z : ℂ) (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < absorbingTime (U · ω) z ∧
      infDist z (leftHull (U · ω) t) < ε :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ComplexSLE.Internal.proposition_3_2_a a b c ha hb hc p hp hII Ω P U hU z hz
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE

end
-- FROZEN_ANCHOR_SUFFIX_END
