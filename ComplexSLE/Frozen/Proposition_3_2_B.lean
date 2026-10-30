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
import ComplexSLE.Internal.Proposition_3_2_B

/-!
# Proposition 3.2(b)
-/

public section

open MeasureTheory Metric

open scoped NNReal ENNReal

namespace ComplexSLE

/-- **Proposition 3.2(b)** (paper.tex:L1276-1283): a.s. `lim_{t → T_z⁻} dist(z, L_t) > 0`. -/
theorem proposition_3_2_b (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (p : ℝ → ℝ) (hp : IsAdmissibleDensity a b c p) (hII : 0 < integralII a b c p)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ℝ≥0 → Ω → ℂ) (hU : IsSLEDriver a b c U P) (z : ℂ) (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, ∃ ε > 0, ∀ t : ℝ≥0, (t : ℝ≥0∞) < absorbingTime (U · ω) z →
      ε ≤ infDist z (leftHull (U · ω) t) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE

end
-- FROZEN_ANCHOR_SUFFIX_END
