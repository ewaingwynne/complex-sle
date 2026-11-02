/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsAdmissibleDensity
public import ComplexSLE.Frozen.Defs.IntegralII
public import ComplexSLE.Frozen.Defs.IsSLEDriver
public import ComplexSLE.Frozen.Defs.LeftHull
import ComplexSLE.Internal.Phases.Prop32A

/-!
# Provider for `ComplexSLE.proposition_3_2_a`

Implementation module for the frozen anchor `ComplexSLE/Frozen/Proposition_3_2_A.lean`. The anchor is SEALED: it is
proved by `Internal.proposition_3_2_a_main` (`Internal/Phases/Prop32A.lean`: Lemma 3.7 ratio limit, the Koebe hitting
bound, Lemma 3.3).
-/

public section

open scoped NNReal ENNReal
open MeasureTheory Metric

namespace ComplexSLE.Internal

theorem proposition_3_2_a (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (p : ℝ → ℝ) (hp : IsAdmissibleDensity a b c p) (hII : integralII a b c p < 0)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ℝ≥0 → Ω → ℂ) (hU : IsSLEDriver a b c U P) (z : ℂ) (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < absorbingTime (U · ω) z ∧
      infDist z (leftHull (U · ω) t) < ε :=
  proposition_3_2_a_main a b c ha hb hc p hp hII Ω P U hU z hz

end ComplexSLE.Internal

end
