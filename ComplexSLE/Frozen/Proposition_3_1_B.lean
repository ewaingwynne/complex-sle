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
public import ComplexSLE.Frozen.Defs.IntegralI
import ComplexSLE.Internal.Proposition_3_1_B

/-!
# Proposition 3.1(b)
-/

public section

open MeasureTheory

open scoped NNReal ENNReal

namespace ComplexSLE

/-- **Proposition 3.1(b)** (paper.tex:L1265-1270). -/
theorem proposition_3_1_b (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (p : ℝ → ℝ) (hp : IsAdmissibleDensity a b c p) (hI : integralI a b c p < 0)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ℝ≥0 → Ω → ℂ) (hU : IsSLEDriver a b c U P) (z : ℂ) (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, absorbingTime (U · ω) z < ∞ :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ComplexSLE.Internal.proposition_3_1_b a b c ha hb hc p hp hI Ω P U hU z hz
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE

end
-- FROZEN_ANCHOR_SUFFIX_END
