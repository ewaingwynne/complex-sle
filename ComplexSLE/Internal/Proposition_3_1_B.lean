/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsAdmissibleDensity
public import ComplexSLE.Frozen.Defs.IntegralI
public import ComplexSLE.Frozen.Defs.IsSLEDriver
public import ComplexSLE.Frozen.Defs.LeftHull
import ComplexSLE.Internal.Phases.Prop31B

/-!
# Provider for `ComplexSLE.proposition_3_1_b`

Implementation module for the frozen anchor `ComplexSLE/Frozen/Proposition_3_1_B.lean`. The anchor
is SEALED: it is
proved here from `Internal.proposition_3_1_b_core` (`Internal/Phases/Prop31B.lean`; Lemmas
3.3, 3.4, 3.6).
-/

public section

open scoped NNReal ENNReal
open MeasureTheory

namespace ComplexSLE.Internal

theorem proposition_3_1_b (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (p : ℝ → ℝ) (hp : IsAdmissibleDensity a b c p) (hI : integralI a b c p < 0)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ℝ≥0 → Ω → ℂ) (hU : IsSLEDriver a b c U P) (z : ℂ) (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, absorbingTime (U · ω) z < ∞ :=
  proposition_3_1_b_core a b c ha hb hc p hp hI Ω P U hU z hz

end ComplexSLE.Internal

end
