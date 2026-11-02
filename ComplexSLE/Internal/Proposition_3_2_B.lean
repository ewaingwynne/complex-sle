/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsAdmissibleDensity
public import ComplexSLE.Frozen.Defs.IntegralII
public import ComplexSLE.Frozen.Defs.IsSLEDriver
public import ComplexSLE.Frozen.Defs.LeftHull
import ComplexSLE.Internal.Phases.Prop32BUp
import ComplexSLE.Internal.Phases.ConverseMain

/-!
# Provider for `ComplexSLE.proposition_3_2_b`

Implementation module for the frozen anchor `ComplexSLE/Frozen/Proposition_3_2_B.lean`. The
anchor is SEALED: it is proved by `Internal.proposition_3_2_b_of_conv_on`
(`Internal/Phases/Prop32BUp.lean`: the upgrade from the random point `𝐳` to every `z`, with the
hitting lemma of ruling R27 in place of Girsanov), whose input `hconv` is Lemma 3.8
(`lem-converse-w-o-upgrade`, `Internal.converse_w_o_upgrade` in
`Internal/Phases/ConverseMain.lean`).
-/

public section

open scoped NNReal ENNReal
open MeasureTheory Metric

namespace ComplexSLE.Internal

theorem proposition_3_2_b (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (p : ℝ → ℝ) (hp : IsAdmissibleDensity a b c p) (hII : 0 < integralII a b c p)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ℝ≥0 → Ω → ℂ) (hU : IsSLEDriver a b c U P) (z : ℂ) (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, ∃ ε > 0, ∀ t : ℝ≥0, (t : ℝ≥0∞) < absorbingTime (U · ω) z →
      ε ≤ infDist z (leftHull (U · ω) t) :=
  proposition_3_2_b_of_conv_on a b c ha hb hc p hp hII Ω P
    (fun _ _ hU' => converse_w_o_upgrade hU' ha hb hc hp hII) U hU z hz

end ComplexSLE.Internal

end
