/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsAdmissibleDensity
public import ComplexSLE.Frozen.Defs.IntegralII
public import ComplexSLE.Frozen.Defs.IsSLEDriver
public import ComplexSLE.Frozen.Defs.LeftHull
public import ComplexSLE.Internal.Stationary.ThetaHatSolution
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import ComplexSLE.Internal.Phases.Prop31Core
import ComplexSLE.Internal.Phases.Prop32ARatio
import ComplexSLE.Internal.Phases.Prop32AEvents

/-!
# Proposition 3.2(a), assembled (M7/D2)

`proposition_3_2_a_main` has exactly the type of the frozen anchor `ComplexSLE.proposition_3_2_a`
(paper.tex:L1276-1281): if `(II) < 0` then a.s. `∀ ε > 0, ∃ t < T_z, dist(z, L_t) < ε` (the R14
`ε`-form of `lim_{t → T_z⁻} dist(z, L_t) = 0`), for every `z ≠ 0`.

Proof (paper.tex:L1430-1466):

* by Lemma 3.3 (`lemma_3_3`, through `ae_event_of_ae_ae_unit`) it suffices to treat the random
  point `𝐳 = e^{i𝐮}`, for the event family `𝓔(z) = {∀ ε > 0, ∃ t < T_z, dist(z, L_t) < ε}`, which is
  measurable (`measurableEvents_hull_approach`), scale invariant
  (`scaleInvariantEvents_hull_approach`) and future dependent
  (`futureDependentEvents_hull_approach`);
* at the random point, by Lemma 3.7 (`ae_tendsto_sigmaLogRatio_div`)
  `log(|f̂'_s|/|f̂_s|) / s → -(II) > 0`, so `log(|f̂'_s|/|f̂_s|) → +∞`, and the Koebe hitting bound
  in σ-time (`ae_exists_infDist_leftHull_lt_of_tendsto`) gives the `ε`-form
  (`ae_ae_hull_approach`).

Uses the classical inputs `birkhoff_stationary`, `strongMarkov_sleDriver`, `ito_formula` and
`timeChange_isContLocalMartingale`, all proved in-project (`Internal/ExternalProofs/`).
-/

public section

open scoped NNReal ENNReal
open MeasureTheory Metric

namespace ComplexSLE.Internal

/-- **Proposition 3.2(a)** (paper.tex:L1276-1281): a.s. `lim_{t → T_z⁻} dist(z, L_t) = 0`, in the
R14 `ε`-form. Exactly the type of `ComplexSLE.proposition_3_2_a`. -/
theorem proposition_3_2_a_main (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : c ^ 2 ≤ a * b) (p : ℝ → ℝ) (hp : IsAdmissibleDensity a b c p)
    (hII : integralII a b c p < 0) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (U : ℝ≥0 → Ω → ℂ) (hU : IsSLEDriver a b c U P) (z : ℂ)
    (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < absorbingTime (U · ω) z ∧
      infDist z (leftHull (U · ω) t) < ε :=
  ae_event_of_ae_ae_unit ha hb hc hU hp
    (E := fun u z => ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < absorbingTime u z ∧
      infDist z (leftHull u t) < ε)
    measurableEvents_hull_approach scaleInvariantEvents_hull_approach
    futureDependentEvents_hull_approach
    (fun _ _ hU' => ae_ae_hull_approach hU' ha hb hc hp hII) z hz

end ComplexSLE.Internal

end
