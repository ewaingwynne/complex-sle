/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.IsSLEDriverAdapted
public import ComplexSLE.Frozen.Defs.IsDiffusionSolution
public import ComplexSLE.Frozen.Defs.DiffusionD
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import ComplexSLE.Internal.ExternalProofs.StrongMarkovSLEDriver

/-!
# Classical input (proved): `strongMarkov_sleDriver`

Author-approved classical input (ERRATA.md R24, R25). Proved in-project (M10, ruling R30) by
`ComplexSLE.Internal.ExternalProofs.strongMarkov_sleDriver`.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.External

/-- **E3 (strong Markov property of the planar driver).** If `U` is an SLE_Σ driver with respect
to `ℱ` and `τ` is an a.s. finite `ℱ`-stopping time, then `V_s := U_{τ+s} - U_τ` is again an
SLE_Σ driver, it is independent of `ℱ_τ`, and it is an SLE_Σ driver with respect to the shifted
filtration `𝒢_s = ℱ_{τ+s}` (given here by its defining property, as in
`IsStoppingTime.measurableSpace`; this needs every path of `U` continuous, which
`IsSLEDriverAdapted` requires, so that `V_s` is `𝒢_s`-measurable). Classical (e.g. Revuz–Yor
III.3.7, Karatzas–Shreve 2.6.16).
Serves `step:markov-driver`, `step:rec-renewal`, `step:rec-monotone-in-y`,
`step:sde-regeneration`, `step:kol-markov-semigroup` (the last three also need that the
process they shift is a functional of the post-`τ` driver, which is a consumer step). -/
theorem strongMarkov_sleDriver {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ≥0 ‹_›} {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}
    (hU : IsSLEDriverAdapted a b c U P ℱ) (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime ℱ τ)
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IsSLEDriver a b c (fun s ω => U ((τ ω).untopA + s) ω - U (τ ω).untopA ω) P ∧
    Indep (⨆ s : ℝ≥0, MeasurableSpace.comap
        (fun ω => U ((τ ω).untopA + s) ω - U (τ ω).untopA ω) inferInstance)
      hτ.measurableSpace P ∧
    ∀ 𝒢 : Filtration ℝ≥0 ‹_›,
      (∀ (s : ℝ≥0) (A : Set Ω), MeasurableSet[𝒢 s] A ↔
        MeasurableSet[⨆ t, ℱ t] A ∧ ∀ t : ℝ≥0, MeasurableSet[ℱ t] (A ∩ {ω | τ ω + s ≤ t})) →
      IsSLEDriverAdapted a b c (fun s ω => U ((τ ω).untopA + s) ω - U (τ ω).untopA ω) P 𝒢 :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ComplexSLE.Internal.ExternalProofs.strongMarkov_sleDriver hU τ hτ hfin
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE.External

end
-- FROZEN_ANCHOR_SUFFIX_END
