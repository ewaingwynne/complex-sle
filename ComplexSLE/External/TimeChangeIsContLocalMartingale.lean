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
import ComplexSLE.Internal.ExternalProofs.TimeChangeIsContLocalMartingale

/-!
# Classical input (proved): `timeChange_isContLocalMartingale`

Author-approved classical input (ERRATA.md R24, R25). Proved in-project (M10, ruling R30) by
`ComplexSLE.Internal.ExternalProofs.timeChange_isContLocalMartingale`.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.External

/-- **E2c (time change of continuous local martingales; Revuz–Yor V.1.5).** If `σ` is a
continuous nondecreasing family of finite `ℱ`-stopping times with `σ 0 = 0` and `𝒢_s = ℱ_{σ_s}`,
then `M ∘ σ` is a continuous `𝒢`-local martingale for every everywhere-continuous `ℱ`-local
martingale `M`. `σ 0 = 0` is necessary (with `σ ≡ ρ` and `M_ρ` non-integrable the conclusion
fails); both consumers have it (`σ_z(0) = 0` in Definition 2.9, `ω(0) = 0` in (2.46)).
Everywhere-continuity of `M` makes `M ∘ σ` progressively measurable without completing the
filtration. Applied to `M`, `M² - ⟨M⟩` and `M N - ⟨M, N⟩` it transports every bracket relation,
so together with E1 and E2a it is the martingale-form content of Lemma 2.11
(`step:polar-time-change`, `step:polar-W-law`) and of `step:rec-time-change-omega`. -/
theorem timeChange_isContLocalMartingale {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 ‹_›) (M : ℝ≥0 → Ω → ℝ)
    (hM : IsContLocalMartingale ℱ M P) (hMc : ∀ ω, Continuous fun t => M t ω)
    (σ : ℝ≥0 → Ω → ℝ≥0)
    (hσ : ∀ s, IsStoppingTime ℱ fun ω => (σ s ω : WithTop ℝ≥0)) (hσ0 : ∀ ω, σ 0 ω = 0)
    (hσc : ∀ ω, Continuous (fun s => σ s ω) ∧ Monotone (fun s => σ s ω))
    (𝒢 : Filtration ℝ≥0 ‹_›) (h𝒢 : ∀ s, 𝒢 s = (hσ s).measurableSpace) :
    IsContLocalMartingale 𝒢 (fun s ω => M (σ s ω) ω) P :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ComplexSLE.Internal.ExternalProofs.timeChange_isContLocalMartingale ℱ M hM hMc σ hσ
      hσ0 hσc 𝒢 h𝒢
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE.External

end
-- FROZEN_ANCHOR_SUFFIX_END
