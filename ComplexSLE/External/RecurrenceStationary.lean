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
import ComplexSLE.Internal.ExternalProofs.RecurrenceStationary

/-!
# Classical input (proved): `recurrence_stationary`

Author-approved classical input (ERRATA.md R24, R25). Proved in-project (M10, ruling R30) by
`ComplexSLE.Internal.ExternalProofs.recurrence_stationary`.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.External

/-- **E7' (recurrence of stationary real sequences with zero conditional mean; the paper's
Lemma `lem-recurrent`).** If `ξ` is stationary, `ξ 0` integrable, and the Cesàro averages tend to
`0` a.s. (equivalently, by Birkhoff, `E(ξ 0 | 𝓘) = 0`), then a.s. for every `ε > 0` the partial
sums are `ε`-close to `0` infinitely often. Classical: G. Atkinson, "Recurrence of co-cycles and
random walks", J. London Math. Soc. 13 (1976) 486–488 (ergodic case); F. M. Dekking, "On
transience and recurrence of generalized random walks", Z. Wahrsch. verw. Gebiete 61 (1982)
459–465, Thm 3 (general stationary case, the form the paper's comment cites); Durrett
PTE Thm 7.3.2 is the `ℤ`-valued case the paper quotes. Serves
`step:recurrent-durrett-adaptation`. -/
theorem recurrence_stationary {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ξ : ℕ → Ω → ℝ) (hmeas : ∀ n, Measurable (ξ n))
    (hstat : ∀ k : ℕ, P.map (fun ω (n : ℕ) => ξ (n + k) ω) = P.map (fun ω (n : ℕ) => ξ n ω))
    (hint : Integrable (ξ 0) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, ξ k ω) / n) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∃ᶠ n in atTop, |∑ k ∈ Finset.range n, ξ k ω| < ε :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ComplexSLE.Internal.ExternalProofs.recurrence_stationary ξ hmeas hstat hint hlim
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE.External

end
-- FROZEN_ANCHOR_SUFFIX_END
