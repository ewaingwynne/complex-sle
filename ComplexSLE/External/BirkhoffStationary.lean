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
import ComplexSLE.Internal.ExternalProofs.BirkhoffStationary

/-!
# Classical input (proved): `birkhoff_stationary`

Author-approved classical input (ERRATA.md R24, R25). Proved in-project (M10, ruling R30) by
`ComplexSLE.Internal.ExternalProofs.birkhoff_stationary`.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.External

/-- **E7 (Birkhoff ergodic theorem, stationary-sequence form).** For a stationary sequence of
real random variables with `ξ 0` integrable, the Cesàro averages converge a.s. to an integrable
limit `L` with `∫ L = ∫ ξ 0` (`L = E(ξ 0 | 𝓘)`, `𝓘` the invariant σ-algebra; the conditional
expectation itself is not named, see the report). Stationarity is equality of the laws of the
shifted sequences on `ℕ → ℝ`. Classical (Birkhoff 1931; Durrett Thm 7.2.1 via the canonical
shift space). Serves `step:sde-birkhoff-limit`. -/
theorem birkhoff_stationary {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ξ : ℕ → Ω → ℝ) (hmeas : ∀ n, Measurable (ξ n))
    (hstat : ∀ k : ℕ, P.map (fun ω (n : ℕ) => ξ (n + k) ω) = P.map (fun ω (n : ℕ) => ξ n ω))
    (hint : Integrable (ξ 0) P) :
    ∃ L : Ω → ℝ, Integrable L P ∧ ∫ ω, L ω ∂P = ∫ ω, ξ 0 ω ∂P ∧
      ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, ξ k ω) / n) atTop (𝓝 (L ω)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ComplexSLE.Internal.ExternalProofs.birkhoff_stationary ξ hmeas hstat hint
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE.External

end
-- FROZEN_ANCHOR_SUFFIX_END
