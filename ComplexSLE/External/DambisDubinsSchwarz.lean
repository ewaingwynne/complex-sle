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

/-!
# EXTERNAL input: `dambis_dubins_schwarz`

Author-approved classical input (ERRATA.md R24, R25). Assumed, not proved: its body is a permanent
`sorry`, and every result that uses it is reported `PROVED_REL`.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.External

/-- **E2b (Dambis–Dubins–Schwarz; Revuz–Yor V.1.6).** A continuous local martingale `N` with
`N 0 = 0` whose quadratic variation `A` (continuous, nondecreasing, `A 0 = 0`, `N² - A` a local
martingale) tends to `∞` a.s. is a time-changed Brownian motion on the same space:
`N_t = β_{A_t}` for a Brownian motion `β`. Serves `step:c0-bdy-martingale-bm` (then
`limsup β = ∞` a.s. for Brownian motion is a consumer step). -/
theorem dambis_dubins_schwarz {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 ‹_›) (N A : ℝ≥0 → Ω → ℝ)
    (hN : IsContLocalMartingale ℱ N P) (hN0 : ∀ᵐ ω ∂P, N 0 ω = 0)
    (hA : IsStronglyProgressive ℱ A)
    (hAc : ∀ᵐ ω ∂P, Continuous (fun t => A t ω) ∧ Monotone (fun t => A t ω) ∧ A 0 ω = 0)
    (hNA : IsContLocalMartingale ℱ (fun t ω => N t ω ^ 2 - A t ω) P)
    (hAtop : ∀ᵐ ω ∂P, Tendsto (fun t => A t ω) atTop atTop) :
    ∃ β : ℝ≥0 → Ω → ℝ, IsBrownianReal β P ∧
      ∀ᵐ ω ∂P, ∀ t, N t ω = β (Real.toNNReal (A t ω)) ω :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE.External

end
-- FROZEN_ANCHOR_SUFFIX_END
