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
# EXTERNAL input: `koebe_quarter`

Author-approved classical input (ERRATA.md R24, R25). Assumed, not proved: its body is a permanent
`sorry`, and every result that uses it is reported `PROVED_REL`.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.External

/-- **E10 (Koebe one-quarter theorem; [Law05, Cor 3.18], Duren Thm 2.3).** A holomorphic
injective function on the unit disc covers the disc of radius `|f'(0)|/4` about `f 0`.
Consumers apply it to `f_t` on `B(z, dist(z, L_t))`, rescaled. -/
theorem koebe_quarter (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hinj : InjOn f (Metric.ball 0 1)) :
    Metric.ball (f 0) (‖deriv f 0‖ / 4) ⊆ f '' Metric.ball 0 1 :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE.External

end
-- FROZEN_ANCHOR_SUFFIX_END
