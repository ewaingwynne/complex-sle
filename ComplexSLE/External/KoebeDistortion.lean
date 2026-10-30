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
# EXTERNAL input: `koebe_distortion`

Author-approved classical input (ERRATA.md R24, R25). Assumed, not proved: its body is a permanent
`sorry`, and every result that uses it is reported `PROVED_REL`.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.External

/-- **E11 (Koebe growth and distortion theorems; [Law05, Cor 3.23], Duren Thms 2.5–2.6).** For
`f` holomorphic and injective on the unit disc with `f 0 = 0`, `f' 0 = 1` (class `S`) and
`|z| < 1`: `|z|/(1+|z|)² ≤ |f z| ≤ |z|/(1-|z|)²` and
`(1-|z|)/(1+|z|)³ ≤ |f' z| ≤ (1+|z|)/(1-|z|)³`. Consumers normalize
`ζ ↦ (f_t(z + rζ) - f_t(z)) / (r f_t'(z))`; the bound `|f_t(w) - f_t(z)| ≤ 8 |w - z| dist(f_t(z), R_t)/dist(z, L_t)`
for `|w - z| ≤ dist(z, L_t)/16` (paper (3.9)) follows from the growth bound and E10. -/
theorem koebe_distortion (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hinj : InjOn f (Metric.ball 0 1)) (h0 : f 0 = 0) (h1 : deriv f 0 = 1) (z : ℂ)
    (hz : ‖z‖ < 1) :
    ‖z‖ / (1 + ‖z‖) ^ 2 ≤ ‖f z‖ ∧ ‖f z‖ ≤ ‖z‖ / (1 - ‖z‖) ^ 2 ∧
      (1 - ‖z‖) / (1 + ‖z‖) ^ 3 ≤ ‖deriv f z‖ ∧ ‖deriv f z‖ ≤ (1 + ‖z‖) / (1 - ‖z‖) ^ 3 :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE.External

end
-- FROZEN_ANCHOR_SUFFIX_END
