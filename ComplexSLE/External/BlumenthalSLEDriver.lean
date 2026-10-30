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
# EXTERNAL input: `blumenthal_sleDriver`

Author-approved classical input (ERRATA.md R24, R25). Assumed, not proved: its body is a permanent
`sorry`, and every result that uses it is reported `PROVED_REL`.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.External

/-- **E5 (Blumenthal 0-1 law for the driver).** Every event in the `P`-completion of the germ
σ-algebra `⋂_{ε>0} σ(U_s : s ≤ ε)` of an SLE_Σ driver has probability `0` or `1`. Stated for the
completed germ σ-algebra (every `ε` has a `σ(U_s : s ≤ ε)`-measurable `B_ε` with
`P (A ∆ B_ε) = 0`), which is the form consumers can verify. Classical (Revuz–Yor III.2.15);
holds for any process with independent increments, `U 0 = 0` a.s. and a.s. continuous paths.
Serves `step:disc-b-blumenthal`. -/
theorem blumenthal_sleDriver {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ} (hU : IsSLEDriver a b c U P)
    (A : Set Ω)
    (hA : ∀ ε : ℝ≥0, 0 < ε → ∃ B : Set Ω,
      MeasurableSet[⨆ (s : ℝ≥0) (_ : s ≤ ε), MeasurableSpace.comap (U s) inferInstance] B ∧
        P (symmDiff A B) = 0) :
    P A = 0 ∨ P A = 1 :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE.External

end
-- FROZEN_ANCHOR_SUFFIX_END
