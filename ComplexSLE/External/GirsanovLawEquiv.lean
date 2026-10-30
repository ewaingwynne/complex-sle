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
# EXTERNAL input: `girsanov_law_equiv`

Author-approved classical input (ERRATA.md R24, R25). Assumed, not proved: its body is a permanent
`sorry`, and every result that uses it is reported `PROVED_REL`.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.External

/-- **E6 (Girsanov, law form; Revuz–Yor VIII.1.7 + Yamada–Watanabe).** Let `β` be Lipschitz
and `h` bounded measurable. If `X` solves `dX = β(X) h(X) dt + β(X) dB` and `Y` solves
`dY = β(Y) dB'` (martingale form, possibly on different spaces) from the same starting point,
then for every horizon `T` the laws of the stopped paths `t ↦ X_{t∧T}` and `t ↦ Y_{t∧T}` on
`ℝ≥0 → ℝ` are mutually absolutely continuous. Serves `step:disc-a-hit-Lambda`,
`step:prop-ii-b-hit-lambda-prime` with `β = √(2D)` (signed root), `h = μ/√(2D)`.
**Scope note:** `h` bounded covers only `c² < ab` (there `D ≥ min D > 0`). In the critical case
`c² = ab`, `D` vanishes at `x + πℤ` and `h` is unbounded, so this theorem does not apply; the
consumers' Girsanov step is then a source gap (the paper gives no argument), not something this
external can absorb. Even for `c² < ab` the consumer still has to show the driftless diffusion
hits a closed positive-measure set with positive probability. -/
theorem girsanov_law_equiv {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (ℱ : Filtration ℝ≥0 ‹_›) (𝒢 : Filtration ℝ≥0 ‹_›) (β h : ℝ → ℝ) {K : ℝ≥0}
    (hβ : LipschitzWith K β) (hh : Measurable h) (hhb : ∃ C : ℝ, ∀ v, |h v| ≤ C)
    (X : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Ω' → ℝ) (u : ℝ)
    (hX : IsDiffusionSolution ℱ (fun v => β v * h v) β X P) (hX0 : ∀ᵐ ω ∂P, X 0 ω = u)
    (hY : IsDiffusionSolution 𝒢 (fun _ => 0) β Y P') (hY0 : ∀ᵐ ω ∂P', Y 0 ω = u) (T : ℝ≥0) :
    P.map (fun ω (t : ℝ≥0) => X (min t T) ω) ≪ P'.map (fun ω (t : ℝ≥0) => Y (min t T) ω) ∧
      P'.map (fun ω (t : ℝ≥0) => Y (min t T) ω) ≪ P.map (fun ω (t : ℝ≥0) => X (min t T) ω) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE.External

end
-- FROZEN_ANCHOR_SUFFIX_END
