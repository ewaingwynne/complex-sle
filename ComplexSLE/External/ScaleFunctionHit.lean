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
# EXTERNAL input: `scale_function_hit`

Author-approved classical input (ERRATA.md R24, R25). Assumed, not proved: its body is a permanent
`sorry`, and every result that uses it is reported `PROVED_REL`.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.External

/-- **E9 (scale-function hitting lemma; [Law05, Lemma 1.24], Karlin–Taylor Ch. 15 §6).** Let
`X` be continuous, started in `(l, u)`, and inside `(l, u)` a diffusion `dX = b(X) dr + dZ` with
unit diffusion coefficient, in martingale form *localised away from the boundary*: for every
`ε > 0`, with `R_ε` the exit time of `(l+ε, u-ε)` and
`M^ε_r := X_{r∧R_ε} - X_0 - ∫₀^r 1_{s<R_ε} b(X_s) ds`, both `M^ε` and `(M^ε)² - ∫₀^r 1_{s<R_ε} ds`
are continuous local martingales (the truncation is needed because `∫₀^R b(X)` diverges when
`b → -∞` at `l`, the case `c² = ab`). If `b` is continuous on `(l, u)` and bounded above near
`l`, then with positive probability the exit time `R` of `(l, u)` is finite and `X_R = l`. The
bound on `b` near `l` makes `l` attracting *and* attainable in finite time (it bounds the scale
density `exp(-2∫b)` near `l`, hence `ψ(l⁺) > -∞`, and gives Feller's `Σ(l) < ∞`); both uses in
Lemma 2.16 satisfy it (`b = μ/(2D)` has a finite limit at `x` if `c² < ab`, and tends to `-∞`
if `c² = ab`). Serves `step:rec-scale-function-hit`. -/
theorem scale_function_hit {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 ‹_›) (l u : ℝ) (hlu : l < u) (b : ℝ → ℝ)
    (hb : ContinuousOn b (Ioo l u)) (hbdd : ∃ η : ℝ, 0 < η ∧ ∃ K : ℝ, ∀ v ∈ Ioo l (l + η), b v ≤ K)
    (X : ℝ≥0 → Ω → ℝ) (hX : IsStronglyProgressive ℱ X) (hXc : ∀ ω, Continuous fun r => X r ω)
    (hX0 : ∀ᵐ ω ∂P, X 0 ω ∈ Ioo l u)
    (hloc : ∀ ε : ℝ, 0 < ε → ∀ Rε : Ω → WithTop ℝ≥0, Rε = hittingAfter X (Ioo (l + ε) (u - ε))ᶜ 0 →
      IsContLocalMartingale ℱ (fun r ω => stoppedProcess X Rε r ω - X 0 ω -
        pathIntegral (fun s ω => if (s : WithTop ℝ≥0) < Rε ω then b (X s ω) else 0) r ω) P ∧
      IsContLocalMartingale ℱ (fun r ω => (stoppedProcess X Rε r ω - X 0 ω -
        pathIntegral (fun s ω => if (s : WithTop ℝ≥0) < Rε ω then b (X s ω) else 0) r ω) ^ 2 -
        pathIntegral (fun s ω => if (s : WithTop ℝ≥0) < Rε ω then 1 else 0) r ω) P)
    (R : Ω → WithTop ℝ≥0) (hR : R = hittingAfter X (Ioo l u)ᶜ 0) :
    0 < P {ω | R ω ≠ ⊤ ∧ stoppedValue X R ω = l} :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE.External

end
-- FROZEN_ANCHOR_SUFFIX_END
