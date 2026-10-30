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
# EXTERNAL input: `levy_characterization`

Author-approved classical input (ERRATA.md R24, R25). Assumed, not proved: its body is a permanent
`sorry`, and every result that uses it is reported `PROVED_REL`.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.External

/-- **E2a (Lévy's characterization, covariance `Σ`; Revuz–Yor IV.3.6).** If `M : ℝ≥0 → Ω → ℂ`
has `M 0 = 0` a.s., `Re M` and `Im M` are continuous local martingales w.r.t. `ℱ`, and
`(Re M)² - a t`, `(Im M)² - b t`, `(Re M)(Im M) - c t` are continuous local martingales, then `M`
is an SLE_Σ driver (`Σ = covMatrix a b c`; the hypotheses force `Σ ⪰ 0`), `ℱ`-adapted, with
increments independent of the past. `M` is only a.s. continuous, so `IsSLEDriverAdapted` (which
asks for continuity of every path) is obtained for an indistinguishable version `M'` and the
`P`-completed filtration `𝒢_t = ℱ_t ⊔ σ(null sets)`; this is the usual-conditions step and is
the only place where completion enters. Serves `step:polar-W-law` (after the time change E2c)
and, trivially, `step:stat-martingale-qv`. -/
theorem levy_characterization {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 ‹_›) (a b c : ℝ) (M : ℝ≥0 → Ω → ℂ)
    (hM0 : ∀ᵐ ω ∂P, M 0 ω = 0)
    (hre : IsContLocalMartingale ℱ (fun t ω => (M t ω).re) P)
    (him : IsContLocalMartingale ℱ (fun t ω => (M t ω).im) P)
    (hqa : IsContLocalMartingale ℱ (fun t ω => (M t ω).re ^ 2 - a * t) P)
    (hqb : IsContLocalMartingale ℱ (fun t ω => (M t ω).im ^ 2 - b * t) P)
    (hqc : IsContLocalMartingale ℱ (fun t ω => (M t ω).re * (M t ω).im - c * t) P) :
    IsSLEDriver a b c M P ∧ Adapted ℱ M ∧
    (∀ s t : ℝ≥0, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => M t ω - M s ω) inferInstance) (ℱ s) P) ∧
    ∀ 𝒢 : Filtration ℝ≥0 ‹_›,
      (∀ t, 𝒢 t = ℱ t ⊔ MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet N ∧ P N = 0}) →
      ∃ M' : ℝ≥0 → Ω → ℂ, (∀ᵐ ω ∂P, ∀ t, M' t ω = M t ω) ∧ IsSLEDriverAdapted a b c M' P 𝒢 :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE.External

end
-- FROZEN_ANCHOR_SUFFIX_END
