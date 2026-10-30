/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsSLEDriver
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# IsSLEDriverAdapted (auxiliary vocabulary for the martingale-form external inputs, ERRATA.md R24, R25)
-/

@[expose] public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- An SLE_Σ driver that is a Brownian motion *with respect to the filtration `ℱ`*: `U` is
`ℱ`-adapted and for `s ≤ t` the increment `U t - U s` is independent of `ℱ s`. The natural
filtration of `U` qualifies; so does any enlargement by independent data (e.g. the random point
`𝐳` of Section 3). -/
structure IsSLEDriverAdapted (a b c : ℝ) (U : ℝ≥0 → Ω → ℂ) (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 m) : Prop where
  toIsSLEDriver : IsSLEDriver a b c U P
  /-- Every path is continuous (not only a.s.), so that stopped values and time changes of `U`
  are measurable without completing the filtration. -/
  cont : ∀ ω, Continuous fun t => U t ω
  adapted : Adapted ℱ U
  indep_increment : ∀ s t : ℝ≥0, s ≤ t →
    Indep (MeasurableSpace.comap (fun ω => U t ω - U s ω) inferInstance) (ℱ s) P

end ComplexSLE

end
