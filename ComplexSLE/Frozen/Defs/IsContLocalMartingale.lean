/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# IsContLocalMartingale (auxiliary vocabulary for the martingale-form external inputs, ERRATA.md R24, R25)
-/

@[expose] public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- `M` is a continuous local martingale with respect to `ℱ`: progressively measurable, a.s.
continuous paths, and there are `ℱ`-stopping times `τ n` that are a.s. eventually above every
level, such that each stopped process `M^{τ n}` is a (Mathlib) martingale. -/
def IsContLocalMartingale (ℱ : Filtration ℝ≥0 m) (M : ℝ≥0 → Ω → ℝ) (P : Measure Ω) : Prop :=
  IsStronglyProgressive ℱ M ∧ (∀ᵐ ω ∂P, Continuous fun t => M t ω) ∧
    ∃ τ : ℕ → Ω → WithTop ℝ≥0, (∀ n, IsStoppingTime ℱ (τ n)) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, ∀ᶠ n in atTop, (t : WithTop ℝ≥0) ≤ τ n ω) ∧
      ∀ n, Martingale (stoppedProcess M (τ n)) ℱ P

end ComplexSLE

end
