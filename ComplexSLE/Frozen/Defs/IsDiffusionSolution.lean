/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.PathIntegral
public import ComplexSLE.Frozen.Defs.IsContLocalMartingale
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# IsDiffusionSolution (auxiliary vocabulary for the martingale-form external inputs, ERRATA.md R24, R25)
-/

@[expose] public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- `X` solves `dX = α(X) dt + β(X) dB` in martingale form (it solves the martingale problem for
the generator `α ∂ + ½ β² ∂²`): `X` is progressively measurable with a.s. continuous paths,
`M := X - X₀ - ∫₀ᵗ α(X_s) ds` is a continuous local martingale, and so is
`M² - ∫₀ᵗ β(X_s)² ds`. Only `β²` enters. -/
def IsDiffusionSolution (ℱ : Filtration ℝ≥0 m) (α β : ℝ → ℝ) (X : ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) : Prop :=
  IsStronglyProgressive ℱ X ∧ (∀ᵐ ω ∂P, Continuous fun t => X t ω) ∧
    IsContLocalMartingale ℱ
      (fun t ω => X t ω - X 0 ω - pathIntegral (fun s ω => α (X s ω)) t ω) P ∧
    IsContLocalMartingale ℱ
      (fun t ω => (X t ω - X 0 ω - pathIntegral (fun s ω => α (X s ω)) t ω) ^ 2 -
        pathIntegral (fun s ω => β (X s ω) ^ 2) t ω) P

end ComplexSLE

end
