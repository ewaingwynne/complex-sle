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
# pathIntegral (auxiliary vocabulary for the martingale-form external inputs, ERRATA.md R24, R25)
-/

@[expose] public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- `∫₀ᵗ ξ_s ds`, the Lebesgue integral of a path over `[0, t]`
(notation-level abbreviation; could be inlined). -/
noncomputable def pathIntegral (ξ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..(t : ℝ), ξ (Real.toNNReal s) ω

end ComplexSLE

end
