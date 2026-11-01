/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Zipper.QuantumZipper.Proofs.Probability.BMExistence
public import Mathlib.Probability.BrownianMotion.Basic

/-!
# Existence of Brownian motion (proof of the external input)

A complete proof of the exact statement of `ComplexSLE.External.exists_isBrownianReal`, ported
from the zipper repository (`QuantumZipper.BMExist.exists_isBrownianReal_stdP`, in
`ComplexSLE.Infrastructure.Zipper.QuantumZipper.Proofs.Probability.BMExistence`).

The Brownian motion is built on the i.i.d. standard Gaussian sequence space `(ℕ → ℝ, stdP)` from
a Gaussian process with covariance `min s t` (Gaussian series in `L²(ℝ)`), made path-continuous by
a dyadic Kolmogorov-chaining modification (eighth-moment bound).

This module deliberately does not import `ComplexSLE.External.*`; the statement is a verbatim copy.
-/

public section

open scoped NNReal
open MeasureTheory ProbabilityTheory

namespace ComplexSLE.Internal.ExternalProofs

/-- **Existence of Brownian motion.** Some probability space carries a standard real Brownian
motion (Mathlib's `IsBrownianReal`). Same statement as `ComplexSLE.External.exists_isBrownianReal`,
proved. -/
theorem exists_isBrownianReal :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P := by
  obtain ⟨B, hB⟩ := QuantumZipper.BMExist.exists_isBrownianReal_stdP
  exact ⟨ℕ → ℝ, inferInstance, LQGDimension.ExistAsm.stdP, inferInstance, B, hB⟩

end ComplexSLE.Internal.ExternalProofs

end
