/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
Ported from leobon12/lean-formalizations @31e7483,
QuantumZipper/Proofs/Probability/BMMoments.lean;
trimmed and adapted to Lean v4.36 and the module system.
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Absolute Gaussian moments (trimmed)

Only the constant `gaussianAbsMoment n`, the `n`-th absolute moment of the standard Gaussian, and
its nonnegativity are kept from the upstream file; the Brownian moment bounds are not needed for
the existence proof.
-/

public section

open MeasureTheory ProbabilityTheory

namespace QuantumZipper

/-- The `n`-th absolute moment of the standard Gaussian `gaussianReal 0 1`. -/
@[expose] noncomputable def gaussianAbsMoment (n : ℕ) : ℝ := ∫ x, |x| ^ n ∂ (gaussianReal 0 1)

theorem gaussianAbsMoment_nonneg (n : ℕ) : 0 ≤ gaussianAbsMoment n :=
  integral_nonneg fun x => pow_nonneg (abs_nonneg x) n

end QuantumZipper
