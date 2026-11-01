/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
Ported from leobon12/lean-formalizations @31e7483,
QuantumZipper/Common/Basic.lean;
trimmed and adapted to Lean v4.36 and the module system.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Basic conventions (trimmed)

The closed upper half-plane `Hbar` and dyadic rounding, used by the dyadic Kolmogorov chaining in
`QuantumZipper.Proofs.GFF.CircleContinuity`.
-/

@[expose] public section

namespace QuantumZipper

/-- The closed upper half-plane `{z : Im z ≥ 0}`. -/
def Hbar : Set ℂ := {z | 0 ≤ z.im}

/-- Round down to the dyadic grid of mesh `2^{-n}`. -/
noncomputable def dyadicRound (n : ℕ) (x : ℝ) : ℝ := ⌊(2 : ℝ) ^ n * x⌋ / (2 : ℝ) ^ n

/-- Round both coordinates down to the dyadic grid of mesh `2^{-n}`. -/
noncomputable def dyadicRoundC (n : ℕ) (z : ℂ) : ℂ := ⟨dyadicRound n z.re, dyadicRound n z.im⟩

end QuantumZipper
