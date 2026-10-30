/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Loewner.Transform

/-!
# Provider for `ComplexSLE.reflection_leftHull`

Implementation module for the frozen anchor `ComplexSLE/Frozen/Reflection_LeftHull.lean`.
The anchor is SEALED: it is proved by this module.

Loewner solutions are preserved by conjugation and negation, so the absorbing times and left
hulls are (see `ComplexSLE.Internal.Loewner.Transform`).
-/

public section

open scoped NNReal ComplexConjugate

namespace ComplexSLE.Internal

theorem reflection_leftHull (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) :
    leftHull (fun s => conj (U s)) t = conj '' leftHull U t ∧
      leftHull (fun s => -U s) t = Neg.neg '' leftHull U t :=
  ⟨leftHull_conj U t, leftHull_neg U t⟩

end ComplexSLE.Internal

end
