/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.RightHull
import ComplexSLE.Internal.Reflection_CenteredLoewnerMap

/-!
# Reflection property for the centered Loewner maps
-/

public section

open scoped NNReal ComplexConjugate

namespace ComplexSLE

/-- **Reflection for the maps** (derived from Def 1.1; the source states (2.2) for hulls and uses it
for the maps at L984, L1165): `f_t^{U*}(z) = (f_t(z*))*` and `f_t^{-U}(z) = -f_t(-z)`. -/
theorem reflection_centeredLoewnerMap (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) :
    (∀ (z : ℂ) (hz : z ∈ (leftHull (fun s => conj (U s)) t)ᶜ) (hz' : conj z ∈ (leftHull U t)ᶜ),
        centeredLoewnerMap (fun s => conj (U s)) (by fun_prop) t ⟨z, hz⟩ =
          conj (centeredLoewnerMap U hU t ⟨conj z, hz'⟩)) ∧
      ∀ (z : ℂ) (hz : z ∈ (leftHull (fun s => -U s) t)ᶜ) (hz' : -z ∈ (leftHull U t)ᶜ),
        centeredLoewnerMap (fun s => -U s) (by fun_prop) t ⟨z, hz⟩ =
          -centeredLoewnerMap U hU t ⟨-z, hz'⟩ :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE

end
-- FROZEN_ANCHOR_SUFFIX_END
