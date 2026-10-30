/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.RightHull
public import ComplexSLE.Internal.Loewner.Concatenation

/-!
# Provider for `ComplexSLE.concatenation_centeredLoewnerMap`

Implementation module for the frozen anchor `ComplexSLE/Frozen/Concatenation_CenteredLoewnerMap.lean`.
The anchor is SEALED: it is proved by this module.
-/

public section

open scoped NNReal
open Set

namespace ComplexSLE.Internal

/-- Concatenation property (2.3), maps. -/
theorem concatenation_centeredLoewnerMap (U : ℝ≥0 → ℂ) (hU : Continuous U) (s t : ℝ≥0) (z : ℂ)
    (hz : z ∈ (leftHull U (s + t))ᶜ) (hz₁ : z ∈ (leftHull U t)ᶜ)
    (hz₂ : centeredLoewnerMap U hU t ⟨z, hz₁⟩ ∈ (leftHull (fun r => U (r + t) - U t) s)ᶜ) :
    centeredLoewnerMap U hU (s + t) ⟨z, hz⟩ =
      centeredLoewnerMap (fun r => U (r + t) - U t) (by fun_prop) s
        ⟨centeredLoewnerMap U hU t ⟨z, hz₁⟩, hz₂⟩ :=
  centeredLoewnerMap_add_eq hU s t z hz hz₁ hz₂

end ComplexSLE.Internal

end
