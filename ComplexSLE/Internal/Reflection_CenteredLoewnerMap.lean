/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.RightHull
public import ComplexSLE.Internal.Loewner.MapTransform

/-!
# Provider for `ComplexSLE.reflection_centeredLoewnerMap`

Implementation module for the frozen anchor `ComplexSLE/Frozen/Reflection_CenteredLoewnerMap.lean`.
The anchor is SEALED: it is proved by this module.
-/

public section

open scoped NNReal ComplexConjugate
open Set

namespace ComplexSLE.Internal

/-- Reflection for the centered Loewner maps. -/
theorem reflection_centeredLoewnerMap (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) :
    (∀ (z : ℂ) (hz : z ∈ (leftHull (fun s => conj (U s)) t)ᶜ) (hz' : conj z ∈ (leftHull U t)ᶜ),
        centeredLoewnerMap (fun s => conj (U s)) (by fun_prop) t ⟨z, hz⟩ =
          conj (centeredLoewnerMap U hU t ⟨conj z, hz'⟩)) ∧
      ∀ (z : ℂ) (hz : z ∈ (leftHull (fun s => -U s) t)ᶜ) (hz' : -z ∈ (leftHull U t)ᶜ),
        centeredLoewnerMap (fun s => -U s) (by fun_prop) t ⟨z, hz⟩ =
          -centeredLoewnerMap U hU t ⟨-z, hz'⟩ := by
  exact ⟨fun z hz hz' => centeredLoewnerMap_conj U hU t z hz hz',
    fun z hz hz' => centeredLoewnerMap_neg U hU t z hz hz'⟩

end ComplexSLE.Internal

end
