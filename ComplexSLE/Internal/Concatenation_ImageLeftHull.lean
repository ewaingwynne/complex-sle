/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.RightHull
public import ComplexSLE.Internal.Loewner.Concatenation

/-!
# Provider for `ComplexSLE.concatenation_image_leftHull`

Implementation module for the frozen anchor `ComplexSLE/Frozen/Concatenation_ImageLeftHull.lean`.
The anchor is SEALED: it is proved by this module.
-/

public section

open scoped NNReal
open Set

namespace ComplexSLE.Internal

/-- Concatenation property (2.3), image of the new part of the hull (read with ERRATA R18). -/
theorem concatenation_image_leftHull (U : ℝ≥0 → ℂ) (hU : Continuous U) (s t : ℝ≥0) :
    (fun z : ↥(leftHull U t)ᶜ => centeredLoewnerMap U hU t z) ''
        {z | (z : ℂ) ∈ leftHull U (s + t)} =
      leftHull (fun r => U (r + t) - U t) s \ rightHull U hU t := by
  ext w
  constructor
  · rintro ⟨⟨z, hz⟩, hzs, rfl⟩
    exact ⟨(mem_leftHull_add_iff hU s t z hz).1 hzs, fun h => h ⟨⟨z, hz⟩, rfl⟩⟩
  · rintro ⟨hw, hR⟩
    obtain ⟨⟨z, hz⟩, rfl⟩ : w ∈ Set.range (centeredLoewnerMap U hU t) := not_not.1 hR
    exact ⟨⟨z, hz⟩, (mem_leftHull_add_iff hU s t z hz).2 hw, rfl⟩

end ComplexSLE.Internal

end
