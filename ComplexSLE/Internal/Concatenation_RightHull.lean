/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.RightHull
public import ComplexSLE.Internal.Loewner.Concatenation
public import ComplexSLE.Internal.Loewner.Injective

/-!
# Provider for `ComplexSLE.concatenation_rightHull`

Implementation module for the frozen anchor `ComplexSLE/Frozen/Concatenation_RightHull.lean`.
The anchor is SEALED: it is proved by this module.
-/

public section

open scoped NNReal
open Set

namespace ComplexSLE.Internal

/-- Concatenation property (2.3), right hulls. -/
theorem concatenation_rightHull (U : ℝ≥0 → ℂ) (hU : Continuous U) (s t : ℝ≥0) :
    rightHull U hU (s + t) =
      rightHull (fun r => U (r + t) - U t) (by fun_prop) s ∪
        (fun w : ↥(leftHull (fun r => U (r + t) - U t) s)ᶜ =>
            centeredLoewnerMap (fun r => U (r + t) - U t) (by fun_prop) s w) ''
          {w | (w : ℂ) ∈ rightHull U hU t} := by
  have hinj := centeredLoewnerMap_injective (U := fun r => U (r + t) - U t) (by fun_prop) s
  ext u
  constructor
  · intro hu
    by_cases hR : u ∈ rightHull (fun r => U (r + t) - U t) (by fun_prop) s
    · exact Or.inl hR
    · obtain ⟨w, rfl⟩ : u ∈ Set.range
          (centeredLoewnerMap (fun r => U (r + t) - U t) (by fun_prop) s) := not_not.1 hR
      refine Or.inr ⟨w, fun hwr => hu ?_, rfl⟩
      exact (mem_range_centeredLoewnerMap_add_iff hU s t _).2 ⟨w, hwr, rfl⟩
  · intro hu hrange
    obtain ⟨w', hw'r, hw'u⟩ := (mem_range_centeredLoewnerMap_add_iff hU s t u).1 hrange
    rcases hu with hR | ⟨w, hwR, hwu⟩
    · exact hR ⟨w', hw'u⟩
    · exact hwR (by rw [hinj (hwu.trans hw'u.symm)]; exact hw'r)

end ComplexSLE.Internal

end
