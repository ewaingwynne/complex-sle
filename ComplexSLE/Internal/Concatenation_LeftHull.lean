/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.RightHull
public import ComplexSLE.Internal.Loewner.Concatenation

/-!
# Provider for `ComplexSLE.concatenation_leftHull`

Implementation module for the frozen anchor `ComplexSLE/Frozen/Concatenation_LeftHull.lean`.
The anchor is SEALED: it is proved by this module.
-/

public section

open scoped NNReal
open Set

namespace ComplexSLE.Internal

/-- Concatenation property (2.3), left hulls. -/
theorem concatenation_leftHull (U : ℝ≥0 → ℂ) (hU : Continuous U) (s t : ℝ≥0) :
    leftHull U (s + t) = leftHull U t ∪
      {z | ∃ h : z ∈ (leftHull U t)ᶜ,
        centeredLoewnerMap U hU t ⟨z, h⟩ ∈
          leftHull (fun r => U (r + t) - U t) s \ rightHull U hU t} := by
  ext z
  constructor
  · intro hzs
    by_cases hz : z ∈ leftHull U t
    · exact Or.inl hz
    · refine Or.inr ⟨hz, (mem_leftHull_add_iff hU s t z hz).1 hzs, ?_⟩
      exact fun h => h ⟨⟨z, hz⟩, rfl⟩
  · rintro (hz | ⟨hz, h1, -⟩)
    · exact leftHull_mono le_add_self hz
    · exact (mem_leftHull_add_iff hU s t z hz).2 h1

end ComplexSLE.Internal

end
