/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.LoewnerMap

/-!
# Provider for `ComplexSLE.loewnerMap_exists_solution`

Implementation module for the frozen anchor `ComplexSLE/Frozen/LoewnerMap_ExistsSolution.lean`.
-/

public section

open scoped NNReal ENNReal

namespace ComplexSLE.Internal

/-- See `ComplexSLE.loewnerMap_exists_solution`. -/
theorem loewnerMap_exists_solution (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) :
    ∃ γ : ℝ → ℂ, IsLoewnerSolution U z (absorbingTime U z) γ ∧
      ∀ (t : ℝ≥0) (h : z ∈ (leftHull U t)ᶜ), loewnerMap U hU t ⟨z, h⟩ = γ t :=
  ⟨Classical.choose (loewner_wellDefined U hU z).1,
   Classical.choose_spec (loewner_wellDefined U hU z).1, fun _ _ => rfl⟩

end ComplexSLE.Internal

end
