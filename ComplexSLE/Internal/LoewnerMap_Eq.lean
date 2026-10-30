/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.LoewnerMap

/-!
# Provider for `ComplexSLE.loewnerMap_eq`

Implementation module for the frozen anchor `ComplexSLE/Frozen/LoewnerMap_Eq.lean`.
-/

public section

open scoped NNReal ENNReal

namespace ComplexSLE.Internal

/-- See `ComplexSLE.loewnerMap_eq`. -/
theorem loewnerMap_eq (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) (z : ↥(leftHull U t)ᶜ)
    (τ : ℝ≥0∞) (γ : ℝ → ℂ) (hγ : IsLoewnerSolution U z τ γ) (ht : (t : ℝ≥0∞) < τ) :
    loewnerMap U hU t z = γ t := by
  have hz : (t : ℝ≥0∞) < absorbingTime U z := not_le.1 z.2
  have hspec := Classical.choose_spec (loewner_wellDefined U hU z).1
  have hof : ENNReal.ofReal (t : ℝ) = (t : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
  exact (loewner_wellDefined U hU z).2 (min (absorbingTime U z) τ) _ _
    ⟨hspec.1, fun s hs hsτ => hspec.2 s hs (lt_of_lt_of_le hsτ (min_le_left _ _))⟩
    ⟨hγ.1, fun s hs hsτ => hγ.2 s hs (lt_of_lt_of_le hsτ (min_le_right _ _))⟩
    ⟨t.2, by rw [hof]; exact lt_min hz ht⟩

end ComplexSLE.Internal

end
