/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsContLocalMartingale
public import ComplexSLE.External.TimeChangeIsContLocalMartingale

/-!
# Helper lemmas for stopped local martingales

Source-independent helper lemmas:

* `measurableSpace_prod_mono`: monotonicity of the product σ-algebra (used in the filtration
  transfer lemma `isContLocalMartingale_of_le_of_inter_lt`);
* `MeasureTheory.IsStoppingTime.measurableSpace_congr`: the σ-algebra of a stopping time only
  depends on the stopping time as a function.
-/

public section

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

section Transfer

variable (ℱ : Filtration ℝ≥0 mΩ) {ρ : Ω → ℝ≥0}

/-- Monotonicity of the product σ-algebra. -/
theorem measurableSpace_prod_mono {α β : Type*} {m₁ m₁' : MeasurableSpace α}
    {m₂ m₂' : MeasurableSpace β} (h₁ : m₁ ≤ m₁') (h₂ : m₂ ≤ m₂') :
    m₁.prod m₂ ≤ m₁'.prod m₂' :=
  sup_le_sup (MeasurableSpace.comap_mono h₁) (MeasurableSpace.comap_mono h₂)

/-- The σ-algebra of a stopping time only depends on the stopping time as a function. -/
theorem _root_.MeasureTheory.IsStoppingTime.measurableSpace_congr {τ₁ τ₂ : Ω → WithTop ℝ≥0}
    (h₁ : IsStoppingTime ℱ τ₁) (h₂ : IsStoppingTime ℱ τ₂) (h : τ₁ = τ₂) :
    h₁.measurableSpace = h₂.measurableSpace := by
  subst h; rfl

end Transfer

end ComplexSLE

end
