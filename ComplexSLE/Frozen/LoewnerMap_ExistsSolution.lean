/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.LoewnerMap
import ComplexSLE.Internal.LoewnerMap_ExistsSolution

/-!
# Characterization of the Loewner map: existence
-/

public section

open scoped NNReal ENNReal

namespace ComplexSLE

/-- Characterization of `g_t`, existence half (Def 1.1): `t ↦ g_t(z)` is a solution of the
Loewner problem from `z` on `[0, T_z)`. -/
theorem loewnerMap_exists_solution (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) :
    ∃ γ : ℝ → ℂ, IsLoewnerSolution U z (absorbingTime U z) γ ∧
      ∀ (t : ℝ≥0) (h : z ∈ (leftHull U t)ᶜ), loewnerMap U hU t ⟨z, h⟩ = γ t :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ComplexSLE.Internal.loewnerMap_exists_solution U hU z
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE

end
-- FROZEN_ANCHOR_SUFFIX_END
