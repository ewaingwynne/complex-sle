/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.LoewnerMap
import ComplexSLE.Internal.LoewnerMap_Eq

/-!
# Characterization of the Loewner map: uniqueness
-/

public section

open scoped NNReal ENNReal

namespace ComplexSLE

/-- Characterization of `g_t`, uniqueness half (Def 1.1): for `z ∉ L_t` and any solution `γ` of
the Loewner problem from `z` on `[0, τ)` with `t < τ`, `g_t(z) = γ t`. -/
theorem loewnerMap_eq (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) (z : ↥(leftHull U t)ᶜ)
    (τ : ℝ≥0∞) (γ : ℝ → ℂ) (hγ : IsLoewnerSolution U z τ γ) (ht : (t : ℝ≥0∞) < τ) :
    loewnerMap U hU t z = γ t :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ComplexSLE.Internal.loewnerMap_eq U hU t z τ γ hγ ht
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE

end
-- FROZEN_ANCHOR_SUFFIX_END
