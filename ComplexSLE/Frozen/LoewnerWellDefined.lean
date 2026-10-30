/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.AbsorbingTime
import ComplexSLE.Internal.LoewnerWellDefined

/-!
# Well-definedness of the Loewner chain
-/

public section

open scoped NNReal ENNReal

namespace ComplexSLE

/-- **Well-definedness of the Loewner chain** (Def 1.1, paper.tex:L251-268).
For continuous `U`, the Loewner initial value problem started at `z` has a solution on
`[0, T_z)`, and any two solutions on a common interval `[0, τ)` agree there. The maps `g_t`
are defined from this theorem only after it is proved. -/
theorem loewner_wellDefined (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) :
    (∃ γ, IsLoewnerSolution U z (absorbingTime U z) γ) ∧
      ∀ (τ : ℝ≥0∞) (γ₁ γ₂ : ℝ → ℂ), IsLoewnerSolution U z τ γ₁ → IsLoewnerSolution U z τ γ₂ →
          Set.EqOn γ₁ γ₂ {t | 0 ≤ t ∧ ENNReal.ofReal t < τ} :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE

end
-- FROZEN_ANCHOR_SUFFIX_END
