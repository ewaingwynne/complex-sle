/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.LoewnerMap
import ComplexSLE.Internal.ExternalProofs.LoewnerMapTendstoUniformly

/-!
# Classical input (proved): Convergence of Loewner maps under driver convergence

Author-approved classical input (ERRATA.md R23). Proved in-project (M10, ruling R30) by
`ComplexSLE.Internal.ExternalProofs.loewnerMap_tendstoUniformly`.
-/

public section

open scoped NNReal Topology
open Filter

namespace ComplexSLE.External

/-- **E12 (Loewner convergence; [Law05, Prop 4.43] extended to ℂ).** If continuous drivers
`V n → U` locally uniformly, then for every `T`, `ε > 0`, eventually every `z` at distance
`≥ ε` from `L_T` lies outside the hulls `L^{V n}_t`, `t ≤ T`, and `g^{V n}_t(z) → g_t(z)`
uniformly in such `(t, z)` (Lemma 4.3 first bullet, paper.tex:L1999-2003; the source's `K_T` is
read as `L_T`). -/
theorem loewnerMap_tendstoUniformly (U : ℝ≥0 → ℂ) (hU : Continuous U) (V : ℕ → ℝ≥0 → ℂ)
    (hV : ∀ n, Continuous (V n)) (hconv : TendstoLocallyUniformly V U atTop) (T : ℝ≥0)
    (ε : ℝ) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ t ≤ T, ∀ z : ℂ, ε ≤ Metric.infDist z (leftHull U T) →
      ∃ (h₁ : z ∈ (leftHull (V n) t)ᶜ) (h₂ : z ∈ (leftHull U t)ᶜ),
        ‖loewnerMap (V n) (hV n) t ⟨z, h₁⟩ - loewnerMap U hU t ⟨z, h₂⟩‖ < η :=
-- FROZEN_ANCHOR_PROOF_BEGIN
 by exact ComplexSLE.Internal.ExternalProofs.loewnerMap_tendstoUniformly U hU V hV hconv T ε hε η hη
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE.External

end
-- FROZEN_ANCHOR_SUFFIX_END
