/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.RightHull
import ComplexSLE.Internal.Concatenation_CenteredLoewnerMap

/-!
# Concatenation property (2.3)
-/

public section

open scoped NNReal

namespace ComplexSLE

/-- **Concatenation property (2.3), maps** (paper.tex:L559-565): with `f_{t,s+t}` the centered chain
driven by `U(· + t) - U(t)`, `f_{s+t} = f_{t,s+t} ∘ f_t` on `ℂ ∖ L_{s+t}`. -/
theorem concatenation_centeredLoewnerMap (U : ℝ≥0 → ℂ) (hU : Continuous U) (s t : ℝ≥0) (z : ℂ)
    (hz : z ∈ (leftHull U (s + t))ᶜ) (hz₁ : z ∈ (leftHull U t)ᶜ)
    (hz₂ : centeredLoewnerMap U hU t ⟨z, hz₁⟩ ∈ (leftHull (fun r => U (r + t) - U t) s)ᶜ) :
    centeredLoewnerMap U hU (s + t) ⟨z, hz⟩ =
      centeredLoewnerMap (fun r => U (r + t) - U t) (by fun_prop) s
        ⟨centeredLoewnerMap U hU t ⟨z, hz₁⟩, hz₂⟩ :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE

end
-- FROZEN_ANCHOR_SUFFIX_END
