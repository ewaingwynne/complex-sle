/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.RightHull
import ComplexSLE.Internal.Concatenation_LeftHull

/-!
# Concatenation property (2.3)
-/

public section

open scoped NNReal

namespace ComplexSLE

/-- **Concatenation property (2.3), left hulls** (paper.tex:L559-565):
`L_{s+t} = L_t ∪ f_t^{-1}(L_{t,s+t} ∖ R_t)`. Since `f_t` takes values in `ℂ ∖ R_t`, the preimage of
`L_{t,s+t} ∖ R_t` equals the preimage of `L_{t,s+t}`. -/
theorem concatenation_leftHull (U : ℝ≥0 → ℂ) (hU : Continuous U) (s t : ℝ≥0) :
    leftHull U (s + t) = leftHull U t ∪
      {z | ∃ h : z ∈ (leftHull U t)ᶜ,
        centeredLoewnerMap U hU t ⟨z, h⟩ ∈ leftHull (fun r => U (r + t) - U t) s \ rightHull U hU t} :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ComplexSLE.Internal.concatenation_leftHull U hU s t
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE

end
-- FROZEN_ANCHOR_SUFFIX_END
