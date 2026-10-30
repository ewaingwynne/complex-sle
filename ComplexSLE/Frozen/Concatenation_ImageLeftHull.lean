/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.RightHull
import ComplexSLE.Internal.Concatenation_ImageLeftHull

/-!
# Concatenation property (2.3)
-/

public section

open scoped NNReal

namespace ComplexSLE

/-- **Concatenation property (2.3), image of the new part of the hull** (paper.tex:L559-565, read with
ERRATA R18): `f_t(L_{s+t} ∖ L_t) = L_{t,s+t} ∖ R_t`. -/
theorem concatenation_image_leftHull (U : ℝ≥0 → ℂ) (hU : Continuous U) (s t : ℝ≥0) :
    (fun z : ↥(leftHull U t)ᶜ => centeredLoewnerMap U hU t z) '' {z | (z : ℂ) ∈ leftHull U (s + t)} =
      leftHull (fun r => U (r + t) - U t) s \ rightHull U hU t :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE

end
-- FROZEN_ANCHOR_SUFFIX_END
