/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.RightHull
import ComplexSLE.Internal.Concatenation_RightHull

/-!
# Concatenation property (2.3)
-/

public section

open scoped NNReal

namespace ComplexSLE

/-- **Concatenation property (2.3), right hulls** (paper.tex:L559-565):
`R_{s+t} = R_{t,s+t} ∪ f_{t,s+t}(R_t ∖ L_{t,s+t})`. -/
theorem concatenation_rightHull (U : ℝ≥0 → ℂ) (hU : Continuous U) (s t : ℝ≥0) :
    rightHull U hU (s + t) =
      rightHull (fun r => U (r + t) - U t) (by fun_prop) s ∪
        (fun w : ↥(leftHull (fun r => U (r + t) - U t) s)ᶜ =>
            centeredLoewnerMap (fun r => U (r + t) - U t) (by fun_prop) s w) ''
          {w | (w : ℂ) ∈ rightHull U hU t} :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ComplexSLE.Internal.concatenation_rightHull U hU s t
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE

end
-- FROZEN_ANCHOR_SUFFIX_END
