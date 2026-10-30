/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.RightHull
import ComplexSLE.Internal.Scaling_CenteredLoewnerMap

/-!
# Scaling property (2.1) for the centered Loewner maps
-/

public section

open scoped NNReal ComplexConjugate

namespace ComplexSLE

/-- **Scaling property (2.1), maps** (paper.tex:L549-552): `f_t^{rU(·/r²)}(z) = r f_{t/r²}(z/r)`. -/
theorem scaling_centeredLoewnerMap (U : ℝ≥0 → ℂ) (hU : Continuous U) (r : ℝ≥0) (hr : 0 < r) (t : ℝ≥0) (z : ℂ)
    (hz : z ∈ (leftHull (fun s => (r : ℂ) * U (s / r ^ 2)) t)ᶜ)
    (hz' : z / r ∈ (leftHull U (t / r ^ 2))ᶜ) :
    centeredLoewnerMap (fun s => (r : ℂ) * U (s / r ^ 2)) (by fun_prop) t ⟨z, hz⟩ =
      r * centeredLoewnerMap U hU (t / r ^ 2) ⟨z / r, hz'⟩ :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ComplexSLE.Internal.scaling_centeredLoewnerMap U hU r hr t z hz hz'
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE

end
-- FROZEN_ANCHOR_SUFFIX_END
