/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.RightHull
import ComplexSLE.Internal.Scaling_RightHull

/-!
# Scaling property (2.1) for right hulls
-/

public section

open scoped NNReal ComplexConjugate

namespace ComplexSLE

/-- **Scaling property (2.1), right hulls** (paper.tex:L549-552): `R_t^{rU(·/r²)} = r R_{t/r²}`. -/
theorem scaling_rightHull (U : ℝ≥0 → ℂ) (hU : Continuous U) (r : ℝ≥0) (hr : 0 < r) (t : ℝ≥0) :
    rightHull (fun s => (r : ℂ) * U (s / r ^ 2)) (by fun_prop) t =
      (fun z => (r : ℂ) * z) '' rightHull U hU (t / r ^ 2) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ComplexSLE.Internal.scaling_rightHull U hU r hr t
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE

end
-- FROZEN_ANCHOR_SUFFIX_END
