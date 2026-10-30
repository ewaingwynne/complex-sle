/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.LeftHull
import ComplexSLE.Internal.Scaling_LeftHull

/-!
# Scaling property (2.1) for left hulls
-/

public section

open scoped NNReal

namespace ComplexSLE

/-- **Scaling property (2.1), left hulls** (paper.tex:L549-552): `L^{rU(·/r²)}_t = r L_{t/r²}`. -/
theorem scaling_leftHull (U : ℝ≥0 → ℂ) (hU : Continuous U) (r : ℝ≥0) (hr : 0 < r)
    (t : ℝ≥0) :
    leftHull (fun s => (r : ℂ) * U (s / r ^ 2)) t =
      (fun z => (r : ℂ) * z) '' leftHull U (t / r ^ 2) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE

end
-- FROZEN_ANCHOR_SUFFIX_END
