/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Loewner.Transform

/-!
# Provider for `ComplexSLE.scaling_leftHull`

Implementation module for the frozen anchor `ComplexSLE/Frozen/Scaling_LeftHull.lean`.
The anchor is SEALED: it is proved by this module.

Loewner solutions transform under `γ ↦ r γ(·/r²)`, hence absorbing times scale by `r²`
(see `ComplexSLE.Internal.Loewner.Transform`).
-/

public section

open scoped NNReal

namespace ComplexSLE.Internal

theorem scaling_leftHull (U : ℝ≥0 → ℂ) (hU : Continuous U) (r : ℝ≥0) (hr : 0 < r)
    (t : ℝ≥0) :
    leftHull (fun s => (r : ℂ) * U (s / r ^ 2)) t =
      (fun z => (r : ℂ) * z) '' leftHull U (t / r ^ 2) :=
  leftHull_scale U r hr t

end ComplexSLE.Internal

end
