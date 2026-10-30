/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.RightHull
public import ComplexSLE.Internal.Loewner.MapTransform

/-!
# Provider for `ComplexSLE.scaling_centeredLoewnerMap`

Implementation module for the frozen anchor `ComplexSLE/Frozen/Scaling_CenteredLoewnerMap.lean`.
The anchor is SEALED: it is proved by this module.
-/

public section

open scoped NNReal ComplexConjugate
open Set

namespace ComplexSLE.Internal

/-- Scaling property (2.1) for the centered Loewner maps. -/
theorem scaling_centeredLoewnerMap (U : ℝ≥0 → ℂ) (hU : Continuous U) (r : ℝ≥0) (hr : 0 < r)
    (t : ℝ≥0) (z : ℂ)
    (hz : z ∈ (leftHull (fun s => (r : ℂ) * U (s / r ^ 2)) t)ᶜ)
    (hz' : z / r ∈ (leftHull U (t / r ^ 2))ᶜ) :
    centeredLoewnerMap (fun s => (r : ℂ) * U (s / r ^ 2)) (by fun_prop) t ⟨z, hz⟩ =
      r * centeredLoewnerMap U hU (t / r ^ 2) ⟨z / r, hz'⟩ := by
  exact centeredLoewnerMap_scale U hU r hr t z hz hz'

end ComplexSLE.Internal

end
