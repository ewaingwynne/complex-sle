/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.LoewnerMap

/-!
# The centered Loewner map
-/

@[expose] public section

open scoped NNReal

namespace ComplexSLE

/-- The centered Loewner map `f_t = g_t - U_t` on `ℂ ∖ L_t` (Def 1.1). -/
noncomputable def centeredLoewnerMap (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0)
    (z : ↥(leftHull U t)ᶜ) : ℂ :=
  loewnerMap U hU t z - U t

end ComplexSLE

end
