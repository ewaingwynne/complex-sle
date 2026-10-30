/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.LoewnerMap

/-!
# EXTERNAL input: Conformality of the Loewner maps

Author-approved classical input (ERRATA.md R23). Assumed, not proved: its body is a permanent
`sorry`, and every result that uses it is reported `PROVED_REL`.
-/

public section

open scoped NNReal Topology
open Filter

namespace ComplexSLE.External

/-- **E-L4.5 (conformality of g_t; [Law05, Thm 4.5] for complex drivers).** For continuous `U`
and `t ≥ 0`, `ℂ ∖ L_t` is open, `L_t` is bounded, and `g_t` extends to a function that is
holomorphic and injective on `ℂ ∖ L_t` with `z (g_t(z) - z) → 2t` as `z → ∞`. The paper asserts
this "using exactly the same arguments as" Lawler (paper.tex:L279-281). -/
theorem loewnerMap_conformal (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) :
    IsOpen (leftHull U t)ᶜ ∧ Bornology.IsBounded (leftHull U t) ∧
      ∃ G : ℂ → ℂ, (∀ z : ↥(leftHull U t)ᶜ, G z = loewnerMap U hU t z) ∧
        DifferentiableOn ℂ G (leftHull U t)ᶜ ∧ Set.InjOn G (leftHull U t)ᶜ ∧
        Tendsto (fun z => z * (G z - z)) (Bornology.cobounded ℂ) (𝓝 (2 * (t : ℂ))) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE.External

end
-- FROZEN_ANCHOR_SUFFIX_END
