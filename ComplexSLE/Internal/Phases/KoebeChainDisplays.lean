/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.KoebeChain
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# Transfer through `f_t` for `step:converse-event-converges` (M7/E3)

Companion of `KoebeChain.lean`: the deterministic lemma `exists_infDist_futureHull_lt`, the first
half of the `SOURCE_GAP` of `step:converse-event-converges`. If `z ∉ L_t`, smallness of
`dist(z, L_{s+t})` forces smallness of `dist(f_t z, L_{t,s+t})`, uniformly in `s`.

No EXTERNAL input is consumed here.
-/

public section

open scoped NNReal ENNReal Topology
open Set Metric Filter ComplexSLE.Internal ComplexSLE.Internal.Polar

namespace ComplexSLE.Internal.KoebeChain

variable {U : ℝ≥0 → ℂ}

section Displays

variable (hU : Continuous U) {t s : ℝ≥0} {z : ℂ}

/-! ### `step:converse-event-converges`: `1_{E_s} → 1` (deterministic form) -/

/-- **Transfer through `f_t` at the interior point `z`** (the first half of the `SOURCE_GAP` of
`step:converse-event-converges`): if `z ∉ L_t` then for every `ε > 0` there is `δ > 0` such that
`dist(z, L_{s+t}) < δ` implies `dist(f_t z, L_{t,s+t}) < ε` (for every `s`). Only continuity of
`f_t` at `z` and the concatenation property (2.3) (`f_t(L_{s+t} ∖ L_t) ⊆ L_{t,s+t}`) are used. -/
theorem exists_infDist_futureHull_lt (hU : Continuous U) {t : ℝ≥0} {z : ℂ}
    (hz₁ : z ∉ leftHull U t) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s : ℝ≥0, infDist z (leftHull U (s + t)) < δ →
      infDist (fPath U hU z t) (leftHull (futureDriver U t) s) < ε := by
  have hdt : 0 < infDist z (leftHull U t) := infDist_leftHull_pos hU hz₁
  have hcont : ContinuousAt (fun w => fPath U hU w t) z :=
    (hasDerivAt_fPath_initial hU (coe_mem_lifeSet_iff.2 hz₁)).continuousAt
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuousAt_iff.1 hcont ε hε
  refine ⟨min δ₁ (infDist z (leftHull U t)), lt_min hδ₁ hdt, fun s hs => ?_⟩
  obtain ⟨p, hpL, hpd⟩ := (infDist_lt_iff (leftHull_nonempty U (s + t))).1 hs
  have hp₁ : p ∉ leftHull U t := by
    intro hp
    have h1 := infDist_le_dist_of_mem (x := z) hp
    exact absurd (lt_of_lt_of_le hpd (min_le_right _ _)) (not_lt.2 h1)
  have hpB : fPath U hU p t ∈ leftHull (futureDriver U t) s :=
    (fPath_mem_leftHull_iff hU t s hp₁).2 hpL
  have hdp : dist p z < δ₁ := by
    rw [dist_comm]; exact lt_of_lt_of_le hpd (min_le_left _ _)
  have := hδ₁' hdp
  rw [dist_comm] at this
  exact lt_of_le_of_lt (infDist_le_dist_of_mem hpB) this

end Displays

end ComplexSLE.Internal.KoebeChain

end
