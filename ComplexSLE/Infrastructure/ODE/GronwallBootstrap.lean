/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Analysis.ODE.Gronwall

/-!
# Grönwall's inequality with a bootstrap (tube) hypothesis

Mathlib's `norm_le_gronwallBound_of_norm_deriv_right_le` needs the differential inequality
`‖f' x‖ ≤ K ‖f x‖ + ε` at every point of `[a, b)`. For ODE stability estimates the inequality is
usually only available while the difference `f` stays in a small tube `‖f x‖ ≤ r` (the vector
fields are Lipschitz only away from a singularity). Since the Grönwall bound itself stays below
`r` on `[a, b]`, the tube hypothesis is self-improving, and it suffices to assume the inequality
at the points where `‖f x‖ ≤ r`
(`norm_le_gronwallBound_of_forall_le`).
-/

public section

open Set Filter Topology Real

namespace ComplexSLE.Infrastructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Grönwall with a tube hypothesis.** Let `f : ℝ → E` be continuous on `[a, b]` with right
derivative `f' x` on `[a, b)` and `‖f a‖ ≤ δ`. Suppose the Grönwall bound
`gronwallBound δ K ε (b - a)` is `< r` and the differential inequality `‖f' x‖ ≤ K ‖f x‖ + ε`
holds at every `x ∈ [a, b)` with `‖f x‖ ≤ r`. Then `‖f x‖ ≤ gronwallBound δ K ε (x - a)` on
`[a, b]`. -/
theorem norm_le_gronwallBound_of_forall_le {f f' : ℝ → E} {δ K ε r a b : ℝ} (hδ : 0 ≤ δ)
    (hK : 0 ≤ K) (hε : 0 ≤ ε) (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x) (ha : ‖f a‖ ≤ δ)
    (hr : gronwallBound δ K ε (b - a) < r)
    (bound : ∀ x ∈ Ico a b, ‖f x‖ ≤ r → ‖f' x‖ ≤ K * ‖f x‖ + ε) :
    ∀ x ∈ Icc a b, ‖f x‖ ≤ gronwallBound δ K ε (x - a) := by
  intro x hx
  -- for `ε' > ε` close to `ε` the bound stays below `r`
  have hev : ∀ᶠ ε' in 𝓝 ε, gronwallBound δ K ε' (b - a) < r :=
    (gronwallBound_continuous_ε δ K (b - a)).continuousAt.eventually (gt_mem_nhds hr)
  have hev' : ∀ᶠ ε' in 𝓝[>] ε, ‖f x‖ ≤ gronwallBound δ K ε' (x - a) := by
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with ε' hε'r hε'
    have hε'0 : 0 ≤ ε' := hε.trans (le_of_lt hε')
    have hmono := gronwallBound_mono hδ hε'0 hK
    refine image_le_of_liminf_slope_right_lt_deriv_boundary
      (f := fun y => ‖f y‖) (f' := fun y => ‖f' y‖) (B := gronwallBound δ K ε' ∘ fun y => y - a)
      (B' := fun y => K * gronwallBound δ K ε' (y - a) + ε')
      (continuous_norm.comp_continuousOn hf)
      (fun y hy _ hr' => (hf' y hy).liminf_right_slope_norm_le hr')
      ?_ (fun y => hasDerivAt_gronwallBound_shift δ K ε' y a) ?_ hx
    · simpa [gronwallBound_x0] using ha
    · intro y hy hyeq
      have hyB : gronwallBound δ K ε' (y - a) ≤ gronwallBound δ K ε' (b - a) :=
        hmono (by linarith [hy.2])
      have hyr : ‖f y‖ ≤ r := by
        have : ‖f y‖ = gronwallBound δ K ε' (y - a) := hyeq
        linarith
      have h1 := bound y hy hyr
      have h2 : ‖f y‖ = gronwallBound δ K ε' (y - a) := hyeq
      rw [h2] at h1
      have hεε' : ε < ε' := hε'
      linarith
  exact ge_of_tendsto
    ((gronwallBound_continuous_ε δ K (x - a)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    hev'

end ComplexSLE.Infrastructure

end
