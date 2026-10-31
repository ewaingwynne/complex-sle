/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.External.KoebeQuarter
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# Two-sided Koebe comparison for an injective holomorphic map (M7/E3, general)

Source: paper.tex:L1700-1705 (the Koebe quarter theorem in the form
`|φ'(z)| dist(z, K₁) ≍ dist(φ(z), K₂)` for a conformal map `φ : ℂ ∖ K₁ → ℂ ∖ K₂`), with the
implicit constants made explicit (`1/4` and `4`). Deterministic; no Loewner input.

Let `F : ℂ → ℂ` be holomorphic and injective on `Kᶜ`, `z ∉ K`.

* `ball_subset_image_ball`: the Koebe quarter theorem rescaled to a disc `B(z, ρ)`: the image of
  `B(z, ρ)` under `F` contains `B(F z, |F'(z)| ρ / 4)`.
* `norm_deriv_mul_infDist_le` (**lower bound for the image distance**): if `F` maps `Kᶜ` into
  `K'ᶜ` then `|F'(z)| · dist(z, K) ≤ 4 · dist(F z, K')`.
* `infDist_image_le` (**upper bound for the image distance**): if `Kᶜ` is open, `F' ≠ 0` on `Kᶜ`
  and `K'ᶜ ⊆ F(Kᶜ)`, then `dist(F z, K') ≤ 4 · |F'(z)| · dist(z, K)`. Proof: the inverse
  `G = F⁻¹ : F(Kᶜ) → Kᶜ` is holomorphic on the disc `B(F z, dist(F z, K')) ⊆ F(Kᶜ)` (inverse
  function theorem, one complex variable) and injective, with `G'(F z) = 1 / F'(z)`; apply
  `ball_subset_image_ball` to `G`.

Every result here consumes the EXTERNAL `koebe_quarter` (`PROVED_REL{koebe_quarter}`).
-/

public section

open scoped Topology
open Set Metric Filter Function

namespace ComplexSLE.Internal.KoebeChain

/-- **Koebe quarter theorem on a disc** (rescaled `koebe_quarter`): if `F` is holomorphic and
injective on `B(z, ρ)`, `ρ > 0`, then `F(B(z, ρ)) ⊇ B(F z, |F'(z)| ρ / 4)`. -/
theorem ball_subset_image_ball (F : ℂ → ℂ) {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hF : DifferentiableOn ℂ F (ball z ρ)) (hinj : InjOn F (ball z ρ)) :
    ball (F z) (‖deriv F z‖ * ρ / 4) ⊆ F '' ball z ρ := by
  set H : ℂ → ℂ := fun ζ => F (z + (ρ : ℂ) * ζ) with hH
  have hmaps : ∀ ζ ∈ ball (0 : ℂ) 1, z + (ρ : ℂ) * ζ ∈ ball z ρ := by
    intro ζ hζ
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hρ.le]
    have : ‖ζ‖ < 1 := by simpa using hζ
    nlinarith
  have hFat : ∀ ζ ∈ ball (0 : ℂ) 1, DifferentiableAt ℂ F (z + (ρ : ℂ) * ζ) := fun ζ hζ =>
    (hF _ (hmaps ζ hζ)).differentiableAt (isOpen_ball.mem_nhds (hmaps ζ hζ))
  have hderiv : ∀ ζ ∈ ball (0 : ℂ) 1,
      HasDerivAt H (deriv F (z + (ρ : ℂ) * ζ) * (ρ : ℂ)) ζ := by
    intro ζ hζ
    have h2 : HasDerivAt (fun ζ : ℂ => z + (ρ : ℂ) * ζ) (ρ : ℂ) ζ := by
      simpa using ((hasDerivAt_id ζ).const_mul (ρ : ℂ)).const_add z
    exact (hFat ζ hζ).hasDerivAt.comp ζ h2
  have hdiff : DifferentiableOn ℂ H (ball (0 : ℂ) 1) := fun ζ hζ =>
    (hderiv ζ hζ).differentiableAt.differentiableWithinAt
  have hρ0 : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ.ne'
  have hHinj : InjOn H (ball (0 : ℂ) 1) := by
    intro ζ₁ h₁ ζ₂ h₂ h
    exact mul_left_cancel₀ hρ0
      (add_left_cancel (hinj (hmaps ζ₁ h₁) (hmaps ζ₂ h₂) h))
  have hkoebe := External.koebe_quarter H hdiff hHinj
  have hH0 : H 0 = F z := by simp [hH]
  have hdH0 : deriv H 0 = deriv F z * (ρ : ℂ) := by
    have := hderiv 0 (mem_ball_self one_pos)
    simpa using this.deriv
  intro y hy
  have hy' : y ∈ ball (H 0) (‖deriv H 0‖ / 4) := by
    rw [hH0, hdH0, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    exact hy
  obtain ⟨ζ, hζ, rfl⟩ := hkoebe hy'
  exact ⟨z + (ρ : ℂ) * ζ, hmaps ζ hζ, rfl⟩

/-- A disc `B(z, ρ)` with `ρ = dist(z, K)` does not meet `K`. -/
theorem ball_infDist_subset_compl (z : ℂ) (K : Set ℂ) : ball z (infDist z K) ⊆ Kᶜ := by
  intro w hw hwK
  have h1 := infDist_le_dist_of_mem (x := z) hwK
  rw [mem_ball, dist_comm] at hw
  exact absurd hw (not_lt.2 h1)

/-- If `B(z, r) ∩ K = ∅` then `r ≤ dist(z, K)` (for nonempty `K`). -/
theorem le_infDist_of_ball_subset {z : ℂ} {K : Set ℂ} {r : ℝ} (hK : K.Nonempty)
    (h : ball z r ⊆ Kᶜ) : r ≤ infDist z K := by
  refine (le_infDist hK).2 fun k hk => ?_
  by_contra hlt
  exact h (mem_ball.2 (by rw [dist_comm]; exact not_le.1 hlt)) hk

/-- **Koebe quarter, lower bound for the image distance**: if `F` is holomorphic and injective on
`Kᶜ` and maps `Kᶜ` into `K'ᶜ` (`K'` nonempty), then for `z ∉ K`,
`|F'(z)| · dist(z, K) ≤ 4 · dist(F z, K')`. -/
theorem norm_deriv_mul_infDist_le (F : ℂ → ℂ) {K K' : Set ℂ} (hK' : K'.Nonempty)
    (hF : DifferentiableOn ℂ F Kᶜ) (hinj : InjOn F Kᶜ) (hmaps : ∀ x, x ∉ K → F x ∉ K')
    {z : ℂ} :
    ‖deriv F z‖ * infDist z K ≤ 4 * infDist (F z) K' := by
  set ρ : ℝ := infDist z K with hρ
  rcases (infDist_nonneg (x := z) (s := K)).eq_or_lt with h0 | hpos
  · have hρ0 : ρ = 0 := h0.symm
    rw [hρ0, mul_zero]
    exact mul_nonneg (by norm_num) infDist_nonneg
  have hball : ball z ρ ⊆ Kᶜ := ball_infDist_subset_compl z K
  have hkoebe := ball_subset_image_ball F hpos (hF.mono hball) (hinj.mono hball)
  have hsub : ball (F z) (‖deriv F z‖ * ρ / 4) ⊆ K'ᶜ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hkoebe hy
    exact hmaps x (hball hx)
  have := le_infDist_of_ball_subset hK' hsub
  linarith

/-- The local inverse of an injective holomorphic map with nonzero derivative on an open set
`Ω`: `G = invFunOn F Ω` is differentiable at `u = F p`, `p ∈ Ω`, with derivative `(F' p)⁻¹`. -/
theorem hasDerivAt_invFunOn (F : ℂ → ℂ) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℂ F Ω) (hinj : InjOn F Ω) (hd : ∀ p ∈ Ω, deriv F p ≠ 0)
    {p : ℂ} (hp : p ∈ Ω) :
    HasDerivAt (invFunOn F Ω) (deriv F p)⁻¹ (F p) := by
  have hstrict : HasStrictDerivAt F (deriv F p) p :=
    (hF.analyticAt (hΩ.mem_nhds hp)).hasStrictDerivAt
  have hne := hd p hp
  set Gl := hstrict.localInverse F (deriv F p) p hne with hGl
  have hGl_d : HasStrictDerivAt Gl (deriv F p)⁻¹ (F p) := hstrict.to_localInverse hne
  have hleft : Gl (F p) = p := (hstrict.eventually_left_inverse hne).self_of_nhds
  have hGlcont : ContinuousAt Gl (F p) := hGl_d.hasDerivAt.continuousAt
  have hmem : ∀ᶠ y in 𝓝 (F p), Gl y ∈ Ω := by
    refine hGlcont.eventually_mem (hΩ.mem_nhds ?_)
    rwa [hleft]
  have hright := hstrict.eventually_right_inverse hne
  have heq : Gl =ᶠ[𝓝 (F p)] invFunOn F Ω := by
    filter_upwards [hmem, hright] with y hy1 hy2
    have h3 := hinj.leftInvOn_invFunOn hy1
    rw [hy2] at h3
    exact h3.symm
  exact hGl_d.hasDerivAt.congr_of_eventuallyEq heq.symm

/-- **Koebe quarter, upper bound for the image distance**: if `Kᶜ` is open, `F` is holomorphic and
injective on `Kᶜ` with `F' ≠ 0` there, and `K'ᶜ ⊆ F(Kᶜ)` (`K, K'` nonempty), then for `z ∉ K`,
`dist(F z, K') ≤ 4 · |F'(z)| · dist(z, K)`. -/
theorem infDist_image_le (F : ℂ → ℂ) {K K' : Set ℂ} (hK : K.Nonempty) (hKo : IsOpen Kᶜ)
    (hF : DifferentiableOn ℂ F Kᶜ) (hinj : InjOn F Kᶜ) (hd : ∀ p ∈ Kᶜ, deriv F p ≠ 0)
    (hsurj : K'ᶜ ⊆ F '' Kᶜ) {z : ℂ} (hz : z ∉ K) :
    infDist (F z) K' ≤ 4 * (‖deriv F z‖ * infDist z K) := by
  set w : ℂ := F z with hw
  set ρ : ℝ := infDist w K' with hρ
  rcases (infDist_nonneg (x := w) (s := K')).eq_or_lt with h0 | hpos
  · have hρ0 : ρ = 0 := h0.symm
    rw [hρ0]
    exact mul_nonneg (by norm_num) (mul_nonneg (norm_nonneg _) infDist_nonneg)
  set G : ℂ → ℂ := invFunOn F Kᶜ with hG
  have hball : ball w ρ ⊆ F '' Kᶜ := fun y hy =>
    hsurj (ball_infDist_subset_compl w K' hy)
  have hGmem : ∀ y ∈ ball w ρ, G y ∈ Kᶜ := fun y hy => invFunOn_mem (hball hy)
  have hFG : ∀ y ∈ ball w ρ, F (G y) = y := fun y hy => invFunOn_eq (hball hy)
  have hGinj : InjOn G (ball w ρ) := by
    intro a ha b hb h
    rw [← hFG a ha, ← hFG b hb, h]
  have hGd : ∀ y ∈ ball w ρ, HasDerivAt G (deriv F (G y))⁻¹ y := by
    intro y hy
    have := hasDerivAt_invFunOn F hKo hF hinj hd (hGmem y hy)
    rwa [hFG y hy] at this
  have hGdiff : DifferentiableOn ℂ G (ball w ρ) := fun y hy =>
    (hGd y hy).differentiableAt.differentiableWithinAt
  have hGw : G w = z := hinj.leftInvOn_invFunOn hz
  have hkoebe := ball_subset_image_ball G hpos hGdiff hGinj
  have hderivw : deriv G w = (deriv F z)⁻¹ := by
    have := (hGd w (mem_ball_self hpos)).deriv
    rwa [hGw] at this
  rw [hGw, hderivw] at hkoebe
  have hsub : ball z (‖(deriv F z)⁻¹‖ * ρ / 4) ⊆ Kᶜ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hkoebe hy
    exact hGmem x hx
  have hle := le_infDist_of_ball_subset hK hsub
  have hFz : 0 < ‖deriv F z‖ := norm_pos_iff.2 (hd z hz)
  rw [norm_inv] at hle
  have h1 : ‖deriv F z‖⁻¹ * ρ ≤ 4 * infDist z K := by linarith
  have h2 := mul_le_mul_of_nonneg_left h1 hFz.le
  rw [← mul_assoc, mul_inv_cancel₀ hFz.ne', one_mul] at h2
  linarith

end ComplexSLE.Internal.KoebeChain

end
