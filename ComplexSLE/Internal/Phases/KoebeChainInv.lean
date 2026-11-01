/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Zipper.QuantumZipper.Proofs.Complex.KoebeCovering
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# Two-sided Koebe comparison for an injective holomorphic map (M7/E3, general)

Source: paper.tex:L1700-1705 (the Koebe `1/4` theorem in the form
`|φ'(z)| dist(z, K₁) ≍ dist(φ(z), K₂)` for a conformal map `φ : ℂ ∖ K₁ → ℂ ∖ K₂`), with the
implicit constants made explicit. The sharp Koebe constant `1/4` is not available (it needs the
area theorem); this file uses the covering theorem with the non-sharp constant `1/48`
(`QuantumZipper.CA.Koebe.ball_subset_image_koebe`, fully proved, ported from a third-party
repository), i.e. the universal constant `koebeK = 48` in place of `4`. The paper only uses
"some universal constant". Deterministic; no Loewner input.

Let `F : ℂ → ℂ` be holomorphic and injective on `Kᶜ`, `z ∉ K`.

* `koebeK = 48`: the Koebe constant of this project (`1 / koebeCovConst`).
* `ball_subset_image_ball`: the Koebe covering theorem on a disc `B(z, ρ)`: the image of
  `B(z, ρ)` under `F` contains `B(F z, |F'(z)| ρ / koebeK)`.
* `norm_deriv_mul_infDist_le` (**lower bound for the image distance**): if `F` maps `Kᶜ` into
  `K'ᶜ` then `|F'(z)| · dist(z, K) ≤ koebeK · dist(F z, K')`.
* `infDist_image_le` (**upper bound for the image distance**): if `Kᶜ` is open, `F' ≠ 0` on `Kᶜ`
  and `K'ᶜ ⊆ F(Kᶜ)`, then `dist(F z, K') ≤ koebeK · |F'(z)| · dist(z, K)`. Proof: the inverse
  `G = F⁻¹ : F(Kᶜ) → Kᶜ` is holomorphic on the disc `B(F z, dist(F z, K')) ⊆ F(Kᶜ)` (inverse
  function theorem, one complex variable) and injective, with `G'(F z) = 1 / F'(z)`; apply
  `ball_subset_image_ball` to `G`.

No EXTERNAL input is consumed here.
-/

public section

open scoped Topology
open Set Metric Filter Function

namespace ComplexSLE.Internal.KoebeChain

/-- **The Koebe constant** `K = 48` of this project: the (non-sharp) Koebe covering theorem
`QuantumZipper.CA.Koebe.ball_subset_image_koebe` covers a disc of radius `|f'(c)| r / 48`. It
replaces the sharp constant `4` (`= 1 / (1/4)`) of the paper's Koebe `1/4` theorem. -/
@[expose] def koebeK : ℝ := 48

theorem koebeK_eq : koebeK = 48 := rfl

theorem koebeK_pos : 0 < koebeK := by norm_num [koebeK]

theorem one_le_koebeK : 1 ≤ koebeK := by norm_num [koebeK]

theorem koebeCovConst_eq_inv : QuantumZipper.CA.Koebe.koebeCovConst = koebeK⁻¹ := by
  norm_num [QuantumZipper.CA.Koebe.koebeCovConst, koebeK]

/-- **Koebe covering theorem on a disc**: if `F` is holomorphic and injective on `B(z, ρ)`,
`ρ > 0`, then `F(B(z, ρ)) ⊇ B(F z, |F'(z)| ρ / koebeK)` (`koebeK = 48`). -/
theorem ball_subset_image_ball (F : ℂ → ℂ) {z : ℂ} {ρ : ℝ} (_hρ : 0 < ρ)
    (hF : DifferentiableOn ℂ F (ball z ρ)) (hinj : InjOn F (ball z ρ)) :
    ball (F z) (‖deriv F z‖ * ρ / koebeK) ⊆ F '' ball z ρ := by
  have h := QuantumZipper.CA.Koebe.ball_subset_image_koebe hF hinj
  have e : ‖deriv F z‖ * ρ / koebeK = QuantumZipper.CA.Koebe.koebeCovConst * ρ * ‖deriv F z‖ := by
    rw [koebeCovConst_eq_inv]; ring
  rwa [e]

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

/-- **Koebe, lower bound for the image distance**: if `F` is holomorphic and injective on
`Kᶜ` and maps `Kᶜ` into `K'ᶜ` (`K'` nonempty), then for `z ∉ K`,
`|F'(z)| · dist(z, K) ≤ koebeK · dist(F z, K')`. -/
theorem norm_deriv_mul_infDist_le (F : ℂ → ℂ) {K K' : Set ℂ} (hK' : K'.Nonempty)
    (hF : DifferentiableOn ℂ F Kᶜ) (hinj : InjOn F Kᶜ) (hmaps : ∀ x, x ∉ K → F x ∉ K')
    {z : ℂ} :
    ‖deriv F z‖ * infDist z K ≤ koebeK * infDist (F z) K' := by
  set ρ : ℝ := infDist z K with hρ
  rcases (infDist_nonneg (x := z) (s := K)).eq_or_lt with h0 | hpos
  · have hρ0 : ρ = 0 := h0.symm
    rw [hρ0, mul_zero]
    exact mul_nonneg koebeK_pos.le infDist_nonneg
  have hball : ball z ρ ⊆ Kᶜ := ball_infDist_subset_compl z K
  have hkoebe := ball_subset_image_ball F hpos (hF.mono hball) (hinj.mono hball)
  have hsub : ball (F z) (‖deriv F z‖ * ρ / koebeK) ⊆ K'ᶜ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hkoebe hy
    exact hmaps x (hball hx)
  have := le_infDist_of_ball_subset hK' hsub
  rwa [div_le_iff₀ koebeK_pos, mul_comm (infDist (F z) K')] at this

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

/-- **Koebe, upper bound for the image distance**: if `Kᶜ` is open, `F` is holomorphic and
injective on `Kᶜ` with `F' ≠ 0` there, and `K'ᶜ ⊆ F(Kᶜ)` (`K, K'` nonempty), then for `z ∉ K`,
`dist(F z, K') ≤ koebeK · |F'(z)| · dist(z, K)`. -/
theorem infDist_image_le (F : ℂ → ℂ) {K K' : Set ℂ} (hK : K.Nonempty) (hKo : IsOpen Kᶜ)
    (hF : DifferentiableOn ℂ F Kᶜ) (hinj : InjOn F Kᶜ) (hd : ∀ p ∈ Kᶜ, deriv F p ≠ 0)
    (hsurj : K'ᶜ ⊆ F '' Kᶜ) {z : ℂ} (hz : z ∉ K) :
    infDist (F z) K' ≤ koebeK * (‖deriv F z‖ * infDist z K) := by
  set w : ℂ := F z with hw
  set ρ : ℝ := infDist w K' with hρ
  rcases (infDist_nonneg (x := w) (s := K')).eq_or_lt with h0 | hpos
  · have hρ0 : ρ = 0 := h0.symm
    rw [hρ0]
    exact mul_nonneg koebeK_pos.le (mul_nonneg (norm_nonneg _) infDist_nonneg)
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
  have hsub : ball z (‖(deriv F z)⁻¹‖ * ρ / koebeK) ⊆ Kᶜ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hkoebe hy
    exact hGmem x hx
  have hle := le_infDist_of_ball_subset hK hsub
  have hFz : 0 < ‖deriv F z‖ := norm_pos_iff.2 (hd z hz)
  rw [norm_inv, div_le_iff₀ koebeK_pos] at hle
  have h1 : ‖deriv F z‖⁻¹ * ρ ≤ koebeK * infDist z K := by linarith
  have h2 := mul_le_mul_of_nonneg_left h1 hFz.le
  rw [← mul_assoc, mul_inv_cancel₀ hFz.ne', one_mul] at h2
  linarith

end ComplexSLE.Internal.KoebeChain

end
