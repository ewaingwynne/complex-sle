/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Planar.Chain
public import ComplexSLE.Infrastructure.Planar.ChainArg
public import ComplexSLE.Infrastructure.Planar.ArgBranch
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Chain crossing (CL)

Let `B` be a preconnected subset of the strip `|Re| < ε` which reaches above `Im = h` and below
`Im = -h`, and let `β₀, …, βₙ` be a `ρ`-chain with `|Im βₖ| + 2ρ ≤ h` which goes from `Re ≤ -ε` to
`Re ≥ ε`. Then some `βₖ` is within `ρ` of `B`.

The proof uses the chain argument: if the chain stays at distance `> ρ` from `B`, then the chain
argument `Φ` is continuous on `B`, never vanishes on `B` (for `w ∈ B` the vector `w - β₀` points
to the right and `w - βₙ` to the left), and has opposite signs at the two far points of `B`
(computed along vertical rays), which contradicts the intermediate value theorem on `B`.
-/

public section

open Set Metric Complex Filter Topology

namespace ComplexSLE.Planar

lemma tendsto_ray_cocompact {b u : ℂ} (hu : u ≠ 0) :
    Tendsto (fun τ : ℝ => b + (τ : ℂ) * u) atTop (cocompact ℂ) := by
  rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
  have hu' : 0 < ‖u‖ := norm_pos_iff.2 hu
  have h1 : Tendsto (fun τ : ℝ => τ * ‖u‖ + (-‖b‖)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_id.atTop_mul_const hu')
  refine tendsto_atTop_mono' _ ?_ h1
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with τ hτ
  have h2 : ‖((τ : ℂ) * u)‖ ≤ ‖b + (τ : ℂ) * u‖ + ‖b‖ := by
    calc ‖((τ : ℂ) * u)‖ = ‖(b + (τ : ℂ) * u) - b‖ := by congr 1; ring
      _ ≤ ‖b + (τ : ℂ) * u‖ + ‖b‖ := norm_sub_le _ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ] at h2
  linarith

/-- Along a ray avoiding the chain, on which the quotient stays in the slit plane, the chain
argument at the base point equals `arg ((b - β₀) / (b - βₙ))`: both are continuous branches of the
argument along the ray, which tend to `0` at infinity. -/
theorem chainArg_eq_arg_of_ray {n : ℕ} {β : Fin (n + 1) → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hβd : ∀ k : Fin n, dist (β k.castSucc) (β k.succ) < ρ) {b u : ℂ} (hu : u ≠ 0)
    (havoid : ∀ τ : ℝ, 0 ≤ τ → ∀ k, ρ < ‖b + (τ : ℂ) * u - β k‖)
    (hslit : ∀ τ : ℝ, 0 ≤ τ →
      (b + (τ : ℂ) * u - β 0) / (b + (τ : ℂ) * u - β (Fin.last n)) ∈ slitPlane) :
    chainArg β b = Complex.arg ((b - β 0) / (b - β (Fin.last n))) := by
  set ray : ℝ → ℂ := fun τ => b + (τ : ℂ) * u with hray
  have hraycont : Continuous ray := by fun_prop
  have hne : ∀ τ : ℝ, 0 ≤ τ → ∀ k, ray τ ≠ β k := by
    intro τ hτ k h
    have := havoid τ hτ k
    change ρ < ‖ray τ - β k‖ at this
    rw [h, sub_self, norm_zero] at this
    linarith
  have hcf : ContinuousOn (fun τ : ℝ => chainArg β (ray τ)) (Ici 0) :=
    (continuousOn_chainArg hβd).comp hraycont.continuousOn fun τ hτ k => havoid τ hτ k
  have hcg : ContinuousOn (fun τ : ℝ => Complex.arg ((ray τ - β 0) / (ray τ - β (Fin.last n))))
      (Ici 0) := by
    intro τ hτ
    have hv : ray τ - β (Fin.last n) ≠ 0 := sub_ne_zero.2 (hne τ hτ _)
    refine ContinuousAt.continuousWithinAt ?_
    have hc : ContinuousAt (fun τ : ℝ => (ray τ - β 0) / (ray τ - β (Fin.last n))) τ :=
      ((hraycont.continuousAt.sub continuousAt_const)).div
        (hraycont.continuousAt.sub continuousAt_const) hv
    exact ContinuousAt.comp (g := Complex.arg) (Complex.continuousAt_arg (hslit τ hτ)) hc
  have hexp : ∀ τ ∈ Ici (0 : ℝ), Complex.exp (chainArg β (ray τ) * Complex.I) =
      Complex.exp (Complex.arg ((ray τ - β 0) / (ray τ - β (Fin.last n))) * Complex.I) :=
    fun τ hτ => exp_chainArg_mul_I_eq_exp_arg (hne τ hτ)
  obtain ⟨c, -, hc⟩ := exists_const_of_exp_mul_I_eq isPreconnected_Ici hcf hcg hexp
    (a := (0 : ℝ)) (le_refl 0)
  have hT := tendsto_ray_cocompact (b := b) hu
  have hf : Tendsto (fun τ : ℝ => chainArg β (ray τ)) atTop (𝓝 0) :=
    (tendsto_chainArg β).comp hT
  have hg : Tendsto (fun τ : ℝ => Complex.arg ((ray τ - β 0) / (ray τ - β (Fin.last n))))
      atTop (𝓝 0) := by
    have h1 := (tendsto_arg_ratio (β 0) (β (Fin.last n))).comp hT
    exact h1
  have hg' := hg.add_const c
  have hf' : Tendsto (fun τ : ℝ => chainArg β (ray τ)) atTop (𝓝 (0 + c)) := by
    refine hg'.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with τ hτ
    exact (hc τ hτ).symm
  have hc0 : c = 0 := by
    have := tendsto_nhds_unique hf hf'
    linarith
  have h0 := hc 0 (le_refl 0)
  rw [hc0, add_zero] at h0
  simpa [hray] using h0

lemma im_div_neg_of_pos {u v : ℂ} (h1 : 0 < u.im) (h2 : v.re < 0) (h3 : 0 < u.re) (h4 : 0 < v.im) :
    (u / v).im < 0 := by
  have hv0 : v ≠ 0 := fun h => by simp [h] at h4
  rw [Complex.div_im, ← sub_div]
  exact div_neg_of_neg_of_pos (by nlinarith) (Complex.normSq_pos.2 hv0)

lemma im_div_pos_of_neg {u v : ℂ} (h1 : u.im < 0) (h2 : v.re < 0) (h3 : 0 < u.re) (h4 : v.im < 0) :
    0 < (u / v).im := by
  have hv0 : v ≠ 0 := fun h => by simp [h] at h4
  rw [Complex.div_im, ← sub_div]
  exact div_pos (by nlinarith) (Complex.normSq_pos.2 hv0)

/-- **(CL) Chain crossing.** -/
theorem exists_dist_le_of_chain_crossing {B : Set ℂ} (hBc : IsPreconnected B) {ε h ρ : ℝ}
    (hBre : ∀ w ∈ B, |w.re| < ε) {b₁ b₂ : ℂ} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    (hb₁h : h < b₁.im) (hb₂h : b₂.im < -h) {n : ℕ} (β : Fin (n + 1) → ℂ)
    (hβd : ∀ k : Fin n, dist (β k.castSucc) (β k.succ) < ρ)
    (hβim : ∀ k, |(β k).im| + 2 * ρ ≤ h) (hβ0 : (β 0).re ≤ -ε)
    (hβl : ε ≤ (β (Fin.last n)).re) :
    ∃ k, ∃ w ∈ B, dist (β k) w ≤ ρ := by
  by_contra hcon
  push Not at hcon
  have hε : 0 < ε := lt_of_le_of_lt (abs_nonneg _) (hBre b₁ hb₁)
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : (β (Fin.last 0)).re = (β 0).re := rfl
      linarith
    · exact hn
  have hρ : 0 < ρ := lt_of_le_of_lt dist_nonneg (hβd ⟨0, hn⟩)
  -- on `B`
  have hBav : ∀ w ∈ B, ∀ k, ρ < ‖w - β k‖ := by
    intro w hw k
    have := hcon k w hw
    rwa [dist_comm, dist_eq_norm] at this
  have hΦB : ContinuousOn (chainArg β) B := (continuousOn_chainArg hβd).mono hBav
  have hnonzero : ∀ w ∈ B, chainArg β w ≠ 0 := by
    intro w hwB h0
    have hne : ∀ k, w ≠ β k := by
      intro k hk
      have := hBav w hwB k
      rw [hk, sub_self, norm_zero] at this
      linarith
    have h1 := exp_chainArg_mul_I (β := β) (hne)
    rw [h0, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at h1
    have hr : (w - β 0) / (w - β (Fin.last n)) ≠ 0 := chain_ratio_ne_zero (hne _) (hne _)
    have h2 := eq_ofReal_norm_of_div_eq_one hr h1.symm
    have hv : w - β (Fin.last n) ≠ 0 := sub_ne_zero.2 (hne _)
    have h3 : w - β 0 = ((‖(w - β 0) / (w - β (Fin.last n))‖ : ℝ) : ℂ) *
        (w - β (Fin.last n)) := by
      rw [← h2]; field_simp
    have h4 := congrArg Complex.re h3
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.sub_im] at h4
    have hlam : 0 < ‖(w - β 0) / (w - β (Fin.last n))‖ := norm_pos_iff.2 hr
    have hwre := abs_lt.1 (hBre w hwB)
    nlinarith [mul_pos hlam (show 0 < (β (Fin.last n)).re - w.re by linarith)]
  -- on the rays
  have hβb : ∀ k, |(β k).im| + 2 * ρ ≤ h := hβim
  -- ray above `b₁`
  have hup : ∀ τ : ℝ, 0 ≤ τ → ∀ k, 2 * ρ < (b₁ + (τ : ℂ) * Complex.I - β k).im := by
    intro τ hτ k
    have := hβb k
    have h2 := neg_abs_le (β k).im
    have h3 := le_abs_self (β k).im
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero]
    linarith
  have hdown : ∀ τ : ℝ, 0 ≤ τ → ∀ k, (b₂ + (τ : ℂ) * (-Complex.I) - β k).im < -(2 * ρ) := by
    intro τ hτ k
    have := hβb k
    have h2 := neg_abs_le (β k).im
    have h3 := le_abs_self (β k).im
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.ofReal_im, Complex.I_re, Complex.neg_im, mul_one,
      mul_zero, add_zero, mul_neg]
    linarith
  have hnorm_ge : ∀ w : ℂ, ∀ k, 2 * ρ < |(w - β k).im| → ρ < ‖w - β k‖ := by
    intro w k hlt
    have := Complex.abs_im_le_norm (w - β k)
    linarith
  have hΦ₁ : chainArg β b₁ = Complex.arg ((b₁ - β 0) / (b₁ - β (Fin.last n))) := by
    refine chainArg_eq_arg_of_ray hρ hβd (Complex.I_ne_zero) (fun τ hτ k =>
      hnorm_ge _ k ?_) (fun τ hτ => ?_)
    · rw [abs_of_pos (lt_trans (by linarith) (hup τ hτ k))]; exact hup τ hτ k
    · exact div_mem_slitPlane_of_im_pos (lt_trans (by linarith) (hup τ hτ 0))
        (lt_trans (by linarith) (hup τ hτ (Fin.last n)))
  have hΦ₂ : chainArg β b₂ = Complex.arg ((b₂ - β 0) / (b₂ - β (Fin.last n))) := by
    refine chainArg_eq_arg_of_ray hρ hβd (neg_ne_zero.2 Complex.I_ne_zero) (fun τ hτ k =>
      hnorm_ge _ k ?_) (fun τ hτ => ?_)
    · rw [abs_of_neg (lt_trans (hdown τ hτ k) (by linarith))]
      linarith [hdown τ hτ k]
    · exact div_mem_slitPlane_of_im_neg (lt_trans (hdown τ hτ 0) (by linarith))
        (lt_trans (hdown τ hτ (Fin.last n)) (by linarith))
  -- signs
  have hb1re := abs_lt.1 (hBre b₁ hb₁)
  have hb2re := abs_lt.1 (hBre b₂ hb₂)
  have hβ0b := (abs_nonneg (β 0).im)
  have hβlb := (abs_nonneg (β (Fin.last n)).im)
  have hs₁ : Complex.arg ((b₁ - β 0) / (b₁ - β (Fin.last n))) < 0 := by
    refine Complex.arg_neg_iff.2 (im_div_neg_of_pos ?_ ?_ ?_ ?_) <;>
      simp only [Complex.sub_re, Complex.sub_im] <;>
      linarith [le_abs_self (β 0).im, le_abs_self (β (Fin.last n)).im, hβb 0, hβb (Fin.last n)]
  have hs₂ : 0 < Complex.arg ((b₂ - β 0) / (b₂ - β (Fin.last n))) := by
    refine arg_pos_of_im_pos (im_div_pos_of_neg ?_ ?_ ?_ ?_) <;>
      simp only [Complex.sub_re, Complex.sub_im] <;>
      linarith [neg_abs_le (β 0).im, neg_abs_le (β (Fin.last n)).im, hβb 0, hβb (Fin.last n)]
  -- intermediate value theorem
  have hmem : (0 : ℝ) ∈ Icc (chainArg β b₁) (chainArg β b₂) := by
    rw [hΦ₁, hΦ₂]; exact ⟨hs₁.le, hs₂.le⟩
  obtain ⟨w, hwB, hw⟩ := hBc.intermediate_value hb₁ hb₂ hΦB hmem
  exact hnonzero w hwB hw

end ComplexSLE.Planar

end
