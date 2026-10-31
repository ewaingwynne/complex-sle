/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Planar.Chain
public import ComplexSLE.Infrastructure.Planar.ChainArg
public import ComplexSLE.Infrastructure.Planar.ArgBranch
public import ComplexSLE.Infrastructure.Planar.Disconnect
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Path
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Separation by two connected sets (P2)

Let `A` and `B` be compact connected subsets of `ℂ` such that `A` lies in the strip `|Im| < ε`,
`B` avoids the ball of radius `3ε` about a real point `x₀`, and both contain a point with
`Re ≤ x₀ - ε` and a point with `Re ≥ x₀ + ε`. Then `A ∪ B` disconnects from infinity at least one
of any two points `z₁ ∈ B_ε(x₀ + 2εi)`, `z₂ ∈ B_ε(x₀ - 2εi)`.

The proof uses the chain argument: if neither point is disconnected, a chain from `z₁` to `z₂`
avoiding `A ∪ B` gives a continuous branch `Θ` of `arg ((w - z₁) / (w - z₂))` on `A ∪ B`.
-/

public section

open Set Metric Complex

namespace ComplexSLE.Planar

lemma abs_re_sub_lt_of_mem_ball {z c : ℂ} {ε : ℝ} (h : z ∈ ball c ε) : |z.re - c.re| < ε := by
  have h1 : ‖z - c‖ < ε := by rwa [mem_ball, dist_eq_norm] at h
  exact lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (z - c)) h1

lemma abs_im_sub_lt_of_mem_ball {z c : ℂ} {ε : ℝ} (h : z ∈ ball c ε) : |z.im - c.im| < ε := by
  have h1 : ‖z - c‖ < ε := by rwa [mem_ball, dist_eq_norm] at h
  exact lt_of_le_of_lt (by simpa using Complex.abs_im_le_norm (z - c)) h1

lemma im_div_pos {u v : ℂ} (h1 : u.im < 0) (h2 : v.re < 0) (h3 : u.re < 0) (h4 : 0 < v.im) :
    0 < (u / v).im := by
  have hv0 : v ≠ 0 := fun h => by simp [h] at h4
  rw [Complex.div_im, ← sub_div]
  exact div_pos (by nlinarith) (Complex.normSq_pos.2 hv0)

lemma im_div_neg {u v : ℂ} (h1 : u.im < 0) (h2 : 0 < v.re) (h3 : 0 < u.re) (h4 : 0 < v.im) :
    (u / v).im < 0 := by
  have hv0 : v ≠ 0 := fun h => by simp [h] at h4
  rw [Complex.div_im, ← sub_div]
  exact div_neg_of_neg_of_pos (by nlinarith) (Complex.normSq_pos.2 hv0)

/-- A compact set disjoint from a closed set `K` is at distance `> ρ` from it for some `ρ > 0`. -/
lemma exists_pos_forall_lt_dist {s K : Set ℂ} (hs : IsCompact s) (hK : IsClosed K)
    (hd : Disjoint s K) : ∃ ρ > 0, ∀ x ∈ s, ∀ y ∈ K, ρ < dist x y := by
  obtain ⟨r, hr, h⟩ := Metric.exists_pos_forall_lt_edist hs hK hd
  refine ⟨(r : ℝ) / 2, by positivity, fun x hx y hy => ?_⟩
  have := h x hx y hy
  rw [edist_dist] at this
  have h2 : (r : ℝ) < dist x y := by
    have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (r.2)).1 (by simpa using this)
    exact this
  have : (0 : ℝ) < r := hr
  linarith

/-- On `B`, avoiding the ball `B_{3ε}(x₀)` which contains `z₁` and `z₂`, the quotient
`(w - z₁) / (w - z₂)` lies in the slit plane. -/
lemma div_mem_slitPlane_of_far {x0 ε : ℝ} {z₁ z₂ w : ℂ}
    (hz₁ : ‖z₁ - x0‖ < 3 * ε) (hz₂ : ‖z₂ - x0‖ < 3 * ε) (hw : 3 * ε ≤ ‖w - x0‖) :
    (w - z₁) / (w - z₂) ∈ slitPlane := by
  have hv : w - z₂ ≠ 0 := by
    intro h
    have : w = z₂ := sub_eq_zero.1 h
    rw [this] at hw
    linarith
  by_contra h
  obtain ⟨t, ht, heq⟩ := exists_nonneg_of_div_not_mem_slitPlane hv h
  have h1 : (1 + (t : ℂ)) * (w - x0) = (z₁ - x0) + t * (z₂ - x0) := by
    have : w - z₁ = -(t : ℂ) * (w - z₂) := heq
    linear_combination this
  have h2 := congrArg norm h1
  have h3 : ‖(1 + (t : ℂ)) * (w - x0)‖ = (1 + t) * ‖w - x0‖ := by
    rw [norm_mul]
    congr 1
    have : (1 + (t : ℂ)) = ((1 + t : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have h4 : ‖(z₁ - x0) + t * (z₂ - x0)‖ ≤ ‖z₁ - x0‖ + t * ‖z₂ - x0‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  rw [h3] at h2
  nlinarith

/-- **(P2) Separation by two connected sets.** -/
theorem disconnectsFromInfinity_of_two_connected
    {A B : Set ℂ} (hA : IsCompact A) (hAc : IsPreconnected A)
    (hB : IsCompact B) (hBc : IsPreconnected B) {x0 ε : ℝ} (hε : 0 < ε)
    (hAim : ∀ w ∈ A, |w.im| < ε) (hB3 : Disjoint B (ball (x0 : ℂ) (3 * ε)))
    {q p : ℂ} (hqA : q ∈ A) (hqB : q ∈ B) (hpA : p ∈ A) (hpB : p ∈ B)
    (hq : q.re ≤ x0 - ε) (hp : x0 + ε ≤ p.re) {z₁ z₂ : ℂ}
    (hz₁ : z₁ ∈ ball ((x0 : ℂ) + 2 * ε * Complex.I) ε)
    (hz₂ : z₂ ∈ ball ((x0 : ℂ) - 2 * ε * Complex.I) ε) :
    DisconnectsFromInfinity (A ∪ B) {z₁} ∨ DisconnectsFromInfinity (A ∪ B) {z₂} := by
  by_contra hcon
  obtain ⟨h1, h2⟩ := not_or.1 hcon
  rw [disconnectsFromInfinity_singleton_iff, not_or] at h1 h2
  obtain ⟨hz1K, hz1u⟩ := h1
  obtain ⟨hz2K, hz2u⟩ := h2
  have hKc : IsCompact (A ∪ B) := hA.union hB
  -- coordinates of z₁ and z₂
  have hz1re := abs_re_sub_lt_of_mem_ball hz₁
  have hz1im := abs_im_sub_lt_of_mem_ball hz₁
  have hz2re := abs_re_sub_lt_of_mem_ball hz₂
  have hz2im := abs_im_sub_lt_of_mem_ball hz₂
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
    Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, sub_zero, add_zero, mul_one,
    zero_add, sub_self, zero_sub] at hz1re hz1im hz2re hz2im
  rw [abs_lt] at hz1re hz1im hz2re hz2im
  have hz1n : ‖z₁ - x0‖ < 3 * ε := by
    have h1 : ‖z₁ - ((x0 : ℂ) + 2 * ε * Complex.I)‖ < ε := by
      rwa [mem_ball, dist_eq_norm] at hz₁
    have h2 : ‖(2 * ε * Complex.I : ℂ)‖ = 2 * ε := by simp [abs_of_pos hε]
    calc ‖z₁ - x0‖ = ‖(z₁ - ((x0 : ℂ) + 2 * ε * Complex.I)) + 2 * ε * Complex.I‖ := by
          congr 1; ring
      _ ≤ ‖z₁ - ((x0 : ℂ) + 2 * ε * Complex.I)‖ + ‖(2 * ε * Complex.I : ℂ)‖ := norm_add_le _ _
      _ < 3 * ε := by rw [h2]; linarith
  have hz2n : ‖z₂ - x0‖ < 3 * ε := by
    have h1 : ‖z₂ - ((x0 : ℂ) - 2 * ε * Complex.I)‖ < ε := by
      rwa [mem_ball, dist_eq_norm] at hz₂
    have h2 : ‖(2 * ε * Complex.I : ℂ)‖ = 2 * ε := by simp [abs_of_pos hε]
    calc ‖z₂ - x0‖ = ‖(z₂ - ((x0 : ℂ) - 2 * ε * Complex.I)) - 2 * ε * Complex.I‖ := by
          congr 1; ring
      _ ≤ ‖z₂ - ((x0 : ℂ) - 2 * ε * Complex.I)‖ + ‖(2 * ε * Complex.I : ℂ)‖ := norm_sub_le _ _
      _ < 3 * ε := by rw [h2]; linarith
  -- z₂ lies in the unbounded component of z₁
  have hcc := connectedComponentIn_eq_of_unbounded hKc.isBounded hz1u hz2u
  have hz2cc : z₂ ∈ connectedComponentIn (A ∪ B)ᶜ z₁ := hcc ▸ mem_connectedComponentIn hz2K
  have hCopen : IsOpen (connectedComponentIn (A ∪ B)ᶜ z₁) :=
    hKc.isClosed.isOpen_compl.connectedComponentIn
  have hz1cc : z₁ ∈ connectedComponentIn (A ∪ B)ᶜ z₁ := mem_connectedComponentIn hz1K
  have hCconn : IsConnected (connectedComponentIn (A ∪ B)ᶜ z₁) :=
    ⟨⟨z₁, hz1cc⟩, isPreconnected_connectedComponentIn⟩
  have hCpath := hCopen.isConnected_iff_isPathConnected.1 hCconn
  have hjoin := hCpath.joinedIn z₁ hz1cc z₂ hz2cc
  set γ := hjoin.somePath with hγ
  set s : Set ℂ := range γ with hs
  have hscomp : IsCompact s := isCompact_range γ.continuous
  have hsconn : IsPreconnected s := (isConnected_range γ.continuous).isPreconnected
  have hz1s : z₁ ∈ s := ⟨0, by simp [γ]⟩
  have hz2s : z₂ ∈ s := ⟨1, by simp [γ]⟩
  have hsK : Disjoint s (A ∪ B) := by
    rw [Set.disjoint_left]
    rintro _ ⟨t, rfl⟩ hK
    exact (connectedComponentIn_subset _ _ (hjoin.somePath_mem t)) hK
  obtain ⟨ρ, hρ, hdist⟩ := exists_pos_forall_lt_dist hscomp hKc.isClosed hsK
  obtain ⟨n, β, hβ0, hβl, hβs, hβd⟩ := exists_chain_of_isPreconnected hsconn hz1s hz2s hρ
  have hfar : ∀ w ∈ A ∪ B, ∀ k, ρ < ‖w - β k‖ := by
    intro w hw k
    have := hdist (β k) (hβs k) w hw
    rwa [dist_comm, dist_eq_norm] at this
  have hcontΘ : ContinuousOn (chainArg β) (A ∪ B) :=
    (continuousOn_chainArg hβd).mono fun w hw k => hfar w hw k
  have hne : ∀ w ∈ A ∪ B, ∀ k, w ≠ β k := by
    intro w hw k h
    have := hfar w hw k
    rw [h, sub_self, norm_zero] at this
    linarith
  -- the ratio `r`
  set r : ℂ → ℂ := fun w => (w - z₁) / (w - z₂) with hr
  have hexp : ∀ w ∈ A ∪ B, Complex.exp (chainArg β w * Complex.I) = r w / ((‖r w‖ : ℝ) : ℂ) := by
    intro w hw
    have := exp_chainArg_mul_I (β := β) (hne w hw)
    rwa [hβ0, hβl] at this
  have hrne : ∀ w ∈ A ∪ B, r w ≠ 0 := by
    intro w hw
    have h1 : w ≠ z₁ := fun h => hz1K (h ▸ hw)
    have h2 : w ≠ z₂ := fun h => hz2K (h ▸ hw)
    exact chain_ratio_ne_zero h1 h2
  -- on `B`: `Θ = arg r + c`
  have hBslit : ∀ w ∈ B, r w ∈ slitPlane := by
    intro w hwB
    have hw3 : 3 * ε ≤ ‖w - x0‖ := by
      have : w ∉ ball (x0 : ℂ) (3 * ε) := fun h => Set.disjoint_left.1 hB3 hwB h
      rwa [mem_ball, dist_eq_norm, not_lt] at this
    exact div_mem_slitPlane_of_far hz1n hz2n hw3
  have hcontD : ContinuousOn (fun w => Complex.arg (r w)) B := by
    intro w hwB
    have hw : w ∈ A ∪ B := Or.inr hwB
    have hv : w - z₂ ≠ 0 := sub_ne_zero.2 (fun h => hz2K (h ▸ hw))
    refine ContinuousAt.continuousWithinAt ?_
    have hc : ContinuousAt r w :=
      (continuousAt_id.sub continuousAt_const).div (continuousAt_id.sub continuousAt_const) hv
    exact ContinuousAt.comp (g := Complex.arg) (Complex.continuousAt_arg (hBslit w hwB)) hc
  have hexpD : ∀ w ∈ B, Complex.exp (chainArg β w * Complex.I) =
      Complex.exp (Complex.arg (r w) * Complex.I) := by
    intro w hwB
    have hw : w ∈ A ∪ B := Or.inr hwB
    rw [hexp w hw]
    have h := Complex.norm_mul_exp_arg_mul_I (r w)
    have hn : ((‖r w‖ : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.2 (hrne w hw)
    rw [div_eq_iff hn, mul_comm]
    exact h.symm
  obtain ⟨c, hc1, hc⟩ := exists_const_of_exp_mul_I_eq hBc (hcontΘ.mono subset_union_right)
    hcontD hexpD hqB
  -- signs at `q` and `p`
  have hqim := hAim q hqA
  have hpim := hAim p hpA
  rw [abs_lt] at hqim hpim
  have hrq : 0 < (r q).im := by
    refine im_div_pos ?_ ?_ ?_ ?_ <;> simp only [Complex.sub_re, Complex.sub_im] <;> linarith
  have hrp : (r p).im < 0 := by
    refine im_div_neg ?_ ?_ ?_ ?_ <;> simp only [Complex.sub_re, Complex.sub_im] <;> linarith
  have hDq : 0 < Complex.arg (r q) := arg_pos_of_im_pos hrq
  have hDp : Complex.arg (r p) < 0 := Complex.arg_neg_iff.2 hrp
  have hΘq : c < chainArg β q := by rw [hc q hqB]; linarith
  have hΘp : chainArg β p < c := by rw [hc p hpB]; linarith
  -- IVT on `A`
  obtain ⟨w, hwA, hw⟩ := hAc.intermediate_value hpA hqA (hcontΘ.mono subset_union_left)
    ⟨hΘp.le, hΘq.le⟩
  have hwK : w ∈ A ∪ B := Or.inl hwA
  have h1 := hexp w hwK
  rw [hw, hc1] at h1
  have h2 := eq_ofReal_norm_of_div_eq_one (hrne w hwK) h1.symm
  have hv : w - z₂ ≠ 0 := sub_ne_zero.2 (fun h => hz2K (h ▸ hwK))
  have hlam : 0 < ‖r w‖ := norm_pos_iff.2 (hrne w hwK)
  have h3 : w - z₁ = ((‖r w‖ : ℝ) : ℂ) * (w - z₂) := by
    have : r w = (w - z₁) / (w - z₂) := rfl
    rw [this] at h2
    rw [← h2]
    field_simp
  have h4 := congrArg Complex.im h3
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero] at h4
  have hwim := hAim w hwA
  rw [abs_lt] at hwim
  nlinarith [mul_pos hlam (show 0 < w.im - z₂.im by linarith)]

end ComplexSLE.Planar

end
