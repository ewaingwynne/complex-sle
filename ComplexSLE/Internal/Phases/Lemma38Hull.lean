/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Hull.EndpointCont
public import ComplexSLE.Internal.Hull.LocalExistence
public import ComplexSLE.Internal.Polar.PolarDerivShift
public import ComplexSLE.Internal.Hull.Basic

/-!
# Lemma 3.10, deterministic hull estimates (M7/E2)

Two elementary facts about left hulls of a continuous driver `U`, used for the multi-scale argument
of Lemma 3.10 (paper.tex:L1550-1630):

* `infDist_leftHull_le_of_forall_gt` (**right-continuity of `t ↦ dist(z, L_t)`**): if
  `dist(z, L_s) ≤ r` for all `s > t` then `dist(z, L_t) ≤ r`. Hence the first time `t` at which
  `dist(z, L_t) ≤ r` is attained, and `{τ ≤ t} = {dist(z, L_t) ≤ r}` is an event of `ℱ_t` for an
  adapted driver. (`L_t = ⋂_{s > t} L_s` and the openness of `{T > s}`.)
* `lifeSet_and_norm_bounds_of_small` (**the hull of a small-oscillation driver is small**): if
  `V_0 = 0` and `|V_s| ≤ ε` for `s ≤ u₀`, and `4ε ≤ |w|`, `16 u₀ < |w|²`, then `w ∉ L_{u₀}(V)` and
  `|w|/2 < |f_s(w)| ≤ |w| + 4u₀/|w| + ε` for `s ∈ [0, u₀]`. In particular for `|w| = 1`,
  `ε = 1/16`, `u₀ < 1/16` the clock rate `|f_s(w)|⁻²` is `≥ 1/4` on `[0, u₀]`, uniformly in `w`,
  which is the substitute for the paper's tacit uniformity over the restart direction.

No external input is used.
-/

public section

open scoped NNReal ENNReal Topology
open Set Metric Filter

namespace ComplexSLE.Internal.Polar

variable {U : ℝ≥0 → ℂ}

/-- `dd t = dist(z, L_t)` is non-increasing in `t`. -/
theorem infDist_leftHull_anti {s t : ℝ≥0} (z : ℂ) (h : s ≤ t) :
    infDist z (leftHull U t) ≤ infDist z (leftHull U s) :=
  infDist_le_infDist_of_subset (leftHull_mono h) (leftHull_nonempty U s)

/-- **Right-continuity of the distance to the left hull** (in the form needed to show that hitting
times of `{dist(z, L_t) ≤ r}` are attained). -/
theorem infDist_leftHull_le_of_forall_gt (hU : Continuous U) (z : ℂ) (t : ℝ≥0) (r : ℝ)
    (h : ∀ s : ℝ≥0, t < s → infDist z (leftHull U s) ≤ r) : infDist z (leftHull U t) ≤ r := by
  set s : ℕ → ℝ≥0 := fun n => t + ((n : ℝ≥0) + 1)⁻¹ with hs
  have hspos : ∀ n, t < s n := fun n => by
    simp only [hs]; exact lt_add_of_pos_right _ (by positivity)
  have hex : ∀ n : ℕ, ∃ x ∈ leftHull U (s n), dist z x < r + 1 / ((n : ℝ) + 1) := fun n =>
    (infDist_lt_iff (leftHull_nonempty U (s n))).1
      (lt_of_le_of_lt (h (s n) (hspos n)) (by linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity]))
  choose x hxL hxd using hex
  have hxb : ∀ n, x n ∈ closedBall z (|r| + 1) := fun n => by
    rw [mem_closedBall]
    have : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    rw [dist_comm]
    linarith [(hxd n).le, le_abs_self r]
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall z (|r| + 1)).tendsto_subseq hxb
  have haL : a ∈ leftHull U t := by
    by_contra haL
    have hta : (t : ℝ≥0∞) < absorbingTime U a := notMem_leftHull_iff.1 haL
    obtain ⟨t', htt', ht'a⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hta
    have htt'' : t < t' := by exact_mod_cast htt'
    have hopen : IsOpen (leftHull U t')ᶜ := isOpen_compl_leftHull U hU t'
    have hat' : a ∈ (leftHull U t')ᶜ := notMem_leftHull_iff.2 ht'a
    have hev1 : ∀ᶠ n in atTop, x (φ n) ∈ (leftHull U t')ᶜ := hlim.eventually (hopen.mem_nhds hat')
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (show (0 : ℝ) < (t' : ℝ) - t by
      have : (t : ℝ) < t' := by exact_mod_cast htt''
      linarith)
    have hev2 : ∀ᶠ n in atTop, N ≤ n := eventually_ge_atTop N
    obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
    refine hn1 (leftHull_mono ?_ (hxL (φ n)))
    have hNφ : N ≤ φ n := hn2.trans (hφ.id_le n)
    have h1 : ((φ n : ℝ) + 1)⁻¹ ≤ 1 / ((N : ℝ) + 1) := by
      rw [one_div]
      exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hNφ 1)
    have h2 : 1 / ((N : ℝ) + 1) < (t' : ℝ) - t := lt_of_le_of_lt le_rfl hN
    change s (φ n) ≤ t'
    rw [← NNReal.coe_le_coe]
    simp only [hs, NNReal.coe_add, NNReal.coe_inv, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
    linarith
  have hdist : Tendsto (fun n => dist z (x (φ n))) atTop (𝓝 (dist z a)) :=
    tendsto_const_nhds.dist hlim
  have hbound : Tendsto (fun n => r + 1 / ((φ n : ℝ) + 1)) atTop (𝓝 r) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
    simpa using tendsto_const_nhds.add this
  have hle : dist z a ≤ r :=
    le_of_tendsto_of_tendsto hdist hbound (Eventually.of_forall fun n => (hxd (φ n)).le)
  exact (infDist_le_dist_of_mem haL).trans hle

/-- **Right-continuity of `t ↦ dist(z, L_t)`** (the non-trivial inequality): for `t` and `ε > 0`
there is `δ > 0` with `dist(z, L_t) - ε ≤ dist(z, L_s)` for all `s ∈ (t, t + δ)`. -/
theorem exists_forall_sub_le_infDist_leftHull (hU : Continuous U) (z : ℂ) (t : ℝ≥0) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ s : ℝ≥0, t < s → s < t + δ →
      infDist z (leftHull U t) - ε ≤ infDist z (leftHull U s) := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ s : ℝ≥0, t < s → infDist z (leftHull U s) ≤ infDist z (leftHull U t) - ε := by
    intro s hs
    obtain ⟨s', hs'1, hs'2, hs'3⟩ := hcon (s - t) (tsub_pos_of_lt hs)
    have hs'lt : s' < s := by
      have : t + (s - t) = s := add_tsub_cancel_of_le hs.le
      rwa [this] at hs'2
    have := infDist_leftHull_anti (U := U) z hs'lt.le
    linarith
  have := infDist_leftHull_le_of_forall_gt hU z t _ hall
  linarith

/-- **The hull of a small-oscillation driver is small.** Let `V` be a continuous driver with
`V 0 = 0` and `‖V s‖ ≤ ε` for `s ≤ u₀`, and `w` a point with `4 ε ≤ ‖w‖` and `16 u₀ < ‖w‖²`. Then
`w ∉ L_{u₀}(V)` and for all `s ∈ [0, u₀]`,
`‖w‖ / 2 < ‖f_s(w)‖ ≤ ‖w‖ + 4 u₀ / ‖w‖ + ε`. -/
theorem lifeSet_and_norm_bounds_of_small {V : ℝ≥0 → ℂ} (hV : Continuous V) {ε : ℝ} {u₀ : ℝ≥0}
    {w : ℂ} (h0 : V 0 = 0) (hosc : ∀ s : ℝ≥0, s ≤ u₀ → ‖V s‖ ≤ ε) (hw1 : 4 * ε ≤ ‖w‖)
    (hw2 : 16 * (u₀ : ℝ) < ‖w‖ ^ 2) :
    (u₀ : ℝ) ∈ lifeSet V w ∧ ∀ s : ℝ, s ∈ Icc (0 : ℝ) u₀ →
      ‖w‖ / 2 < ‖fPath V hV w s‖ ∧ ‖fPath V hV w s‖ ≤ ‖w‖ + 4 * u₀ / ‖w‖ + ε := by
  have hu0 : (0 : ℝ) ≤ u₀ := u₀.coe_nonneg
  have hwpos : 0 < ‖w‖ := by
    by_contra h
    have : ‖w‖ = 0 := le_antisymm (not_lt.1 h) (norm_nonneg _)
    rw [this] at hw2; nlinarith
  have hε0 : 0 ≤ ε := by simpa [h0] using hosc 0 bot_le
  set α : ℝ := ‖w‖ / 2 with hα
  have hαpos : 0 < α := by positivity
  have hf0 : fPath V hV w 0 = w := by rw [fPath_zero, h0, sub_zero]
  -- the integral estimate along `[0, s]` when `‖f‖ ≥ α` there
  have hest : ∀ s : ℝ, s ∈ lifeSet V w → s ≤ u₀ → (∀ r ∈ Icc (0 : ℝ) s, α ≤ ‖fPath V hV w r‖) →
      ‖fPath V hV w s - w‖ ≤ 4 * u₀ / ‖w‖ + ε := by
    intro s hs hsu hlow
    have h1 := norm_fPath_sub_le hV hαpos le_rfl hs.1 hs hlow
    rw [hf0] at h1
    have h2 : ‖V s.toNNReal - V (0 : ℝ).toNNReal‖ ≤ ε := by
      rw [Real.toNNReal_zero, h0, sub_zero]
      exact hosc _ (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]; exact hsu)
    have h3 : 2 * (s - 0) / α ≤ 4 * u₀ / ‖w‖ := by
      rw [sub_zero, hα, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hLb : ‖w‖ / 2 < ‖w‖ - (4 * u₀ / ‖w‖ + ε) := by
    have h4 : 4 * (u₀ : ℝ) / ‖w‖ < ‖w‖ / 4 := by
      rw [div_lt_div_iff₀ hwpos (by norm_num)]; nlinarith
    linarith
  -- (A) `‖f_s(w)‖ > α` on `lifeSet ∩ [0, u₀]`
  have hA : ∀ s : ℝ, s ∈ lifeSet V w → s ≤ u₀ → α < ‖fPath V hV w s‖ := by
    intro s₁ hs₁ hs₁u
    by_contra hcon
    push Not at hcon
    set S : Set ℝ := Icc 0 s₁ ∩ (fun s => ‖fPath V hV w s‖) ⁻¹' Iic α with hS
    have hcl : IsClosed S :=
      ((continuousOn_norm_fPath hV w).mono (Icc_subset_lifeSet hs₁)).preimage_isClosed_of_isClosed
        isClosed_Icc isClosed_Iic
    have hne : S.Nonempty := ⟨s₁, ⟨hs₁.1, le_rfl⟩, hcon⟩
    have hbdd : BddBelow S := ⟨0, fun s hs => hs.1.1⟩
    set s₂ := sInf S with hs₂
    have hs₂S : s₂ ∈ S := hcl.csInf_mem hne hbdd
    have hs₂1 : s₂ ≤ s₁ := hs₂S.1.2
    have hs₂0 : 0 ≤ s₂ := hs₂S.1.1
    have hs₂life : s₂ ∈ lifeSet V w := mem_lifeSet_of_le hs₁ hs₂0 hs₂1
    have hs₂le : ‖fPath V hV w s₂‖ ≤ α := hs₂S.2
    have hbefore : ∀ s ∈ Ico (0 : ℝ) s₂, α < ‖fPath V hV w s‖ := by
      intro s hs
      by_contra hcon2
      push Not at hcon2
      have : s ∈ S := ⟨⟨hs.1, hs.2.le.trans hs₂1⟩, hcon2⟩
      exact absurd (csInf_le hbdd this) (not_le.2 hs.2)
    have hs₂pos : 0 < s₂ := by
      rcases hs₂0.eq_or_lt with h | h
      · exfalso
        rw [← h, hf0] at hs₂le
        linarith
      · exact h
    have hlower : ∀ s ∈ Ico (0 : ℝ) s₂, ‖w‖ - (4 * u₀ / ‖w‖ + ε) ≤ ‖fPath V hV w s‖ := by
      intro s hs
      have hsl : s ∈ lifeSet V w := mem_lifeSet_of_le hs₂life hs.1 hs.2.le
      have := hest s hsl (hs.2.le.trans (hs₂1.trans hs₁u)) (fun r hr => (hbefore r ⟨hr.1, lt_of_le_of_lt hr.2 hs.2⟩).le)
      have h5 : ‖w‖ - ‖fPath V hV w s‖ ≤ ‖fPath V hV w s - w‖ := by
        have := norm_sub_norm_le w (fPath V hV w s)
        rwa [norm_sub_rev] at this
      linarith
    have hclosed2 : IsClosed (Icc 0 s₂ ∩ (fun s => ‖fPath V hV w s‖) ⁻¹'
        Ici (‖w‖ - (4 * u₀ / ‖w‖ + ε))) :=
      ((continuousOn_norm_fPath hV w).mono (Icc_subset_lifeSet hs₂life)).preimage_isClosed_of_isClosed
        isClosed_Icc isClosed_Ici
    have hsub : Ico 0 s₂ ⊆ Icc 0 s₂ ∩ (fun s => ‖fPath V hV w s‖) ⁻¹'
        Ici (‖w‖ - (4 * u₀ / ‖w‖ + ε)) :=
      fun s hs => ⟨Ico_subset_Icc_self hs, hlower s hs⟩
    have hcl2 := closure_minimal hsub hclosed2
    rw [closure_Ico hs₂pos.ne] at hcl2
    have := (hcl2 ⟨hs₂0, le_rfl⟩).2
    simp only [mem_preimage, mem_Ici] at this
    linarith
  -- (B) `u₀ ∈ lifeSet`
  have hB : (u₀ : ℝ) ∈ lifeSet V w := by
    by_contra hB
    have hpos : 0 < absorbingTime V w := absorbingTime_pos_of_ne hV (by
      intro h; rw [h, h0] at hwpos; simp at hwpos)
    have hT : absorbingTime V w ≤ (u₀ : ℝ≥0∞) := by
      by_contra hT
      exact hB (by
        rw [mem_lifeSet, ENNReal.ofReal_coe_nnreal]
        exact ⟨hu0, not_le.1 hT⟩)
    have hTne : absorbingTime V w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hT
    obtain ⟨s, hs, -, hslt⟩ := exists_norm_fPath_lt hV hTne hαpos
      (a := 0) (zero_mem_lifeSet_iff.2 hpos)
    have hsu : s ≤ u₀ := by
      have h1 : ENNReal.ofReal s < absorbingTime V w := hs.2
      have h2 := h1.trans_le hT
      rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs.1] at h2
      exact h2.le
    exact absurd (hA s hs hsu) (not_lt.2 hslt.le)
  refine ⟨hB, fun s hs => ⟨hA s (mem_lifeSet_of_le hB hs.1 hs.2) hs.2, ?_⟩⟩
  have hsl : s ∈ lifeSet V w := mem_lifeSet_of_le hB hs.1 hs.2
  have := hest s hsl hs.2 (fun r hr => (hA r (mem_lifeSet_of_le hsl hr.1 hr.2)
    (hr.2.trans hs.2)).le)
  have h5 : ‖fPath V hV w s‖ - ‖w‖ ≤ ‖fPath V hV w s - w‖ := norm_sub_norm_le _ _
  linarith

end ComplexSLE.Internal.Polar

end
