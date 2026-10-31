/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.Path
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Lemma 2.5 (`lem-endpt-cont`): `|f_t(z)| → 0` as `t → T_z⁻` (M7/C1)

Source: paper.tex:L667-690. For a continuous driver `U` and a point `z` with `T_z < ∞`,

  `lim_{t → T_z⁻} |f_t(z)| = 0`

(`tendsto_norm_fPath_nhdsWithin`; the statement is within the life set `[0, T_z)`, off which
`fPath` is junk, and `𝓝[lifeSet] T_z` is the filter `t → T_z⁻`; it is `⊥`, and the statement
trivial, when `T_z = 0`), hence `log |f_t(z)| → -∞` (`tendsto_log_norm_fPath_nhdsWithin`).

The `liminf` version is `exists_norm_fPath_lt` (`Polar/Path.lean`). To pass to the limit we follow
the paper's upcrossing argument.

* The integral form of the Loewner equation (paper (2.7), `g' = 2/f`) gives
  `|f_{t₂} - f_{t₁}| ≤ 2 (t₂ - t₁) / α + |U_{t₂} - U_{t₁}|` whenever `|f| ≥ α` on `[t₁, t₂]`
  (`norm_fPath_sub_le`; the integral is bounded through the mean value inequality).
* Uniform continuity of `U` on the compact `[0, T_z]` then shows that every upcrossing
  `(t₁, t₂)` of `[α, β]` (`|f_{t₁}| ≤ α`, `|f_{t₂}| ≥ β`, `|f| ≥ α` in between) lasts at least a
  time `ε = ε(T_z, α, β) > 0` (`exists_pos_upcrossing_length`, paper (`eqn-endpt-cont-bd`)).
* Upcrossings of `[β/2, β]` that start after the liminf has brought `|f|` below `β/2`, and that
  occur in an arbitrarily short window before `T_z`, cannot last `ε`: this replaces the paper's
  count of at most `T_z / ε` disjoint upcrossings (same estimate, no counting).
-/

public section

open scoped NNReal ENNReal Topology
open Set Filter

namespace ComplexSLE.Internal.Polar

variable {U : ℝ≥0 → ℂ}

/-! ### The integral estimate (2.7) -/

/-- **Paper (2.7)**, `eqn-endpt-cont-bd`: on a segment `[t₁, t₂] ⊆ [0, T_z)` along which
`|f_s(z)| ≥ α > 0`, `|f_{t₂}(z) - f_{t₁}(z)| ≤ 2 (t₂ - t₁) / α + |U_{t₂} - U_{t₁}|`. -/
theorem norm_fPath_sub_le (hU : Continuous U) {z : ℂ} {t₁ t₂ α : ℝ} (hα : 0 < α) (h0 : 0 ≤ t₁)
    (h12 : t₁ ≤ t₂) (ht₂ : t₂ ∈ lifeSet U z)
    (hlow : ∀ s ∈ Icc t₁ t₂, α ≤ ‖fPath U hU z s‖) :
    ‖fPath U hU z t₂ - fPath U hU z t₁‖ ≤
      2 * (t₂ - t₁) / α + ‖U t₂.toNNReal - U t₁.toNNReal‖ := by
  have hsub : Icc t₁ t₂ ⊆ lifeSet U z := fun s hs => mem_lifeSet_of_le ht₂ (h0.trans hs.1) hs.2
  have hg : ‖solPath U hU z t₂ - solPath U hU z t₁‖ ≤ 2 / α * ‖t₂ - t₁‖ := by
    refine (convex_Icc t₁ t₂).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := solPath U hU z) (f' := fun s => 2 / fPath U hU z s) (C := 2 / α) ?_ ?_
      ⟨le_rfl, h12⟩ ⟨h12, le_rfl⟩
    · intro s hs
      exact (hasDerivWithinAt_solPath hU (hsub hs)).mono fun u hu => h0.trans hu.1
    · intro s hs
      rw [norm_div]
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      rw [h2]
      exact div_le_div_of_nonneg_left (by norm_num) hα (hlow s hs)
  have hdecomp : fPath U hU z t₂ - fPath U hU z t₁ =
      (solPath U hU z t₂ - solPath U hU z t₁) - (U t₂.toNNReal - U t₁.toNNReal) := by
    simp only [fPath]; ring
  rw [hdecomp]
  refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 h12)] at hg
  calc ‖solPath U hU z t₂ - solPath U hU z t₁‖ ≤ 2 / α * (t₂ - t₁) := hg
    _ = 2 * (t₂ - t₁) / α := by ring

/-! ### Upcrossings take a definite time -/

/-- **Each upcrossing of `[α, β]` takes time at least `ε = ε(T_z, α, β) > 0`** (paper.tex:L686-689,
the consequence of (`eqn-endpt-cont-bd`) and the uniform continuity of `U` on `[0, T_z]`). -/
theorem exists_pos_upcrossing_length (hU : Continuous U) {z : ℂ} (hT : absorbingTime U z ≠ ⊤)
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    ∃ ε > 0, ∀ t₁ t₂ : ℝ, t₁ ∈ lifeSet U z → t₂ ∈ lifeSet U z → t₁ ≤ t₂ →
      ‖fPath U hU z t₁‖ ≤ α → β ≤ ‖fPath U hU z t₂‖ →
      (∀ s ∈ Icc t₁ t₂, α ≤ ‖fPath U hU z s‖) → ε ≤ t₂ - t₁ := by
  set T := (absorbingTime U z).toReal with hTdef
  have hV : Continuous fun t : ℝ => U t.toNNReal := hU.comp continuous_real_toNNReal
  have huc : UniformContinuousOn (fun t : ℝ => U t.toNNReal) (Icc 0 T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hV.continuousOn
  obtain ⟨δ, hδ, hδU⟩ := Metric.uniformContinuousOn_iff.1 huc ((β - α) / 2) (by linarith)
  refine ⟨min (δ / 2) (α * (β - α) / 8), lt_min (by positivity) (by nlinarith),
    fun t₁ t₂ ht₁ ht₂ h12 hα₁ hβ₂ hlow => ?_⟩
  by_contra hlt
  push Not at hlt
  have hmin1 : min (δ / 2) (α * (β - α) / 8) ≤ δ / 2 := min_le_left _ _
  have hmin2 : min (δ / 2) (α * (β - α) / 8) ≤ α * (β - α) / 8 := min_le_right _ _
  have h1 : t₁ ∈ Icc 0 T := by
    have := (lifeSet_eq_Ico hT ▸ ht₁ : t₁ ∈ Ico 0 T)
    exact ⟨this.1, this.2.le⟩
  have h2 : t₂ ∈ Icc 0 T := by
    have := (lifeSet_eq_Ico hT ▸ ht₂ : t₂ ∈ Ico 0 T)
    exact ⟨this.1, this.2.le⟩
  have hdist : dist t₁ t₂ < δ := by
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h12)]
    linarith
  have hU12 := hδU t₁ h1 t₂ h2 hdist
  rw [dist_eq_norm, ← norm_neg, neg_sub] at hU12
  have hbound := norm_fPath_sub_le hU hα ht₁.1 h12 ht₂ hlow
  have hlow2 : β - α ≤ ‖fPath U hU z t₂ - fPath U hU z t₁‖ :=
    (sub_le_sub hβ₂ hα₁).trans (norm_sub_norm_le _ _)
  have hlt3 : 2 * (t₂ - t₁) / α < (β - α) / 4 := by
    rw [div_lt_iff₀ hα]
    nlinarith
  linarith

/-! ### The limit -/

/-- **Lemma 2.5** (`lem-endpt-cont`, paper.tex:L667-690): for a continuous driver `U` and `z` with
`T_z < ∞`, `|f_t(z)| → 0` as `t → T_z⁻` (within the life set `[0, T_z)`). -/
theorem tendsto_norm_fPath_nhdsWithin (hU : Continuous U) {z : ℂ} (hT : absorbingTime U z ≠ ⊤) :
    Tendsto (fun t => ‖fPath U hU z t‖) (𝓝[lifeSet U z] (absorbingTime U z).toReal) (𝓝 0) := by
  set T := (absorbingTime U z).toReal with hTdef
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro β hβ
  by_contra hcon
  push Not at hcon
  obtain ⟨ε, hε, hεB⟩ := exists_pos_upcrossing_length hU hT (α := β / 2) (β := β) (by positivity)
    (by linarith)
  -- a time `a` in the life set within `ε` of `T_z`
  obtain ⟨a, ha, haT, -⟩ := hcon ε hε
  have haIco : a ∈ Ico 0 T := lifeSet_eq_Ico hT ▸ ha
  -- the liminf brings `|f|` below `β / 2` after `a`
  obtain ⟨s₁, hs₁, has₁, hs₁lt⟩ := exists_norm_fPath_lt hU hT (η := β / 2) (by positivity) ha
  have hs₁Ico : s₁ ∈ Ico 0 T := lifeSet_eq_Ico hT ▸ hs₁
  -- a later time with `|f| ≥ β`
  obtain ⟨t₂, ht₂, ht₂T, ht₂β⟩ := hcon (T - s₁) (by linarith [hs₁Ico.2])
  have ht₂Ico : t₂ ∈ Ico 0 T := lifeSet_eq_Ico hT ▸ ht₂
  have hβ₂ : β ≤ ‖fPath U hU z t₂‖ := by
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using ht₂β
  have hs₁t₂ : s₁ < t₂ := by
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [ht₂Ico.2])] at ht₂T
    linarith
  -- the last time in `[s₁, t₂]` with `|f| ≤ β / 2`
  have hcont : ContinuousOn (fun s => ‖fPath U hU z s‖) (Icc s₁ t₂) :=
    (continuousOn_norm_fPath hU z).mono (Icc_subset_lifeSet ht₂ |>.trans' fun s hs =>
      ⟨hs₁Ico.1.trans hs.1, hs.2⟩)
  have hclosed : IsClosed (Icc s₁ t₂ ∩ (fun s => ‖fPath U hU z s‖) ⁻¹' Iic (β / 2)) :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hKc : IsCompact (Icc s₁ t₂ ∩ (fun s => ‖fPath U hU z s‖) ⁻¹' Iic (β / 2)) :=
    isCompact_Icc.of_isClosed_subset hclosed inter_subset_left
  obtain ⟨t₁, ht₁K, ht₁gr⟩ := hKc.exists_isGreatest
    ⟨s₁, ⟨le_rfl, hs₁t₂.le⟩, hs₁lt.le⟩
  have ht₁I : t₁ ∈ Icc s₁ t₂ := ht₁K.1
  have ht₁le : ‖fPath U hU z t₁‖ ≤ β / 2 := ht₁K.2
  have ht₁t₂ : t₁ < t₂ := by
    refine lt_of_le_of_ne ht₁I.2 fun h => ?_
    rw [h] at ht₁le
    linarith
  have hgt : ∀ s ∈ Ioc t₁ t₂, β / 2 ≤ ‖fPath U hU z s‖ := by
    intro s hs
    by_contra hlt
    push Not at hlt
    have : s ∈ Icc s₁ t₂ ∩ (fun s => ‖fPath U hU z s‖) ⁻¹' Iic (β / 2) :=
      ⟨⟨ht₁I.1.trans hs.1.le, hs.2⟩, hlt.le⟩
    exact absurd (ht₁gr this) (not_le.2 hs.1)
  have hlow : ∀ s ∈ Icc t₁ t₂, β / 2 ≤ ‖fPath U hU z s‖ := by
    intro s hs
    have hsub : Icc t₁ t₂ ⊆ Icc s₁ t₂ := Icc_subset_Icc_left ht₁I.1
    refine le_on_closure (f := fun _ => β / 2) (g := fun s => ‖fPath U hU z s‖)
      (s := Ioc t₁ t₂) hgt continuousOn_const ?_ (x := s) (by rwa [closure_Ioc ht₁t₂.ne])
    rw [closure_Ioc ht₁t₂.ne]
    exact hcont.mono hsub
  have ht₁life : t₁ ∈ lifeSet U z :=
    mem_lifeSet_of_le ht₂ (hs₁Ico.1.trans ht₁I.1) ht₁t₂.le
  have hdur := hεB t₁ t₂ ht₁life ht₂ ht₁t₂.le ht₁le hβ₂ hlow
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [haIco.2])] at haT
  linarith [ht₁I.1, ht₂Ico.2]

/-- `log |f_t(z)| → -∞` as `t → T_z⁻` when `T_z < ∞`. -/
theorem tendsto_log_norm_fPath_nhdsWithin (hU : Continuous U) {z : ℂ}
    (hT : absorbingTime U z ≠ ⊤) :
    Tendsto (fun t => Real.log ‖fPath U hU z t‖) (𝓝[lifeSet U z] (absorbingTime U z).toReal)
      atBot := by
  refine Real.tendsto_log_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
  · exact tendsto_norm_fPath_nhdsWithin hU hT
  · exact eventually_nhdsWithin_of_forall fun t ht => norm_fPath_pos hU ht

/-- The `ε`-form of Lemma 2.5: if `0 < T_z < ∞`, for every `ε > 0` there is `a < T_z` such that
`|f_t(z)| < ε` for all `t ∈ [a, T_z)`. -/
theorem exists_forall_norm_fPath_lt (hU : Continuous U) {z : ℂ} (hz : 0 < absorbingTime U z)
    (hT : absorbingTime U z ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ lifeSet U z, ∀ t ∈ lifeSet U z, a ≤ t → ‖fPath U hU z t‖ < ε := by
  set T := (absorbingTime U z).toReal with hTdef
  have hTpos : 0 < T := ENNReal.toReal_pos hz.ne' hT
  have hev := (tendsto_norm_fPath_nhdsWithin hU hT).eventually (gt_mem_nhds hε)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  set a := max 0 (T - δ / 2) with hadef
  have haT : a < T := max_lt hTpos (by linarith)
  have ha : a ∈ lifeSet U z := by
    rw [lifeSet_eq_Ico hT]; exact ⟨le_max_left _ _, haT⟩
  refine ⟨a, ha, fun t ht hat => hball ⟨?_, ht⟩⟩
  have htT : t < T := (lifeSet_eq_Ico hT ▸ ht : t ∈ Ico 0 T).2
  rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
  have := (le_max_right 0 (T - δ / 2)).trans hat
  linarith

end ComplexSLE.Internal.Polar

end
