/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.Path
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Algebra.Order.ToIntervalMod

/-!
# The continuous argument `θ_t(z)` (Definition 2.10, `def-arg`, `step:arg-lift`)

For a continuous driver `U` and a point `z`, the direction `f_t(z)/|f_t(z)|` is a continuous
`Circle`-valued path on the life set `[0, T_z)`. We lift it through the covering map
`Circle.exp : ℝ → Circle` (Mathlib's path lifting, `IsCoveringMap.liftPath`) on every compact
`[0, T] ⊆ [0, T_z)` and glue by uniqueness of lifts. The result `argPath` is the unique function
`θ` continuous on `[0, T_z)` with `f_t(z) = |f_t(z)| e^{iθ_t}` there and `θ_0 ∈ [0, 2π)`
(paper.tex:L851-853). Off the life set `argPath` is junk.
-/

public section

open scoped NNReal ENNReal Real
open Set Complex

namespace ComplexSLE.Internal.Polar

variable {U : ℝ≥0 → ℂ}

/-! ### Lifting circle-valued paths on compact intervals -/

/-- A continuous `Circle`-valued path on `[0, T]` lifts continuously through `Circle.exp`, with a
prescribed initial value. -/
theorem exists_lift_Icc {γ : ℝ → Circle} {T : ℝ} (hT : 0 ≤ T) (hγ : ContinuousOn γ (Icc 0 T))
    {e : ℝ} (he : Circle.exp e = γ 0) :
    ∃ Γ : ℝ → ℝ, ContinuousOn Γ (Icc 0 T) ∧ Γ 0 = e ∧ ∀ t ∈ Icc 0 T, Circle.exp (Γ t) = γ t := by
  rcases eq_or_lt_of_le hT with h0 | hTpos
  · subst h0
    refine ⟨fun _ => e, continuousOn_const, rfl, fun t ht => ?_⟩
    have : t = 0 := le_antisymm ht.2 ht.1
    rw [this, he]
  · have hmem : ∀ s : unitInterval, (s : ℝ) * T ∈ Icc 0 T := fun s =>
      ⟨mul_nonneg s.2.1 hT, mul_le_of_le_one_left hT s.2.2⟩
    let p : C(unitInterval, Circle) :=
      ⟨fun s => γ ((s : ℝ) * T), hγ.comp_continuous (by fun_prop) hmem⟩
    have hp0 : p 0 = Circle.exp e := by
      simp only [p, ContinuousMap.coe_mk, Set.Icc.coe_zero, zero_mul]
      exact he.symm
    set Γ₀ := Circle.isCoveringMap_exp.liftPath p e hp0 with hΓ₀
    refine ⟨fun t => Γ₀ (projIcc 0 1 zero_le_one (t / T)), ?_, ?_, ?_⟩
    · exact (Γ₀.continuous.comp (continuous_projIcc.comp (continuous_id.div_const T))).continuousOn
    · simp only [zero_div, projIcc_left]
      exact Circle.isCoveringMap_exp.liftPath_zero p e hp0
    · intro t ht
      have htT : t / T ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg ht.1 hT, (div_le_one hTpos).2 ht.2⟩
      show Circle.exp (Γ₀ (projIcc 0 1 zero_le_one (t / T))) = γ t
      rw [projIcc_of_mem _ htT]
      have hl := congrFun (Circle.isCoveringMap_exp.liftPath_lifts p e hp0) ⟨t / T, htT⟩
      simp only [Function.comp_apply] at hl
      rw [← hΓ₀] at hl
      rw [hl]
      simp only [p, ContinuousMap.coe_mk]
      rw [div_mul_cancel₀ t hTpos.ne']

/-- Uniqueness of lifts through `Circle.exp` on a preconnected set. -/
theorem lift_unique_of_isPreconnected {Γ₁ Γ₂ : ℝ → ℝ} {s : Set ℝ} (hs : IsPreconnected s)
    (h₁ : ContinuousOn Γ₁ s) (h₂ : ContinuousOn Γ₂ s)
    (he : ∀ t ∈ s, Circle.exp (Γ₁ t) = Circle.exp (Γ₂ t)) {a : ℝ} (ha : a ∈ s)
    (h0 : Γ₁ a = Γ₂ a) : EqOn Γ₁ Γ₂ s :=
  Circle.isCoveringMap_exp.eqOn_of_comp_eqOn hs h₁ h₂ (fun t ht => he t ht) ha h0

/-- The life set is order-connected, hence preconnected. -/
theorem lifeSet_ordConnected (U : ℝ≥0 → ℂ) (z : ℂ) : (lifeSet U z).OrdConnected :=
  ⟨fun _ hx _ hy _ ht => mem_lifeSet_of_le hy (hx.1.trans ht.1) ht.2⟩

theorem lifeSet_isPreconnected (U : ℝ≥0 → ℂ) (z : ℂ) : IsPreconnected (lifeSet U z) :=
  (lifeSet_ordConnected U z).isPreconnected

/-! ### The direction `f_t(z)/|f_t(z)|` on the circle -/

/-- The direction `f_t(z)/|f_t(z)| = e^{i arg f_t(z)}` as a point of the unit circle. -/
noncomputable def dirPath (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) (t : ℝ) : Circle :=
  Circle.exp (arg (fPath U hU z t))

theorem coe_dirPath (hU : Continuous U) (z : ℂ) (t : ℝ) :
    (dirPath U hU z t : ℂ) = exp (arg (fPath U hU z t) * I) := by
  simp [dirPath, Circle.coe_exp]

theorem coe_dirPath_eq_div (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    (dirPath U hU z t : ℂ) = fPath U hU z t / ‖fPath U hU z t‖ := by
  rw [coe_dirPath]
  have h := norm_mul_exp_arg_mul_I (fPath U hU z t)
  have hn : (‖fPath U hU z t‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_fPath_pos hU ht).ne'
  rw [eq_div_iff hn, mul_comm]
  exact h

theorem continuousOn_dirPath (hU : Continuous U) (z : ℂ) :
    ContinuousOn (dirPath U hU z) (lifeSet U z) := by
  have hind : Topology.IsInducing ((↑) : Circle → ℂ) := Topology.IsInducing.subtypeVal
  refine hind.continuousOn_iff.2 ?_
  refine ContinuousOn.congr ?_ fun t ht => coe_dirPath_eq_div hU ht
  refine (continuousOn_fPath hU z).div ?_ fun t ht => ?_
  · exact Complex.continuous_ofReal.comp_continuousOn (continuousOn_norm_fPath hU z)
  · exact_mod_cast (norm_fPath_pos hU ht).ne'

/-! ### The argument process -/

/-- The initial argument `θ_0 ∈ [0, 2π)`: `arg (z - U_0)` reduced modulo `2π` into `[0, 2π)`. -/
noncomputable def argInit (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) : ℝ :=
  toIcoMod Real.two_pi_pos 0 (arg (fPath U hU z 0))

theorem argInit_mem_Ico (hU : Continuous U) (z : ℂ) : argInit U hU z ∈ Ico 0 (2 * π) :=
  toIcoMod_mem_Ico' _ _

theorem circleExp_argInit (hU : Continuous U) (z : ℂ) :
    Circle.exp (argInit U hU z) = dirPath U hU z 0 := by
  unfold argInit dirPath
  rw [Circle.exp_eq_exp]
  refine ⟨-toIcoDiv Real.two_pi_pos 0 (arg (fPath U hU z 0)), ?_⟩
  have := toIcoMod_sub_self Real.two_pi_pos 0 (arg (fPath U hU z 0))
  rw [zsmul_eq_mul] at this
  push_cast at this ⊢
  linarith

/-- `step:arg-lift`, existence: a continuous lift of the direction on the life set, starting in
`[0, 2π)`. -/
theorem exists_argLift (hU : Continuous U) (z : ℂ) :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (lifeSet U z) ∧ θ 0 = argInit U hU z ∧
      ∀ t ∈ lifeSet U z, Circle.exp (θ t) = dirPath U hU z t := by
  classical
  by_cases hz : (0 : ℝ) ∈ lifeSet U z
  swap
  · refine ⟨fun _ => argInit U hU z, continuousOn_const, rfl, fun t ht => ?_⟩
    exact absurd (mem_lifeSet_of_le ht le_rfl ht.1) hz
  -- lifts on the compact pieces `[0, T]`
  have hpiece : ∀ T ∈ lifeSet U z, ∃ Γ : ℝ → ℝ, ContinuousOn Γ (Icc 0 T) ∧ Γ 0 = argInit U hU z ∧
      ∀ t ∈ Icc 0 T, Circle.exp (Γ t) = dirPath U hU z t := fun T hT =>
    exists_lift_Icc hT.1 ((continuousOn_dirPath hU z).mono (Icc_subset_lifeSet hT))
      (circleExp_argInit hU z)
  choose! Γ hΓc hΓ0 hΓe using hpiece
  -- the glued lift: use the piece for a point above `t`
  have hchoice : ∀ t ∈ lifeSet U z, ∃ T ∈ lifeSet U z, t < T := fun t ht =>
    exists_gt_mem_lifeSet ht
  choose! Tof hTof hltTof using hchoice
  refine ⟨fun t => Γ (Tof t) t, ?_, ?_, ?_⟩
  · -- continuity: near `t`, the glued lift agrees with one piece
    intro t ht
    have hT' := hTof t ht
    have hlt := hltTof t ht
    have hagree : ∀ s ∈ lifeSet U z ∩ Iio (Tof t), Γ (Tof s) s = Γ (Tof t) s := by
      intro s ⟨hs, hslt⟩
      have hTs := hTof s hs
      have hslt' := hltTof s hs
      -- both pieces are lifts on `[0, min (Tof s) (Tof t)]`
      set m := min (Tof s) (Tof t) with hm
      have hm0 : 0 ≤ m := le_min hTs.1 hT'.1
      have hsm : s ∈ Icc 0 m := ⟨hs.1, le_min hslt'.le (hslt.le)⟩
      have hsub1 : Icc 0 m ⊆ Icc 0 (Tof s) := Icc_subset_Icc le_rfl (min_le_left _ _)
      have hsub2 : Icc 0 m ⊆ Icc 0 (Tof t) := Icc_subset_Icc le_rfl (min_le_right _ _)
      refine lift_unique_of_isPreconnected isPreconnected_Icc ((hΓc _ hTs).mono hsub1)
        ((hΓc _ hT').mono hsub2) (fun u hu => ?_) (left_mem_Icc.2 hm0) ?_ hsm
      · rw [hΓe _ hTs u (hsub1 hu), hΓe _ hT' u (hsub2 hu)]
      · rw [hΓ0 _ hTs, hΓ0 _ hT']
    have hnhds : lifeSet U z ∩ Iio (Tof t) ∈ nhdsWithin t (lifeSet U z) :=
      Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hlt))
    have hcont : ContinuousWithinAt (Γ (Tof t)) (lifeSet U z) t := by
      have h1 : ContinuousWithinAt (Γ (Tof t)) (Icc 0 (Tof t)) t :=
        (hΓc _ hT') t ⟨ht.1, hlt.le⟩
      refine h1.mono_of_mem_nhdsWithin ?_
      exact Filter.mem_of_superset hnhds fun s hs => ⟨hs.1.1, hs.2.le⟩
    refine hcont.congr_of_eventuallyEq ?_ (hagree t ⟨ht, hlt⟩)
    exact Filter.eventually_of_mem hnhds fun s hs => hagree s hs
  · exact hΓ0 _ (hTof 0 hz)
  · intro t ht
    exact hΓe _ (hTof t ht) t ⟨ht.1, (hltTof t ht).le⟩

/-- **The argument process `θ_t(z)`** (Definition 2.10, paper.tex:L851-853): the unique function
continuous on `[0, T_z)` with `f_t(z)/|f_t(z)| = e^{iθ_t(z)}` there and `θ_0(z) ∈ [0, 2π)`.
Junk off the life set. -/
noncomputable def argPath (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) : ℝ → ℝ :=
  Classical.choose (exists_argLift hU z)

theorem continuousOn_argPath (hU : Continuous U) (z : ℂ) :
    ContinuousOn (argPath U hU z) (lifeSet U z) :=
  (Classical.choose_spec (exists_argLift hU z)).1

theorem argPath_zero (hU : Continuous U) (z : ℂ) : argPath U hU z 0 = argInit U hU z :=
  (Classical.choose_spec (exists_argLift hU z)).2.1

theorem argPath_zero_mem_Ico (hU : Continuous U) (z : ℂ) :
    argPath U hU z 0 ∈ Ico 0 (2 * π) := by
  rw [argPath_zero]; exact argInit_mem_Ico hU z

theorem circleExp_argPath (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    Circle.exp (argPath U hU z t) = dirPath U hU z t :=
  (Classical.choose_spec (exists_argLift hU z)).2.2 t ht

/-- `f_t(z) = |f_t(z)| e^{iθ_t(z)}` on the life set. -/
theorem fPath_eq_norm_mul_exp (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    fPath U hU z t = ‖fPath U hU z t‖ * exp (argPath U hU z t * I) := by
  have h := congrArg (fun w : Circle => (w : ℂ)) (circleExp_argPath hU ht)
  simp only [Circle.coe_exp] at h
  rw [coe_dirPath_eq_div hU ht] at h
  have hn : (‖fPath U hU z t‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_fPath_pos hU ht).ne'
  rw [h, mul_div_cancel₀ _ hn]

theorem exp_argPath_mul_I (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    exp (argPath U hU z t * I) = fPath U hU z t / ‖fPath U hU z t‖ := by
  have hn : (‖fPath U hU z t‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_fPath_pos hU ht).ne'
  rw [eq_div_iff hn, mul_comm, ← fPath_eq_norm_mul_exp hU ht]

theorem re_fPath (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    (fPath U hU z t).re = ‖fPath U hU z t‖ * Real.cos (argPath U hU z t) := by
  conv_lhs => rw [fPath_eq_norm_mul_exp hU ht]
  rw [re_ofReal_mul, exp_ofReal_mul_I_re]

theorem im_fPath (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    (fPath U hU z t).im = ‖fPath U hU z t‖ * Real.sin (argPath U hU z t) := by
  conv_lhs => rw [fPath_eq_norm_mul_exp hU ht]
  rw [im_ofReal_mul, exp_ofReal_mul_I_im]

/-- **Uniqueness of the argument process** (`step:arg-lift`): any function continuous on the life
set with `f_t(z) = |f_t(z)| e^{iθ_t}` there and `θ_0 ∈ [0, 2π)` agrees with `argPath` on the life
set. -/
theorem argPath_unique (hU : Continuous U) {z : ℂ} {θ : ℝ → ℝ}
    (hc : ContinuousOn θ (lifeSet U z))
    (he : ∀ t ∈ lifeSet U z, fPath U hU z t = ‖fPath U hU z t‖ * exp (θ t * I))
    (h0 : θ 0 ∈ Ico 0 (2 * π)) : EqOn θ (argPath U hU z) (lifeSet U z) := by
  intro t ht
  have hz : (0 : ℝ) ∈ lifeSet U z := mem_lifeSet_of_le ht le_rfl ht.1
  -- the two lifts agree on the circle
  have hexp : ∀ s ∈ lifeSet U z, Circle.exp (θ s) = Circle.exp (argPath U hU z s) := by
    intro s hs
    apply Circle.ext
    simp only [Circle.coe_exp]
    have hn : (‖fPath U hU z s‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_fPath_pos hU hs).ne'
    have h1 := he s hs
    have h2 := fPath_eq_norm_mul_exp hU hs
    exact mul_left_cancel₀ hn (h1.symm.trans h2)
  -- and at time `0`, both values lie in `[0, 2π)`
  have h00 : θ 0 = argPath U hU z 0 := by
    have := (Circle.exp_eq_exp).1 (hexp 0 hz)
    obtain ⟨m, hm⟩ := this
    have hθ := h0
    have hA := argPath_zero_mem_Ico hU z
    have hm0 : m = 0 := by
      have hlt1 : (m : ℝ) * (2 * π) < 2 * π := by linarith [hθ.2, hA.1]
      have hgt1 : -(2 * π) < (m : ℝ) * (2 * π) := by linarith [hθ.1, hA.2]
      have hpos := Real.two_pi_pos
      have h1 : (m : ℝ) < 1 := by
        by_contra h; push Not at h; nlinarith
      have h2 : (-1 : ℝ) < m := by
        by_contra h; push Not at h; nlinarith
      have h1' : m < 1 := by exact_mod_cast h1
      have h2' : -1 < m := by exact_mod_cast h2
      omega
    rw [hm, hm0]; simp
  exact lift_unique_of_isPreconnected (lifeSet_isPreconnected U z) hc
    (continuousOn_argPath hU z) hexp hz h00 ht

end ComplexSLE.Internal.Polar

end
