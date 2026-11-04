/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.Sigma
public import ComplexSLE.Internal.Polar.PolarDerivShift

/-!
# Continuity of the clock, `σ_z(s)` and `f̂_s(z)` in the starting point `z` (M7/A3)

Fix a continuous driver `U`. By `exists_lipschitz_initial` (Lipschitz dependence of `f_r(·)` on the
initial point, uniformly on `[0, t] ⊆ [0, T_z)`) we prove, for fixed `t` and `s`:

* `continuousAt_clock_initial`: `w ↦ A_t(w) = ∫₀ᵗ |f_r(w)|⁻² dr` is continuous at every `z` with
  `t ∈ [0, T_z)` (dominated convergence);
* `isOpen_sigmaDomSet`: `{w | s ∈ sigmaDom U hU w}` is open;
* `continuousAt_sigmaTime_initial`: `w ↦ σ_w(s)` is continuous at every `z` with
  `s ∈ sigmaDom U hU z` (strict monotonicity of the clock);
* `continuousAt_fPath_sigmaTime_initial`, `continuousAt_log_norm_fPath_sigmaTime_initial`:
  `w ↦ f̂_s(w) = f_{σ_w(s)}(w)` and `w ↦ log|f̂_s(w)|` are continuous there.

The argument `θ̂_s(w)` is treated in `PolarContArg.lean`.
-/

public section

open scoped NNReal ENNReal Topology
open Set Filter

namespace ComplexSLE.Internal.Polar

variable {U : ℝ≥0 → ℂ}

/-! ### Local uniform control of `f_r(w)` for `w` near `z` -/

/-- For `r ∈ [0, t] ⊆ [0, T_z)`, `w ↦ f_r(w)` is continuous at `z`. -/
theorem continuousAt_fPath_initial (hU : Continuous U) {z : ℂ} {t r : ℝ} (ht : t ∈ lifeSet U z)
    (hr : r ∈ Icc (0 : ℝ) t) : ContinuousAt (fun w => fPath U hU w r) z := by
  obtain ⟨ρ, hρ, C, -, hC⟩ := exists_lipschitz_initial hU ht
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine squeeze_zero' (g := fun w : ℂ => C * ‖w - z‖)
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [Metric.ball_mem_nhds z hρ] with w hw
    exact (hC w (by simpa [dist_eq_norm] using hw)).2 r hr
  · have : Tendsto (fun w : ℂ => C * ‖w - z‖) (𝓝 z) (𝓝 (C * ‖z - z‖)) :=
      tendsto_const_nhds.mul ((continuous_id.sub continuous_const).norm.tendsto z)
    simpa using this

/-- Near `z`, the time `t ∈ [0, T_z)` stays in the life set and `|f_r(w)|` stays bounded below on
`[0, t]` by a constant independent of `w`. -/
theorem eventually_forall_le_norm_fPath_initial (hU : Continuous U) {z : ℂ} {t : ℝ}
    (ht : t ∈ lifeSet U z) :
    ∃ η > 0, ∀ᶠ w in 𝓝 z, t ∈ lifeSet U w ∧ ∀ r ∈ Icc (0 : ℝ) t, η ≤ ‖fPath U hU w r‖ := by
  obtain ⟨η, hη, hηle⟩ := exists_pos_le_norm_fPath hU ht
  obtain ⟨ρ, hρ, C, hC0, hC⟩ := exists_lipschitz_initial hU ht
  refine ⟨η / 2, by positivity, ?_⟩
  have hδ : 0 < min ρ (η / (2 * (C + 1))) := lt_min hρ (by positivity)
  filter_upwards [Metric.ball_mem_nhds z hδ] with w hw
  have hw' : ‖w - z‖ < min ρ (η / (2 * (C + 1))) := by simpa [dist_eq_norm] using hw
  obtain ⟨hlife, hbd⟩ := hC w (lt_of_lt_of_le hw' (min_le_left _ _))
  refine ⟨hlife, fun r hr => ?_⟩
  have h1 := hbd r hr
  have h2 : C * ‖w - z‖ ≤ η / 2 := by
    have h3 : ‖w - z‖ ≤ η / (2 * (C + 1)) := (hw'.trans_le (min_le_right _ _)).le
    calc C * ‖w - z‖ ≤ C * (η / (2 * (C + 1))) := mul_le_mul_of_nonneg_left h3 hC0
      _ ≤ (C + 1) * (η / (2 * (C + 1))) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = η / 2 := by field_simp
  have h4 := hηle r hr
  have h5 := norm_sub_norm_le (fPath U hU z r) (fPath U hU w r)
  rw [norm_sub_rev] at h5
  linarith

/-! ### Continuity of the clock in the starting point -/

/-- **The clock `A_t(w)` is continuous in the starting point** at every `z` with
`t ∈ [0, T_z)`. -/
theorem continuousAt_clock_initial (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    ContinuousAt (fun w => clock U hU w t) z := by
  obtain ⟨η, hη, hev⟩ := eventually_forall_le_norm_fPath_initial hU ht
  unfold clock
  refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => (η ^ 2)⁻¹) ?_ ?_
    intervalIntegrable_const ?_
  · filter_upwards [hev] with w hw
    rw [uIoc_of_le ht.1]
    exact ((continuousOn_clockRate hU w).mono (Ioc_subset_Icc_self.trans
      (Icc_subset_lifeSet hw.1))).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [hev] with w hw
    refine Eventually.of_forall fun r hr => ?_
    rw [uIoc_of_le ht.1] at hr
    have hrw := hw.2 r (Ioc_subset_Icc_self hr)
    have hpos : 0 < ‖fPath U hU w r‖ := lt_of_lt_of_le hη hrw
    unfold clockRate
    rw [Real.norm_of_nonneg (by positivity)]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hη.le hrw 2)
  · refine Eventually.of_forall fun r hr => ?_
    rw [uIoc_of_le ht.1] at hr
    have hcont := continuousAt_fPath_initial hU ht (Ioc_subset_Icc_self hr)
    unfold clockRate
    refine (hcont.norm.pow 2).inv₀ ?_
    exact pow_ne_zero 2 (norm_fPath_pos hU (Icc_subset_lifeSet ht (Ioc_subset_Icc_self hr))).ne'

/-! ### Openness of the domain of `σ_w` and continuity of `σ_w(s)` -/

/-- **Upper control.** If `s ∈ sigmaDom U hU z` and `σ_z(s) < t₂ ∈ [0, T_z)`, then for `w` near `z`
also `s ∈ sigmaDom U hU w` and `σ_w(s) < t₂`. -/
theorem eventually_mem_sigmaDom_sigmaTime_lt (hU : Continuous U) {z : ℂ} {s : ℝ}
    (hs : s ∈ sigmaDom U hU z) {t₂ : ℝ} (ht₂ : t₂ ∈ lifeSet U z)
    (hlt : sigmaTime U hU z s < t₂) :
    ∀ᶠ w in 𝓝 z, s ∈ sigmaDom U hU w ∧ sigmaTime U hU w s < t₂ := by
  have hσ : sigmaTime U hU z s ∈ lifeSet U z := sigmaTime_mem_lifeSet hU hs
  have hcl : s < clock U hU z t₂ := by
    have := clock_lt_clock hU hσ.1 hlt ht₂
    rwa [clock_sigmaTime hU hs] at this
  have hev1 : ∀ᶠ w in 𝓝 z, s < clock U hU w t₂ :=
    (continuousAt_clock_initial hU ht₂).eventually (lt_mem_nhds hcl)
  have hev2 : ∀ᶠ w in 𝓝 z, t₂ ∈ lifeSet U w :=
    (isOpen_lifeSet_initial U hU t₂).mem_nhds ht₂
  filter_upwards [hev1, hev2] with w h1 h2
  have hsw : s ∈ sigmaDom U hU w := by
    refine ⟨hs.1, lt_of_lt_of_le ?_ (ofReal_clock_le_clockSup hU h2)⟩
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hs.1 h1)).2 h1
  refine ⟨hsw, ?_⟩
  have hσw := sigmaTime_mem_lifeSet hU hsw
  have : clock U hU w (sigmaTime U hU w s) < clock U hU w t₂ := by
    rwa [clock_sigmaTime hU hsw]
  exact (clock_strictMonoOn hU w).lt_iff_lt hσw h2 |>.1 this

/-- **Lower control.** If `s ∈ sigmaDom U hU z` and `0 ≤ t₁ < σ_z(s)`, then for `w` near `z`,
`t₁ < σ_w(s)` whenever `s ∈ sigmaDom U hU w`. -/
theorem eventually_lt_sigmaTime (hU : Continuous U) {z : ℂ} {s : ℝ} (hs : s ∈ sigmaDom U hU z)
    {t₁ : ℝ} (h0 : 0 ≤ t₁) (hlt : t₁ < sigmaTime U hU z s) :
    ∀ᶠ w in 𝓝 z, s ∈ sigmaDom U hU w → t₁ < sigmaTime U hU w s := by
  have hσ : sigmaTime U hU z s ∈ lifeSet U z := sigmaTime_mem_lifeSet hU hs
  have ht₁ : t₁ ∈ lifeSet U z := mem_lifeSet_of_le hσ h0 hlt.le
  have hcl : clock U hU z t₁ < s := by
    have := clock_lt_clock hU h0 hlt hσ
    rwa [clock_sigmaTime hU hs] at this
  have hev1 : ∀ᶠ w in 𝓝 z, clock U hU w t₁ < s :=
    (continuousAt_clock_initial hU ht₁).eventually (gt_mem_nhds hcl)
  have hev2 : ∀ᶠ w in 𝓝 z, t₁ ∈ lifeSet U w :=
    (isOpen_lifeSet_initial U hU t₁).mem_nhds ht₁
  filter_upwards [hev1, hev2] with w h1 h2 hsw
  have hσw := sigmaTime_mem_lifeSet hU hsw
  have : clock U hU w t₁ < clock U hU w (sigmaTime U hU w s) := by
    rwa [clock_sigmaTime hU hsw]
  exact (clock_strictMonoOn hU w).lt_iff_lt h2 hσw |>.1 this

/-- A time `t₂` in the life set strictly above `t₀` and below a given bound. -/
theorem exists_mem_lifeSet_between {z : ℂ} {t₀ b : ℝ} (ht₀ : t₀ ∈ lifeSet U z) (hb : t₀ < b) :
    ∃ t₂ ∈ lifeSet U z, t₀ < t₂ ∧ t₂ < b := by
  obtain ⟨t', ht', hlt'⟩ := exists_gt_mem_lifeSet ht₀
  obtain ⟨t₂, h1, h2⟩ := exists_between (lt_min hlt' hb)
  exact ⟨t₂, mem_lifeSet_of_le ht' (ht₀.1.trans h1.le) (h2.le.trans (min_le_left _ _)), h1,
    h2.trans_le (min_le_right _ _)⟩

/-- `{w | s ∈ sigmaDom U hU w}` is open: the domain `[0, clockSup)` of `σ_w` contains `s` for
all `w` near any `z` for which it does. -/
theorem eventually_mem_sigmaDom_initial (hU : Continuous U) {z : ℂ} {s : ℝ}
    (hs : s ∈ sigmaDom U hU z) : ∀ᶠ w in 𝓝 z, s ∈ sigmaDom U hU w := by
  have hσ : sigmaTime U hU z s ∈ lifeSet U z := sigmaTime_mem_lifeSet hU hs
  obtain ⟨t₂, ht₂, hlt, -⟩ := exists_mem_lifeSet_between hσ (lt_add_one (sigmaTime U hU z s))
  filter_upwards [eventually_mem_sigmaDom_sigmaTime_lt hU hs ht₂ hlt] with w hw using hw.1

/-- The set of starting points `w` with `s ∈ sigmaDom U hU w`. -/
@[expose] def sigmaDomSet (U : ℝ≥0 → ℂ) (hU : Continuous U) (s : ℝ) : Set ℂ :=
  {w | s ∈ sigmaDom U hU w}

/-- **`{w | s ∈ sigmaDom U hU w}` is open.** -/
theorem isOpen_sigmaDomSet (U : ℝ≥0 → ℂ) (hU : Continuous U) (s : ℝ) :
    IsOpen (sigmaDomSet U hU s) :=
  isOpen_iff_mem_nhds.2 fun _ hz => eventually_mem_sigmaDom_initial hU hz

/-- Starting points in `sigmaDom` at time `s` are not the initial value of the driver
(`T_z > 0`). -/
theorem ne_driver_zero_of_mem_sigmaDomSet {hU : Continuous U} {s : ℝ} {w : ℂ}
    (hw : w ∈ sigmaDomSet U hU s) : (0 : ℝ) ∈ lifeSet U w := by
  have := sigmaTime_mem_lifeSet hU hw
  exact mem_lifeSet_of_le this le_rfl this.1

/-- **`z ↦ σ_z(s)` is continuous** at every `z` with `s ∈ sigmaDom U hU z` (as a function on all
of `ℂ`; it is junk off the open set `sigmaDomSet U hU s`). -/
theorem continuousAt_sigmaTime_initial (hU : Continuous U) {z : ℂ} {s : ℝ}
    (hs : s ∈ sigmaDom U hU z) : ContinuousAt (fun w => sigmaTime U hU w s) z := by
  have hσ : sigmaTime U hU z s ∈ lifeSet U z := sigmaTime_mem_lifeSet hU hs
  have hdom := eventually_mem_sigmaDom_initial hU hs
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · by_cases ha0 : 0 ≤ a
    · filter_upwards [eventually_lt_sigmaTime hU hs ha0 ha, hdom] with w h1 h2 using h1 h2
    · push Not at ha0
      filter_upwards [hdom] with w hw
      exact lt_of_lt_of_le ha0 (sigmaTime_nonneg hU hw)
  · obtain ⟨t₂, ht₂, hlt, hlt'⟩ := exists_mem_lifeSet_between hσ hb
    filter_upwards [eventually_mem_sigmaDom_sigmaTime_lt hU hs ht₂ hlt] with w hw
    exact hw.2.trans hlt'

/-! ### Continuity of `f̂_s(w) = f_{σ_w(s)}(w)` and of `log|f̂_s(w)|` -/

/-- `σ_w(s) → σ_z(s)` as `w → z`, within the life set of `z`. -/
theorem tendsto_sigmaTime_nhdsWithin_lifeSet (hU : Continuous U) {z : ℂ} {s : ℝ}
    (hs : s ∈ sigmaDom U hU z) :
    Tendsto (fun w => sigmaTime U hU w s) (𝓝 z) (𝓝[lifeSet U z] sigmaTime U hU z s) := by
  have hσ : sigmaTime U hU z s ∈ lifeSet U z := sigmaTime_mem_lifeSet hU hs
  obtain ⟨t₂, ht₂, hlt, -⟩ := exists_mem_lifeSet_between hσ (lt_add_one (sigmaTime U hU z s))
  refine tendsto_nhdsWithin_iff.2 ⟨continuousAt_sigmaTime_initial hU hs, ?_⟩
  filter_upwards [eventually_mem_sigmaDom_sigmaTime_lt hU hs ht₂ hlt] with w hw
  exact mem_lifeSet_of_le ht₂ (sigmaTime_nonneg hU hw.1) hw.2.le

/-- **`z ↦ f̂_s(z) = f_{σ_z(s)}(z)` is continuous** at every `z` with `s ∈ sigmaDom U hU z`. -/
theorem continuousAt_fPath_sigmaTime_initial (hU : Continuous U) {z : ℂ} {s : ℝ}
    (hs : s ∈ sigmaDom U hU z) :
    ContinuousAt (fun w => fPath U hU w (sigmaTime U hU w s)) z := by
  have hσ : sigmaTime U hU z s ∈ lifeSet U z := sigmaTime_mem_lifeSet hU hs
  obtain ⟨t₂, ht₂, hlt, -⟩ := exists_mem_lifeSet_between hσ (lt_add_one (sigmaTime U hU z s))
  obtain ⟨ρ, hρ, C, -, hC⟩ := exists_lipschitz_initial hU ht₂
  have hev := eventually_mem_sigmaDom_sigmaTime_lt hU hs ht₂ hlt
  -- the part `f_{σ_w(s)}(z) → f_{σ_z(s)}(z)`
  have h1 : Tendsto (fun w => fPath U hU z (sigmaTime U hU w s)) (𝓝 z)
      (𝓝 (fPath U hU z (sigmaTime U hU z s))) :=
    ((continuousOn_fPath hU z) _ hσ).tendsto.comp (tendsto_sigmaTime_nhdsWithin_lifeSet hU hs)
  -- the part `f_{σ_w(s)}(w) - f_{σ_w(s)}(z) → 0`
  have h2 : Tendsto (fun w => fPath U hU w (sigmaTime U hU w s) -
      fPath U hU z (sigmaTime U hU w s)) (𝓝 z) (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
    refine squeeze_zero' (g := fun w : ℂ => C * ‖w - z‖)
      (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
    · filter_upwards [Metric.ball_mem_nhds z hρ, hev] with w hw hw'
      exact (hC w (by simpa [dist_eq_norm] using hw)).2 _
        ⟨sigmaTime_nonneg hU hw'.1, hw'.2.le⟩
    · have : Tendsto (fun w : ℂ => C * ‖w - z‖) (𝓝 z) (𝓝 (C * ‖z - z‖)) :=
        tendsto_const_nhds.mul ((continuous_id.sub continuous_const).norm.tendsto z)
      simpa using this
  have := h2.add h1
  simp only [zero_add, sub_add_cancel] at this
  exact this

/-- `f̂_s(z) ≠ 0` for `s ∈ sigmaDom`. -/
theorem fPath_sigmaTime_ne_zero (hU : Continuous U) {z : ℂ} {s : ℝ} (hs : s ∈ sigmaDom U hU z) :
    fPath U hU z (sigmaTime U hU z s) ≠ 0 :=
  fPath_ne_zero hU (sigmaTime_mem_lifeSet hU hs)

/-- **`z ↦ log|f̂_s(z)|` is continuous** at every `z` with `s ∈ sigmaDom U hU z`. -/
theorem continuousAt_log_norm_fPath_sigmaTime_initial (hU : Continuous U) {z : ℂ} {s : ℝ}
    (hs : s ∈ sigmaDom U hU z) :
    ContinuousAt (fun w => Real.log ‖fPath U hU w (sigmaTime U hU w s)‖) z :=
  (continuousAt_fPath_sigmaTime_initial hU hs).norm.log
    (norm_ne_zero_iff.2 (fPath_sigmaTime_ne_zero hU hs))

end ComplexSLE.Internal.Polar

end
