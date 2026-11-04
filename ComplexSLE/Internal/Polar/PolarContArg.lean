/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.PolarContClock
public import ComplexSLE.Internal.Polar.Argument
public import ComplexSLE.Internal.Polar.ClockArg

/-!
# Continuity of the winding of `θ̂_s(z)` in the starting point `z` (M7/A3)

The argument process `θ_t(z)` (`argPath`) is the continuous lift of the direction of `f_t(z)` with
`θ_0 ∈ [0, 2π)`; as `z` varies the initial value `θ_0(z) = argInit` jumps by `2π` where
`z - U_0` crosses the positive real axis. What is continuous in `z` is the winding
`θ̂_s(z) - θ̂_0(z)` (`continuousAt_argPath_sub_initial`).

**Winding comparison.** For `z` and `t ∈ [0, T_z)`, `w` near `z` and `r ∈ [0, t]` put
`Q_w(r) = (d_w(r) d_z(0)) / (d_w(0) d_z(r))`, where `d_w(r) = f_r(w)/|f_r(w)|` is the direction.
By the Lipschitz dependence of `f_r(w)` on `w` (`exists_lipschitz_initial`), `|Q_w(r) - 1|` is
`O(|w - z|)` uniformly on `[0, t]`. In particular `Q_w(r)` lies in the slit plane, so
`r ↦ arg Q_w(r)` is a continuous lift of `Q_w` vanishing at `0`; by uniqueness of continuous lifts
(`lift_unique_of_isPreconnected`) it equals the difference of the windings
`(θ_r(w) - θ_0(w)) - (θ_r(z) - θ_0(z))` (`argPath_winding_eq_arg`). Since `arg 1 = 0` and `arg`
is continuous at `1`, the winding is continuous in `w` at `z`.
-/

public section

open scoped NNReal ENNReal Topology Real
open Set Filter Complex

namespace ComplexSLE.Internal.Polar

variable {U : ℝ≥0 → ℂ}

/-! ### The direction is Lipschitz in the starting point -/

/-- `‖a/|a| - b/|b|‖ ≤ 2‖a - b‖/|b|` for nonzero `a`, `b`. -/
theorem norm_div_norm_sub_div_norm_le {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖a / (‖a‖ : ℂ) - b / (‖b‖ : ℂ)‖ ≤ 2 * ‖a - b‖ / ‖b‖ := by
  have hα : (0 : ℝ) < ‖a‖ := norm_pos_iff.2 ha
  have hβ : (0 : ℝ) < ‖b‖ := norm_pos_iff.2 hb
  have hα' : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  have hβ' : (‖b‖ : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  have key : a / (‖a‖ : ℂ) - b / (‖b‖ : ℂ) =
      (a - b) / (‖b‖ : ℂ) + (((‖b‖ - ‖a‖ : ℝ) : ℂ) / (‖b‖ : ℂ)) * (a / (‖a‖ : ℂ)) := by
    push_cast
    field_simp
    ring
  have hunit : ‖a / (‖a‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, norm_norm, div_self hα.ne']
  rw [key]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, hunit, mul_one, norm_div, norm_div, Complex.norm_real, Complex.norm_real,
    norm_norm, Real.norm_eq_abs]
  have h1 : |‖b‖ - ‖a‖| ≤ ‖a - b‖ := by
    rw [abs_sub_comm]; exact abs_norm_sub_norm_le a b
  calc ‖a - b‖ / ‖b‖ + |‖b‖ - ‖a‖| / ‖b‖ ≤ ‖a - b‖ / ‖b‖ + ‖a - b‖ / ‖b‖ := by
        gcongr
    _ = 2 * ‖a - b‖ / ‖b‖ := by ring

/-- The direction `d_w(r) = f_r(w)/|f_r(w)|` is Lipschitz in the starting point `w`, uniformly on
`[0, t] ⊆ [0, T_z)`. -/
theorem exists_dirPath_lipschitz_initial (hU : Continuous U) {z : ℂ} {t : ℝ}
    (ht : t ∈ lifeSet U z) :
    ∃ ρ > 0, ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℂ, ‖w - z‖ < ρ →
      t ∈ lifeSet U w ∧ ∀ r ∈ Icc (0 : ℝ) t,
        ‖(dirPath U hU w r : ℂ) - (dirPath U hU z r : ℂ)‖ ≤ K * ‖w - z‖ := by
  obtain ⟨η, hη, hηle⟩ := exists_pos_le_norm_fPath hU ht
  obtain ⟨ρ, hρ, C, hC0, hC⟩ := exists_lipschitz_initial hU ht
  refine ⟨ρ, hρ, 2 * C / η, by positivity, fun w hw => ⟨(hC w hw).1, fun r hr => ?_⟩⟩
  have hrz : r ∈ lifeSet U z := Icc_subset_lifeSet ht hr
  have hrw : r ∈ lifeSet U w := Icc_subset_lifeSet (hC w hw).1 hr
  rw [coe_dirPath_eq_div hU hrw, coe_dirPath_eq_div hU hrz]
  refine (norm_div_norm_sub_div_norm_le (fPath_ne_zero hU hrw) (fPath_ne_zero hU hrz)).trans ?_
  have h1 := (hC w hw).2 r hr
  have h2 := hηle r hr
  calc 2 * ‖fPath U hU w r - fPath U hU z r‖ / ‖fPath U hU z r‖
      ≤ 2 * (C * ‖w - z‖) / η := by
        gcongr
    _ = 2 * C / η * ‖w - z‖ := by ring

/-! ### The winding comparison -/

/-- The unit complex number `Q_w(r) = (d_w(r) d_z(0)) / (d_w(0) d_z(r))`. -/
@[expose] noncomputable def windingRatio (U : ℝ≥0 → ℂ) (hU : Continuous U) (z w : ℂ) (r : ℝ) :
    ℂ :=
  (dirPath U hU w r : ℂ) * (dirPath U hU z 0 : ℂ) /
    ((dirPath U hU w 0 : ℂ) * (dirPath U hU z r : ℂ))

theorem coe_dirPath_ne_zero (hU : Continuous U) (y : ℂ) (r : ℝ) : (dirPath U hU y r : ℂ) ≠ 0 :=
  fun h => by
    have := Circle.norm_coe (dirPath U hU y r)
    rw [h] at this
    simp at this

theorem norm_windingRatio (hU : Continuous U) (z w : ℂ) (r : ℝ) :
    ‖windingRatio U hU z w r‖ = 1 := by
  simp [windingRatio]

theorem windingRatio_zero (hU : Continuous U) (z w : ℂ) : windingRatio U hU z w 0 = 1 := by
  have h1 := coe_dirPath_ne_zero hU w 0
  have h2 := coe_dirPath_ne_zero hU z 0
  unfold windingRatio
  field_simp

/-- `‖Q_w(r) - 1‖ ≤ ‖d_w(r) - d_z(r)‖ + ‖d_w(0) - d_z(0)‖`. -/
theorem norm_windingRatio_sub_one_le (hU : Continuous U) (z w : ℂ) (r : ℝ) :
    ‖windingRatio U hU z w r - 1‖ ≤
      ‖(dirPath U hU w r : ℂ) - (dirPath U hU z r : ℂ)‖ +
        ‖(dirPath U hU w 0 : ℂ) - (dirPath U hU z 0 : ℂ)‖ := by
  set a : ℂ := (dirPath U hU w r : ℂ)
  set a' : ℂ := (dirPath U hU w 0 : ℂ)
  set b : ℂ := (dirPath U hU z r : ℂ)
  set b' : ℂ := (dirPath U hU z 0 : ℂ)
  have ha' : a' ≠ 0 := coe_dirPath_ne_zero hU w 0
  have hb : b ≠ 0 := coe_dirPath_ne_zero hU z r
  have hn : ‖a'‖ = 1 := Circle.norm_coe _
  have hn' : ‖b‖ = 1 := Circle.norm_coe _
  have hn'' : ‖b'‖ = 1 := Circle.norm_coe _
  have key : windingRatio U hU z w r - 1 = ((a - b) * b' + b * (b' - a')) / (a' * b) := by
    unfold windingRatio
    field_simp
    ring
  rw [key, norm_div, norm_mul, hn, hn', mul_one, div_one]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, hn'', hn', mul_one, one_mul, norm_sub_rev b' a']

/-- **Quantitative closeness of the windings' ratio.** For `t ∈ [0, T_z)` there are `ρ > 0` and
`K ≥ 0` such that for `‖w - z‖ < ρ`: `t ∈ [0, T_w)` and `‖Q_w(r) - 1‖ ≤ K ‖w - z‖` on `[0, t]`. -/
theorem exists_norm_windingRatio_sub_one_le (hU : Continuous U) {z : ℂ} {t : ℝ}
    (ht : t ∈ lifeSet U z) :
    ∃ ρ > 0, ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℂ, ‖w - z‖ < ρ →
      t ∈ lifeSet U w ∧ ∀ r ∈ Icc (0 : ℝ) t, ‖windingRatio U hU z w r - 1‖ ≤ K * ‖w - z‖ := by
  obtain ⟨ρ, hρ, K, hK0, hK⟩ := exists_dirPath_lipschitz_initial hU ht
  refine ⟨ρ, hρ, 2 * K, by positivity, fun w hw => ⟨(hK w hw).1, fun r hr => ?_⟩⟩
  refine (norm_windingRatio_sub_one_le hU z w r).trans ?_
  have h1 := (hK w hw).2 r hr
  have h2 := (hK w hw).2 0 ⟨le_rfl, ht.1⟩
  linarith

/-- **Winding comparison.** If `t ∈ [0, T_z) ∩ [0, T_w)` and `‖Q_w(r) - 1‖ < 1` on `[0, t]`, then
for `r ∈ [0, t]`:
`(θ_r(w) - θ_0(w)) - (θ_r(z) - θ_0(z)) = arg Q_w(r)`. -/
theorem argPath_winding_eq_arg (hU : Continuous U) {z w : ℂ} {t : ℝ} (hz : t ∈ lifeSet U z)
    (hw : t ∈ lifeSet U w) (hQ : ∀ r ∈ Icc (0 : ℝ) t, ‖windingRatio U hU z w r - 1‖ < 1) :
    ∀ r ∈ Icc (0 : ℝ) t,
      (argPath U hU w r - argPath U hU w 0) - (argPath U hU z r - argPath U hU z 0) =
        Complex.arg (windingRatio U hU z w r) := by
  have hsubz : Icc (0 : ℝ) t ⊆ lifeSet U z := Icc_subset_lifeSet hz
  have hsubw : Icc (0 : ℝ) t ⊆ lifeSet U w := Icc_subset_lifeSet hw
  -- continuity of `Q_w` on `[0, t]`
  have hdirw : ContinuousOn (fun r => (dirPath U hU w r : ℂ)) (Icc (0 : ℝ) t) :=
    (continuous_subtype_val.comp_continuousOn (continuousOn_dirPath hU w)).mono hsubw
  have hdirz : ContinuousOn (fun r => (dirPath U hU z r : ℂ)) (Icc (0 : ℝ) t) :=
    (continuous_subtype_val.comp_continuousOn (continuousOn_dirPath hU z)).mono hsubz
  have hne : ∀ (y : ℂ) (r : ℝ), (dirPath U hU y r : ℂ) ≠ 0 := coe_dirPath_ne_zero hU
  have hQc : ContinuousOn (fun r => windingRatio U hU z w r) (Icc (0 : ℝ) t) := by
    unfold windingRatio
    refine (hdirw.mul continuousOn_const).div (continuousOn_const.mul hdirz) fun r _ => ?_
    exact mul_ne_zero (hne w 0) (hne z r)
  have hslit : ∀ r ∈ Icc (0 : ℝ) t, windingRatio U hU z w r ∈ slitPlane := fun r hr => by
    refine Or.inl ?_
    have h1 := hQ r hr
    have h2 : |(windingRatio U hU z w r - 1).re| ≤ ‖windingRatio U hU z w r - 1‖ :=
      Complex.abs_re_le_norm _
    have h3 := (abs_lt.1 (lt_of_le_of_lt h2 h1)).1
    simp only [sub_re, one_re] at h3
    linarith
  have hΓ₂ : ContinuousOn (fun r => Complex.arg (windingRatio U hU z w r)) (Icc (0 : ℝ) t) :=
    fun r hr => (Complex.continuousAt_arg (hslit r hr)).comp_continuousWithinAt (hQc r hr)
  have hΓ₁ : ContinuousOn (fun r => (argPath U hU w r - argPath U hU w 0) -
      (argPath U hU z r - argPath U hU z 0)) (Icc (0 : ℝ) t) :=
    (((continuousOn_argPath hU w).mono hsubw).sub continuousOn_const).sub
      (((continuousOn_argPath hU z).mono hsubz).sub continuousOn_const)
  -- exponentials agree
  have hexp : ∀ r ∈ Icc (0 : ℝ) t,
      Circle.exp ((argPath U hU w r - argPath U hU w 0) - (argPath U hU z r - argPath U hU z 0)) =
        Circle.exp (Complex.arg (windingRatio U hU z w r)) := by
    intro r hr
    apply Circle.ext
    rw [Circle.coe_exp, Circle.coe_exp]
    have hA : ∀ (y : ℂ) (r : ℝ), r ∈ lifeSet U y →
        Complex.exp ((argPath U hU y r : ℂ) * I) = (dirPath U hU y r : ℂ) := fun y r hr' => by
      have := congrArg (fun q : Circle => (q : ℂ)) (circleExp_argPath hU hr')
      simpa [Circle.coe_exp] using this
    have hw0 : (0 : ℝ) ∈ lifeSet U w := hsubw ⟨le_rfl, hz.1⟩
    have hz0 : (0 : ℝ) ∈ lifeSet U z := hsubz ⟨le_rfl, hz.1⟩
    have hsplit : ((((argPath U hU w r - argPath U hU w 0) -
        (argPath U hU z r - argPath U hU z 0) : ℝ)) : ℂ) * I =
        (((argPath U hU w r : ℝ) : ℂ) * I - ((argPath U hU w 0 : ℝ) : ℂ) * I) -
          (((argPath U hU z r : ℝ) : ℂ) * I - ((argPath U hU z 0 : ℝ) : ℂ) * I) := by
      push_cast; ring
    rw [hsplit, Complex.exp_sub, Complex.exp_sub, Complex.exp_sub, hA w r (hsubw hr),
      hA w 0 hw0, hA z r (hsubz hr), hA z 0 hz0]
    have hnorm := Complex.norm_mul_exp_arg_mul_I (windingRatio U hU z w r)
    rw [norm_windingRatio] at hnorm
    simp only [Complex.ofReal_one, one_mul] at hnorm
    rw [hnorm]
    unfold windingRatio
    have h1 := hne w 0
    have h2 := hne z r
    have h3 := hne z 0
    have h4 := hne w r
    field_simp
  have h00 : (argPath U hU w 0 - argPath U hU w 0) - (argPath U hU z 0 - argPath U hU z 0) =
      Complex.arg (windingRatio U hU z w 0) := by
    rw [windingRatio_zero]; simp
  intro r hr
  exact lift_unique_of_isPreconnected isPreconnected_Icc hΓ₁ hΓ₂ hexp
    (left_mem_Icc.2 hz.1) h00 hr

/-! ### Continuity of `θ̂_s(w) - θ̂_0(w)` and of `e^{iθ̂_s(w)}` -/

/-- **`w ↦ θ̂_s(w) - θ̂_0(w)` is continuous** at every `z` with `s ∈ sigmaDom U hU z`. (Here
`θ̂_s(w) = θ_{σ_w(s)}(w)`; `θ̂_0(w) = θ_0(w)` since `σ_w(0) = 0`.) -/
theorem continuousAt_argPath_sub_initial (hU : Continuous U) {z : ℂ} {s : ℝ}
    (hs : s ∈ sigmaDom U hU z) :
    ContinuousAt (fun w => argPath U hU w (sigmaTime U hU w s) - argPath U hU w 0) z := by
  have hσ : sigmaTime U hU z s ∈ lifeSet U z := sigmaTime_mem_lifeSet hU hs
  obtain ⟨t₂, ht₂, hlt, -⟩ := exists_mem_lifeSet_between hσ (lt_add_one (sigmaTime U hU z s))
  obtain ⟨ρ, hρ, K, hK0, hK⟩ := exists_norm_windingRatio_sub_one_le hU ht₂
  have hev := eventually_mem_sigmaDom_sigmaTime_lt hU hs ht₂ hlt
  -- `ψ_z(σ_w(s)) → ψ_z(σ_z(s))`
  have h1 : Tendsto (fun w => argPath U hU z (sigmaTime U hU w s) - argPath U hU z 0) (𝓝 z)
      (𝓝 (argPath U hU z (sigmaTime U hU z s) - argPath U hU z 0)) :=
    (((continuousOn_argPath hU z) _ hσ).tendsto.comp
      (tendsto_sigmaTime_nhdsWithin_lifeSet hU hs)).sub_const _
  -- `Q_w(σ_w(s)) → 1`
  have hlim : Tendsto (fun w : ℂ => K * ‖w - z‖) (𝓝 z) (𝓝 0) := by
    have : Tendsto (fun w : ℂ => K * ‖w - z‖) (𝓝 z) (𝓝 (K * ‖z - z‖)) :=
      tendsto_const_nhds.mul ((continuous_id.sub continuous_const).norm.tendsto z)
    simpa using this
  have hQ : Tendsto (fun w => windingRatio U hU z w (sigmaTime U hU w s)) (𝓝 z) (𝓝 1) := by
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    refine squeeze_zero' (g := fun w : ℂ => K * ‖w - z‖)
      (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
    filter_upwards [Metric.ball_mem_nhds z hρ, hev] with w hw hw'
    exact (hK w (by simpa [dist_eq_norm] using hw)).2 _ ⟨sigmaTime_nonneg hU hw'.1, hw'.2.le⟩
  have h2 : Tendsto (fun w => Complex.arg (windingRatio U hU z w (sigmaTime U hU w s))) (𝓝 z)
      (𝓝 0) := by
    have h := (Complex.continuousAt_arg (by simp : (1 : ℂ) ∈ slitPlane)).tendsto.comp hQ
    rw [Complex.arg_one] at h
    exact h
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [Metric.ball_mem_nhds z hρ, hev,
    Metric.ball_mem_nhds z (show (0 : ℝ) < 1 / (K + 1) by positivity)] with w hw hw' hw''
  have hwz : ‖w - z‖ < ρ := by simpa [dist_eq_norm] using hw
  have hwz' : ‖w - z‖ < 1 / (K + 1) := by simpa [dist_eq_norm] using hw''
  obtain ⟨hlife, hbd⟩ := hK w hwz
  have hKlt : K * ‖w - z‖ < 1 := by
    calc K * ‖w - z‖ ≤ K * (1 / (K + 1)) := mul_le_mul_of_nonneg_left hwz'.le hK0
      _ < 1 := by
        rw [mul_one_div, div_lt_one (by positivity)]
        linarith
  have hr : sigmaTime U hU w s ∈ Icc (0 : ℝ) t₂ :=
    ⟨sigmaTime_nonneg hU hw'.1, hw'.2.le⟩
  have := argPath_winding_eq_arg hU ht₂ hlife (fun r hr' => lt_of_le_of_lt (hbd r hr') hKlt)
    _ hr
  linarith

end ComplexSLE.Internal.Polar

end
