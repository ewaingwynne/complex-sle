/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.Sigma
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Proposition 3.1(b): the ODE comparison argument (M7/C1)

Source: paper.tex:L1405-1418 (`eqn-neg-I1-bd`), the deterministic half of the proof of
Proposition 3.1(b): a linear rate of decay of `log|f̂_s(z)|` in σ-time forces `T_z < ∞`.

With `F(t) = A(t) = ∫₀ᵗ |f_u(z)|⁻² du` (the clock), `F'(t) = |f_t(z)|⁻²`
(`hasDerivWithinAt_clock`). If `log|f_t(z)| < -c F(t)` for `t ∈ [t₀, T_z)`, then
`F'(t) e^{-2cF(t)} > 1`, so `G(t) = e^{-2cF(t)} + 2c t` is decreasing on `[t₀, T_z)`, whence
`2c (t - t₀) ≤ e^{-2cF(t₀)} - e^{-2cF(t)} < e^{-2cF(t₀)}` and
`T_z ≤ t₀ + e^{-2cF(t₀)} / (2c) < ∞` (`absorbingTime_le_of_log_norm_lt`; the paper takes
`c = α/2`, getting `T_z ≤ t_* + α⁻¹ e^{-αF(t_*)}`).

In σ-time (`clock_sigmaTime`, `sigmaTime_clock`): if `sigmaDom = [0, ∞)` and
`log|f̂_s(z)| / s → -α < 0` as `s → ∞`, then for `s` large `log|f̂_s(z)| < -(α/2) s`, and since
`s = A(σ_z(s))` this is `log|f_t(z)| < -(α/2) A(t)` for `t` near `T_z`
(`absorbingTime_ne_top_of_tendsto_log_norm_div`).

Everything here is deterministic (a fixed continuous driver); no external input is used.
-/

public section

open scoped NNReal ENNReal Topology
open Set Filter

namespace ComplexSLE.Internal.Polar

variable {U : ℝ≥0 → ℂ}

/-! ### The comparison in original time -/

/-- If `log|f_t(z)| < -c A(t)` on `[t₀, T_z)` (`c > 0`), then `F'(t) e^{-2cF(t)} > 1` there
(paper.tex:L1411-1412). -/
theorem one_lt_clockRate_mul_exp (hU : Continuous U) {z : ℂ} {c t : ℝ} (ht : t ∈ lifeSet U z)
    (h : Real.log ‖fPath U hU z t‖ < -c * clock U hU z t) :
    1 < clockRate U hU z t * Real.exp (-2 * c * clock U hU z t) := by
  have hpos := norm_fPath_pos hU ht
  have h1 : ‖fPath U hU z t‖ < Real.exp (-c * clock U hU z t) :=
    (Real.log_lt_iff_lt_exp hpos).1 h
  have h2 : ‖fPath U hU z t‖ ^ 2 < Real.exp (-2 * c * clock U hU z t) := by
    have : Real.exp (-2 * c * clock U hU z t) = Real.exp (-c * clock U hU z t) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [this]
    exact pow_lt_pow_left₀ h1 hpos.le two_ne_zero
  unfold clockRate
  rw [inv_mul_eq_div, one_lt_div (by positivity)]
  exact h2

/-- **ODE comparison** (paper.tex:L1413-1417): if `c > 0`, `t₀ ∈ [0, T_z)` and
`log|f_t(z)| < -c A(t)` for all `t ∈ [t₀, T_z)`, then
`t - t₀ < e^{-2cA(t₀)} / (2c)` for all `t ∈ [t₀, T_z)`. -/
theorem sub_lt_of_log_norm_lt (hU : Continuous U) {z : ℂ} {c : ℝ} (hc : 0 < c) {t₀ : ℝ}
    (ht₀ : t₀ ∈ lifeSet U z)
    (h : ∀ t ∈ lifeSet U z, t₀ ≤ t → Real.log ‖fPath U hU z t‖ < -c * clock U hU z t)
    {t : ℝ} (ht : t ∈ lifeSet U z) (hle : t₀ ≤ t) :
    t - t₀ < Real.exp (-2 * c * clock U hU z t₀) / (2 * c) := by
  have hsub : Icc t₀ t ⊆ lifeSet U z := fun s hs => mem_lifeSet_of_le ht (ht₀.1.trans hs.1) hs.2
  -- `G(s) = e^{-2cF(s)} + 2c s` is antitone on `[t₀, t]`
  set G : ℝ → ℝ := fun s => Real.exp (-2 * c * clock U hU z s) + 2 * c * s with hG
  have hGcont : ContinuousOn G (Icc t₀ t) := by
    refine ContinuousOn.add ?_ (by fun_prop)
    exact Real.continuous_exp.comp_continuousOn
      (continuousOn_const.mul ((continuousOn_clock hU z).mono hsub))
  have hanti : AntitoneOn G (Icc t₀ t) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc t₀ t) hGcont
      (f' := fun s => Real.exp (-2 * c * clock U hU z s) * (-2 * c * clockRate U hU z s) + 2 * c)
      ?_ ?_
    · intro s hs
      rw [interior_Icc] at hs
      have hsl : s ∈ lifeSet U z := hsub ⟨hs.1.le, hs.2.le⟩
      have hs0 : 0 < s := ht₀.1.trans_lt hs.1
      have hclock : HasDerivAt (clock U hU z) (clockRate U hU z s) s :=
        (hasDerivWithinAt_clock hU hsl).hasDerivAt (Ici_mem_nhds hs0)
      have := (((hclock.const_mul (-2 * c)).exp).add ((hasDerivAt_id' s).const_mul (2 * c)))
      exact (this.congr_deriv (by ring)).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hsl : s ∈ lifeSet U z := hsub ⟨hs.1.le, hs.2.le⟩
      have h1 := one_lt_clockRate_mul_exp hU hsl (h s hsl hs.1.le)
      change Real.exp (-2 * c * clock U hU z s) * (-2 * c * clockRate U hU z s) + 2 * c ≤ 0
      nlinarith [mul_comm (clockRate U hU z s) (Real.exp (-2 * c * clock U hU z s))]
  have hGle : G t ≤ G t₀ := hanti ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩ hle
  simp only [hG] at hGle
  have hexp : 0 < Real.exp (-2 * c * clock U hU z t) := Real.exp_pos _
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

/-- **`T_z` is bounded** (paper.tex:L1417-1418): under the hypotheses of `sub_lt_of_log_norm_lt`,
`T_z ≤ t₀ + e^{-2cA(t₀)} / (2c)`; in particular `T_z < ∞`. -/
theorem absorbingTime_le_of_log_norm_lt (hU : Continuous U) {z : ℂ} {c : ℝ} (hc : 0 < c)
    {t₀ : ℝ} (ht₀ : t₀ ∈ lifeSet U z)
    (h : ∀ t ∈ lifeSet U z, t₀ ≤ t → Real.log ‖fPath U hU z t‖ < -c * clock U hU z t) :
    absorbingTime U z ≤
      ENNReal.ofReal (t₀ + Real.exp (-2 * c * clock U hU z t₀) / (2 * c)) := by
  by_contra hlt
  push Not at hlt
  set t := t₀ + Real.exp (-2 * c * clock U hU z t₀) / (2 * c) with ht
  have hE : 0 ≤ Real.exp (-2 * c * clock U hU z t₀) / (2 * c) := by positivity
  have ht0 : 0 ≤ t := by
    have := ht₀.1
    linarith
  have htl : t ∈ lifeSet U z := ⟨ht0, hlt⟩
  have := sub_lt_of_log_norm_lt hU hc ht₀ h htl (by rw [ht]; linarith)
  rw [ht] at this
  linarith

theorem absorbingTime_ne_top_of_log_norm_lt (hU : Continuous U) {z : ℂ} {c : ℝ} (hc : 0 < c)
    {t₀ : ℝ} (ht₀ : t₀ ∈ lifeSet U z)
    (h : ∀ t ∈ lifeSet U z, t₀ ≤ t → Real.log ‖fPath U hU z t‖ < -c * clock U hU z t) :
    absorbingTime U z ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (absorbingTime_le_of_log_norm_lt hU hc ht₀ h)

/-! ### The comparison in σ-time -/

/-- A linear bound for `log|f̂_s(z)|` in σ-time, eventually, gives the bound in original time:
if `sigmaDom = [0, ∞)` and `log|f_{σ_z(s)}(z)| < -c s` for `s ≥ s₀`, then
`log|f_t(z)| < -c A(t)` for all `t ∈ [σ_z(s₀), T_z)` (as `A(σ_z(s)) = s`). -/
theorem log_norm_lt_clock_of_sigma (hU : Continuous U) {z : ℂ}
    (hdom : sigmaDom U hU z = Ici 0) {c s₀ : ℝ} (hs₀ : 0 ≤ s₀)
    (h : ∀ s, s₀ ≤ s → Real.log ‖fPath U hU z (sigmaTime U hU z s)‖ < -c * s)
    {t : ℝ} (ht : t ∈ lifeSet U z) (hle : sigmaTime U hU z s₀ ≤ t) :
    Real.log ‖fPath U hU z t‖ < -c * clock U hU z t := by
  have hs₀dom : s₀ ∈ sigmaDom U hU z := by rw [hdom]; exact hs₀
  have hcdom : clock U hU z t ∈ sigmaDom U hU z := clock_mem_sigmaDom hU ht
  have hle' : s₀ ≤ clock U hU z t := by
    have := (clock_monotoneOn hU z) (sigmaTime_mem_lifeSet hU hs₀dom) ht hle
    rwa [clock_sigmaTime hU hs₀dom] at this
  have := h _ hle'
  rwa [sigmaTime_clock hU ht] at this

/-- **Proposition 3.1(b), deterministic part, eventual linear bound**: if `sigmaDom = [0, ∞)` and
there are `c > 0`, `s₀ ≥ 0` with `log|f̂_s(z)| < -c s` for all `s ≥ s₀`, then `T_z < ∞`; more
precisely `T_z ≤ σ_z(s₀) + e^{-2c s₀} / (2c)`. -/
theorem absorbingTime_le_of_log_norm_sigma_lt (hU : Continuous U) {z : ℂ}
    (hdom : sigmaDom U hU z = Ici 0) {c s₀ : ℝ} (hc : 0 < c) (hs₀ : 0 ≤ s₀)
    (h : ∀ s, s₀ ≤ s → Real.log ‖fPath U hU z (sigmaTime U hU z s)‖ < -c * s) :
    absorbingTime U z ≤
      ENNReal.ofReal (sigmaTime U hU z s₀ + Real.exp (-2 * c * s₀) / (2 * c)) := by
  have hs₀dom : s₀ ∈ sigmaDom U hU z := by rw [hdom]; exact hs₀
  have ht₀ := sigmaTime_mem_lifeSet hU hs₀dom
  have := absorbingTime_le_of_log_norm_lt hU hc ht₀
    fun t ht hle => log_norm_lt_clock_of_sigma hU hdom hs₀ h ht hle
  rwa [clock_sigmaTime hU hs₀dom] at this

theorem absorbingTime_ne_top_of_log_norm_sigma_lt (hU : Continuous U) {z : ℂ}
    (hdom : sigmaDom U hU z = Ici 0) {c s₀ : ℝ} (hc : 0 < c) (hs₀ : 0 ≤ s₀)
    (h : ∀ s, s₀ ≤ s → Real.log ‖fPath U hU z (sigmaTime U hU z s)‖ < -c * s) :
    absorbingTime U z ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (absorbingTime_le_of_log_norm_sigma_lt hU hdom hc hs₀ h)

/-- **Proposition 3.1(b), deterministic part** (paper.tex:L1405-1418): for a continuous driver `U`
and `z` with `sigmaDom = [0, ∞)` (`clockSup = ∞`), if `log|f̂_s(z)| / s → -α < 0` as `s → ∞`, then
`T_z < ∞`. -/
theorem absorbingTime_ne_top_of_tendsto_log_norm_div (hU : Continuous U) {z : ℂ}
    (hdom : sigmaDom U hU z = Ici 0) {α : ℝ} (hα : 0 < α)
    (h : Tendsto (fun s : ℝ => Real.log ‖fPath U hU z (sigmaTime U hU z s)‖ / s) atTop
      (𝓝 (-α))) :
    absorbingTime U z ≠ ⊤ := by
  have hev : ∀ᶠ s : ℝ in atTop, Real.log ‖fPath U hU z (sigmaTime U hU z s)‖ / s < -(α / 2) :=
    h.eventually (gt_mem_nhds (by linarith))
  obtain ⟨S, hS⟩ := eventually_atTop.1 (hev.and (eventually_gt_atTop 0))
  refine absorbingTime_ne_top_of_log_norm_sigma_lt hU hdom (c := α / 2) (s₀ := max S 1)
    (by positivity) (zero_le_one.trans (le_max_right _ _)) fun s hs => ?_
  have hs' := hS s ((le_max_left _ _).trans hs)
  have hspos : 0 < s := hs'.2
  have := hs'.1
  rw [div_lt_iff₀ hspos] at this
  linarith

/-- The `ℝ≥0`-indexed form of `absorbingTime_ne_top_of_tendsto_log_norm_div` (the process
`s ↦ log|f̂_s(z)|` indexed by `s : ℝ≥0`). -/
theorem absorbingTime_ne_top_of_tendsto_log_norm_div_nnreal (hU : Continuous U) {z : ℂ}
    (hdom : sigmaDom U hU z = Ici 0) {α : ℝ} (hα : 0 < α)
    (h : Tendsto (fun s : ℝ≥0 => Real.log ‖fPath U hU z (sigmaTime U hU z (s : ℝ))‖ / (s : ℝ))
      atTop (𝓝 (-α))) :
    absorbingTime U z ≠ ⊤ := by
  refine absorbingTime_ne_top_of_tendsto_log_norm_div hU hdom hα ?_
  refine (h.comp tendsto_real_toNNReal_atTop).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  simp [Real.coe_toNNReal _ hs]

end ComplexSLE.Internal.Polar

end
