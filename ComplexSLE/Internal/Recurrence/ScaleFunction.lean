/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Recurrence.ExitBound
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Scale and Lyapunov functions for a one-dimensional diffusion, and the uniform hitting bound

For the generator `L = α ∂ + ½ β² ∂²` on an interval `[l, u]` we build two global `C²` functions:

* the **Lyapunov function** `lyapunovFun u k c₀ (θ) = -exp(k(u-θ)) / (c₀ k)`, with `Lg ≤ -1` on
  `[l, u]` as soon as the drift condition `α - k β²/2 ≤ -c₀` holds there;
* the **scale-type function** `scaleFun l ψ (θ) = ∫_l^θ exp(-∫_l^s ψ) ds` for a continuous `ψ`,
  with `LF = e^{-Φ}(α - ½β²ψ) ≤ 0` on `[l, u]` as soon as `α ≤ ½β²ψ` there; `F(l) = 0` and `F` is
  increasing. When `β ≠ 0` and `ψ = 2α/β²` this is the classical scale function
  `S' = exp(-∫ µ/D)` of paper.tex:L1212; the cutoff `ψ = 2α⁺/β²` is what makes it `C²` across the
  degenerate points of the critical case `c² = ab` (ERRATA.md R27).

Both exist under the single hypothesis
`(H) : ∀ v ∈ [l, u], β v = 0 → α v < 0` ("degenerate points have negative drift"):
`exists_drift_condition`, `exists_psi`. The main result `exists_uniform_hit` then gives, for
`l ≤ y₀ < u`, constants `T, δ > 0` depending only on `(α, β, l, y₀, u)` such that every solution
with `X₀ ∈ [l, y₀]` a.s. hits `l` by time `T` with probability `≥ δ`
(`step:rec-hit-fixed-y`, `step:rec-monotone-in-y`, `step:rec-angle-hit-unif`, and the hitting
lemma of R27). No Markov property is used. Uses `ito_formula` (proved in-project).
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
open ComplexSLE.Internal (generator continuous_generator)

namespace ComplexSLE.Recurrence

variable {α β : ℝ → ℝ} {l u : ℝ}

/-! ### The Lyapunov function -/

/-- `g(θ) = -exp(k(u-θ)) / (c₀ k)`. -/
noncomputable def lyapunovFun (u k c₀ : ℝ) (θ : ℝ) : ℝ := -Real.exp (k * (u - θ)) / (c₀ * k)

theorem contDiff_lyapunovFun (u k c₀ : ℝ) : ContDiff ℝ 2 (lyapunovFun u k c₀) := by
  unfold lyapunovFun; fun_prop

theorem hasDerivAt_lyapunovFun (u k c₀ θ : ℝ) :
    HasDerivAt (lyapunovFun u k c₀) (-(Real.exp (k * (u - θ)) * (k * (0 - 1))) / (c₀ * k)) θ := by
  have h : HasDerivAt (fun θ => k * (u - θ)) (k * (0 - 1)) θ :=
    ((hasDerivAt_const θ u).sub (hasDerivAt_id θ)).const_mul k
  exact (h.exp.neg).div_const (c₀ * k)

theorem deriv_lyapunovFun (u c₀ : ℝ) {k : ℝ} (hk : k ≠ 0) :
    deriv (lyapunovFun u k c₀) = fun θ => Real.exp (k * (u - θ)) / c₀ := by
  funext θ
  rw [(hasDerivAt_lyapunovFun u k c₀ θ).deriv]
  field_simp
  ring

theorem deriv_deriv_lyapunovFun (u c₀ : ℝ) {k : ℝ} (hk : k ≠ 0) (θ : ℝ) :
    deriv (deriv (lyapunovFun u k c₀)) θ = -k * Real.exp (k * (u - θ)) / c₀ := by
  rw [deriv_lyapunovFun u c₀ hk]
  have h : HasDerivAt (fun θ => k * (u - θ)) (k * (0 - 1)) θ :=
    ((hasDerivAt_const θ u).sub (hasDerivAt_id θ)).const_mul k
  rw [(h.exp.div_const c₀).deriv]
  ring

/-- `Lg = (e^{k(u-θ)}/c₀)(α - k β²/2)`. -/
theorem generator_lyapunovFun (u c₀ : ℝ) {k : ℝ} (hk : k ≠ 0) (v : ℝ) :
    generator α β (lyapunovFun u k c₀) v =
      Real.exp (k * (u - v)) / c₀ * (α v - k * (β v ^ 2 / 2)) := by
  unfold generator
  rw [deriv_deriv_lyapunovFun u c₀ hk, deriv_lyapunovFun u c₀ hk]
  ring

/-- Under the drift condition `α - k β²/2 ≤ -c₀` on `[l, u]`, `Lg ≤ -1` there. -/
theorem generator_lyapunovFun_le {k c₀ : ℝ} (hk : 0 < k) (hc₀ : 0 < c₀)
    (hdrift : ∀ v ∈ Icc l u, α v - k * (β v ^ 2 / 2) ≤ -c₀) {v : ℝ} (hv : v ∈ Icc l u) :
    generator α β (lyapunovFun u k c₀) v ≤ -1 := by
  rw [generator_lyapunovFun u c₀ hk.ne']
  have h1 := hdrift v hv
  have hexp : 1 ≤ Real.exp (k * (u - v)) :=
    Real.one_le_exp (mul_nonneg hk.le (sub_nonneg.2 hv.2))
  have hpos : 0 < Real.exp (k * (u - v)) / c₀ := by positivity
  calc Real.exp (k * (u - v)) / c₀ * (α v - k * (β v ^ 2 / 2))
      ≤ Real.exp (k * (u - v)) / c₀ * (-c₀) := mul_le_mul_of_nonneg_left h1 hpos.le
    _ = -Real.exp (k * (u - v)) := by field_simp
    _ ≤ -1 := by linarith

/-- `|g| ≤ exp(k(u-l)) / (c₀ k)` on `[l, u]`. -/
theorem abs_lyapunovFun_le {k c₀ : ℝ} (hk : 0 < k) (hc₀ : 0 < c₀) {v : ℝ} (hv : v ∈ Icc l u) :
    |lyapunovFun u k c₀ v| ≤ Real.exp (k * (u - l)) / (c₀ * k) := by
  unfold lyapunovFun
  rw [abs_div, abs_neg, abs_of_pos (Real.exp_pos _), abs_of_pos (by positivity)]
  gcongr
  linarith [hv.1]

/-- **The drift condition from (H).** If every zero of `β` in `[l, u]` has `α < 0`, there are
`k, c₀ > 0` with `α - k β²/2 ≤ -c₀` on `[l, u]`. -/
theorem exists_drift_condition (hα : Continuous α) (hβ : Continuous β) (hlu : l ≤ u)
    (hH : ∀ v ∈ Icc l u, β v = 0 → α v < 0) :
    ∃ k c₀ : ℝ, 0 < k ∧ 0 < c₀ ∧ ∀ v ∈ Icc l u, α v - k * (β v ^ 2 / 2) ≤ -c₀ := by
  -- `c₀`: half the negative of the maximum of `α` on the zero set of `β`
  have hZc : IsCompact (Icc l u ∩ {v | β v = 0}) :=
    isCompact_Icc.inter_right (isClosed_eq hβ continuous_const)
  obtain ⟨c₀, hc₀, hZα⟩ : ∃ c₀, 0 < c₀ ∧ ∀ v ∈ Icc l u ∩ {v | β v = 0}, α v ≤ -2 * c₀ := by
    rcases (Icc l u ∩ {v | β v = 0}).eq_empty_or_nonempty with hZe | hZne
    · exact ⟨1, one_pos, fun v hv => by rw [hZe] at hv; exact absurd hv (notMem_empty v)⟩
    · obtain ⟨v₀, hv₀, hmax⟩ := hZc.exists_isMaxOn hZne hα.continuousOn
      have hneg : α v₀ < 0 := hH v₀ hv₀.1 hv₀.2
      refine ⟨-α v₀ / 2, by linarith, fun v hv => ?_⟩
      have : α v ≤ α v₀ := hmax hv
      linarith
  -- `d₁`: the minimum of `β²` on the compact set `{v ∈ [l, u] | α v ≥ -c₀}`, where `β ≠ 0`
  have hKc : IsCompact (Icc l u ∩ {v | -c₀ ≤ α v}) :=
    isCompact_Icc.inter_right (isClosed_le continuous_const hα)
  obtain ⟨d₁, hd₁, hKβ⟩ : ∃ d₁, 0 < d₁ ∧ ∀ v ∈ Icc l u ∩ {v | -c₀ ≤ α v}, d₁ ≤ β v ^ 2 := by
    rcases (Icc l u ∩ {v | -c₀ ≤ α v}).eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, one_pos, fun v hv => by rw [hKe] at hv; exact absurd hv (notMem_empty v)⟩
    · obtain ⟨v₀, hv₀, hmin⟩ := hKc.exists_isMinOn hKne (hβ.pow 2).continuousOn
      have hβne : β v₀ ≠ 0 := fun h => by
        have h1 := hZα v₀ ⟨hv₀.1, h⟩
        have h2 : -c₀ ≤ α v₀ := hv₀.2
        linarith
      exact ⟨β v₀ ^ 2, by positivity, fun v hv => hmin hv⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hα.continuousOn (s := Icc l u))
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM l ⟨le_rfl, hlu⟩)
  have hkpos : 0 < 2 * (M + c₀) / d₁ + 1 := by
    have : 0 ≤ 2 * (M + c₀) / d₁ := div_nonneg (by linarith) hd₁.le
    linarith
  refine ⟨2 * (M + c₀) / d₁ + 1, c₀, hkpos, hc₀, fun v hv => ?_⟩
  by_cases hv' : -c₀ ≤ α v
  · have hβ2 := hKβ v ⟨hv, hv'⟩
    have hαM : α v ≤ M := le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hM v hv)
    have h1 : (2 * (M + c₀) / d₁ + 1) * (d₁ / 2) ≤ (2 * (M + c₀) / d₁ + 1) * (β v ^ 2 / 2) := by
      gcongr
    have h2 : (2 * (M + c₀) / d₁ + 1) * (d₁ / 2) = (M + c₀) + d₁ / 2 := by
      field_simp
    linarith
  · push Not at hv'
    have : 0 ≤ (2 * (M + c₀) / d₁ + 1) * (β v ^ 2 / 2) := by positivity
    linarith

/-! ### The scale-type function -/

variable {ψ : ℝ → ℝ}

/-- `Φ(s) = ∫_l^s ψ`. -/
noncomputable def scalePhi (l : ℝ) (ψ : ℝ → ℝ) (s : ℝ) : ℝ := ∫ r in l..s, ψ r

/-- `F(θ) = ∫_l^θ exp(-Φ(s)) ds`. -/
noncomputable def scaleFun (l : ℝ) (ψ : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ s in l..θ, Real.exp (-scalePhi l ψ s)

theorem continuous_scalePhi (hψ : Continuous ψ) : Continuous (scalePhi l ψ) :=
  intervalIntegral.continuous_primitive (fun a b => hψ.intervalIntegrable a b) l

theorem hasDerivAt_scalePhi (hψ : Continuous ψ) (s : ℝ) : HasDerivAt (scalePhi l ψ) (ψ s) s :=
  (hψ.integral_hasStrictDerivAt l s).hasDerivAt

theorem continuous_scaleDensity (hψ : Continuous ψ) :
    Continuous fun s => Real.exp (-scalePhi l ψ s) :=
  Real.continuous_exp.comp (continuous_scalePhi hψ).neg

theorem hasDerivAt_scaleFun (hψ : Continuous ψ) (θ : ℝ) :
    HasDerivAt (scaleFun l ψ) (Real.exp (-scalePhi l ψ θ)) θ :=
  ((continuous_scaleDensity hψ).integral_hasStrictDerivAt l θ).hasDerivAt

theorem deriv_scaleFun (hψ : Continuous ψ) :
    deriv (scaleFun l ψ) = fun θ => Real.exp (-scalePhi l ψ θ) :=
  funext fun θ => (hasDerivAt_scaleFun hψ θ).deriv

theorem hasDerivAt_deriv_scaleFun (hψ : Continuous ψ) (θ : ℝ) :
    HasDerivAt (deriv (scaleFun l ψ)) (-ψ θ * Real.exp (-scalePhi l ψ θ)) θ := by
  rw [deriv_scaleFun hψ]
  have := (hasDerivAt_scalePhi (l := l) hψ θ).neg.exp
  convert this using 1
  simp only [Pi.neg_apply]
  ring

theorem deriv_deriv_scaleFun (hψ : Continuous ψ) :
    deriv (deriv (scaleFun l ψ)) = fun θ => -ψ θ * Real.exp (-scalePhi l ψ θ) :=
  funext fun θ => (hasDerivAt_deriv_scaleFun hψ θ).deriv

theorem contDiff_scaleFun (hψ : Continuous ψ) : ContDiff ℝ 2 (scaleFun l ψ) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun θ => (hasDerivAt_scaleFun hψ θ).differentiableAt, fun h => by simp at h, ?_⟩
  rw [contDiff_one_iff_deriv]
  refine ⟨fun θ => (hasDerivAt_deriv_scaleFun hψ θ).differentiableAt, ?_⟩
  rw [deriv_deriv_scaleFun hψ]
  exact hψ.neg.mul (continuous_scaleDensity hψ)

/-- `LF = e^{-Φ}(α - ½β²ψ)`. -/
theorem generator_scaleFun (hψ : Continuous ψ) (v : ℝ) :
    generator α β (scaleFun l ψ) v = Real.exp (-scalePhi l ψ v) * (α v - β v ^ 2 / 2 * ψ v) := by
  unfold generator
  rw [deriv_deriv_scaleFun hψ, deriv_scaleFun hψ]
  ring

theorem generator_scaleFun_nonpos (hψ : Continuous ψ)
    (hψle : ∀ v ∈ Icc l u, α v ≤ β v ^ 2 / 2 * ψ v) {v : ℝ} (hv : v ∈ Icc l u) :
    generator α β (scaleFun l ψ) v ≤ 0 := by
  rw [generator_scaleFun hψ]
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.2 (hψle v hv))

theorem scaleFun_self (l : ℝ) (ψ : ℝ → ℝ) : scaleFun l ψ l = 0 := by
  simp [scaleFun]

theorem scaleFun_sub (hψ : Continuous ψ) (a b : ℝ) :
    scaleFun l ψ b - scaleFun l ψ a = ∫ s in a..b, Real.exp (-scalePhi l ψ s) :=
  intervalIntegral.integral_interval_sub_left ((continuous_scaleDensity hψ).intervalIntegrable _ _)
    ((continuous_scaleDensity hψ).intervalIntegrable _ _)

theorem scaleFun_mono (hψ : Continuous ψ) {a b : ℝ} (hab : a ≤ b) :
    scaleFun l ψ a ≤ scaleFun l ψ b := by
  rw [← sub_nonneg, scaleFun_sub hψ]
  exact intervalIntegral.integral_nonneg hab fun s _ => (Real.exp_pos _).le

theorem scaleFun_strictMono (hψ : Continuous ψ) {a b : ℝ} (hab : a < b) :
    scaleFun l ψ a < scaleFun l ψ b := by
  rw [← sub_pos, scaleFun_sub hψ]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuous_scaleDensity hψ).intervalIntegrable _ _) (fun s _ => Real.exp_pos _) hab

theorem scaleFun_nonneg (hψ : Continuous ψ) {v : ℝ} (hv : l ≤ v) : 0 ≤ scaleFun l ψ v := by
  rw [← scaleFun_self l ψ]
  exact scaleFun_mono hψ hv

/-- **A supermartingale function from (H).** If every zero of `β` in `[l, u]` has `α < 0`, there
is a continuous `ψ` with `α ≤ ½β²ψ` on `[l, u]` (`ψ = 2α⁺/β²`, clamped to `[l, u]`). -/
theorem exists_psi (hα : Continuous α) (hβ : Continuous β) (hlu : l ≤ u)
    (hH : ∀ v ∈ Icc l u, β v = 0 → α v < 0) :
    ∃ ψ : ℝ → ℝ, Continuous ψ ∧ ∀ v ∈ Icc l u, α v ≤ β v ^ 2 / 2 * ψ v := by
  set pr : ℝ → ℝ := fun v => max l (min v u) with hpr
  have hprc : Continuous pr := continuous_const.max (continuous_id.min continuous_const)
  have hprmem : ∀ v, pr v ∈ Icc l u := fun v =>
    ⟨le_max_left _ _, max_le hlu (min_le_right _ _)⟩
  have hprid : ∀ v ∈ Icc l u, pr v = v := fun v hv => by
    simp only [hpr, min_eq_left hv.2, max_eq_right hv.1]
  have hαc : Continuous fun v => α (pr v) := hα.comp hprc
  have hβc : Continuous fun v => β (pr v) := hβ.comp hprc
  refine ⟨fun v => 2 * max (α (pr v)) 0 / β (pr v) ^ 2, ?_, fun v hv => ?_⟩
  · rw [continuous_iff_continuousAt]
    intro v₀
    by_cases hb : β (pr v₀) = 0
    · have hneg : α (pr v₀) < 0 := hH _ (hprmem v₀) hb
      have hev : ∀ᶠ v in 𝓝 v₀, α (pr v) < 0 := hαc.continuousAt.eventually (gt_mem_nhds hneg)
      refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [hev] with v hv
      simp [max_eq_right hv.le]
    · exact ((continuous_const.mul (hαc.max continuous_const)).continuousAt).div
        ((hβc.pow 2).continuousAt) (pow_ne_zero 2 hb)
  · beta_reduce
    rw [hprid v hv]
    by_cases hb : β v = 0
    · have := hH v hv hb
      rw [hb]
      calc α v ≤ 0 := this.le
        _ = (0 : ℝ) ^ 2 / 2 * (2 * max (α v) 0 / 0 ^ 2) := by simp
    · have hb2 : β v ^ 2 ≠ 0 := pow_ne_zero 2 hb
      rw [show β v ^ 2 / 2 * (2 * max (α v) 0 / β v ^ 2) = max (α v) 0 by field_simp]
      exact le_max_left _ _

/-! ### The uniform hitting bound -/

/-- **Uniform positive probability of hitting the lower endpoint by a fixed time.** Let `α, β` be
continuous with `(H) : β v = 0 → α v < 0` on `[l, u]`, and `l ≤ y₀ < u`. There are `T, δ > 0`,
depending only on `(α, β, l, y₀, u)`, such that every martingale-problem solution `X` of
`dX = α(X) dt + β(X) dB` with everywhere-continuous paths and `X₀ ∈ [l, y₀]` a.s. satisfies
`P(∃ t ≤ T, X_t = l) ≥ δ`. (Claim (2.45) of Lemma 2.16 in abstract form, and the hitting lemma
of ERRATA.md R27; here with `δ = ½(1 - F(y₀)/F(u))` for the scale-type function `F`.) -/
theorem exists_uniform_hit (hα : Continuous α) (hβ : Continuous β)
    (hH : ∀ v ∈ Icc l u, β v = 0 → α v < 0) {y₀ : ℝ} (hly : l ≤ y₀) (hyu : y₀ < u) :
    ∃ (T : ℝ≥0) (δ : ℝ), 0 < T ∧ 0 < δ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ≥0 ‹_›) (X : ℝ≥0 → Ω → ℝ), IsDiffusionSolution ℱ α β X P →
        (∀ ω, Continuous fun t => X t ω) → (∀ᵐ ω ∂P, X 0 ω ∈ Icc l y₀) →
        δ ≤ P.real {ω | ∃ t : ℝ≥0, t ≤ T ∧ X t ω = l} := by
  have hlu : l < u := hly.trans_lt hyu
  obtain ⟨k, c₀, hk, hc₀, hdrift⟩ := exists_drift_condition hα hβ hlu.le hH
  obtain ⟨ψ, hψ, hψle⟩ := exists_psi hα hβ hlu.le hH
  have hFu : 0 < scaleFun l ψ u := by
    rw [← scaleFun_self l ψ]; exact scaleFun_strictMono hψ hlu
  have hFy : scaleFun l ψ y₀ < scaleFun l ψ u := scaleFun_strictMono hψ hyu
  have hq0 : 0 < 1 - scaleFun l ψ y₀ / scaleFun l ψ u := by
    rw [sub_pos, div_lt_one hFu]; exact hFy
  set q := 1 - scaleFun l ψ y₀ / scaleFun l ψ u with hq
  set C := Real.exp (k * (u - l)) / (c₀ * k) with hC
  have hCpos : 0 < C := by positivity
  have hTr : 0 ≤ 4 * C / q + 1 := by positivity
  refine ⟨Real.toNNReal (4 * C / q + 1), q / 2, ?_, by positivity, ?_⟩
  · rw [Real.toNNReal_pos]; positivity
  intro Ω _ P _ ℱ X hX hXc h0
  have h0' : ∀ᵐ ω ∂P, X 0 ω ∈ Icc l u := by
    filter_upwards [h0] with ω hω; exact ⟨hω.1, hω.2.trans hyu.le⟩
  have hT : (0 : ℝ≥0) < Real.toNNReal (4 * C / q + 1) := by
    rw [Real.toNNReal_pos]; positivity
  have hmain := measureReal_exit_eq_left_ge hX hXc hα hβ hlu (contDiff_lyapunovFun u k c₀)
    (fun v hv => generator_lyapunovFun_le hk hc₀ hdrift hv)
    (fun v hv => abs_lyapunovFun_le hk hc₀ hv) (contDiff_scaleFun hψ)
    (fun v hv => generator_scaleFun_nonpos hψ hψle hv) (fun v hv => scaleFun_nonneg hψ hv.1)
    hFu h0' hT
  -- `E F(X₀) ≤ F(y₀)`
  have hint : ∫ ω, scaleFun l ψ (X 0 ω) ∂P ≤ scaleFun l ψ y₀ := by
    obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((contDiff_scaleFun hψ).continuous.continuousOn (s := Icc l y₀))
    have hintF : Integrable (fun ω => scaleFun l ψ (X 0 ω)) P := by
      refine (integrable_const Cf).mono' ((contDiff_scaleFun hψ).continuous.measurable.comp
        (Internal.IsDiffusionSolution.measurable hX 0)).aestronglyMeasurable ?_
      filter_upwards [h0] with ω hω using hCf _ hω
    have := integral_mono_ae hintF (integrable_const (scaleFun l ψ y₀)) ?_
    · simpa using this
    · filter_upwards [h0] with ω hω
      exact scaleFun_mono hψ hω.2
  -- `2C/T ≤ q/2`
  have hTcoe : ((Real.toNNReal (4 * C / q + 1) : ℝ≥0) : ℝ) = 4 * C / q + 1 :=
    Real.coe_toNNReal _ hTr
  have htail : 2 * C / ((Real.toNNReal (4 * C / q + 1) : ℝ≥0) : ℝ) ≤ q / 2 := by
    rw [hTcoe, div_le_iff₀ (by positivity)]
    have : q / 2 * (4 * C / q + 1) = 2 * C + q / 2 := by
      field_simp
      ring
    linarith
  have hdiv : (∫ ω, scaleFun l ψ (X 0 ω) ∂P) / scaleFun l ψ u ≤
      scaleFun l ψ y₀ / scaleFun l ψ u := div_le_div_of_nonneg_right hint hFu.le
  -- the event `{R ≤ T, X_R = l}` is contained in `{∃ t ≤ T, X t = l}`
  have hsub : {ω | hittingAfter X (Ioo l u)ᶜ 0 ω ≤ Real.toNNReal (4 * C / q + 1) ∧
      stoppedValue X (hittingAfter X (Ioo l u)ᶜ 0) ω = l} ⊆
      {ω | ∃ t : ℝ≥0, t ≤ Real.toNNReal (4 * C / q + 1) ∧ X t ω = l} := by
    rintro ω ⟨h1, h2⟩
    exact ⟨(hittingAfter X (Ioo l u)ᶜ 0 ω).untopA, WithTop.untopA_le h1, h2⟩
  calc q / 2 = q - q / 2 := by ring
    _ ≤ 1 - 2 * C / ((Real.toNNReal (4 * C / q + 1) : ℝ≥0) : ℝ) -
        (∫ ω, scaleFun l ψ (X 0 ω) ∂P) / scaleFun l ψ u := by
        rw [hq]; linarith
    _ ≤ P.real {ω | hittingAfter X (Ioo l u)ᶜ 0 ω ≤ Real.toNNReal (4 * C / q + 1) ∧
        stoppedValue X (hittingAfter X (Ioo l u)ᶜ 0) ω = l} := hmain
    _ ≤ P.real {ω | ∃ t : ℝ≥0, t ≤ Real.toNNReal (4 * C / q + 1) ∧ X t ω = l} :=
        measureReal_mono hsub

end ComplexSLE.Recurrence

end
