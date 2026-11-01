/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Ergodic.PointwiseErgodic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Birkhoff's pointwise ergodic theorem

For a measure preserving map `T` of a finite measure space `(α, μ)` and an integrable measurable
real function `f`, the Birkhoff averages `(∑ k < n, f (T^[k] x)) / n` converge almost surely to an
integrable limit `L` with `∫ L = ∫ f` (`birkhoff_pointwise`).

The almost sure convergence is `ae_exists_tendsto`. Integrability of the limit follows from
Fatou's lemma (`lintegral_enorm_le_of_tendsto`), and `∫ L = ∫ f` is first shown for bounded `f` by
dominated convergence (`integral_limit_eq_of_bounded`), then for general `f` by truncation
`f = f_K + (f - f_K)` (the limit of `f - f_K` has integral of absolute value at most
`∫ |f - f_K|`, which tends to `0`).
-/

public section

open MeasureTheory Filter Set Function Topology

namespace ComplexSLE.Infrastructure.Ergodic

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {f : α → ℝ}

theorem integrable_birkhoffSum (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (n : ℕ) :
    Integrable (birkhoffSum T f n) μ :=
  integrable_finsetSum _ fun k _ => (hT.iterate k).integrable_comp_of_integrable hf

theorem integral_birkhoffSum (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (n : ℕ) :
    ∫ x, birkhoffSum T f n x ∂μ = n * ∫ x, f x ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp_rw [birkhoffSum_succ_apply]
    have hi : Integrable (fun x => f (T^[n] x)) μ :=
      (hT.iterate n).integrable_comp_of_integrable hf
    rw [integral_add (integrable_birkhoffSum hT hf n) hi, ih,
      integral_comp_eq (hT.iterate n) hf.aestronglyMeasurable]
    push_cast
    ring

theorem integral_average (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) {n : ℕ}
    (hn : 0 < n) : ∫ x, birkhoffSum T f n x / n ∂μ = ∫ x, f x ∂μ := by
  rw [integral_div, integral_birkhoffSum hT hf]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

theorem integral_abs_average_le (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) {n : ℕ}
    (hn : 0 < n) : ∫ x, |birkhoffSum T f n x / n| ∂μ ≤ ∫ x, |f x| ∂μ := by
  have hg : Integrable (fun x => |f x|) μ := hf.abs
  have h1 : ∀ x, |birkhoffSum T f n x / n| ≤ birkhoffSum T (fun x => |f x|) n x / n := by
    intro x
    rw [abs_div, abs_of_pos (show (0 : ℝ) < n from Nat.cast_pos.2 hn)]
    exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)
  calc ∫ x, |birkhoffSum T f n x / n| ∂μ
      ≤ ∫ x, birkhoffSum T (fun x => |f x|) n x / n ∂μ :=
        integral_mono ((integrable_birkhoffSum hT hf n).div_const _).abs
          ((integrable_birkhoffSum hT hg n).div_const _) h1
    _ = ∫ x, |f x| ∂μ := integral_average hT hg hn

/-- Fatou's lemma for the Birkhoff averages: an a.e. limit has `∫⁻ ‖L‖ ≤ ∫ |f|`. -/
theorem lintegral_enorm_le_of_tendsto [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hfm : Measurable f) (hf : Integrable f μ) {L : α → ℝ}
    (hL : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => birkhoffSum T f n x / n) atTop (𝓝 (L x))) :
    ∫⁻ x, ‖L x‖ₑ ∂μ ≤ ENNReal.ofReal (∫ x, |f x| ∂μ) := by
  have hmeas : ∀ n : ℕ, Measurable fun x => ‖birkhoffSum T f n x / n‖ₑ := fun n =>
    ((measurable_birkhoffSum hT.measurable hfm n).div_const (n : ℝ)).enorm
  calc ∫⁻ x, ‖L x‖ₑ ∂μ
      = ∫⁻ x, liminf (fun n : ℕ => ‖birkhoffSum T f n x / n‖ₑ) atTop ∂μ := by
        refine lintegral_congr_ae (hL.mono fun x hx => ?_)
        exact ((continuous_enorm.tendsto _).comp hx).liminf_eq.symm
    _ ≤ liminf (fun n : ℕ => ∫⁻ x, ‖birkhoffSum T f n x / n‖ₑ ∂μ) atTop :=
        lintegral_liminf_le hmeas
    _ ≤ ENNReal.ofReal (∫ x, |f x| ∂μ) := by
        refine liminf_le_of_le (by isBoundedDefault) fun b hb => ?_
        obtain ⟨n, hn, hn1⟩ := (hb.and (eventually_ge_atTop 1)).exists
        refine hn.trans ?_
        rw [← ofReal_integral_norm_eq_lintegral_enorm
          ((integrable_birkhoffSum hT hf n).div_const _)]
        exact ENNReal.ofReal_le_ofReal (integral_abs_average_le hT hf hn1)

/-- The a.e. limit of the Birkhoff averages of an integrable function is integrable. -/
theorem integrable_of_tendsto [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hfm : Measurable f) (hf : Integrable f μ) {L : α → ℝ} (hLm : Measurable L)
    (hL : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => birkhoffSum T f n x / n) atTop (𝓝 (L x))) :
    Integrable L μ :=
  ⟨hLm.aestronglyMeasurable,
    lt_of_le_of_lt (lintegral_enorm_le_of_tendsto hT hfm hf hL) ENNReal.ofReal_lt_top⟩

theorem integral_abs_le_of_tendsto [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hfm : Measurable f) (hf : Integrable f μ) {L : α → ℝ} (hLm : Measurable L)
    (hL : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => birkhoffSum T f n x / n) atTop (𝓝 (L x))) :
    ∫ x, |L x| ∂μ ≤ ∫ x, |f x| ∂μ := by
  have hLi := integrable_of_tendsto hT hfm hf hLm hL
  have h := lintegral_enorm_le_of_tendsto hT hfm hf hL
  have h2 : ∫⁻ x, ‖L x‖ₑ ∂μ = ENNReal.ofReal (∫ x, |L x| ∂μ) := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm hLi]
    simp only [Real.norm_eq_abs]
  rw [h2] at h
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun x => abs_nonneg _)).1 h

/-- For bounded `f`, the a.e. limit `L` of the Birkhoff averages has `∫ L = ∫ f`. -/
theorem integral_limit_eq_of_bounded [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hfm : Measurable f) (hf : Integrable f μ) {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ x, |f x| ≤ K)
    {L : α → ℝ}
    (hL : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => birkhoffSum T f n x / n) atTop (𝓝 (L x))) :
    ∫ x, L x ∂μ = ∫ x, f x ∂μ := by
  have hAm : ∀ n : ℕ, AEStronglyMeasurable (fun x => birkhoffSum T f n x / n) μ := fun n =>
    ((measurable_birkhoffSum hT.measurable hfm n).div_const _).aestronglyMeasurable
  have hbound : ∀ n : ℕ, ∀ᵐ x ∂μ, ‖birkhoffSum T f n x / n‖ ≤ K := by
    intro n
    refine Eventually.of_forall fun x => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa [birkhoffSum_zero_apply] using hK0
    · have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hn', div_le_iff₀ hn']
      refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun k _ => hK _).trans ?_)
      simp [mul_comm]
  have h1 := tendsto_integral_of_dominated_convergence (fun _ => K) hAm (integrable_const K)
    hbound hL
  have h2 : Tendsto (fun n : ℕ => ∫ x, birkhoffSum T f n x / n ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (integral_average hT hf hn).symm
  exact tendsto_nhds_unique h1 h2

/-- Truncation of `y` to the interval `[-K, K]`. -/
@[expose] def clip (K y : ℝ) : ℝ := max (-K) (min K y)

theorem abs_clip_le {K : ℝ} (hK : 0 ≤ K) (y : ℝ) : |clip K y| ≤ K := by
  rw [abs_le]
  unfold clip
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem clip_eq_self {K y : ℝ} (h : |y| ≤ K) : clip K y = y := by
  rw [abs_le] at h
  unfold clip
  rw [min_eq_right h.2, max_eq_right h.1]

theorem abs_sub_clip_le {K : ℝ} (hK : 0 ≤ K) (y : ℝ) : |y - clip K y| ≤ |y| := by
  unfold clip
  rcases le_total y K with h | h
  · rw [min_eq_right h]
    rcases le_total (-K) y with h' | h'
    · rw [max_eq_right h']; simp
    · rw [max_eq_left h', abs_of_nonpos (by linarith : y - -K ≤ 0),
        abs_of_nonpos (by linarith : y ≤ 0)]
      linarith
  · rw [min_eq_left h, max_eq_right (by linarith : -K ≤ K), abs_of_nonneg (by linarith : 0 ≤ y - K),
      abs_of_nonneg (by linarith : 0 ≤ y)]
    linarith

/-- **Birkhoff's pointwise ergodic theorem.** If `T` preserves the finite measure `μ` and `f` is
measurable and integrable, then the Birkhoff averages `(∑ k < n, f (T^[k] x)) / n` converge
almost everywhere to an integrable function `L` with `∫ L = ∫ f`. -/
theorem birkhoff_pointwise [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hfm : Measurable f) (hf : Integrable f μ) :
    ∃ L : α → ℝ, Integrable L μ ∧ ∫ x, L x ∂μ = ∫ x, f x ∂μ ∧
      ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, f (T^[k] x)) / n) atTop
        (𝓝 (L x)) := by
  obtain ⟨L, hLm, hL⟩ := exists_measurable_limit hT hfm hf
  have hLi := integrable_of_tendsto hT hfm hf hLm hL
  refine ⟨L, hLi, ?_, hL⟩
  set fK : ℕ → α → ℝ := fun K x => clip K (f x) with hfK
  set hK : ℕ → α → ℝ := fun K x => f x - clip K (f x) with hhK
  have fK_meas : ∀ K, Measurable (fK K) := fun K =>
    measurable_const.max (measurable_const.min hfm)
  have hK_meas : ∀ K, Measurable (hK K) := fun K => hfm.sub (fK_meas K)
  have fK_bdd : ∀ (K : ℕ) x, |fK K x| ≤ K := fun K x => abs_clip_le (Nat.cast_nonneg K) _
  have fK_int : ∀ K, Integrable (fK K) μ := fun K =>
    Integrable.of_bound (fK_meas K).aestronglyMeasurable (K : ℝ)
      (Eventually.of_forall fun x => by simpa using fK_bdd K x)
  have hK_int : ∀ K, Integrable (hK K) μ := fun K => hf.sub (fK_int K)
  have hsplit : ∀ K : ℕ, f = fK K + hK K := fun K => by funext x; simp [hfK, hhK]
  have key : ∀ K : ℕ, |∫ x, L x ∂μ - ∫ x, f x ∂μ| ≤ 2 * ∫ x, |hK K x| ∂μ := by
    intro K
    obtain ⟨L1, hL1m, hL1⟩ := exists_measurable_limit hT (fK_meas K) (fK_int K)
    obtain ⟨L2, hL2m, hL2⟩ := exists_measurable_limit hT (hK_meas K) (hK_int K)
    have hL1i := integrable_of_tendsto hT (fK_meas K) (fK_int K) hL1m hL1
    have hL2i := integrable_of_tendsto hT (hK_meas K) (hK_int K) hL2m hL2
    have hsum : ∀ (n : ℕ) x, birkhoffSum T f n x = birkhoffSum T (fK K) n x +
        birkhoffSum T (hK K) n x := by
      intro n x
      conv_lhs => rw [hsplit K]
      exact birkhoffSum_add_apply T _ _ n x
    have hLeq : L =ᵐ[μ] fun x => L1 x + L2 x := by
      filter_upwards [hL, hL1, hL2] with x h h1 h2
      refine tendsto_nhds_unique h ((h1.add h2).congr fun n => ?_)
      rw [hsum n x, add_div]
    have hI1 : ∫ x, L1 x ∂μ = ∫ x, fK K x ∂μ :=
      integral_limit_eq_of_bounded hT (fK_meas K) (fK_int K) (Nat.cast_nonneg K) (fK_bdd K) hL1
    have hI : ∫ x, L x ∂μ = ∫ x, L1 x ∂μ + ∫ x, L2 x ∂μ := by
      rw [integral_congr_ae hLeq, integral_add hL1i hL2i]
    have hIf : ∫ x, f x ∂μ = ∫ x, fK K x ∂μ + ∫ x, hK K x ∂μ := by
      rw [← integral_add (fK_int K) (hK_int K)]
      congr 1
      exact hsplit K
    have h2 := integral_abs_le_of_tendsto hT (hK_meas K) (hK_int K) hL2m hL2
    have h3 : |∫ x, L2 x ∂μ| ≤ ∫ x, |L2 x| ∂μ := abs_integral_le_integral_abs
    have h4 : |∫ x, hK K x ∂μ| ≤ ∫ x, |hK K x| ∂μ := abs_integral_le_integral_abs
    have h5 : ∫ x, L x ∂μ - ∫ x, f x ∂μ = ∫ x, L2 x ∂μ - ∫ x, hK K x ∂μ := by
      rw [hI, hIf, hI1]; ring
    rw [h5]
    refine (abs_sub _ _).trans ?_
    linarith
  have hlim : Tendsto (fun K : ℕ => ∫ x, |hK K x| ∂μ) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := μ) (fun x => |f x|)
      (F := fun (K : ℕ) x => |hK K x|) (f := fun _ => (0 : ℝ))
      (fun K => (continuous_abs.measurable.comp (hK_meas K)).aestronglyMeasurable) hf.abs
      (fun K => Eventually.of_forall fun x => by
        simpa using abs_sub_clip_le (Nat.cast_nonneg K) (f x))
      (Eventually.of_forall fun x => ?_)
    · simpa using this
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈|f x|⌉₊] with K hK'
      have : |f x| ≤ K := (Nat.le_ceil _).trans (by exact_mod_cast hK')
      simp [hhK, clip_eq_self this]
  have hlim2 : Tendsto (fun K : ℕ => 2 * ∫ x, |hK K x| ∂μ) atTop (𝓝 (2 * 0)) :=
    hlim.const_mul 2
  have := ge_of_tendsto' hlim2 key
  have h0 : |∫ x, L x ∂μ - ∫ x, f x ∂μ| = 0 := le_antisymm (by simpa using this) (abs_nonneg _)
  exact sub_eq_zero.1 (abs_eq_zero.1 h0)

end ComplexSLE.Infrastructure.Ergodic

end
