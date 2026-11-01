/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Ergodic.MaximalErgodic

/-!
# Almost sure convergence of Birkhoff averages

Let `T` be a measure preserving map of a finite measure space `(α, μ)`, `f` a measurable integrable
real function and `S n = birkhoffSum T f n`.  This file proves the almost sure existence of the
limit of `S n x / n` (the pointwise ergodic theorem, without identification of the limit):

* `ae_exists_tendsto`: for almost every `x`, `S n x / n` converges;
* `exists_measurable_limit`: the limit can be chosen measurable.

The proof follows the classical route.  By the maximal ergodic inequality
(`ComplexSLE.Infrastructure.Ergodic.mul_measureReal_le_setIntegral`) applied to `|f|`, the
sequence `S n x / n` is bounded almost surely.  For `a < b`, the set `FreqBelow T f a ∩
FreqBelow T (-f) (-b)` of points whose Birkhoff averages oscillate below `a` and above `b` is
`T`-invariant (`freqBelow_iff`), and the maximal inequality on invariant sets gives
`b μ(E) ≤ ∫_E f ≤ a μ(E)`, so `μ(E) = 0`.  A bounded real sequence that does not oscillate
between any two rationals converges.
-/

public section

open MeasureTheory Filter Set Function Topology

namespace ComplexSLE.Infrastructure.Ergodic

variable {α : Type*} {T : α → α} {f : α → ℝ}

/-- `FreqBelow T f a` is the set of points `x` for which some rational `q < a` satisfies
`S n x < n q` for infinitely many `n` (that is, the `liminf` of the Birkhoff averages
`S n x / n` is `< a`). -/
@[expose] def FreqBelow (T : α → α) (f : α → ℝ) (a : ℝ) : Set α :=
  {x | ∃ q : ℚ, (q : ℝ) < a ∧ ∃ᶠ n : ℕ in atTop, birkhoffSum T f n x < n * q}

theorem frequently_succ_of_frequently {P : ℕ → Prop} (h : ∃ᶠ n in atTop, P n) :
    ∃ᶠ n in atTop, P (n + 1) := by
  rw [frequently_atTop] at h ⊢
  intro N
  obtain ⟨m, hm, hP⟩ := h (N + 1)
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  exact ⟨n, by omega, hP⟩

theorem frequently_of_frequently_succ {P : ℕ → Prop} (h : ∃ᶠ n in atTop, P (n + 1)) :
    ∃ᶠ n in atTop, P n :=
  (tendsto_add_atTop_nat 1).frequently h

/-- If `S n x < n c` infinitely often, and `c < c'`, then `S n (T x) < n c'` infinitely often. -/
theorem frequently_lt_comp_of_frequently_lt {c c' : ℝ} (hc : c < c') (x : α)
    (h : ∃ᶠ n : ℕ in atTop, birkhoffSum T f n x < n * c) :
    ∃ᶠ n : ℕ in atTop, birkhoffSum T f n (T x) < n * c' := by
  have h1 := frequently_succ_of_frequently h
  have h2 := h1.and_eventually (eventually_ge_atTop ⌈(c - f x) / (c' - c)⌉₊)
  refine h2.mono fun n ⟨hn, hK⟩ => ?_
  rw [birkhoffSum_succ_apply'] at hn
  have hK' : (c - f x) / (c' - c) ≤ n :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hK)
  have h3 : c - f x ≤ n * (c' - c) := by
    rwa [div_le_iff₀ (sub_pos.2 hc)] at hK'
  push_cast at hn
  nlinarith

/-- If `S n (T x) < n c` infinitely often, and `c < c'`, then `S n x < n c'` infinitely often. -/
theorem frequently_lt_of_frequently_lt_comp {c c' : ℝ} (hc : c < c') (x : α)
    (h : ∃ᶠ n : ℕ in atTop, birkhoffSum T f n (T x) < n * c) :
    ∃ᶠ n : ℕ in atTop, birkhoffSum T f n x < n * c' := by
  have h2 := h.and_eventually (eventually_ge_atTop ⌈(f x - c') / (c' - c)⌉₊)
  have h3 : ∃ᶠ n : ℕ in atTop, birkhoffSum T f (n + 1) x < (n + 1 : ℕ) * c' := by
    refine h2.mono fun n ⟨hn, hK⟩ => ?_
    rw [birkhoffSum_succ_apply']
    have hK' : (f x - c') / (c' - c) ≤ n :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hK)
    have h4 : f x - c' ≤ n * (c' - c) := by
      rwa [div_le_iff₀ (sub_pos.2 hc)] at hK'
    push_cast
    nlinarith
  exact frequently_of_frequently_succ h3

/-- `FreqBelow T f a` is `T`-invariant. -/
theorem freqBelow_iff (a : ℝ) (x : α) : T x ∈ FreqBelow T f a ↔ x ∈ FreqBelow T f a := by
  constructor
  · rintro ⟨q, hq, h⟩
    obtain ⟨q', hq1, hq2⟩ := exists_rat_btwn hq
    exact ⟨q', hq2, frequently_lt_of_frequently_lt_comp (by exact_mod_cast hq1) x h⟩
  · rintro ⟨q, hq, h⟩
    obtain ⟨q', hq1, hq2⟩ := exists_rat_btwn hq
    exact ⟨q', hq2, frequently_lt_comp_of_frequently_lt (by exact_mod_cast hq1) x h⟩

theorem measurableSet_frequently [MeasurableSpace α] {p : ℕ → α → Prop}
    (hp : ∀ n, MeasurableSet {x | p n x}) : MeasurableSet {x | ∃ᶠ n in atTop, p n x} := by
  have : {x | ∃ᶠ n in atTop, p n x} = ⋂ N : ℕ, ⋃ n : ℕ, ⋃ _ : N ≤ n, {x | p n x} := by
    ext x
    simp [frequently_atTop]
  rw [this]
  exact MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ =>
    hp n

theorem measurableSet_freqBelow [MeasurableSpace α] (hT : Measurable T) (hf : Measurable f)
    (a : ℝ) : MeasurableSet (FreqBelow T f a) := by
  have : FreqBelow T f a = ⋃ q : ℚ, ⋃ _ : (q : ℝ) < a,
      {x | ∃ᶠ n : ℕ in atTop, birkhoffSum T f n x < n * q} := by
    ext x
    simp [FreqBelow]
  rw [this]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ => ?_
  exact measurableSet_frequently fun n =>
    measurableSet_lt (measurable_birkhoffSum hT hf n) measurable_const

variable [MeasurableSpace α] {μ : Measure α}

/-- The set of points whose Birkhoff averages oscillate below `a` and above `b > a` is null. -/
theorem measure_freqBelow_inter_eq_zero [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hfm : Measurable f) (hf : Integrable f μ) {a b : ℝ} (hab : a < b) :
    μ (FreqBelow T f a ∩ FreqBelow T (-f) (-b)) = 0 := by
  set E := FreqBelow T f a ∩ FreqBelow T (-f) (-b) with hE
  have hEm : MeasurableSet E :=
    (measurableSet_freqBelow hT.measurable hfm a).inter
      (measurableSet_freqBelow hT.measurable hfm.neg (-b))
  have hEinv : ∀ x, T x ∈ E ↔ x ∈ E := fun x => by
    simp only [hE, mem_inter_iff, freqBelow_iff]
  have h1 : ∀ x ∈ E, ∃ n : ℕ, (n : ℝ) * b < birkhoffSum T f n x := by
    rintro x ⟨-, q, hq, hfr⟩
    obtain ⟨n, hn, hn'⟩ := (hfr.and_eventually (eventually_ge_atTop 1)).exists
    refine ⟨n, ?_⟩
    rw [birkhoffSum_neg_apply] at hn
    have hn1 : (0 : ℝ) < n := by exact_mod_cast hn'
    nlinarith
  have h2 : ∀ x ∈ E, ∃ n : ℕ, birkhoffSum T f n x < n * a := by
    rintro x ⟨⟨q, hq, hfr⟩, -⟩
    obtain ⟨n, hn, hn'⟩ := (hfr.and_eventually (eventually_ge_atTop 1)).exists
    refine ⟨n, ?_⟩
    have hn1 : (0 : ℝ) < n := by exact_mod_cast hn'
    nlinarith
  have h3 := mul_measureReal_le_setIntegral_of_forall hT hfm hf hEm hEinv b h1
  have h4 := setIntegral_le_mul_measureReal_of_forall hT hfm hf hEm hEinv a h2
  have h5 : μ.real E ≤ 0 := by
    by_contra h
    push Not at h
    nlinarith
  exact (measureReal_eq_zero_iff).1 (le_antisymm h5 measureReal_nonneg)

/-- Almost surely, the Birkhoff averages of `f` are bounded. -/
theorem ae_exists_abs_birkhoffSum_le [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hfm : Measurable f) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, ∃ C : ℝ, ∀ n : ℕ, |birkhoffSum T f n x| ≤ n * C := by
  set g : α → ℝ := fun x => |f x| with hg
  have hgm : Measurable g := continuous_abs.measurable.comp hfm
  have hgi : Integrable g μ := hf.abs
  set F : ℕ → Set α := fun k => {x | ∃ n : ℕ, (n : ℝ) * ((k : ℝ) + 1) < birkhoffSum T g n x}
    with hF
  have hbound : ∀ k : ℕ, ((k : ℝ) + 1) * μ.real (F k) ≤ ∫ x, g x ∂μ := by
    intro k
    have h := mul_measureReal_le_setIntegral hT hgm hgi MeasurableSet.univ
      (fun x => by simp) ((k : ℝ) + 1)
    rw [univ_inter] at h
    refine h.trans ?_
    exact setIntegral_le_integral hgi (Eventually.of_forall fun x => abs_nonneg _)
  set N : Set α := ⋂ k, F k with hN
  have hNle : ∀ k : ℕ, ((k : ℝ) + 1) * μ.real N ≤ ∫ x, g x ∂μ := by
    intro k
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity)) (hbound k)
    exact measureReal_mono (iInter_subset F k)
  have hN0 : μ.real N ≤ 0 := by
    by_contra h
    push Not at h
    obtain ⟨k, hk⟩ := exists_nat_gt ((∫ x, g x ∂μ) / μ.real N)
    have := hNle k
    rw [div_lt_iff₀ h] at hk
    nlinarith
  have hNnull : μ N = 0 := (measureReal_eq_zero_iff).1 (le_antisymm hN0 measureReal_nonneg)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hNnull] with x hx
  simp only [hN, mem_iInter, not_forall] at hx
  obtain ⟨k, hk⟩ := hx
  refine ⟨(k : ℝ) + 1, fun n => ?_⟩
  have h1 : birkhoffSum T g n x ≤ n * ((k : ℝ) + 1) := by
    by_contra h
    exact hk ⟨n, not_le.1 h⟩
  refine le_trans ?_ h1
  exact Finset.abs_sum_le_sum_abs _ _

/-- A bounded real sequence which does not oscillate between two rationals converges. -/
theorem exists_tendsto_of_not_oscillate {u : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |u n| ≤ B)
    (h : ∀ a b : ℚ, a < b → ¬ ((∃ q : ℚ, (q : ℝ) < a ∧ ∃ᶠ n in atTop, u n < q) ∧
      (∃ q : ℚ, (q : ℝ) < -b ∧ ∃ᶠ n in atTop, -u n < q))) :
    ∃ l, Tendsto u atTop (𝓝 l) := by
  have hbdd1 : IsBoundedUnder (· ≤ ·) atTop u :=
    isBoundedUnder_of ⟨B, fun n => (abs_le.1 (hB n)).2⟩
  have hbdd2 : IsBoundedUnder (· ≥ ·) atTop u :=
    isBoundedUnder_of ⟨-B, fun n => (abs_le.1 (hB n)).1⟩
  have hle : liminf u atTop ≤ limsup u atTop := liminf_le_limsup hbdd1 hbdd2
  have hge : limsup u atTop ≤ liminf u atTop := by
    by_contra hlt
    have hlt := not_le.1 hlt
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn hlt
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn ha2
    obtain ⟨b', hb1', hb2'⟩ := exists_rat_btwn hb2
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn ha1
    have hlo : ∃ᶠ n in atTop, u n < q := frequently_lt_of_liminf_lt hbdd1.isCoboundedUnder_ge hq1
    have hhi : ∃ᶠ n in atTop, (b' : ℝ) < u n :=
      frequently_lt_of_lt_limsup hbdd2.isCoboundedUnder_le hb2'
    refine h a b (by exact_mod_cast hb1) ⟨⟨q, hq2, hlo⟩, ⟨-b', ?_, ?_⟩⟩
    · push_cast
      linarith
    · refine hhi.mono fun n hn => ?_
      push_cast
      linarith
  exact ⟨limsup u atTop, tendsto_of_le_liminf_of_limsup_le hge le_rfl hbdd1 hbdd2⟩

/-- **Pointwise ergodic theorem (existence of the limit).** For a measure preserving map of a finite
measure space and a measurable integrable `f`, the Birkhoff averages converge almost surely. -/
theorem ae_exists_tendsto [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hfm : Measurable f) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, ∃ l : ℝ, Tendsto (fun n : ℕ => birkhoffSum T f n x / n) atTop (𝓝 l) := by
  have hosc : ∀ᵐ x ∂μ, ∀ a b : ℚ, a < b →
      x ∉ FreqBelow T f a ∩ FreqBelow T (-f) (-b) := by
    refine ae_all_iff.2 fun a => ae_all_iff.2 fun b => ?_
    by_cases hab : a < b
    · exact measure_eq_zero_iff_ae_notMem.1
        (measure_freqBelow_inter_eq_zero hT hfm hf (by exact_mod_cast hab)) |>.mono
          fun x hx _ => hx
    · exact Eventually.of_forall fun x h => absurd h hab
  filter_upwards [hosc, ae_exists_abs_birkhoffSum_le hT hfm hf] with x hx hC
  obtain ⟨C, hC⟩ := hC
  have hB : ∀ n : ℕ, |birkhoffSum T f n x / n| ≤ |C| := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [abs_div, abs_of_pos hn', div_le_iff₀ hn']
      calc |birkhoffSum T f n x| ≤ n * C := hC n
        _ ≤ |C| * n := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_abs_self C) hn'.le
  refine exists_tendsto_of_not_oscillate hB fun a b hab ⟨⟨q, hq, h1⟩, ⟨q', hq', h2⟩⟩ => ?_
  refine hx a b hab ⟨⟨q, hq, ?_⟩, ⟨q', hq', ?_⟩⟩
  · refine (h1.and_eventually (eventually_ge_atTop 1)).mono fun n ⟨hn, hn1⟩ => ?_
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
    exact (div_lt_iff₀ hn').1 hn |>.trans_eq (mul_comm _ _)
  · refine (h2.and_eventually (eventually_ge_atTop 1)).mono fun n ⟨hn, hn1⟩ => ?_
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [birkhoffSum_neg_apply]
    have : -(birkhoffSum T f n x / n) = -birkhoffSum T f n x / n := by ring
    rw [this, div_lt_iff₀ hn'] at hn
    linarith

/-- The almost sure limit of the Birkhoff averages can be chosen measurable. -/
theorem exists_measurable_limit [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hfm : Measurable f) (hf : Integrable f μ) :
    ∃ L : α → ℝ, Measurable L ∧
      ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => birkhoffSum T f n x / n) atTop (𝓝 (L x)) := by
  set g : α → ℝ := fun x => limUnder atTop (fun n : ℕ => birkhoffSum T f n x / n) with hg
  have hgt : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => birkhoffSum T f n x / n) atTop (𝓝 (g x)) :=
    (ae_exists_tendsto hT hfm hf).mono fun x hx => tendsto_nhds_limUnder hx
  have hgm : AEMeasurable g μ :=
    aemeasurable_of_tendsto_metrizable_ae atTop
      (fun n => ((measurable_birkhoffSum hT.measurable hfm n).div_const (n : ℝ)).aemeasurable) hgt
  refine ⟨hgm.mk g, hgm.measurable_mk, ?_⟩
  filter_upwards [hgt, hgm.ae_eq_mk] with x hx hx'
  rwa [← hx']

end ComplexSLE.Infrastructure.Ergodic

end
