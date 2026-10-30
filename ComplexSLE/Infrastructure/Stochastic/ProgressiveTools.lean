/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsContLocalMartingale
public import ComplexSLE.Infrastructure.Stochastic.ContinuousOptionalStopping
public import ComplexSLE.Infrastructure.Stochastic.ContinuousModification
public import ComplexSLE.Infrastructure.Stochastic.LocalMartingaleAlgebra
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Progressive measurability tools and modifications of local martingales

Source-independent facts used by the Itô stratum of the polar decomposition (Lemma 2.11):

* `StronglyAdapted.isStronglyProgressive_of_rightContinuous`: an adapted process with
  right-continuous paths is progressively measurable (approximation from the right along the
  dyadic grid on `[0, i]`);
* `isStronglyProgressive_indicator_le`: the indicator `1_{s ≤ ρ}` of the stochastic interval
  `[0, ρ]` of a finite stopping time is progressive;
* `martingale_const_of_stronglyMeasurable`: an integrable `ℱ 0`-measurable random variable, viewed
  as a process constant in time, is a martingale;
* `IsContLocalMartingale.congr_ae`: a progressive process that agrees with a continuous local
  martingale off a `P`-null set (for all times simultaneously) is a continuous local martingale
  (martingale transfer by a.e. equality of the stopped processes);
* `IsContLocalMartingale.of_stopped_seq`: if `M^{ρ_k}` is a continuous local martingale for a
  sequence of stopping times `ρ_k` that is a.s. eventually above every level, then `M` is a
  continuous local martingale (diagonal localising sequence `ρ_k ∧ τ^k_{j_k}` with
  `P(τ^k_{j_k} < k) < 2⁻ᵏ`, and Borel–Cantelli).
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Infrastructure

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}

/-! ### Right-continuous adapted processes are progressive -/

section RightContinuous

variable {E : Type*} [NormedAddCommGroup E]

/-- The dyadic ceiling `⌈2^N x⌉ / 2^N` (a local copy of `dyadicCeil`, whose body is not exposed). -/
noncomputable def ceilN (N : ℕ) (x : ℝ≥0) : ℝ≥0 := (⌈(2 : ℝ≥0) ^ N * x⌉₊ : ℝ≥0) / 2 ^ N

theorem le_ceilN (N : ℕ) (x : ℝ≥0) : x ≤ ceilN N x := by
  unfold ceilN
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact Nat.le_ceil _

theorem ceilN_le (N : ℕ) (x : ℝ≥0) : ceilN N x ≤ x + ((2 : ℝ≥0)⁻¹) ^ N := by
  unfold ceilN
  rw [div_le_iff₀ (by positivity), inv_pow, add_mul, inv_mul_cancel₀ (by positivity), mul_comm]
  exact (Nat.ceil_lt_add_one bot_le).le

theorem tendsto_ceilN (x : ℝ≥0) : Tendsto (fun N => ceilN N x) atTop (𝓝 x) := by
  have h : Tendsto (fun N : ℕ => x + ((2 : ℝ≥0)⁻¹) ^ N) atTop (𝓝 (x + 0)) :=
    tendsto_const_nhds.add (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by simp [inv_lt_one_iff₀]))
  rw [add_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (le_ceilN · x)
    (ceilN_le · x)

/-- The dyadic approximation from the right, capped at `i`. -/
theorem tendsto_min_ceilN {i : ℝ≥0} (x : Iic i) :
    Tendsto (fun N : ℕ => min (ceilN N x) i) atTop (𝓝 (x : ℝ≥0)) := by
  have h := (tendsto_ceilN (x : ℝ≥0)).min (tendsto_const_nhds (x := i))
  have hx : (x : ℝ≥0) ≤ i := x.2
  rwa [min_eq_left hx] at h

/-- **Right-continuous adapted processes are progressive.** -/
theorem _root_.MeasureTheory.StronglyAdapted.isStronglyProgressive_of_rightContinuous
    {X : ℝ≥0 → Ω → E} (hX : StronglyAdapted ℱ X)
    (hrc : ∀ ω r, ContinuousWithinAt (fun t => X t ω) (Ici r) r) :
    IsStronglyProgressive ℱ X := by
  intro i
  let mp : MeasurableSpace (Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
  -- the approximants `X (min (ceilN N p.1) i) p.2`, written as finite sums
  let K : ℕ → ℕ := fun N => ⌈(2 : ℝ≥0) ^ N * i⌉₊
  let g : ℕ → Iic i × Ω → E := fun N p => ∑ j ∈ Finset.range (K N + 1),
    {p : Iic i × Ω | ⌈(2 : ℝ≥0) ^ N * (p.1 : ℝ≥0)⌉₊ = j}.indicator
      (fun p => X (min ((j : ℝ≥0) / 2 ^ N) i) p.2) p
  have hg_eq : ∀ N p, g N p = X (min (ceilN N p.1) i) p.2 := by
    intro N p
    have hj : ⌈(2 : ℝ≥0) ^ N * (p.1 : ℝ≥0)⌉₊ ∈ Finset.range (K N + 1) := by
      rw [Finset.mem_range, Nat.lt_succ_iff]
      exact Nat.ceil_le_ceil (mul_le_mul_of_nonneg_left p.1.2 bot_le)
    simp only [g]
    rw [Finset.sum_eq_single_of_mem _ hj]
    · rw [indicator_of_mem (by simp)]
      rfl
    · intro j _ hne
      exact indicator_of_notMem (fun h => hne (by simpa using h.symm)) _
  have hg_meas : ∀ N, StronglyMeasurable[mp] (g N) := by
    intro N
    refine Finset.stronglyMeasurable_fun_sum _ fun j _ => StronglyMeasurable.indicator ?_ ?_
    · have h1 : StronglyMeasurable[ℱ i] (X (min ((j : ℝ≥0) / 2 ^ N) i)) :=
        (hX _).mono (ℱ.mono (min_le_right _ _))
      exact h1.comp_measurable (@measurable_snd _ _ _ (ℱ i))
    · have hm : Measurable[mp] fun p : Iic i × Ω => ⌈(2 : ℝ≥0) ^ N * (p.1 : ℝ≥0)⌉₊ := by
        have : Measurable[mp] fun p : Iic i × Ω => (p.1 : ℝ≥0) :=
          measurable_subtype_coe.comp (@measurable_fst _ _ _ (ℱ i))
        exact (Nat.measurable_ceil).comp (measurable_const.mul this)
      exact hm (measurableSet_singleton j)
  refine stronglyMeasurable_of_tendsto atTop hg_meas ?_
  rw [tendsto_pi_nhds]
  intro p
  simp only [hg_eq]
  refine ((hrc p.2 p.1).tendsto).comp ?_
  rw [tendsto_nhdsWithin_iff]
  refine ⟨tendsto_min_ceilN p.1, Eventually.of_forall fun N => ?_⟩
  exact le_min (le_ceilN N _) p.1.2

end RightContinuous

/-! ### The indicator of a stochastic interval `[0, ρ]` -/

/-- `s ≤ ρ` iff the stopped time `s ∧ ρ` equals `s`. -/
theorem le_iff_untopA_min_eq {ρ : Ω → WithTop ℝ≥0} {s : ℝ≥0} {ω : Ω} :
    (s : WithTop ℝ≥0) ≤ ρ ω ↔ (min (s : WithTop ℝ≥0) (ρ ω)).untopA = s := by
  have hne : min (s : WithTop ℝ≥0) (ρ ω) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  rw [WithTop.untopA_eq_untop hne]
  constructor
  · intro h
    rw [← WithTop.coe_inj, WithTop.coe_untop, min_eq_left h]
  · intro h
    rw [← WithTop.coe_inj, WithTop.coe_untop] at h
    exact min_eq_left_iff.1 h

/-- **The indicator of `[0, ρ]` is progressive.** -/
theorem isStronglyProgressive_indicator_le {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime ℱ ρ) :
    IsStronglyProgressive ℱ fun s ω => if (s : WithTop ℝ≥0) ≤ ρ ω then (1 : ℝ) else 0 := by
  intro i
  let mp : MeasurableSpace (Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
  have h1 := isStronglyProgressive_min_stopping_time hρ i
  have hset : MeasurableSet[mp] {p : Iic i × Ω | ((p.1 : ℝ≥0) : WithTop ℝ≥0) ≤ ρ p.2} := by
    have : {p : Iic i × Ω | ((p.1 : ℝ≥0) : WithTop ℝ≥0) ≤ ρ p.2} =
        {p : Iic i × Ω | (min ((p.1 : ℝ≥0) : WithTop ℝ≥0) (ρ p.2)).untopA = (p.1 : ℝ≥0)} := by
      ext p; exact le_iff_untopA_min_eq
    rw [this]
    exact measurableSet_eq_fun h1.measurable
      (measurable_subtype_coe.comp (@measurable_fst _ _ _ (ℱ i)))
  exact StronglyMeasurable.ite hset stronglyMeasurable_const stronglyMeasurable_const

/-- `ℝ≥0`-valued form of `isStronglyProgressive_indicator_le`. -/
theorem isStronglyProgressive_indicator_le_nnreal {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0)) :
    IsStronglyProgressive ℱ fun s ω => if s ≤ ρ ω then (1 : ℝ) else 0 := by
  have h := isStronglyProgressive_indicator_le hρ
  simpa only [WithTop.coe_le_coe] using h

/-! ### Constant processes -/

/-- An integrable `ℱ 0`-measurable random variable is, as a process constant in time, a
martingale. -/
theorem martingale_const_of_stronglyMeasurable [IsFiniteMeasure P] {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ 0] ξ) (hint : Integrable ξ P) :
    Martingale (fun _ ω => ξ ω) ℱ P := by
  refine ⟨fun t => hξ.mono (ℱ.mono (zero_le : (0 : ℝ≥0) ≤ t)), fun s t _ => ?_⟩
  have : SigmaFinite (P.trim (ℱ.le s)) := inferInstance
  rw [condExp_of_stronglyMeasurable (ℱ.le s) (hξ.mono (ℱ.mono (zero_le : (0 : ℝ≥0) ≤ s))) hint]

/-! ### Modification of a continuous local martingale -/

/-- **A.e. modification.** A progressive process that agrees with a continuous local martingale
for all times, off a `P`-null set, is a continuous local martingale. -/
theorem _root_.ComplexSLE.IsContLocalMartingale.congr_ae [IsFiniteMeasure P]
    {Y Z : ℝ≥0 → Ω → ℝ} (hY : IsContLocalMartingale ℱ Y P) (hZ : IsStronglyProgressive ℱ Z)
    (h : ∀ᵐ ω ∂P, ∀ t, Z t ω = Y t ω) : IsContLocalMartingale ℱ Z P := by
  obtain ⟨-, hYc, τ, hτ, hτev, hmart⟩ := hY
  refine ⟨hZ, ?_, τ, hτ, hτev, fun n => ?_⟩
  · filter_upwards [hYc, h] with ω h1 h2
    have : (fun t => Z t ω) = fun t => Y t ω := funext h2
    rw [this]; exact h1
  · refine martingale_of_ae_eq_of_le_sup_null (fun t => le_sup_left) (hmart n)
      (hZ.stronglyAdapted_stoppedProcess (hτ n)) fun t => ?_
    filter_upwards [h] with ω hω
    simp only [stoppedProcess, hω]

/-! ### Localisation: local martingales from stopped local martingales -/

/-- If a.e. point is eventually outside the measurable sets `B j`, then `P (B j) → 0`; in
particular some `B j` has measure `< ε`. -/
theorem exists_measure_lt_of_ae_eventually_notMem [IsFiniteMeasure P] {B : ℕ → Set Ω}
    (hB : ∀ j, MeasurableSet (B j)) (h : ∀ᵐ ω ∂P, ∀ᶠ j in atTop, ω ∉ B j) {ε : ℝ≥0∞}
    (hε : 0 < ε) : ∃ j, P (B j) < ε := by
  let S : ℕ → Set Ω := fun j => ⋃ i, ⋃ (_ : j ≤ i), B i
  have hS : ∀ j, MeasurableSet (S j) := fun j =>
    MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hB i
  have hanti : Antitone S := fun j k hjk =>
    iUnion₂_subset fun i hi => subset_iUnion₂ (s := fun i _ => B i) i (hjk.trans hi)
  have hlim : P (⋂ j, S j) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h] with ω hω
    obtain ⟨j, hj⟩ := eventually_atTop.1 hω
    simp only [S, mem_iInter, mem_iUnion, not_forall, not_exists]
    exact ⟨j, fun i hi => hj i hi⟩
  have ht := tendsto_measure_iInter_atTop (fun j => (hS j).nullMeasurableSet) hanti
    ⟨0, measure_ne_top P _⟩
  rw [hlim] at ht
  obtain ⟨j, hj⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact ⟨j, lt_of_le_of_lt (measure_mono (subset_iUnion₂ (s := fun i _ => B i) j le_rfl)) hj⟩

/-- **Localisation.** Let `M` be progressive with a.s. continuous paths, and let `ρ k` be stopping
times that are a.s. eventually above every level. If every stopped process `M^{ρ k}` is a continuous
local martingale, then so is `M`. -/
theorem _root_.ComplexSLE.IsContLocalMartingale.of_stopped_seq [IsProbabilityMeasure P]
    {M : ℝ≥0 → Ω → ℝ} (hprog : IsStronglyProgressive ℱ M)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => M t ω) {ρ : ℕ → Ω → WithTop ℝ≥0}
    (hρ : ∀ k, IsStoppingTime ℱ (ρ k))
    (hρev : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ∀ᶠ k in atTop, (t : WithTop ℝ≥0) ≤ ρ k ω)
    (hM : ∀ k, IsContLocalMartingale ℱ (stoppedProcess M (ρ k)) P) :
    IsContLocalMartingale ℱ M P := by
  choose τ hτ hτev hmart using fun k => (hM k).2.2
  -- for each `k`, a level `j k` with `P (τ k (j k) < k) < 2⁻ᵏ`
  have hchoice : ∀ k : ℕ,
      ∃ j, P {ω | τ k j ω < ((k : ℝ≥0) : WithTop ℝ≥0)} < (2⁻¹ : ℝ≥0∞) ^ k := by
    intro k
    refine exists_measure_lt_of_ae_eventually_notMem
      (fun j => ℱ.le k _ ((hτ k j).measurableSet_lt k)) ?_
      (ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) k)
    filter_upwards [hτev k] with ω hω
    filter_upwards [hω k] with j hj
    exact not_lt.2 hj
  choose j hj using hchoice
  refine ⟨hprog, hcont, fun k ω => min (ρ k ω) (τ k (j k) ω), fun k => (hρ k).min (hτ k (j k)),
    ?_, fun k => ?_⟩
  · have hsum : ∑' k, P {ω | τ k (j k) ω < ((k : ℝ≥0) : WithTop ℝ≥0)} ≠ ∞ := by
      refine ne_of_lt (lt_of_le_of_lt (tsum_le_tsum fun k => (hj k).le) ?_)
      rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
      exact ENNReal.ofNat_lt_top
    have hBC := ae_eventually_notMem hsum
    filter_upwards [hρev, hBC] with ω h1 h2 t
    have h3 : ∀ᶠ k : ℕ in atTop, (t : WithTop ℝ≥0) ≤ ((k : ℝ≥0) : WithTop ℝ≥0) := by
      filter_upwards [eventually_ge_atTop ⌈t⌉₊] with k hk
      exact WithTop.coe_le_coe.2 ((Nat.le_ceil t).trans (by exact_mod_cast hk))
    filter_upwards [h1 t, h2, h3] with k hk1 hk2 hk3
    exact le_min hk1 (hk3.trans (not_lt.1 hk2))
  · have := hmart k (j k)
    rwa [stoppedProcess_stoppedProcess_min, funext fun ω => min_comm (τ k (j k) ω) (ρ k ω)] at this

end ComplexSLE.Infrastructure

end
