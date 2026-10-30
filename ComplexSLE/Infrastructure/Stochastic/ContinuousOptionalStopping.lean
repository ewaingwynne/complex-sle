/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Probability.Martingale.OptionalSampling
public import Mathlib.Probability.Process.Adapted
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Optional stopping for continuous martingales

Source-independent stochastic calculus (Revuz–Yor II.3.3): the process `M^τ = M (· ∧ τ)` obtained
from a martingale `M : ℝ≥0 → Ω → ℝ` with continuous paths by stopping at an arbitrary stopping
time `τ` is again a martingale. No external input is used.

Mathlib has optional sampling only for stopping times with countable range. The route is:

* a bounded finite stopping time `r ≤ t` is approximated from above by the stopping times
  `dyadicCeil k (r ω) ↓ r ω`, which have countable range (and `≤ t + 1`);
* for stopping times `ρ` with countable range, `∫_A M_ρ = ∫_A M_{s ∧ ρ}` for `A ∈ ℱ_s`
  (`setIntegral_apply_eq_min_of_countable`, from Mathlib's discrete optional sampling);
* the family `M_{ρ_k} = E[M_{t+1} | ℱ_{ρ_k}]` is uniformly integrable, `M_{ρ_k} → M_r` pointwise
  by path continuity, so by Vitali the integrals over any set converge
  (`integrable_and_tendsto_setIntegral_apply`);
* passing to the limit in both sides gives `∫_A M_r = ∫_A M_{s ∧ r}` for every bounded finite
  stopping time `r` (`setIntegral_apply_stoppingTime_eq_min`), which is the martingale property of
  `M^τ` with `r = t ∧ τ`.
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory Filter Set

namespace ComplexSLE.Infrastructure

/-! ### Dyadic approximation from above -/

/-- The dyadic ceiling `⌈2^k x⌉ / 2^k` of `x : ℝ≥0`. -/
noncomputable def dyadicCeil (k : ℕ) (x : ℝ≥0) : ℝ≥0 := (⌈(2 : ℝ≥0) ^ k * x⌉₊ : ℝ≥0) / 2 ^ k

/-- `x ≤ ⌈2^k x⌉ / 2^k`. -/
theorem le_dyadicCeil (k : ℕ) (x : ℝ≥0) : x ≤ dyadicCeil k x := by
  unfold dyadicCeil
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact Nat.le_ceil _

/-- `⌈2^k x⌉ / 2^k < x + 1`. -/
theorem dyadicCeil_lt (k : ℕ) (x : ℝ≥0) : dyadicCeil k x < x + 1 := by
  unfold dyadicCeil
  rw [div_lt_iff₀ (by positivity)]
  calc (⌈(2 : ℝ≥0) ^ k * x⌉₊ : ℝ≥0) < 2 ^ k * x + 1 := Nat.ceil_lt_add_one zero_le
    _ ≤ (x + 1) * 2 ^ k := by
      rw [add_mul, one_mul, mul_comm]
      gcongr
      exact one_le_pow₀ (by norm_num)

/-- `⌈2^k x⌉ / 2^k ≤ u` iff `x ≤ ⌊2^k u⌋ / 2^k`. -/
theorem dyadicCeil_le_iff (k : ℕ) (x u : ℝ≥0) :
    dyadicCeil k x ≤ u ↔ x ≤ (⌊(2 : ℝ≥0) ^ k * u⌋₊ : ℝ≥0) / 2 ^ k := by
  unfold dyadicCeil
  rw [div_le_iff₀ (by positivity), le_div_iff₀ (by positivity), mul_comm u, mul_comm x,
    ← Nat.ceil_le, ← Nat.le_floor_iff zero_le]


/-- `⌊2^k u⌋ / 2^k ≤ u`. -/
theorem floor_div_le (k : ℕ) (u : ℝ≥0) : (⌊(2 : ℝ≥0) ^ k * u⌋₊ : ℝ≥0) / 2 ^ k ≤ u := by
  rw [div_le_iff₀ (by positivity), mul_comm]
  exact Nat.floor_le zero_le

/-- The dyadic ceilings converge to `x`. -/
theorem tendsto_dyadicCeil (x : ℝ≥0) : Tendsto (fun k => dyadicCeil k x) atTop (𝓝 x) := by
  have h : Tendsto (fun k : ℕ => x + ((2 : ℝ≥0)⁻¹) ^ k) atTop (𝓝 (x + 0)) :=
    tendsto_const_nhds.add (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by simp [inv_lt_one_iff₀]))
  rw [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (le_dyadicCeil · x) fun k => ?_
  unfold dyadicCeil
  rw [div_le_iff₀ (by positivity), inv_pow, add_mul, inv_mul_cancel₀ (by positivity), mul_comm]
  exact (Nat.ceil_lt_add_one zero_le).le


section Stopping

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}

/-- `{ρ ≤ u} ∈ ℱ_u` for an `ℝ≥0`-valued stopping time. -/
theorem measurableSet_nnreal_le {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0)) (u : ℝ≥0) :
    MeasurableSet[ℱ u] {ω | ρ ω ≤ u} := by
  have : {ω | ρ ω ≤ u} = {ω | (ρ ω : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0)} := by
    ext ω; simp only [mem_ofPred_eq, WithTop.coe_le_coe]
  rw [this]; exact hρ u

/-- Criterion for an `ℝ≥0`-valued function to be a stopping time. -/
theorem isStoppingTime_of_nnreal_le {ρ : Ω → ℝ≥0}
    (h : ∀ u, MeasurableSet[ℱ u] {ω | ρ ω ≤ u}) :
    IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0) := fun u => by
  have : {ω | (ρ ω : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0)} = {ω | ρ ω ≤ u} := by
    ext ω; simp only [mem_ofPred_eq, WithTop.coe_le_coe]
  rw [this]; exact h u

/-- The dyadic ceiling of a finite stopping time is a stopping time. -/
theorem isStoppingTime_dyadicCeil {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0)) (k : ℕ) :
    IsStoppingTime ℱ fun ω => (dyadicCeil k (ρ ω) : WithTop ℝ≥0) := by
  refine isStoppingTime_of_nnreal_le fun u => ?_
  have : {ω | dyadicCeil k (ρ ω) ≤ u} =
      {ω | ρ ω ≤ (⌊(2 : ℝ≥0) ^ k * u⌋₊ : ℝ≥0) / 2 ^ k} := by
    ext ω; simp only [mem_ofPred_eq]; exact dyadicCeil_le_iff _ _ _
  rw [this]
  exact ℱ.mono (floor_div_le k u) _ (measurableSet_nnreal_le hρ _)

/-- `s ∧ ρ` is a stopping time. -/
theorem isStoppingTime_min_const_nnreal {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0)) (s : ℝ≥0) :
    IsStoppingTime ℱ fun ω => ((min s (ρ ω) : ℝ≥0) : WithTop ℝ≥0) := by
  refine isStoppingTime_of_nnreal_le fun u => ?_
  by_cases hsu : s ≤ u
  · have : {ω | min s (ρ ω) ≤ u} = univ := by
      ext ω; simp [(min_le_left _ _).trans hsu]
    rw [this]; exact MeasurableSet.univ
  · have : {ω | min s (ρ ω) ≤ u} = {ω | ρ ω ≤ u} := by
      ext ω; simp only [mem_ofPred_eq, min_le_iff, hsu, false_or]
    rw [this]; exact measurableSet_nnreal_le hρ u

/-- Countable range is preserved by the coercion into `WithTop ℝ≥0`. -/
theorem countable_range_coe {f : Ω → ℝ≥0} (hf : (range f).Countable) :
    (range fun ω => (f ω : WithTop ℝ≥0)).Countable := by
  have := hf.image (fun x : ℝ≥0 => (x : WithTop ℝ≥0))
  rwa [← Set.range_comp] at this

/-- The dyadic ceiling of any function has countable range. -/
theorem countable_range_dyadicCeil (ρ : Ω → ℝ≥0) (k : ℕ) :
    (range fun ω => dyadicCeil k (ρ ω)).Countable :=
  (countable_range fun n : ℕ => (n : ℝ≥0) / 2 ^ k).mono
    (range_subset_iff.2 fun ω => mem_range.2 ⟨⌈(2 : ℝ≥0) ^ k * ρ ω⌉₊, rfl⟩)

/-- `s ∧ ρ` has countable range when `ρ` does. -/
theorem countable_range_min_const {ρ : Ω → ℝ≥0} (hρ : (range ρ).Countable) (s : ℝ≥0) :
    (range fun ω => min s (ρ ω)).Countable := by
  refine ((countable_singleton s).union hρ).mono (range_subset_iff.2 fun ω => ?_)
  rcases min_choice s (ρ ω) with h | h
  · exact Or.inl (by simp [h])
  · exact Or.inr ⟨ω, by simp [h]⟩

/-- For `A ∈ ℱ_s`, the set `A ∩ {s < ρ}` is `ℱ_{s ∧ ρ}`-measurable. -/
theorem measurableSet_inter_lt_min_const {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0)) {s : ℝ≥0} {A : Set Ω}
    (hA : MeasurableSet[ℱ s] A) :
    MeasurableSet[(isStoppingTime_min_const_nnreal hρ s).measurableSpace]
      (A ∩ {ω | s < ρ ω}) := by
  have hlt : MeasurableSet[ℱ s] {ω | s < ρ ω} := by
    have : {ω | s < ρ ω} = {ω | ρ ω ≤ s}ᶜ := by ext ω; simp
    rw [this]; exact (measurableSet_nnreal_le hρ s).compl
  have hAs : MeasurableSet[ℱ s] (A ∩ {ω | s < ρ ω}) := hA.inter hlt
  refine ⟨le_iSup (fun t => ℱ t) s _ hAs, fun u => ?_⟩
  by_cases hus : s ≤ u
  · have : A ∩ {ω | s < ρ ω} ∩ {ω | ((min s (ρ ω) : ℝ≥0) : WithTop ℝ≥0) ≤ u} =
        A ∩ {ω | s < ρ ω} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, and_iff_left_iff_imp]
      intro _
      exact_mod_cast (min_le_left _ _).trans hus
    rw [this]
    exact ℱ.mono hus _ hAs
  · push Not at hus
    have : A ∩ {ω | s < ρ ω} ∩ {ω | ((min s (ρ ω) : ℝ≥0) : WithTop ℝ≥0) ≤ u} = ∅ := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      rintro ⟨-, hlt⟩ hle
      have h1 : min s (ρ ω) = s := min_eq_left hlt.le
      rw [h1] at hle
      exact absurd (by exact_mod_cast hle : s ≤ u) (not_le.2 hus)
    rw [this]
    exact @MeasurableSet.empty _ (ℱ u)

end Stopping


section Martingale

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {ℱ : Filtration ℝ≥0 m}

/-- The stopped value at a finite (`ℝ≥0`-valued) time is `M (ρ ω) ω`. -/
theorem stoppedValue_coe (M : ℝ≥0 → Ω → ℝ) (ρ : Ω → ℝ≥0) :
    stoppedValue M (fun ω => (ρ ω : WithTop ℝ≥0)) = fun ω => M (ρ ω) ω := by
  funext ω; rfl

/-- The value of a martingale at a stopping time `≤ n` with countable range is a.e. equal to the
conditional expectation of `M n` given the stopping-time σ-algebra. -/
theorem stoppedValue_ae_eq_condExp_nnreal {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ P)
    {ρ : Ω → ℝ≥0} (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0))
    (hcount : (range ρ).Countable) {n : ℝ≥0} (hle : ∀ ω, ρ ω ≤ n) :
    (fun ω => M (ρ ω) ω) =ᵐ[P] P[M n | hρ.measurableSpace] := by
  have := hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range (n := n) hρ
    (fun ω => by exact_mod_cast hle ω) (countable_range_coe hcount)
  rwa [stoppedValue_coe] at this

theorem integrable_apply_nnreal {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ P)
    {ρ : Ω → ℝ≥0} (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0))
    (hcount : (range ρ).Countable) {n : ℝ≥0} (hle : ∀ ω, ρ ω ≤ n) :
    Integrable (fun ω => M (ρ ω) ω) P :=
  integrable_condExp.congr (stoppedValue_ae_eq_condExp_nnreal hM hρ hcount hle).symm

/-- Discrete optional sampling in integrated form: for a bounded stopping time `ρ` with countable
range, `∫_A M_ρ = ∫_A M_{s ∧ ρ}` for `A ∈ ℱ_s`. -/
theorem setIntegral_apply_eq_min_of_countable {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ P)
    {ρ : Ω → ℝ≥0} (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0))
    (hcount : (range ρ).Countable) {n : ℝ≥0} (hle : ∀ ω, ρ ω ≤ n) {s : ℝ≥0} {A : Set Ω}
    (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A, M (ρ ω) ω ∂P = ∫ ω in A, M (min s (ρ ω)) ω ∂P := by
  have hσ := isStoppingTime_min_const_nnreal hρ s
  have hσcount := countable_range_min_const hcount s
  have hcond := hM.stoppedValue_ae_eq_condExp_of_le_of_countable_range hρ hσ
    (fun ω => WithTop.coe_le_coe.2 (min_le_right _ _)) (fun ω => WithTop.coe_le_coe.2 (hle ω))
    (countable_range_coe hcount) (countable_range_coe hσcount)
  rw [stoppedValue_coe, stoppedValue_coe] at hcond
  have hint := integrable_apply_nnreal hM hρ hcount hle
  have hmeas : MeasurableSet A := ℱ.le s A hA
  have hle_meas : MeasurableSet {ω | ρ ω ≤ s} := ℱ.le s _ (measurableSet_nnreal_le hρ s)
  have hlt_meas : MeasurableSet {ω | s < ρ ω} := by
    have : {ω | s < ρ ω} = {ω | ρ ω ≤ s}ᶜ := by ext ω; simp
    rw [this]; exact hle_meas.compl
  have hint' := integrable_apply_nnreal hM hσ hσcount (n := n)
    fun ω => (min_le_right _ _).trans (hle ω)
  have hsplit : A = (A ∩ {ω | ρ ω ≤ s}) ∪ (A ∩ {ω | s < ρ ω}) := by
    ext ω
    simp only [mem_union, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro hω
      rcases le_or_gt (ρ ω) s with h | h
      · exact Or.inl ⟨hω, h⟩
      · exact Or.inr ⟨hω, h⟩
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  have hdisj : Disjoint (A ∩ {ω | ρ ω ≤ s}) (A ∩ {ω | s < ρ ω}) := by
    rw [Set.disjoint_left]
    rintro ω ⟨-, h1⟩ ⟨-, h2⟩
    exact absurd h1 (not_le.2 h2)
  have hA₂σ := measurableSet_inter_lt_min_const hρ hA
  have hA₂meas : MeasurableSet (A ∩ {ω | s < ρ ω}) := hmeas.inter hlt_meas
  rw [hsplit, setIntegral_union hdisj hA₂meas hint.integrableOn hint.integrableOn,
    setIntegral_union hdisj hA₂meas hint'.integrableOn hint'.integrableOn]
  congr 1
  · refine setIntegral_congr_fun (hmeas.inter hle_meas) fun ω hω => ?_
    rw [min_eq_right (show ρ ω ≤ s from hω.2)]
  · rw [← setIntegral_condExp hσ.measurableSpace_le hint hA₂σ]
    exact setIntegral_congr_ae hA₂meas (by filter_upwards [hcond] with ω hω _ using hω.symm)

/-- Let `ρ k` be stopping times with countable range, all `≤ n`, converging pointwise to `r`. For a
continuous martingale `M`, `M_r` is integrable and `∫_A M_{ρ k} → ∫_A M_r` for every set `A`
(uniform integrability of `E[M n | ℱ_{ρ k}]` plus Vitali). -/
theorem integrable_and_tendsto_setIntegral_apply {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ P)
    (hc : ∀ ω, Continuous fun t => M t ω) {n : ℝ≥0} {ρ : ℕ → Ω → ℝ≥0}
    (hρ : ∀ k, IsStoppingTime ℱ fun ω => (ρ k ω : WithTop ℝ≥0))
    (hcount : ∀ k, (range (ρ k)).Countable) (hle : ∀ k ω, ρ k ω ≤ n) {r : Ω → ℝ≥0}
    (hlim : ∀ ω, Tendsto (fun k => ρ k ω) atTop (𝓝 (r ω))) :
    Integrable (fun ω => M (r ω) ω) P ∧ ∀ A : Set Ω,
      Tendsto (fun k => ∫ ω in A, M (ρ k ω) ω ∂P) atTop (𝓝 (∫ ω in A, M (r ω) ω ∂P)) := by
  have hUI0 : UniformIntegrable (fun k => P[M n | (hρ k).measurableSpace]) 1 P :=
    (hM.integrable n).uniformIntegrable_condExp fun k => (hρ k).measurableSpace_le
  have hUI : UniformIntegrable (fun k ω => M (ρ k ω) ω) 1 P :=
    hUI0.ae_eq fun k => (stoppedValue_ae_eq_condExp_nnreal hM (hρ k) (hcount k) (hle k)).symm
  have hlim' : ∀ᵐ ω ∂P, Tendsto (fun k => M (ρ k ω) ω) atTop (𝓝 (M (r ω) ω)) :=
    ae_of_all _ fun ω => ((hc ω).tendsto (r ω)).comp (hlim ω)
  have hint : Integrable (fun ω => M (r ω) ω) P := hUI.integrable_of_ae_tendsto hlim'
  refine ⟨hint, fun A => ?_⟩
  have hL1 := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
    (fun k => hUI.aestronglyMeasurable k) (memLp_one_iff_integrable.2 hint) hUI.unifIntegrable
    hlim'
  exact tendsto_setIntegral_of_L1' _
    (Eventually.of_forall fun k => integrable_apply_nnreal hM (hρ k) (hcount k) (hle k)) hL1 A

/-- The value `M_r` of a continuous martingale at a bounded finite stopping time is integrable. -/
theorem integrable_apply_stoppingTime {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ P)
    (hc : ∀ ω, Continuous fun t => M t ω) {r : Ω → ℝ≥0}
    (hr : IsStoppingTime ℱ fun ω => (r ω : WithTop ℝ≥0)) {t : ℝ≥0} (hrt : ∀ ω, r ω ≤ t) :
    Integrable (fun ω => M (r ω) ω) P :=
  (integrable_and_tendsto_setIntegral_apply hM hc (n := t + 1)
    (ρ := fun k ω => dyadicCeil k (r ω)) (fun k => isStoppingTime_dyadicCeil hr k)
    (fun k => countable_range_dyadicCeil r k)
    (fun k ω => ((dyadicCeil_lt k (r ω)).trans_le (add_le_add_left (hrt ω) 1)).le)
    (fun ω => tendsto_dyadicCeil (r ω))).1

/-- **Optional sampling (integrated form) for continuous martingales and bounded stopping
times.** -/
theorem setIntegral_apply_stoppingTime_eq_min {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ P)
    (hc : ∀ ω, Continuous fun t => M t ω) {r : Ω → ℝ≥0}
    (hr : IsStoppingTime ℱ fun ω => (r ω : WithTop ℝ≥0)) {t : ℝ≥0} (hrt : ∀ ω, r ω ≤ t)
    {s : ℝ≥0} {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A, M (r ω) ω ∂P = ∫ ω in A, M (min s (r ω)) ω ∂P := by
  have hle : ∀ k ω, dyadicCeil k (r ω) ≤ t + 1 := fun k ω =>
    ((dyadicCeil_lt k (r ω)).trans_le (add_le_add_left (hrt ω) 1)).le
  have h1 := (integrable_and_tendsto_setIntegral_apply hM hc (n := t + 1)
    (ρ := fun k ω => dyadicCeil k (r ω)) (fun k => isStoppingTime_dyadicCeil hr k)
    (fun k => countable_range_dyadicCeil r k) hle
    (fun ω => tendsto_dyadicCeil (r ω))).2 A
  have h2 := (integrable_and_tendsto_setIntegral_apply hM hc (n := t + 1)
    (ρ := fun k ω => min s (dyadicCeil k (r ω)))
    (fun k => isStoppingTime_min_const_nnreal (isStoppingTime_dyadicCeil hr k) s)
    (fun k => countable_range_min_const (countable_range_dyadicCeil r k) s)
    (fun k ω => (min_le_right _ _).trans (hle k ω))
    (r := fun ω => min s (r ω))
    (fun ω => tendsto_const_nhds.min (tendsto_dyadicCeil (r ω)))).2 A
  have heq : ∀ k, ∫ ω in A, M (dyadicCeil k (r ω)) ω ∂P =
      ∫ ω in A, M (min s (dyadicCeil k (r ω))) ω ∂P := fun k =>
    setIntegral_apply_eq_min_of_countable hM (isStoppingTime_dyadicCeil hr k)
      (countable_range_dyadicCeil r k) (hle k) hA
  simp only [← heq] at h2
  exact tendsto_nhds_unique h1 h2

end Martingale

end ComplexSLE.Infrastructure

namespace MeasureTheory.Martingale

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {ℱ : Filtration ℝ≥0 m}

open ComplexSLE.Infrastructure

/-- **Optional stopping for continuous martingales** (Revuz–Yor II.3.3): the process `M`
stopped at an arbitrary (possibly infinite) stopping time `τ` is again a martingale. -/
theorem stoppedProcess_of_continuous {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ P)
    (hc : ∀ ω, Continuous fun t => M t ω) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) :
    Martingale (stoppedProcess M τ) ℱ P := by
  have hprog : IsStronglyProgressive ℱ M :=
    hM.stronglyAdapted.isStronglyProgressive_of_continuous hc
  refine ⟨hprog.stronglyAdapted_stoppedProcess hτ, fun i j hij => ?_⟩
  -- the finite bounded stopping times `r t = t ∧ τ`
  let r : ℝ≥0 → Ω → ℝ≥0 := fun t ω => (min (t : WithTop ℝ≥0) (τ ω)).untopA
  have hr_coe : ∀ t ω, (r t ω : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) (τ ω) := by
    intro t ω
    have hne : min (t : WithTop ℝ≥0) (τ ω) ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
    simp only [r]
    rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop]
  have hr_st : ∀ t, IsStoppingTime ℱ fun ω => (r t ω : WithTop ℝ≥0) := fun t => by
    have : (fun ω => (r t ω : WithTop ℝ≥0)) = fun ω => min (τ ω) (t : WithTop ℝ≥0) := by
      funext ω; rw [hr_coe, min_comm]
    rw [this]; exact hτ.min_const t
  have hr_le : ∀ t ω, r t ω ≤ t := fun t ω => by
    rw [← WithTop.coe_le_coe, hr_coe]; exact min_le_left _ _
  have hmin : ∀ ω, min i (r j ω) = r i ω := fun ω => by
    refine WithTop.coe_injective ?_
    rw [WithTop.coe_min, hr_coe, hr_coe, ← min_assoc,
      min_eq_left (show (i : WithTop ℝ≥0) ≤ j from by exact_mod_cast hij)]
  have hint : ∀ t, Integrable (stoppedProcess M τ t) P := fun t =>
    integrable_apply_stoppingTime hM hc (hr_st t) (hr_le t)
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le i) (hint j)
    (fun A _ _ => (hint i).integrableOn) (fun A hA _ => ?_)
    (hprog.stronglyAdapted_stoppedProcess hτ i).aestronglyMeasurable).symm
  have := setIntegral_apply_stoppingTime_eq_min hM hc (hr_st j) (hr_le j) hA
  simp only [hmin] at this
  exact this.symm

end MeasureTheory.Martingale
