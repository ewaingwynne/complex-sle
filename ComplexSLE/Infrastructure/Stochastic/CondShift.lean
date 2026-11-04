/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsContLocalMartingale
public import ComplexSLE.Infrastructure.Stochastic.LocalMartingaleAlgebra
public import Mathlib.Probability.ConditionalProbability

/-!
# Shifting a martingale in time and conditioning on the past

Source-independent stochastic calculus. For a filtration `ℱ`, a deterministic time `s`, a set
`A ∈ ℱ s` with `P A ≠ 0` and the conditional probability `P[|A]`:

* `shiftFiltration ℱ s` is the filtration `t ↦ ℱ (s + t)`;
* `Martingale.shift_cond`: if `N` is an `ℱ`-martingale under `P`, then
  `t ↦ N (s + t) - N s` is a `shiftFiltration ℱ s`-martingale under `P[|A]` (integrals over
  `B ∈ ℱ (s + r)` become integrals over `A ∩ B`);
* `isStronglyProgressive_shift`: shifting preserves progressive measurability;
* `shiftTime s T = (T - s)⁺` and `stoppedProcess_shiftTime`: the stopped process of the shifted
  process at `(T - s)⁺` is the shifted stopped process;
* `IsContLocalMartingale.shift_cond`: `t ↦ M (s + t) - M s` is a continuous local martingale for
  the shifted filtration under `P[|A]` (localising times `(τ n - s)⁺`);
* `IsContLocalMartingale.mul_initial`: the product of an `ℱ 0`-measurable random variable with a
  continuous local martingale started at `0` is a continuous local martingale (localising by
  `1_{|ξ| ≤ n}`), used for the cross term `2 M_s (M_{s+t} - M_s)`.

No external input is used.
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}

/-! ### The shifted filtration -/

/-- The filtration `t ↦ ℱ (s + t)`. -/
@[expose] def shiftFiltration (ℱ : Filtration ℝ≥0 m) (s : ℝ≥0) : Filtration ℝ≥0 m where
  seq t := ℱ (s + t)
  mono' _ _ h := ℱ.mono (add_le_add_right h s)
  le' t := ℱ.le (s + t)

/-! ### Conditional probability: integrals -/

theorem integrable_cond {f : Ω → ℝ} (hf : Integrable f P) {A : Set Ω} (hA0 : P A ≠ 0) :
    Integrable f P[|A] := by
  unfold ProbabilityTheory.cond
  exact hf.restrict.smul_measure (ENNReal.inv_ne_top.2 hA0)

theorem setIntegral_cond {f : Ω → ℝ} {A B : Set Ω} (hB : MeasurableSet B) :
    ∫ ω in B, f ω ∂P[|A] = ((P A)⁻¹).toReal * ∫ ω in B ∩ A, f ω ∂P := by
  unfold ProbabilityTheory.cond
  rw [Measure.restrict_smul, integral_smul_measure, Measure.restrict_restrict hB, smul_eq_mul]

/-- A strongly adapted process with integrable marginals whose conditional expectations over
`ℱ i`-sets agree is a martingale. -/
theorem martingale_of_setIntegral_eq {μ : Measure Ω} [IsFiniteMeasure μ] {f : ℝ≥0 → Ω → ℝ}
    {𝒢 : Filtration ℝ≥0 m} (hadapt : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ)
    (h : ∀ i j, i ≤ j → ∀ B, MeasurableSet[𝒢 i] B → ∫ ω in B, f j ω ∂μ = ∫ ω in B, f i ω ∂μ) :
    Martingale f 𝒢 μ := by
  refine ⟨hadapt, fun i j hij => ?_⟩
  exact (ae_eq_condExp_of_forall_setIntegral_eq (𝒢.le i) (hint j)
    (fun B _ _ => (hint i).integrableOn) (fun B hB _ => (h i j hij B hB).symm)
    (hadapt i).aestronglyMeasurable).symm

/-! ### Martingales: shift and condition -/

theorem _root_.MeasureTheory.Martingale.shift_cond [IsFiniteMeasure P] {N : ℝ≥0 → Ω → ℝ}
    (hN : Martingale N ℱ P)
    (s : ℝ≥0) {A : Set Ω} (hA : MeasurableSet[ℱ s] A) (hA0 : P A ≠ 0) :
    Martingale (fun t ω => N (s + t) ω - N s ω) (shiftFiltration ℱ s) P[|A] := by
  have : IsProbabilityMeasure P[|A] := cond_isProbabilityMeasure hA0
  have hAm : MeasurableSet A := ℱ.le s A hA
  refine martingale_of_setIntegral_eq ?_ ?_ ?_
  · intro t
    exact ((hN.stronglyAdapted (s + t)).sub
      ((hN.stronglyAdapted s).mono (ℱ.mono le_self_add)))
  · intro t
    exact integrable_cond ((hN.integrable (s + t)).sub (hN.integrable s)) hA0
  · intro r t hrt B hB
    have hBm : MeasurableSet B := ℱ.le (s + r) B hB
    have hBA : MeasurableSet[ℱ (s + r)] (B ∩ A) :=
      hB.inter (ℱ.mono le_self_add _ hA)
    rw [setIntegral_cond hBm, setIntegral_cond hBm,
      integral_sub (hN.integrable (s + t)).integrableOn (hN.integrable s).integrableOn,
      integral_sub (hN.integrable (s + r)).integrableOn (hN.integrable s).integrableOn,
      hN.setIntegral_eq (add_le_add_right hrt s) hBA]

/-! ### Progressive measurability -/

/-- Time-shifting preserves progressive measurability (for the shifted filtration). -/
theorem isStronglyProgressive_shift {X : ℝ≥0 → Ω → ℝ} (hX : IsStronglyProgressive ℱ X)
    (s : ℝ≥0) :
    IsStronglyProgressive (shiftFiltration ℱ s) fun t ω => X (s + t) ω := by
  intro i
  let mp : MeasurableSpace (Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ (s + i))
  have hmeas : @Measurable (Iic i × Ω) (Iic (s + i) × Ω) mp
      (Subtype.instMeasurableSpace.prod (ℱ (s + i)))
      fun p => (⟨s + (p.1 : ℝ≥0), add_le_add_right p.1.2 s⟩, p.2) := by
    refine @Measurable.prodMk _ mp _ _ _ _ _ _ ?_ (@measurable_snd _ _ _ (ℱ (s + i)))
    refine Measurable.subtype_mk ?_
    exact measurable_const.add (measurable_subtype_coe.comp (@measurable_fst _ _ _ (ℱ (s + i))))
  exact (hX (s + i)).comp_measurable hmeas

/-- A time-constant random variable that is measurable for the initial σ-algebra is progressive. -/
theorem isStronglyProgressive_of_initial {ℱ' : Filtration ℝ≥0 m} {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ' 0] ξ) : IsStronglyProgressive ℱ' fun _ ω => ξ ω := by
  intro i
  let mp : MeasurableSpace (Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ' i)
  exact (hξ.mono (ℱ'.mono (zero_le : (0 : ℝ≥0) ≤ i))).comp_measurable (@measurable_snd _ _ _ (ℱ' i))

/-! ### Shifted stopping times -/

theorem untopA_coe_nnreal (a : ℝ≥0) : (a : WithTop ℝ≥0).untopA = a := rfl

/-- `(T - s)⁺` for a possibly infinite time `T`. -/
@[expose] def shiftTime (s : ℝ≥0) (T : WithTop ℝ≥0) : WithTop ℝ≥0 := T.map fun v => v - s

theorem shiftTime_le_iff {s u : ℝ≥0} {T : WithTop ℝ≥0} :
    shiftTime s T ≤ (u : WithTop ℝ≥0) ↔ T ≤ ((s + u : ℝ≥0) : WithTop ℝ≥0) := by
  induction T with
  | top =>
    rw [shiftTime, WithTop.map_top]
    exact iff_of_false (fun h => WithTop.coe_ne_top (top_le_iff.1 h))
      (fun h => WithTop.coe_ne_top (top_le_iff.1 h))
  | coe v =>
    rw [shiftTime, WithTop.map_coe, WithTop.coe_le_coe, WithTop.coe_le_coe, tsub_le_iff_left]

theorem le_shiftTime {s t : ℝ≥0} {T : WithTop ℝ≥0} (h : ((s + t : ℝ≥0) : WithTop ℝ≥0) ≤ T) :
    (t : WithTop ℝ≥0) ≤ shiftTime s T := by
  induction T with
  | top => exact le_top
  | coe v =>
    rw [shiftTime, WithTop.map_coe, WithTop.coe_le_coe]
    rw [WithTop.coe_le_coe] at h
    exact le_tsub_of_add_le_left h

theorem isStoppingTime_shiftTime {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) (s : ℝ≥0) :
    IsStoppingTime (shiftFiltration ℱ s) fun ω => shiftTime s (τ ω) := by
  intro u
  have : {ω | shiftTime s (τ ω) ≤ (u : WithTop ℝ≥0)} =
      {ω | τ ω ≤ ((s + u : ℝ≥0) : WithTop ℝ≥0)} := by
    ext ω; exact shiftTime_le_iff
  rw [this]
  exact hτ (s + u)

/-- The stopped process of the shifted process at `(T - s)⁺` is the shifted stopped process. -/
theorem stoppedProcess_shiftTime {M : ℝ≥0 → Ω → ℝ} (s : ℝ≥0) (T : Ω → WithTop ℝ≥0) :
    stoppedProcess (fun t ω => M (s + t) ω - M s ω) (fun ω => shiftTime s (T ω)) =
      fun t ω => stoppedProcess M T (s + t) ω - stoppedProcess M T s ω := by
  funext t ω
  simp only [stoppedProcess]
  generalize T ω = v
  induction v with
  | top =>
    simp only [shiftTime, WithTop.map_top, min_top_right, untopA_coe_nnreal]
  | coe v =>
    simp only [shiftTime, WithTop.map_coe, ← WithTop.coe_min, untopA_coe_nnreal]
    rcases le_total v s with hvs | hsv
    · rw [tsub_eq_zero_of_le hvs, min_eq_right (zero_le : (0 : ℝ≥0) ≤ t), add_zero,
        min_eq_right (hvs.trans le_self_add), min_eq_right hvs, sub_self, sub_self]
    · rw [min_eq_left hsv, ← min_add_add_left, add_tsub_cancel_of_le hsv]

/-! ### Continuous local martingales: shift and condition -/

/-- **Conditioning a continuous local martingale on the past.** If `M` is a continuous local
martingale for `ℱ` under `P`, `A ∈ ℱ s` and `P A ≠ 0`, then `t ↦ M (s + t) - M s` is a continuous
local martingale for the shifted filtration `t ↦ ℱ (s + t)` under `P[|A]`. -/
theorem IsContLocalMartingale.shift_cond [IsFiniteMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : IsContLocalMartingale ℱ M P) (s : ℝ≥0) {A : Set Ω} (hA : MeasurableSet[ℱ s] A)
    (hA0 : P A ≠ 0) :
    IsContLocalMartingale (shiftFiltration ℱ s) (fun t ω => M (s + t) ω - M s ω) P[|A] := by
  obtain ⟨hprog, hcont, τ, hτ, hτev, hmart⟩ := hM
  have hac : P[|A] ≪ P := cond_absolutelyContinuous
  refine ⟨?_, ?_, fun n ω => shiftTime s (τ n ω), fun n => isStoppingTime_shiftTime (hτ n) s,
    ?_, fun n => ?_⟩
  · refine (isStronglyProgressive_shift hprog s).sub (isStronglyProgressive_of_initial ?_)
    exact (hprog.stronglyAdapted s).mono (ℱ.mono (add_zero s).ge)
  · filter_upwards [hac.ae_le hcont] with ω h
    exact (h.comp (continuous_const.add continuous_id)).sub continuous_const
  · filter_upwards [hac.ae_le hτev] with ω hω t
    filter_upwards [hω (s + t)] with n hn
    exact le_shiftTime hn
  · rw [stoppedProcess_shiftTime]
    exact (hmart n).shift_cond s hA hA0

/-! ### Multiplying by an initial random variable -/

/-- A bounded `ℱ 0`-measurable random variable times a martingale is a martingale. -/
theorem _root_.MeasureTheory.Martingale.initial_mul {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ' : Filtration ℝ≥0 m}
    {N : ℝ≥0 → Ω → ℝ} (hN : Martingale N ℱ' μ) {c : Ω → ℝ} (hc : StronglyMeasurable[ℱ' 0] c)
    {C : ℝ} (hC : ∀ ω, |c ω| ≤ C) : Martingale (fun t ω => c ω * N t ω) ℱ' μ := by
  have hcm : ∀ t, StronglyMeasurable[ℱ' t] c := fun t =>
    hc.mono (ℱ'.mono (zero_le : (0 : ℝ≥0) ≤ t))
  have hint : ∀ t, Integrable (fun ω => c ω * N t ω) μ := fun t =>
    (hN.integrable t).bdd_mul ((hcm t).mono (ℱ'.le t)).aestronglyMeasurable
      (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hC ω)
  refine ⟨fun t => (hcm t).mul (hN.stronglyAdapted t), fun i j hij => ?_⟩
  have h1 := condExp_mul_of_stronglyMeasurable_left (hcm i) (hint j) (hN.integrable j)
  have h2 := hN.condExp_ae_eq hij
  filter_upwards [h1, h2] with ω h1 h2
  have : (fun ω => c ω * N j ω) = c * N j := rfl
  rw [this, h1, Pi.mul_apply, h2]

/-- **Initial multiplier.** If `M` is a continuous local martingale with `M 0 = 0` and `ξ` is
`ℱ 0`-measurable, then `ξ M` is a continuous local martingale (localised by `1_{|ξ| ≤ n}`). -/
theorem IsContLocalMartingale.initial_mul {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ' : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ} (hM : IsContLocalMartingale ℱ' M μ)
    (h0 : ∀ ω, M 0 ω = 0) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ' 0] ξ) :
    IsContLocalMartingale ℱ' (fun t ω => ξ ω * M t ω) μ := by
  obtain ⟨hprog, hcont, τ, hτ, hτev, hmart⟩ := hM
  classical
  -- the stopping times `σ n = 0` on `{n < |ξ|}`, `⊤` elsewhere
  let σ : ℕ → Ω → WithTop ℝ≥0 := fun n ω => if |ξ ω| ≤ n then ⊤ else 0
  have hσtop : ∀ (n : ℕ) ω, |ξ ω| ≤ n → σ n ω = ⊤ := fun n ω h => by
    simp only [σ]
    split_ifs
    rfl
  have hσzero : ∀ (n : ℕ) ω, ¬ |ξ ω| ≤ n → σ n ω = 0 := fun n ω h => by
    simp only [σ]
    split_ifs
    rfl
  have hσ : ∀ n, IsStoppingTime ℱ' (σ n) := by
    intro n u
    have hset : {ω | σ n ω ≤ (u : WithTop ℝ≥0)} = {ω | (n : ℝ) < |ξ ω|} := by
      ext ω
      by_cases h : |ξ ω| ≤ n
      · rw [mem_ofPred_eq, mem_ofPred_eq, hσtop n ω h]
        exact iff_of_false (fun h' => WithTop.coe_ne_top (top_le_iff.1 h')) (not_lt.2 h)
      · rw [mem_ofPred_eq, mem_ofPred_eq, hσzero n ω h]
        exact iff_of_true zero_le (not_le.1 h)
    rw [hset]
    have hm : MeasurableSet[ℱ' 0] {ω | (n : ℝ) < |ξ ω|} :=
      measurableSet_lt measurable_const (continuous_abs.comp_stronglyMeasurable hξ).measurable
    exact ℱ'.mono (zero_le : (0 : ℝ≥0) ≤ u) _ hm
  refine ⟨(isStronglyProgressive_of_initial hξ).mul hprog, ?_, fun n ω => min (τ n ω) (σ n ω),
    fun n => (hτ n).min (hσ n), ?_, fun n => ?_⟩
  · filter_upwards [hcont] with ω h using h.const_smul (ξ ω)
  · filter_upwards [hτev] with ω hω t
    obtain ⟨k, hk⟩ := exists_nat_ge |ξ ω|
    filter_upwards [hω t, eventually_ge_atTop k] with n hn hkn
    refine le_min hn ?_
    have : |ξ ω| ≤ n := hk.trans (by exact_mod_cast hkn)
    rw [hσtop n ω this]
    exact le_top
  · -- the stopped process is `(ξ 1_{|ξ| ≤ n}) · M^{τ n}`
    have hfun : stoppedProcess (fun t ω => ξ ω * M t ω) (fun ω => min (τ n ω) (σ n ω)) =
        fun t ω => (if |ξ ω| ≤ n then ξ ω else 0) * stoppedProcess M (τ n) t ω := by
      funext t ω
      by_cases h : |ξ ω| ≤ n
      · simp only [stoppedProcess, hσtop n ω h, min_top_right, h, ite_true]
      · simp only [stoppedProcess, hσzero n ω h, zero_mul, h, ite_false]
        rw [min_eq_right zero_le, min_eq_right zero_le]
        have : ((0 : WithTop ℝ≥0)).untopA = 0 := rfl
        rw [this, h0, mul_zero]
    rw [hfun]
    refine (hmart n).initial_mul (c := fun ω => if |ξ ω| ≤ n then ξ ω else 0) (C := n) ?_ ?_
    · have hmeas : MeasurableSet[ℱ' 0] {ω | |ξ ω| ≤ n} :=
        measurableSet_le (continuous_abs.comp_stronglyMeasurable hξ).measurable measurable_const
      exact StronglyMeasurable.ite hmeas hξ stronglyMeasurable_const
    · intro ω
      by_cases h : |ξ ω| ≤ n
      · simp [h]
      · simp only [h, ite_false, abs_zero]
        exact (Nat.cast_nonneg n)

end ComplexSLE

end
