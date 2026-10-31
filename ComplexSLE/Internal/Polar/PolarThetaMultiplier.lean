/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Stochastic.LocalMartingaleAlgebra
public import ComplexSLE.Infrastructure.Stochastic.ProgressiveTools

/-!
# Multipliers measurable at a stopping time, and cross brackets of differently stopped processes
(M6/S11, stochastic infrastructure for `step:polar-real-imag`, imaginary part)

Source-independent stochastic calculus used by the Itô step for the argument `θ`, where the state
fed to Itô's formula contains `f` stopped at two successive sector times `ρ ≤ σ`.

* `martingale_mul_sub_min`, `IsContLocalMartingale.mul_sub_min`: if `M` is a continuous
  (local) martingale, `ρ` a finite stopping time and `V` a bounded random variable with
  `V 1_{ρ ≤ u}` `ℱ_u`-measurable for every `u` (i.e. `V` is `ℱ_ρ`-measurable), then
  `V (M_t - M_{t ∧ ρ})` is a continuous (local) martingale. The martingale property is checked on
  `A ∈ ℱ_s`: on `{ρ ≤ s}` the multiplier is `ℱ_s`-measurable; on `{s < ρ}` the increment is
  `M_t - M_{t ∧ ρ}` and the multiplier is `ℱ_{ρ ∧ t}`-measurable, so that optional sampling at the
  bounded stopping time `ρ ∧ t` applies (dyadic approximation from above with countable range,
  Mathlib's discrete optional sampling, and an `L¹` limit as in `ContinuousOptionalStopping.lean`).
* `isContLocalMartingale_min_mul_min`: if `M N - A` is a continuous local martingale (`A` the
  bracket), `N` is bounded and `ρ ≤ σ`, then `M^σ N^ρ - A^ρ` is a continuous local martingale:
  `M^σ N^ρ - A^ρ = [N_ρ (M - M^ρ)]^σ + (M N - A)^ρ`.
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Internal.Polar

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}

/-! ### Elementary facts about `min` with finite stopping times -/

theorem stoppedProcess_coe_min {β : Type*} (M : ℝ≥0 → Ω → β) (ρ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    stoppedProcess M (fun ω => (ρ ω : WithTop ℝ≥0)) t ω = M (min t (ρ ω)) ω := by
  simp only [stoppedProcess]
  rw [← WithTop.coe_min]
  rfl

theorem min_coe_le_coe_iff (r t u : ℝ≥0) :
    min (r : WithTop ℝ≥0) (t : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0) ↔ r ≤ u ∨ t ≤ u := by
  rw [← WithTop.coe_min, WithTop.coe_le_coe, min_le_iff]

theorem untopA_coe' (a : ℝ≥0) : ((a : WithTop ℝ≥0)).untopA = a := by
  rw [WithTop.untopA_eq_untop WithTop.coe_ne_top]; rfl

theorem untopA_min_coe_min (t r : ℝ≥0) (c : WithTop ℝ≥0) :
    (min ((min t r : ℝ≥0) : WithTop ℝ≥0) c).untopA = min (min (t : WithTop ℝ≥0) c).untopA r := by
  cases c with
  | top => rw [min_eq_left le_top, min_eq_left le_top, untopA_coe', untopA_coe']
  | coe a =>
    rw [← WithTop.coe_min, ← WithTop.coe_min, untopA_coe', untopA_coe', min_right_comm]

/-- An `ℝ≥0`-valued function whose cut-offs `V 1_{ρ ≤ u}` are `ℱ_u`-measurable is measurable. -/
theorem measurable_of_measurable_ite_le {ρ : Ω → ℝ≥0} {V : Ω → ℝ}
    (hV : ∀ u : ℝ≥0, Measurable[ℱ u] fun ω => if ρ ω ≤ u then V ω else 0) : Measurable V := by
  refine measurable_of_tendsto_metrizable (f := fun k : ℕ => fun ω => if ρ ω ≤ k then V ω else 0)
    (fun k => (hV k).mono (ℱ.le k) le_rfl) ?_
  rw [tendsto_pi_nhds]
  intro ω
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈ρ ω⌉₊] with k hk
  have : ρ ω ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  simp [this]

/-! ### Martingale identities with bounded multipliers -/

section Multiplier

variable [IsFiniteMeasure P] {M : ℝ≥0 → Ω → ℝ}

/-- The martingale property with a bounded `ℱ_s`-measurable multiplier. -/
theorem integral_mul_eq_of_martingale (hM : Martingale M ℱ P) {s t : ℝ≥0} (hst : s ≤ t)
    {g : Ω → ℝ} (hg : StronglyMeasurable[ℱ s] g) {C : ℝ} (hgb : ∀ ω, |g ω| ≤ C) :
    ∫ ω, g ω * M t ω ∂P = ∫ ω, g ω * M s ω ∂P := by
  have hgm : AEStronglyMeasurable g P := (hg.mono (ℱ.le s)).aestronglyMeasurable
  have hint : Integrable (g * M t) P :=
    (hM.integrable t).bdd_mul hgm (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hgb ω)
  have h1 := condExp_mul_of_stronglyMeasurable_left (μ := P) hg hint (hM.integrable t)
  have h2 := hM.condExp_ae_eq hst
  have : SigmaFinite (P.trim (ℱ.le s)) := inferInstance
  calc ∫ ω, g ω * M t ω ∂P = ∫ ω, (P[g * M t | ℱ s]) ω ∂P := (integral_condExp (ℱ.le s)).symm
    _ = ∫ ω, g ω * M s ω ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [h1, h2] with ω hω1 hω2
      rw [hω1, Pi.mul_apply, hω2]

/-- Optional sampling with a bounded `ℱ_ρ`-measurable multiplier, for a bounded stopping time
with countable range. -/
theorem integral_mul_apply_eq_of_countable (hM : Martingale M ℱ P) {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0)) (hcount : (range ρ).Countable)
    {n : ℝ≥0} (hle : ∀ ω, ρ ω ≤ n) {g : Ω → ℝ} (hg : Measurable[hρ.measurableSpace] g)
    {C : ℝ} (hgb : ∀ ω, |g ω| ≤ C) :
    ∫ ω, g ω * M (ρ ω) ω ∂P = ∫ ω, g ω * M n ω ∂P := by
  have hcond := Infrastructure.stoppedValue_ae_eq_condExp_nnreal hM hρ hcount hle
  have hgm : AEStronglyMeasurable g P := (hg.mono hρ.measurableSpace_le le_rfl).aestronglyMeasurable
  have hint : Integrable (g * M n) P :=
    (hM.integrable n).bdd_mul hgm (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hgb ω)
  have h1 := condExp_mul_of_stronglyMeasurable_left (μ := P) hg.stronglyMeasurable hint
    (hM.integrable n)
  have : SigmaFinite (P.trim hρ.measurableSpace_le) := inferInstance
  calc ∫ ω, g ω * M (ρ ω) ω ∂P = ∫ ω, (P[g * M n | hρ.measurableSpace]) ω ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [h1, hcond] with ω hω1 hω2
        rw [hω1, Pi.mul_apply, hω2]
    _ = ∫ ω, g ω * M n ω ∂P := integral_condExp hρ.measurableSpace_le

/-- `L¹` limit with a bounded multiplier: for countable-range stopping times `ρ k ≤ n` converging
to `r` and a continuous martingale `M`, `∫ g M_{ρ k} → ∫ g M_r`. -/
theorem tendsto_integral_mul_apply (hM : Martingale M ℱ P) (hc : ∀ ω, Continuous fun t => M t ω)
    {n : ℝ≥0} {ρ : ℕ → Ω → ℝ≥0} (hρ : ∀ k, IsStoppingTime ℱ fun ω => (ρ k ω : WithTop ℝ≥0))
    (hcount : ∀ k, (range (ρ k)).Countable) (hle : ∀ k ω, ρ k ω ≤ n) {r : Ω → ℝ≥0}
    (hlim : ∀ ω, Tendsto (fun k => ρ k ω) atTop (𝓝 (r ω))) {g : Ω → ℝ}
    (hg : AEStronglyMeasurable g P) {C : ℝ} (hgb : ∀ ω, |g ω| ≤ C) :
    Tendsto (fun k => ∫ ω, g ω * M (ρ k ω) ω ∂P) atTop (𝓝 (∫ ω, g ω * M (r ω) ω ∂P)) := by
  have hUI0 : UniformIntegrable (fun k => P[M n | (hρ k).measurableSpace]) 1 P :=
    (hM.integrable n).uniformIntegrable_condExp fun k => (hρ k).measurableSpace_le
  have hUI : UniformIntegrable (fun k ω => M (ρ k ω) ω) 1 P :=
    hUI0.ae_eq fun k =>
      (Infrastructure.stoppedValue_ae_eq_condExp_nnreal hM (hρ k) (hcount k) (hle k)).symm
  have hlim' : ∀ᵐ ω ∂P, Tendsto (fun k => M (ρ k ω) ω) atTop (𝓝 (M (r ω) ω)) :=
    ae_of_all _ fun ω => ((hc ω).tendsto (r ω)).comp (hlim ω)
  have hint : Integrable (fun ω => M (r ω) ω) P := hUI.integrable_of_ae_tendsto hlim'
  have hL1 := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
    (fun k => hUI.aestronglyMeasurable k) (memLp_one_iff_integrable.2 hint) hUI.unifIntegrable
    hlim'
  have hgb' : ∀ ω, ‖g ω‖ ≤ C := fun ω => by rw [Real.norm_eq_abs]; exact hgb ω
  refine tendsto_integral_of_L1 (fun ω => g ω * M (r ω) ω) (hg.mul hint.aestronglyMeasurable)
    (Eventually.of_forall fun k =>
      (Infrastructure.integrable_apply_nnreal hM (hρ k) (hcount k) (hle k)).bdd_mul hg
        (ae_of_all _ hgb')) ?_
  have hbound : ∀ k, ∫⁻ ω, ‖g ω * M (ρ k ω) ω - g ω * M (r ω) ω‖ₑ ∂P ≤
      ENNReal.ofReal C * eLpNorm ((fun ω => M (ρ k ω) ω) - fun ω => M (r ω) ω) 1 P := by
    intro k
    rw [eLpNorm_one_eq_lintegral_enorm ((hUI.aestronglyMeasurable k).sub hint.aestronglyMeasurable),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ω => ?_
    rw [← mul_sub, enorm_mul, Pi.sub_apply]
    gcongr
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hgb' ω)
  have hmul : Tendsto (fun k => ENNReal.ofReal C *
      eLpNorm ((fun ω => M (ρ k ω) ω) - fun ω => M (r ω) ω) 1 P) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) hL1 (Or.inr ENNReal.ofReal_ne_top)
    rwa [mul_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul (fun _ => zero_le)
    hbound

/-- **Optional sampling at `ρ ∧ t` with a bounded `ℱ_{ρ ∧ t}`-measurable multiplier**, for a
continuous martingale and a finite stopping time `ρ`. -/
theorem integral_mul_min_eq (hM : Martingale M ℱ P) (hc : ∀ ω, Continuous fun t => M t ω)
    {ρ : Ω → ℝ≥0} (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0)) (t : ℝ≥0) {g : Ω → ℝ}
    (hg : Measurable[(hρ.min_const t).measurableSpace] g) {C : ℝ} (hgb : ∀ ω, |g ω| ≤ C) :
    ∫ ω, g ω * M (min t (ρ ω)) ω ∂P = ∫ ω, g ω * M t ω ∂P := by
  let ρk : ℕ → Ω → ℝ≥0 := fun k ω => min t (Infrastructure.dyadicCeil k (ρ ω))
  have hρk : ∀ k, IsStoppingTime ℱ fun ω => (ρk k ω : WithTop ℝ≥0) := fun k =>
    Infrastructure.isStoppingTime_min_const_nnreal (Infrastructure.isStoppingTime_dyadicCeil hρ k) t
  have hcount : ∀ k, (range (ρk k)).Countable := fun k =>
    Infrastructure.countable_range_min_const (Infrastructure.countable_range_dyadicCeil ρ k) t
  have hle : ∀ k ω, ρk k ω ≤ t := fun k ω => min_le_left _ _
  have hlim : ∀ ω, Tendsto (fun k => ρk k ω) atTop (𝓝 (min t (ρ ω))) := fun ω =>
    tendsto_const_nhds.min (Infrastructure.tendsto_dyadicCeil (ρ ω))
  have hmono : ∀ k, (hρ.min_const t).measurableSpace ≤ (hρk k).measurableSpace := fun k =>
    IsStoppingTime.measurableSpace_mono _ _ fun ω => by
      simp only [ρk]
      rw [WithTop.coe_min, min_comm]
      exact min_le_min_left _ (WithTop.coe_le_coe.2 (Infrastructure.le_dyadicCeil k _))
  have heq : ∀ k, ∫ ω, g ω * M (ρk k ω) ω ∂P = ∫ ω, g ω * M t ω ∂P := fun k =>
    integral_mul_apply_eq_of_countable hM (hρk k) (hcount k) (hle k)
      (hg.mono (hmono k) le_rfl) hgb
  have hgm : AEStronglyMeasurable g P :=
    (hg.mono (hρ.min_const t).measurableSpace_le le_rfl).aestronglyMeasurable
  have hlimit := tendsto_integral_mul_apply hM hc hρk hcount hle hlim hgm hgb
  simp only [heq] at hlimit
  exact tendsto_nhds_unique hlimit tendsto_const_nhds

/-! ### `ℱ_{ρ ∧ t}`-measurability of cut-offs -/

/-- If `V 1_{ρ ≤ u}` is `ℱ_u`-measurable for every `u`, then `V 1_{ρ ≤ t}` is
`ℱ_{ρ ∧ t}`-measurable. -/
theorem measurable_ite_le_min_const {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0)) {V : Ω → ℝ}
    (hV : ∀ u : ℝ≥0, Measurable[ℱ u] fun ω => if ρ ω ≤ u then V ω else 0) (t : ℝ≥0) :
    Measurable[(hρ.min_const t).measurableSpace] fun ω => if ρ ω ≤ t then V ω else 0 := by
  intro E hE
  rw [IsStoppingTime.measurableSet]
  refine ⟨le_iSup (fun u => ℱ u) t _ (hV t hE), fun u => ?_⟩
  by_cases htu : t ≤ u
  · have : {ω | min ((ρ ω : WithTop ℝ≥0)) (t : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0)} = univ := by
      ext ω
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact (min_le_right _ _).trans (WithTop.coe_le_coe.2 htu)
    rw [this, inter_univ]
    exact ℱ.mono htu _ (hV t hE)
  · replace htu : u < t := lt_of_not_ge htu
    have : (fun ω => if ρ ω ≤ t then V ω else 0) ⁻¹' E ∩
        {ω | min ((ρ ω : WithTop ℝ≥0)) (t : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0)} =
        (fun ω => if ρ ω ≤ u then V ω else 0) ⁻¹' E ∩ {ω | ρ ω ≤ u} := by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, min_coe_le_coe_iff, not_le.mpr htu,
        or_false]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        simp only [h2.trans (le_of_lt htu), ↓reduceIte] at h1
        simpa only [h2, ↓reduceIte]
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        simp only [h2, ↓reduceIte] at h1
        simpa only [h2.trans (le_of_lt htu), ↓reduceIte]
    rw [this]
    exact (hV u hE).inter (Infrastructure.measurableSet_nnreal_le hρ u)

/-- For `A ∈ ℱ_s` and `s ≤ t`, the set `A ∩ {s < ρ}` is `ℱ_{ρ ∧ t}`-measurable. -/
theorem measurableSet_inter_lt_min_const' {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0)) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω}
    (hA : MeasurableSet[ℱ s] A) :
    MeasurableSet[(hρ.min_const t).measurableSpace] (A ∩ {ω | s < ρ ω}) := by
  have hlt : MeasurableSet[ℱ s] {ω | s < ρ ω} := by
    have : {ω | s < ρ ω} = {ω | ρ ω ≤ s}ᶜ := by ext ω; simp
    rw [this]; exact (Infrastructure.measurableSet_nnreal_le hρ s).compl
  rw [IsStoppingTime.measurableSet]
  refine ⟨le_iSup (fun u => ℱ u) s _ (hA.inter hlt), fun u => ?_⟩
  by_cases htu : t ≤ u
  · have : {ω | min ((ρ ω : WithTop ℝ≥0)) (t : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0)} = univ := by
      ext ω
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact (min_le_right _ _).trans (WithTop.coe_le_coe.2 htu)
    rw [this, inter_univ]
    exact ℱ.mono (hst.trans htu) _ (hA.inter hlt)
  · replace htu : u < t := lt_of_not_ge htu
    have hset : {ω | min ((ρ ω : WithTop ℝ≥0)) (t : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0)} =
        {ω | ρ ω ≤ u} := by
      ext ω; simp only [mem_ofPred_eq, min_coe_le_coe_iff, not_le.mpr htu, or_false]
    rw [hset]
    by_cases hsu : s ≤ u
    · exact (ℱ.mono hsu _ (hA.inter hlt)).inter (Infrastructure.measurableSet_nnreal_le hρ u)
    · replace hsu : u < s := lt_of_not_ge hsu
      have : A ∩ {ω | s < ρ ω} ∩ {ω | ρ ω ≤ u} = ∅ := by
        ext ω
        simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        rintro ⟨-, h1⟩ h2
        exact absurd (lt_of_lt_of_le h1 h2) (not_lt.mpr (le_of_lt hsu))
      rw [this]
      exact @MeasurableSet.empty _ (ℱ u)

/-! ### The martingale `V (M - M^ρ)` -/

/-- **Bounded `ℱ_ρ`-measurable multiplier of a post-`ρ` increment.** For a continuous martingale
`M`, a finite stopping time `ρ` and a bounded `V` with `V 1_{ρ ≤ u}` `ℱ_u`-measurable for every
`u`, the process `V (M_t - M_{t ∧ ρ})` is a martingale. -/
theorem martingale_mul_sub_min (hM : Martingale M ℱ P) (hc : ∀ ω, Continuous fun t => M t ω)
    {ρ : Ω → ℝ≥0} (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0)) {V : Ω → ℝ} {C : ℝ}
    (hVb : ∀ ω, |V ω| ≤ C) (hV : ∀ u : ℝ≥0, Measurable[ℱ u] fun ω => if ρ ω ≤ u then V ω else 0) :
    Martingale (fun t ω => V ω * (M t ω - M (min t (ρ ω)) ω)) ℱ P := by
  have hprog : IsStronglyProgressive ℱ M := hM.stronglyAdapted.isStronglyProgressive_of_continuous hc
  have hVm : Measurable V := measurable_of_measurable_ite_le hV
  -- the stopped process is adapted
  have hstop : ∀ t, StronglyMeasurable[ℱ t] fun ω => M (min t (ρ ω)) ω := fun t => by
    have h := hprog.stronglyAdapted_stoppedProcess hρ t
    have e : stoppedProcess M (fun ω => (ρ ω : WithTop ℝ≥0)) t = fun ω => M (min t (ρ ω)) ω :=
      funext fun ω => stoppedProcess_coe_min M ρ t ω
    rw [e] at h
    exact h
  -- `Z t = W t * (M t - M (t ∧ ρ))`
  have hZ : ∀ t ω, V ω * (M t ω - M (min t (ρ ω)) ω) =
      (if ρ ω ≤ t then V ω else 0) * (M t ω - M (min t (ρ ω)) ω) := by
    intro t ω
    split_ifs with h
    · rfl
    · replace h : t < ρ ω := lt_of_not_ge h
      rw [min_eq_left h.le, sub_self, mul_zero, mul_zero]
  have hint : ∀ t, Integrable (fun ω => V ω * (M t ω - M (min t (ρ ω)) ω)) P := fun t =>
    ((hM.integrable t).sub (Infrastructure.integrable_apply_stoppingTime hM hc
      (Infrastructure.isStoppingTime_min_const_nnreal hρ t) fun ω => min_le_left _ _)).bdd_mul
      hVm.aestronglyMeasurable (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hVb ω)
  have hadapted : ∀ t, StronglyMeasurable[ℱ t] fun ω => V ω * (M t ω - M (min t (ρ ω)) ω) := by
    intro t
    simp only [hZ]
    exact (hV t).stronglyMeasurable.mul ((hM.stronglyAdapted t).sub (hstop t))
  refine ⟨hadapted, fun s t hst => ?_⟩
  have : SigmaFinite (P.trim (ℱ.le s)) := inferInstance
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) (hint t)
    (fun A _ _ => (hint s).integrableOn) (fun A hA _ => ?_)
    (hadapted s).aestronglyMeasurable).symm
  -- the two multipliers
  set g₁ : Ω → ℝ := A.indicator fun ω => if ρ ω ≤ s then V ω else 0 with hg₁
  set g₂ : Ω → ℝ := (A ∩ {ω | s < ρ ω}).indicator fun ω => if ρ ω ≤ t then V ω else 0 with hg₂
  have hAm : MeasurableSet A := ℱ.le s A hA
  have hC0 : ∀ ω, |(0 : ℝ)| ≤ C := fun ω => by
    rw [abs_zero]; exact (abs_nonneg _).trans (hVb ω)
  have hg₁b : ∀ ω, |g₁ ω| ≤ C := fun ω => by
    simp only [hg₁, indicator]
    split_ifs <;> first | exact hVb ω | exact hC0 ω
  have hg₂b : ∀ ω, |g₂ ω| ≤ C := fun ω => by
    simp only [hg₂, indicator]
    split_ifs <;> first | exact hVb ω | exact hC0 ω
  have hg₁m : StronglyMeasurable[ℱ s] g₁ := (hV s).stronglyMeasurable.indicator hA
  have hg₂m : Measurable[(hρ.min_const t).measurableSpace] g₂ :=
    (measurable_ite_le_min_const hρ hV t).indicator (measurableSet_inter_lt_min_const' hρ hst hA)
  -- pointwise decomposition of the increment
  have hdecomp : ∀ ω, A.indicator (fun ω => V ω * (M t ω - M (min t (ρ ω)) ω)) ω -
      A.indicator (fun ω => V ω * (M s ω - M (min s (ρ ω)) ω)) ω =
      g₁ ω * (M t ω - M s ω) + g₂ ω * (M t ω - M (min t (ρ ω)) ω) := by
    intro ω
    by_cases hωA : ω ∈ A
    · rw [indicator_of_mem hωA, indicator_of_mem hωA, hg₁, indicator_of_mem hωA, hg₂]
      by_cases hρs : ρ ω ≤ s
      · have hρt : ρ ω ≤ t := le_trans hρs hst
        have hns : ω ∉ A ∩ {ω | s < ρ ω} := fun h => (not_lt.mpr hρs) h.2
        rw [indicator_of_notMem hns, if_pos hρs, min_eq_right hρs, min_eq_right hρt]
        ring
      · have hsρ : s < ρ ω := lt_of_not_ge hρs
        rw [indicator_of_mem (⟨hωA, hsρ⟩ : ω ∈ A ∩ {ω | s < ρ ω}), if_neg hρs,
          min_eq_left (le_of_lt hsρ), sub_self, mul_zero, sub_zero, zero_mul, zero_add]
        split_ifs with hρt
        · rfl
        · have htρ : t < ρ ω := lt_of_not_ge hρt
          rw [min_eq_left (le_of_lt htρ), sub_self, mul_zero, mul_zero]
    · rw [indicator_of_notMem hωA, indicator_of_notMem hωA, hg₁, indicator_of_notMem hωA, hg₂,
        indicator_of_notMem (fun h : ω ∈ A ∩ {ω | s < ρ ω} => hωA h.1)]
      ring
  -- the two integrals vanish
  have hi1 : ∫ ω, g₁ ω * (M t ω - M s ω) ∂P = 0 := by
    have hA1 : Integrable (fun ω => g₁ ω * M t ω) P :=
      (hM.integrable t).bdd_mul (hg₁m.mono (ℱ.le s)).aestronglyMeasurable
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hg₁b ω)
    have hA2 : Integrable (fun ω => g₁ ω * M s ω) P :=
      (hM.integrable s).bdd_mul (hg₁m.mono (ℱ.le s)).aestronglyMeasurable
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hg₁b ω)
    simp only [mul_sub]
    rw [integral_sub hA1 hA2, integral_mul_eq_of_martingale hM hst hg₁m hg₁b, sub_self]
  have hi2 : ∫ ω, g₂ ω * (M t ω - M (min t (ρ ω)) ω) ∂P = 0 := by
    have hg₂am : AEStronglyMeasurable g₂ P :=
      (hg₂m.mono (hρ.min_const t).measurableSpace_le le_rfl).aestronglyMeasurable
    have hA1 : Integrable (fun ω => g₂ ω * M t ω) P :=
      (hM.integrable t).bdd_mul hg₂am (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hg₂b ω)
    have hA2 : Integrable (fun ω => g₂ ω * M (min t (ρ ω)) ω) P :=
      (Infrastructure.integrable_apply_stoppingTime hM hc
        (Infrastructure.isStoppingTime_min_const_nnreal hρ t) fun ω => min_le_left _ _).bdd_mul
        hg₂am (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hg₂b ω)
    simp only [mul_sub]
    rw [integral_sub hA1 hA2, integral_mul_min_eq hM hc hρ t hg₂m hg₂b, sub_self]
  -- assemble
  have hintA : ∀ u, Integrable (A.indicator fun ω => V ω * (M u ω - M (min u (ρ ω)) ω)) P :=
    fun u => (hint u).indicator hAm
  have hsub : ∫ ω in A, V ω * (M t ω - M (min t (ρ ω)) ω) ∂P -
      ∫ ω in A, V ω * (M s ω - M (min s (ρ ω)) ω) ∂P = 0 := by
    rw [← integral_indicator hAm, ← integral_indicator hAm, ← integral_sub (hintA t) (hintA s)]
    simp only [hdecomp]
    have hI1 : Integrable (fun ω => g₁ ω * (M t ω - M s ω)) P :=
      ((hM.integrable t).sub (hM.integrable s)).bdd_mul (hg₁m.mono (ℱ.le s)).aestronglyMeasurable
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hg₁b ω)
    have hI2 : Integrable (fun ω => g₂ ω * (M t ω - M (min t (ρ ω)) ω)) P :=
      ((hM.integrable t).sub (Infrastructure.integrable_apply_stoppingTime hM hc
        (Infrastructure.isStoppingTime_min_const_nnreal hρ t) fun ω => min_le_left _ _)).bdd_mul
        (hg₂m.mono (hρ.min_const t).measurableSpace_le le_rfl).aestronglyMeasurable
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hg₂b ω)
    rw [integral_add hI1 hI2, hi1, hi2, add_zero]
  exact (sub_eq_zero.1 hsub).symm

end Multiplier

/-! ### Local martingale versions -/

section LocalMartingale

variable [IsProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ}

/-- The cut-off process `(u, ω) ↦ V ω 1_{ρ ω ≤ u}` is progressive (adapted and right-continuous). -/
theorem isStronglyProgressive_ite_le {ρ : Ω → ℝ≥0} {V : Ω → ℝ}
    (hV : ∀ u : ℝ≥0, Measurable[ℱ u] fun ω => if ρ ω ≤ u then V ω else 0) :
    IsStronglyProgressive ℱ fun u ω => if ρ ω ≤ u then V ω else 0 := by
  refine StronglyAdapted.isStronglyProgressive_of_rightContinuous
    (fun u => (hV u).stronglyMeasurable) fun ω r => ?_
  by_cases h : ρ ω ≤ r
  · refine (continuousWithinAt_const (b := V ω)).congr (fun u hu => ?_) ?_
    · simp [le_trans h hu]
    · simp [h]
  · replace h : r < ρ ω := lt_of_not_ge h
    refine (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds h)] with u hu
      simp [not_le.mpr hu]
    · simp [not_le.mpr h]

/-- **Bounded `ℱ_ρ`-measurable multiplier of a post-`ρ` increment, local version.** -/
theorem _root_.ComplexSLE.IsContLocalMartingale.mul_sub_min (hM : IsContLocalMartingale ℱ M P)
    (hMc : ∀ ω, Continuous fun t => M t ω) {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0)) {V : Ω → ℝ} {C : ℝ}
    (hVb : ∀ ω, |V ω| ≤ C) (hV : ∀ u : ℝ≥0, Measurable[ℱ u] fun ω => if ρ ω ≤ u then V ω else 0) :
    IsContLocalMartingale ℱ (fun t ω => V ω * (M t ω - M (min t (ρ ω)) ω)) P := by
  obtain ⟨hprog, -, τ, hτ, hτev, hmart⟩ := hM
  have hZ : (fun t ω => V ω * (M t ω - M (min t (ρ ω)) ω)) =
      fun t ω => (if ρ ω ≤ t then V ω else 0) * (M t ω - M (min t (ρ ω)) ω) := by
    funext t ω
    split_ifs with h
    · rfl
    · replace h : t < ρ ω := lt_of_not_ge h
      rw [min_eq_left h.le, sub_self, mul_zero, mul_zero]
  refine ⟨?_, ae_of_all _ fun ω => ?_, τ, hτ, hτev, fun n => ?_⟩
  · rw [hZ]
    intro i
    have h1 := hprog.stoppedProcess hρ
    simp only [funext fun t => funext fun ω => stoppedProcess_coe_min M ρ t ω] at h1
    exact (isStronglyProgressive_ite_le hV i).mul ((hprog i).sub (h1 i))
  · exact continuous_const.mul ((hMc ω).sub ((hMc ω).comp (continuous_id.min continuous_const)))
  · have h := martingale_mul_sub_min (hmart n) (continuous_stoppedProcess hMc (τ n)) hρ hVb hV
    have e : stoppedProcess (fun t ω => V ω * (M t ω - M (min t (ρ ω)) ω)) (τ n) =
        fun t ω => V ω * (stoppedProcess M (τ n) t ω - stoppedProcess M (τ n) (min t (ρ ω)) ω) := by
      funext t ω
      simp only [stoppedProcess, untopA_min_coe_min]
    rw [e]
    exact h

/-- **Cross bracket of differently stopped processes.** If `M N - A` is a continuous local
martingale (so that `A` is the bracket of `M` and `N`), `N` is bounded and progressive with
continuous paths, and `ρ ≤ σ` are finite stopping times, then `M^σ N^ρ - A^ρ` is a continuous
local martingale. -/
theorem isContLocalMartingale_min_mul_min {N A : ℝ≥0 → Ω → ℝ}
    (hM : IsContLocalMartingale ℱ M P) (hMc : ∀ ω, Continuous fun t => M t ω)
    (hN : IsStronglyProgressive ℱ N) (hNc : ∀ ω, Continuous fun t => N t ω) {C : ℝ}
    (hNb : ∀ t ω, |N t ω| ≤ C)
    (hMN : IsContLocalMartingale ℱ (fun t ω => M t ω * N t ω - A t ω) P)
    (hMNc : ∀ ω, Continuous fun t => M t ω * N t ω - A t ω)
    {ρ σ : Ω → ℝ≥0} (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0))
    (hσ : IsStoppingTime ℱ fun ω => (σ ω : WithTop ℝ≥0)) (hρσ : ∀ ω, ρ ω ≤ σ ω) :
    IsContLocalMartingale ℱ
      (fun t ω => M (min t (σ ω)) ω * N (min t (ρ ω)) ω - A (min t (ρ ω)) ω) P := by
  have hV : ∀ u : ℝ≥0, Measurable[ℱ u] fun ω => if ρ ω ≤ u then N (ρ ω) ω else 0 := by
    intro u
    have h1 : StronglyMeasurable[ℱ u] fun ω => N (min u (ρ ω)) ω := by
      have h := hN.stronglyAdapted_stoppedProcess hρ u
      have e : stoppedProcess N (fun ω => (ρ ω : WithTop ℝ≥0)) u = fun ω => N (min u (ρ ω)) ω :=
        funext fun ω => stoppedProcess_coe_min N ρ u ω
      rw [e] at h
      exact h
    have : (fun ω => if ρ ω ≤ u then N (ρ ω) ω else 0) =
        fun ω => if ρ ω ≤ u then N (min u (ρ ω)) ω else 0 := by
      funext ω
      split_ifs with h
      · rw [min_eq_right h]
      · rfl
    rw [this]
    exact Measurable.ite (Infrastructure.measurableSet_nnreal_le hρ u) h1.measurable
      measurable_const
  have h1 := (hM.mul_sub_min hMc hρ (V := fun ω => N (ρ ω) ω) (fun ω => hNb _ ω) hV)
  have h1c : ∀ ω, Continuous fun t => N (ρ ω) ω * (M t ω - M (min t (ρ ω)) ω) := fun ω =>
    continuous_const.mul ((hMc ω).sub ((hMc ω).comp (continuous_id.min continuous_const)))
  have h1s := h1.stopped_min_of_continuous ℱ h1c hσ
  have h2 := hMN.stopped_min_of_continuous ℱ hMNc hρ
  have h2c : ∀ ω, Continuous fun t => M (min t (ρ ω)) ω * N (min t (ρ ω)) ω - A (min t (ρ ω)) ω :=
    fun ω => (hMNc ω).comp (continuous_id.min continuous_const)
  have h1sc : ∀ ω, Continuous fun t => N (ρ ω) ω *
      (M (min t (σ ω)) ω - M (min (min t (σ ω)) (ρ ω)) ω) := fun ω =>
    (h1c ω).comp (continuous_id.min continuous_const)
  have hsum := h1s.add h2 h1sc h2c
  convert hsum using 1
  funext t ω
  simp only [Pi.add_apply]
  have hmin : min (min t (σ ω)) (ρ ω) = min t (ρ ω) := by
    rw [min_assoc, min_eq_right (hρσ ω)]
  rw [hmin]
  by_cases h : ρ ω ≤ t
  · rw [min_eq_right h]; ring
  · have h' : t < ρ ω := lt_of_not_ge h
    rw [min_eq_left (le_of_lt h'), min_eq_left (le_trans (le_of_lt h') (hρσ ω))]; ring

end LocalMartingale

end ComplexSLE.Internal.Polar

end
