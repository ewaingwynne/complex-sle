/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsContLocalMartingale
public import ComplexSLE.Infrastructure.Stochastic.StoppedLocalMartingale
public import ComplexSLE.Infrastructure.Stochastic.ProgressiveTools

/-!
# Time changes: filtration transfer and limits of consistent stopped families

Source-independent tools for time-changed local martingales (M6/S12).

* `isContLocalMartingale_of_le_of_inter_lt`: a continuous local martingale with respect to a
  filtration `𝒢'` with `𝒢'_s ≤ 𝒢_s` is one with respect to `𝒢` provided it is constant on
  `[ρ, ∞)` for a `𝒢`-stopping time `ρ` such that `A ∩ {s < ρ} ∈ 𝒢'_s` for every `A ∈ 𝒢_s`. This
  generalises `isContLocalMartingale_of_min_const` (`𝒢'_s = ℱ_{s ∧ ρ}`, `𝒢 = ℱ`); the application
  is `𝒢'_s = ℱ_{σ_s ∧ τ_n}`, `𝒢_s = ℱ_{σ_s}` for the σ-time parametrisation stopped at the exit
  times `τ_n`.
* `isStronglyProgressive_indicator_lt`: the indicator of the stochastic interval `[0, ρ)` of a
  stopping time is progressive (adapted and right-continuous).
* `IsContLocalMartingale.of_consistent_seq`: if `L` agrees with continuous local martingales
  `N k` on `[0, ρ k]`, where the stopping times `ρ k` increase a.s. to `∞` and `N k` is constant
  after `ρ k`, then `L` is a continuous local martingale (progressive measurability as a pointwise
  limit of `1_{s < ρ k} N k`, a.s. continuity, and `IsContLocalMartingale.of_stopped_seq`).
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ### Filtration transfer -/

section Transfer

variable [IsProbabilityMeasure P] (𝒢' 𝒢 : Filtration ℝ≥0 mΩ) {ρ : Ω → ℝ≥0}

/-- **Filtration transfer.** Let `𝒢'_s ≤ 𝒢_s`, let `ρ` be a `𝒢`-stopping time with
`A ∩ {s < ρ} ∈ 𝒢'_s` for every `A ∈ 𝒢_s`, and let `N` be a continuous `𝒢'`-local martingale that
is constant on `[ρ, ∞)`. Then `N` is a continuous `𝒢`-local martingale. -/
theorem isContLocalMartingale_of_le_of_inter_lt (h_le : ∀ s, 𝒢' s ≤ 𝒢 s)
    (hρ : IsStoppingTime 𝒢 fun ω => (ρ ω : WithTop ℝ≥0))
    (hinter : ∀ (s : ℝ≥0) (A : Set Ω), MeasurableSet[𝒢 s] A →
      MeasurableSet[𝒢' s] (A ∩ {ω | s < ρ ω}))
    {N : ℝ≥0 → Ω → ℝ} (hN : IsContLocalMartingale 𝒢' N P)
    (hconst : ∀ ω (s t : ℝ≥0), s ≤ t → ρ ω ≤ s → N t ω = N s ω) :
    IsContLocalMartingale 𝒢 N P := by
  obtain ⟨hprog, hcont, τ, hτ, hτev, hmart⟩ := hN
  refine ⟨fun i => (hprog i).mono (measurableSpace_prod_mono le_rfl (h_le i)), hcont, τ,
    fun n i => h_le i _ (hτ n i), hτev, fun n => ?_⟩
  set Y := stoppedProcess N (τ n) with hYdef
  have hY : Martingale Y 𝒢' P := hmart n
  refine ⟨fun i => (hY.stronglyAdapted i).mono (h_le i), fun s t hst => ?_⟩
  -- `Y` is constant between `s` and `t` on `{ρ ≤ s}`
  have hYconst : ∀ ω, ρ ω ≤ s → Y t ω = Y s ω := by
    intro ω hρs
    simp only [hYdef, stoppedProcess]
    rcases le_total (τ n ω) (ρ ω : WithTop ℝ≥0) with hτρ | hρτ
    · have h1 : min (t : WithTop ℝ≥0) (τ n ω) = τ n ω :=
        min_eq_right (hτρ.trans (by exact_mod_cast hρs.trans hst))
      have h2 : min (s : WithTop ℝ≥0) (τ n ω) = τ n ω :=
        min_eq_right (hτρ.trans (by exact_mod_cast hρs))
      rw [h1, h2]
    · have hρs' : (ρ ω : WithTop ℝ≥0) ≤ s := by exact_mod_cast hρs
      have hst' : (s : WithTop ℝ≥0) ≤ t := by exact_mod_cast hst
      have hmin_s : min (s : WithTop ℝ≥0) (τ n ω) ≠ ⊤ :=
        ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
      have hmin_t : min (t : WithTop ℝ≥0) (τ n ω) ≠ ⊤ :=
        ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
      have hle : (min (s : WithTop ℝ≥0) (τ n ω)).untopA ≤
          (min (t : WithTop ℝ≥0) (τ n ω)).untopA := by
        rw [WithTop.untopA_eq_untop hmin_s, WithTop.untopA_eq_untop hmin_t, ← WithTop.coe_le_coe,
          WithTop.coe_untop, WithTop.coe_untop]
        exact min_le_min_right _ hst'
      have hρle : ρ ω ≤ (min (s : WithTop ℝ≥0) (τ n ω)).untopA := by
        rw [WithTop.untopA_eq_untop hmin_s, ← WithTop.coe_le_coe, WithTop.coe_untop]
        exact le_min hρs' hρτ
      exact hconst ω _ _ hle hρle
  have : SigmaFiniteFiltration P 𝒢' := inferInstance
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝒢.le s) (hY.integrable t)
    (fun A _ _ => (hY.integrable s).integrableOn) (fun A hA _ => ?_)
    ((hY.stronglyAdapted s).mono (h_le s)).aestronglyMeasurable).symm
  have hA' : MeasurableSet A := 𝒢.le s A hA
  have hle_meas : MeasurableSet {ω | ρ ω ≤ s} :=
    𝒢.le s _ (Infrastructure.measurableSet_nnreal_le hρ s)
  have hlt_meas : MeasurableSet {ω | s < ρ ω} := by
    have : {ω | s < ρ ω} = {ω | ρ ω ≤ s}ᶜ := by ext ω; simp
    rw [this]; exact hle_meas.compl
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
  rw [hsplit, setIntegral_union hdisj (hA'.inter hlt_meas) (hY.integrable s).integrableOn
    (hY.integrable s).integrableOn, setIntegral_union hdisj (hA'.inter hlt_meas)
    (hY.integrable t).integrableOn (hY.integrable t).integrableOn]
  congr 1
  · exact setIntegral_congr_fun (hA'.inter hle_meas) fun ω hω => (hYconst ω hω.2).symm
  · exact hY.setIntegral_eq hst (hinter s A hA)

end Transfer

/-! ### The indicator of `[0, ρ)` -/

namespace Infrastructure

variable {ℱ : Filtration ℝ≥0 mΩ}

/-- **The indicator of `[0, ρ)` is progressive** (adapted and right-continuous). -/
theorem isStronglyProgressive_indicator_lt {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime ℱ ρ) :
    IsStronglyProgressive ℱ fun s ω => if (s : WithTop ℝ≥0) < ρ ω then (1 : ℝ) else 0 := by
  refine StronglyAdapted.isStronglyProgressive_of_rightContinuous (fun s => ?_) fun ω r => ?_
  · have hset : MeasurableSet[ℱ s] {ω | (s : WithTop ℝ≥0) < ρ ω} := by
      have : {ω | (s : WithTop ℝ≥0) < ρ ω} = {ω | ρ ω ≤ s}ᶜ := by
        ext ω; simp only [mem_ofPred_eq, mem_compl_iff, not_le]
      rw [this]; exact (hρ s).compl
    exact StronglyMeasurable.ite hset stronglyMeasurable_const stronglyMeasurable_const
  · by_cases h : (r : WithTop ℝ≥0) < ρ ω
    · have hopen : IsOpen {s : ℝ≥0 | (s : WithTop ℝ≥0) < ρ ω} := by
        by_cases htop : ρ ω = ⊤
        · have : {s : ℝ≥0 | (s : WithTop ℝ≥0) < ρ ω} = univ := by
            ext s; simp only [mem_ofPred_eq, mem_univ, iff_true, htop]; exact WithTop.coe_lt_top s
          rw [this]; exact isOpen_univ
        · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 htop
          have : {s : ℝ≥0 | (s : WithTop ℝ≥0) < ρ ω} = Iio a := by
            ext s; simp only [mem_ofPred_eq, mem_Iio, ← ha]; exact WithTop.coe_lt_coe
          rw [this]; exact isOpen_Iio
      refine (continuousWithinAt_const (b := (1 : ℝ))).congr_of_eventuallyEq ?_ (ite_eq_left h)
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds h)] with s hs
      exact ite_eq_left hs
    · refine (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq ?_ (ite_eq_right h)
      filter_upwards [self_mem_nhdsWithin] with s hs
      have : ¬ (s : WithTop ℝ≥0) < ρ ω := fun h' =>
        h (lt_of_le_of_lt (WithTop.coe_le_coe.2 hs) h')
      exact ite_eq_right this

end Infrastructure

/-! ### Limits of consistent stopped families -/

/-- **Local martingales from a consistent family of stopped local martingales.** Let `ρ k` be
finite stopping times, nondecreasing in `k` and a.s. eventually above every level. Let `N k` be
continuous local martingales with everywhere continuous paths, constant on `[ρ k, ∞)`, and let
`L` agree with `N k` on `[0, ρ k]` for every `k` and vanish where no `ρ k` is above. Then `L` is
a continuous local martingale. -/
theorem IsContLocalMartingale.of_consistent_seq [IsProbabilityMeasure P] {𝒢 : Filtration ℝ≥0 mΩ}
    {ρ : ℕ → Ω → ℝ≥0} (hρ : ∀ k, IsStoppingTime 𝒢 fun ω => (ρ k ω : WithTop ℝ≥0))
    (hρmono : ∀ ω, Monotone fun k => ρ k ω)
    (hρev : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ∀ᶠ k in atTop, t ≤ ρ k ω)
    {N : ℕ → ℝ≥0 → Ω → ℝ} (hN : ∀ k, IsContLocalMartingale 𝒢 (N k) P)
    (hNc : ∀ k ω, Continuous fun s => N k s ω)
    (hconst : ∀ k ω (s t : ℝ≥0), s ≤ t → ρ k ω ≤ s → N k t ω = N k s ω)
    {L : ℝ≥0 → Ω → ℝ} (hL : ∀ k ω (s : ℝ≥0), s < ρ k ω → L s ω = N k s ω)
    (hLρ : ∀ k ω, L (ρ k ω) ω = N k (ρ k ω) ω)
    (hL0 : ∀ ω (s : ℝ≥0), (∀ k, ρ k ω ≤ s) → L s ω = 0) :
    IsContLocalMartingale 𝒢 L P := by
  -- the stopped processes `L^{ρ k}` are the `N k`
  have hstop : ∀ k, stoppedProcess L (fun ω => (ρ k ω : WithTop ℝ≥0)) = N k := by
    intro k; funext s ω
    simp only [stoppedProcess]
    rw [← WithTop.coe_min]
    change L (min s (ρ k ω)) ω = N k s ω
    rcases lt_or_ge s (ρ k ω) with h | h
    · rw [min_eq_left h.le]; exact hL k ω s h
    · rw [min_eq_right h, hLρ, hconst k ω _ _ h le_rfl]
  -- progressive measurability: `L = lim_K 1_{s < ρ K} N K`
  have hprog : IsStronglyProgressive 𝒢 L := by
    intro i
    let X : ℕ → Iic i × Ω → ℝ := fun K p =>
      (if ((p.1 : ℝ≥0) : WithTop ℝ≥0) < (ρ K p.2 : WithTop ℝ≥0) then (1 : ℝ) else 0) *
        N K p.1 p.2
    have hX : ∀ K, StronglyMeasurable[Subtype.instMeasurableSpace.prod (𝒢 i)] (X K) := fun K =>
      ((Infrastructure.isStronglyProgressive_indicator_lt (hρ K)) i).mul ((hN K).1 i)
    refine stronglyMeasurable_of_tendsto atTop hX ?_
    rw [tendsto_pi_nhds]
    intro p
    by_cases h : ∃ k, (p.1 : ℝ≥0) < ρ k p.2
    · obtain ⟨k, hk⟩ := h
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop k] with K hK
      have hK' : (p.1 : ℝ≥0) < ρ K p.2 := lt_of_lt_of_le hk (hρmono p.2 hK)
      simp only [X, WithTop.coe_lt_coe, hK', ite_true, one_mul]
      exact hL K p.2 p.1 hK'
    · push Not at h
      refine tendsto_const_nhds.congr' (Eventually.of_forall fun K => ?_)
      have : ¬ ((p.1 : ℝ≥0) : WithTop ℝ≥0) < ρ K p.2 := by
        rw [WithTop.coe_lt_coe]; exact not_lt.2 (h K)
      simp only [X, this, ite_false, zero_mul]
      exact hL0 p.2 p.1 h
  -- a.s. continuity: near `s < ρ k`, `L = N k`
  have hcont : ∀ᵐ ω ∂P, Continuous fun s => L s ω := by
    filter_upwards [hρev] with ω hω
    rw [continuous_iff_continuousAt]
    intro s
    obtain ⟨k, hk⟩ := (hω (s + 1)).exists
    have hsk : s < ρ k ω := lt_of_lt_of_le (lt_add_one s) hk
    refine ((hNc k ω).continuousAt (x := s)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Iio.mem_nhds (show s ∈ Iio (ρ k ω) from hsk)] with u hu
    exact hL k ω u hu
  refine IsContLocalMartingale.of_stopped_seq hprog hcont hρ ?_ fun k => ?_
  · filter_upwards [hρev] with ω hω t
    filter_upwards [hω t] with k hk
    exact WithTop.coe_le_coe.2 hk
  · rw [hstop]; exact hN k

end ComplexSLE

end
