/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Ito.Progressive
public import ComplexSLE.Infrastructure.Stochastic.BoundedBracket
public import ComplexSLE.Infrastructure.Stochastic.TimeChangeExitTimes
public import Mathlib.Probability.Process.HittingTime

/-!
# Genuine stopping times for the total variation of a progressive density

Source-independent tools for the localisation of Itô's formula. The filtration is arbitrary (not
complete, not right-continuous), and the densities `A`, `Q` of the drift and the diffusion matrix
are only almost surely locally integrable, so "the first time `∫₀ᵗ |A| ≥ n`" need not be a stopping
time. The device:

* `lintPath φ t ω = ∫⁻_{(0,t]} ofReal (φ_s ω) ds` is jointly measurable on `[0, i] × Ω` for a
  progressive `φ` (Tonelli), in particular `ℱ_t`-measurable.
* `gate φ s ω = 1_{lintPath φ s ω < ∞}` is progressive, and `tilde φ = gate φ * φ`: the density
  `φ` switched off from the first time its integral becomes infinite.
* `V = lintPath (tilde φ)` is monotone, `ℱ_t`-adapted, and **right-continuous for every `ω`** as an
  `[0,∞]`-valued process: either `lintPath φ` is finite just after `t` and the lintegral over a
  short interval is small, or `tilde φ` vanishes after `t`.
* Consequently `variationTime φ n = hittingBtwn V [n, ∞] 0 n` is a genuine stopping time (`{ρ ≤ t}`
  is `{V_t ≥ n}`), `V (ρ ω) ≤ n` for every `ω` (left limits), and `t ≤ ρ ω` as soon as
  `t ≤ n` and `lintPath φ t ω < n`.
-/

@[expose] public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Infrastructure

section LintPath

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}

/-- `∫⁻_{(0,t]} ofReal φ_s ds`, the lintegral of the positive part of a path over `(0, t]`. -/
noncomputable def lintPath (φ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ s in Ioc (0 : ℝ) (t : ℝ), ENNReal.ofReal (φ s.toNNReal ω)

/-- **Tonelli for progressive processes**: `(s, ω) ↦ ∫⁻_{(0,s]} ofReal φ` is measurable on
`[0, i] × Ω` for the product `σ`-algebra with `ℱ i`. -/
theorem measurable_lintPath {φ : ℝ≥0 → Ω → ℝ} (hφ : IsStronglyProgressive ℱ φ) (i : ℝ≥0) :
    Measurable[Subtype.instMeasurableSpace.prod (ℱ i)]
      fun p : Iic i × Ω => lintPath φ (p.1 : ℝ≥0) p.2 := by
  let mI : MeasurableSpace (Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
  let mR : MeasurableSpace ℝ := inferInstance
  let F : (Iic i × Ω) × ℝ → ℝ≥0∞ := fun q =>
    {q : (Iic i × Ω) × ℝ | 0 < q.2 ∧ q.2 ≤ ((q.1.1 : ℝ≥0) : ℝ)}.indicator
      (fun q => ENNReal.ofReal (φ (min (Real.toNNReal q.2) i) q.1.2)) q
  have hφm : Measurable[mI.prod mR, mI] fun q : (Iic i × Ω) × ℝ =>
      ((⟨min (Real.toNNReal q.2) i, mem_Iic.2 (min_le_right _ _)⟩ : Iic i), q.1.2) := by
    refine Measurable.prodMk ?_ ?_
    · refine Measurable.subtype_mk ?_
      exact (measurable_real_toNNReal.comp (@measurable_snd _ _ mI mR)).min measurable_const
    · exact (@measurable_snd _ _ Subtype.instMeasurableSpace (ℱ i)).comp
        (@measurable_fst _ _ mI mR)
  have hF : Measurable[mI.prod mR] F := by
    refine Measurable.indicator (ENNReal.measurable_ofReal.comp ((hφ i).measurable.comp hφm)) ?_
    have h1 : Measurable[mI.prod mR] fun q : (Iic i × Ω) × ℝ => q.2 :=
      @measurable_snd _ _ mI mR
    have h2 : Measurable[mI.prod mR] fun q : (Iic i × Ω) × ℝ => ((q.1.1 : ℝ≥0) : ℝ) :=
      (measurable_subtype_coe.comp
        (@measurable_fst _ _ Subtype.instMeasurableSpace (ℱ i))).comp
          (@measurable_fst _ _ mI mR) |>.coe_nnreal_real
    exact (measurableSet_lt measurable_const h1).inter (measurableSet_le h1 h2)
  have key := @Measurable.lintegral_prod_right' (Iic i × Ω) ℝ mI mR volume _ F hF
  have e : (fun p : Iic i × Ω => lintPath φ (p.1 : ℝ≥0) p.2) = fun p => ∫⁻ y, F (p, y) := by
    funext p
    simp only [lintPath]
    rw [← lintegral_indicator measurableSet_Ioc]
    refine lintegral_congr fun s => ?_
    by_cases h1 : 0 < s ∧ s ≤ ((p.1 : ℝ≥0) : ℝ)
    · have : Real.toNNReal s ≤ i := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ h1.1.le]
        exact h1.2.trans (NNReal.coe_le_coe.2 p.1.2)
      simp only [F, indicator, mem_Ioc, mem_ofPred_eq, h1, and_self, ite_true, min_eq_left this]
    · simp only [F, indicator, mem_Ioc, mem_ofPred_eq, h1, ite_false]
  rw [e]; exact key

/-- `lintPath φ t` is `ℱ t`-measurable. -/
theorem measurable_lintPath_apply {φ : ℝ≥0 → Ω → ℝ} (hφ : IsStronglyProgressive ℱ φ) (t : ℝ≥0) :
    Measurable[ℱ t] fun ω => lintPath φ t ω := by
  have h := measurable_lintPath hφ t
  have h2 : Measurable[ℱ t, Subtype.instMeasurableSpace.prod (ℱ t)]
      fun ω : Ω => ((⟨t, mem_Iic.2 le_rfl⟩ : Iic t), ω) :=
    @Measurable.prodMk Ω (ℱ t) (Iic t) Ω Subtype.instMeasurableSpace (ℱ t)
      (fun _ => ⟨t, mem_Iic.2 le_rfl⟩) id (@measurable_const _ _ _ (ℱ t) _) (@measurable_id _ (ℱ t))
  exact h.comp h2

/-- `lintPath φ t ω` as the mass of `(0, t]` for the measure with density `ofReal φ`. -/
theorem lintPath_eq_measure (φ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    lintPath φ t ω =
      (volume.withDensity fun r : ℝ => ENNReal.ofReal (φ r.toNNReal ω)) (Ioc (0 : ℝ) (t : ℝ)) := by
  rw [withDensity_apply _ measurableSet_Ioc]; rfl

theorem lintPath_mono (φ : ℝ≥0 → Ω → ℝ) (ω : Ω) : Monotone fun t => lintPath φ t ω := by
  intro s t hst
  exact lintegral_mono_set (Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 hst))

theorem lintPath_zero (φ : ℝ≥0 → Ω → ℝ) (ω : Ω) : lintPath φ 0 ω = 0 := by
  simp [lintPath]

/-- Additivity over `(0, s] ∪ (s, t]`. -/
theorem lintPath_add {φ : ℝ≥0 → Ω → ℝ} {ω : Ω} {s t : ℝ≥0} (hst : s ≤ t) :
    lintPath φ t ω = lintPath φ s ω +
      ∫⁻ r in Ioc (s : ℝ) (t : ℝ), ENNReal.ofReal (φ r.toNNReal ω) := by
  unfold lintPath
  rw [← Ioc_union_Ioc_eq_Ioc (NNReal.coe_nonneg s) (NNReal.coe_le_coe.2 hst),
    lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl)]

/-- The gate: `1` as long as the lintegral of `φ` is finite, then `0`. -/
noncomputable def gate (φ : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  if lintPath φ s ω < ⊤ then 1 else 0

/-- `φ` switched off from the first time its lintegral becomes infinite. -/
noncomputable def tilde (φ : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ := gate φ s ω * φ s ω

theorem isStronglyProgressive_gate {φ : ℝ≥0 → Ω → ℝ} (hφ : IsStronglyProgressive ℱ φ) :
    IsStronglyProgressive ℱ (gate φ) := fun i => by
  let _ : MeasurableSpace (Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
  have hset : MeasurableSet {p : Iic i × Ω | lintPath φ (p.1 : ℝ≥0) p.2 < ⊤} :=
    measurableSet_lt (measurable_lintPath hφ i) measurable_const
  exact StronglyMeasurable.ite hset stronglyMeasurable_const stronglyMeasurable_const

theorem isStronglyProgressive_tilde {φ : ℝ≥0 → Ω → ℝ} (hφ : IsStronglyProgressive ℱ φ) :
    IsStronglyProgressive ℱ (tilde φ) :=
  fun i => ((isStronglyProgressive_gate hφ) i).mul (hφ i)

theorem tilde_eq_of_lt_top {φ : ℝ≥0 → Ω → ℝ} {s : ℝ≥0} {ω : Ω} (h : lintPath φ s ω < ⊤) :
    tilde φ s ω = φ s ω := by
  simp [tilde, gate, h]

theorem tilde_eq_zero_of_not_lt_top {φ : ℝ≥0 → Ω → ℝ} {s : ℝ≥0} {ω : Ω}
    (h : ¬ lintPath φ s ω < ⊤) : tilde φ s ω = 0 := by
  simp [tilde, gate, h]

theorem ofReal_tilde_le (φ : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) :
    ENNReal.ofReal (tilde φ s ω) ≤ ENNReal.ofReal (φ s ω) := by
  by_cases h : lintPath φ s ω < ⊤
  · rw [tilde_eq_of_lt_top h]
  · rw [tilde_eq_zero_of_not_lt_top h]; simp

theorem lintPath_tilde_le (φ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    lintPath (tilde φ) t ω ≤ lintPath φ t ω :=
  lintegral_mono fun _ => ofReal_tilde_le _ _ _

/-- Sections of a progressive process are measurable in the real time variable. -/
theorem measurable_toNNReal_section {ξ : ℝ≥0 → Ω → ℝ} (hξ : IsStronglyProgressive ℱ ξ) (ω : Ω) :
    Measurable fun r : ℝ => ξ r.toNNReal ω :=
  (measurable_time_of_isStronglyProgressive hξ ω).comp measurable_real_toNNReal

/-- **Right continuity of the switched-off lintegral**, as an `[0,∞]`-valued process, for every
`ω`. -/
theorem tendsto_lintPath_tilde_right (φ : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0) :
    Tendsto (fun s : ℝ≥0 => lintPath (tilde φ) s ω) (𝓝[>] t) (𝓝 (lintPath (tilde φ) t ω)) := by
  by_cases h : ∃ t' > t, lintPath φ t' ω < ⊤
  · obtain ⟨t', htt', hfin⟩ := h
    set μ : Measure ℝ := volume.withDensity fun r : ℝ => ENNReal.ofReal (tilde φ r.toNNReal ω)
      with hμ
    have hfinμ : μ (Ioc (0 : ℝ) (t' : ℝ)) ≠ ⊤ := by
      rw [hμ, ← lintPath_eq_measure]
      exact ((lintPath_tilde_le φ t' ω).trans_lt hfin).ne
    have htt'R : (t : ℝ) < (t' : ℝ) := NNReal.coe_lt_coe.2 htt'
    have hlim := tendsto_measure_biInter_gt (μ := μ) (s := fun r : ℝ => Ioc (0 : ℝ) r)
      (a := (t : ℝ)) (fun r _ => measurableSet_Ioc.nullMeasurableSet)
      (fun i j _ hij => Ioc_subset_Ioc_right hij) ⟨(t' : ℝ), htt'R, hfinμ⟩
    have hbi : (⋂ r > (t : ℝ), Ioc (0 : ℝ) r) = Ioc (0 : ℝ) (t : ℝ) := by
      ext x
      simp only [mem_iInter, mem_Ioc]
      constructor
      · intro hx
        refine ⟨(hx ((t : ℝ) + 1) (by linarith)).1, le_of_forall_gt_imp_ge_of_dense fun r hr => ?_⟩
        exact (hx r hr).2
      · rintro ⟨h1, h2⟩ r hr
        exact ⟨h1, h2.trans hr.le⟩
    rw [hbi] at hlim
    have hcoe : Tendsto (fun s : ℝ≥0 => (s : ℝ)) (𝓝[>] t) (𝓝[Ioi (t : ℝ)] (t : ℝ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((NNReal.continuous_coe.tendsto t).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact NNReal.coe_lt_coe.2 hs
    have := hlim.comp hcoe
    simpa only [Function.comp_def, hμ, ← lintPath_eq_measure] using this
  · push Not at h
    have hconst : ∀ s : ℝ≥0, t < s → lintPath (tilde φ) s ω = lintPath (tilde φ) t ω := by
      intro s hts
      rw [lintPath_add (φ := tilde φ) hts.le]
      have : ∫⁻ r in Ioc (t : ℝ) (s : ℝ), ENNReal.ofReal (tilde φ r.toNNReal ω) = 0 := by
        rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => 0) ?_]
        · simp
        · intro r hr
          have hr0 : (0 : ℝ) ≤ r := le_trans (NNReal.coe_nonneg t) hr.1.le
          have htr : t < r.toNNReal := by
            rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0]; exact hr.1
          have := h _ htr
          change ENNReal.ofReal (tilde φ r.toNNReal ω) = 0
          rw [tilde_eq_zero_of_not_lt_top (not_lt.2 this)]
          simp
      rw [this, add_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hconst s hs).symm

/-- **Left limits.** If `lintPath ξ s ω ≤ c` for all `s < ρ`, then `lintPath ξ ρ ω ≤ c`. -/
theorem lintPath_le_of_forall_lt {ξ : ℝ≥0 → Ω → ℝ} {ω : Ω} {ρ : ℝ≥0} {c : ℝ≥0∞}
    (h : ∀ s < ρ, lintPath ξ s ω ≤ c) : lintPath ξ ρ ω ≤ c := by
  rcases eq_or_ne ρ 0 with rfl | hρ0
  · rw [lintPath_zero]; exact zero_le
  have hρ : (0 : ℝ≥0) < ρ := pos_iff_ne_zero.2 hρ0
  obtain ⟨u, hu, hu_mem, hu_lim⟩ := exists_seq_strictMono_tendsto' hρ
  set μ : Measure ℝ := volume.withDensity fun r : ℝ => ENNReal.ofReal (ξ r.toNNReal ω) with hμ
  have hmono : Monotone fun k => Ioc (0 : ℝ) (u k : ℝ) := fun a b hab =>
    Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 (hu.monotone hab))
  have htend := tendsto_measure_iUnion_atTop (μ := μ) hmono
  have hU : (⋃ k, Ioc (0 : ℝ) (u k : ℝ)) = Ioo (0 : ℝ) (ρ : ℝ) := by
    ext x
    simp only [mem_iUnion, mem_Ioc, mem_Ioo]
    constructor
    · rintro ⟨k, hk0, hk⟩
      exact ⟨hk0, hk.trans_lt (NNReal.coe_lt_coe.2 (hu_mem k).2)⟩
    · rintro ⟨hx0, hxρ⟩
      have hlim : Tendsto (fun k => (u k : ℝ)) atTop (𝓝 (ρ : ℝ)) :=
        (NNReal.continuous_coe.tendsto ρ).comp hu_lim
      obtain ⟨k, hk⟩ := (hlim.eventually (lt_mem_nhds hxρ)).exists
      exact ⟨k, hx0, hk.le⟩
  rw [hU] at htend
  have hae : Ioo (0 : ℝ) (ρ : ℝ) =ᵐ[μ] Ioc (0 : ℝ) (ρ : ℝ) :=
    (withDensity_absolutelyContinuous volume _).ae_eq Ioo_ae_eq_Ioc
  rw [measure_congr hae] at htend
  rw [lintPath_eq_measure]
  refine le_of_tendsto' htend fun k => ?_
  simp only [Function.comp_apply]
  rw [← lintPath_eq_measure]
  exact h _ (hu_mem k).2

/-- **Hitting times of a monotone, right-continuous, adapted `[0,∞]`-valued process** are stopping
times of the (arbitrary) filtration: `{hit ≤ u} = {c ≤ V u}`. -/
theorem isStoppingTime_hittingBtwn_of_rightContinuous {V : ℝ≥0 → Ω → ℝ≥0∞}
    (hV : ∀ t, Measurable[ℱ t] (V t)) (hmono : ∀ ω, Monotone fun t => V t ω)
    (hrc : ∀ ω t, Tendsto (fun s => V s ω) (𝓝[>] t) (𝓝 (V t ω))) (c : ℝ≥0∞) (T : ℝ≥0) :
    IsStoppingTime ℱ fun ω => ((hittingBtwn V (Ici c) 0 T ω : ℝ≥0) : WithTop ℝ≥0) := by
  intro u
  simp only [WithTop.coe_le_coe]
  by_cases hTu : T ≤ u
  · have : {ω | hittingBtwn V (Ici c) 0 T ω ≤ u} = Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact (hittingBtwn_le ω).trans hTu
    rw [this]; exact MeasurableSet.univ
  have huT : u < T := lt_of_not_ge hTu
  have key : {ω | hittingBtwn V (Ici c) 0 T ω ≤ u} = V u ⁻¹' Ici c := by
    ext ω
    simp only [Set.mem_ofPred_eq, mem_preimage, mem_Ici]
    constructor
    · intro h
      by_contra hlt
      rw [not_le] at hlt
      by_cases hex : ∃ j ∈ Icc (0 : ℝ≥0) T, V j ω ∈ Ici c
      · set S : Set ℝ≥0 := Icc (0 : ℝ≥0) T ∩ {i | V i ω ∈ Ici c} with hS
        have heq : hittingBtwn V (Ici c) 0 T ω = sInf S := by
          simp only [hittingBtwn, hex, ↓reduceIte, hS]
        rw [heq] at h
        have hne : S.Nonempty := by
          obtain ⟨j, hj, hjK⟩ := hex; exact ⟨j, hj, hjK⟩
        obtain ⟨b, hub, hb⟩ :=
          mem_nhdsGT_iff_exists_Ioo_subset.1 ((hrc ω u).eventually (gt_mem_nhds hlt))
        obtain ⟨j, hjS, hjb⟩ := exists_lt_of_csInf_lt hne (lt_of_le_of_lt h hub)
        rcases le_or_gt j u with hju | huj
        · exact absurd (show c ≤ V j ω from hjS.2) (not_le.2 ((hmono ω hju).trans_lt hlt))
        · exact absurd (show c ≤ V j ω from hjS.2) (not_le.2 (hb ⟨huj, hjb⟩))
      · have heq : hittingBtwn V (Ici c) 0 T ω = T := by
          simp only [hittingBtwn, hex, ↓reduceIte]
        rw [heq] at h
        exact absurd h (not_le.mpr huT)
    · intro h
      exact hittingBtwn_le_of_mem zero_le huT.le h
  rw [key]
  exact hV u measurableSet_Ici

/-- The first time the switched-off total variation `lintPath (tilde φ)` reaches `n`, capped at
`n`. -/
noncomputable def variationTime (φ : ℝ≥0 → Ω → ℝ) (n : ℕ) : Ω → ℝ≥0 :=
  hittingBtwn (fun t ω => lintPath (tilde φ) t ω) (Ici (n : ℝ≥0∞)) 0 (n : ℝ≥0)

/-- **The variation time is a genuine stopping time** of an arbitrary filtration. -/
theorem isStoppingTime_variationTime {φ : ℝ≥0 → Ω → ℝ} (hφ : IsStronglyProgressive ℱ φ) (n : ℕ) :
    IsStoppingTime ℱ fun ω => (variationTime φ n ω : WithTop ℝ≥0) :=
  isStoppingTime_hittingBtwn_of_rightContinuous
    (fun t => measurable_lintPath_apply (isStronglyProgressive_tilde hφ) t)
    (fun ω => lintPath_mono _ ω) (fun ω t => tendsto_lintPath_tilde_right φ ω t) _ _

/-- **The switched-off total variation up to the variation time is at most `n`** (for every `ω`). -/
theorem lintPath_tilde_variationTime_le (φ : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) :
    lintPath (tilde φ) (variationTime φ n ω) ω ≤ n := by
  refine lintPath_le_of_forall_lt fun s hs => ?_
  have h := notMem_of_lt_hittingBtwn (u := fun t ω => lintPath (tilde φ) t ω)
    (s := Ici (n : ℝ≥0∞)) (n := 0) (m := (n : ℝ≥0)) (ω := ω) (k := s) hs zero_le
  simpa only [mem_Ici, not_le] using (not_le.1 h).le

/-- The variation time is `≥ t` as soon as `t ≤ n` and `lintPath φ t ω < n`. -/
theorem le_variationTime {φ : ℝ≥0 → Ω → ℝ} {ω : Ω} {n : ℕ} {t : ℝ≥0} (htn : t ≤ n)
    (h : lintPath φ t ω < n) : t ≤ variationTime φ n ω := by
  unfold variationTime hittingBtwn
  split_ifs with hex
  · refine le_csInf (by obtain ⟨j, hj, hjK⟩ := hex; exact ⟨j, hj, hjK⟩) fun j hj => ?_
    by_contra hjt
    rw [not_le] at hjt
    have h1 : lintPath (tilde φ) j ω ≤ lintPath φ t ω :=
      ((lintPath_mono (tilde φ) ω hjt.le).trans (lintPath_tilde_le φ t ω))
    exact absurd (show (n : ℝ≥0∞) ≤ lintPath (tilde φ) j ω from hj.2) (not_le.2 (h1.trans_lt h))
  · exact htn

end LintPath

end ComplexSLE.Infrastructure

end
