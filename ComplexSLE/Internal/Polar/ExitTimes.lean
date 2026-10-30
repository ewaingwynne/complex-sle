/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.Measurability

/-!
# The annulus exit times are stopping times (M6/S6)

For `n : ℕ` the exit time `τ_n = exitTime (U ω) z n` of `Path.lean` (the first time in the life set
at which `|f_t(z)| ≤ 1/n`, `|f_t(z)| ≥ n` or `t = n`) is an `ℱ`-stopping time. For `n ≥ 1` and a
fixed deterministic driver,

  `s < τ_n  ⟺  s ∈ [0, T_z) ∧ s < n ∧ 1/n < |f_r(z)| < n for all r ∈ [0, s]`   (`lt_exitTime_iff`),

and by continuity of `r ↦ |f_r(z)|` on `[0, s]` the last condition may be tested on a countable
dense set of times (`forall_Icc_iff_exists_forall_dense`), at each of which the value `f_r(z)` is
`ℱ r ⊆ ℱ s`-measurable (`measurable_centeredPath`).
-/

public section

open scoped NNReal ENNReal
open Set MeasureTheory

namespace ComplexSLE.Internal.Polar

/-! ### Deterministic characterisation of `{s < τ_n}` -/

section Deterministic

variable {V : ℝ≥0 → ℂ}

/-- `{s < τ_n}` in terms of the path `f`. -/
theorem lt_exitTime_iff (hV : Continuous V) {z : ℂ} {n : ℕ} {s : ℝ} (hs : 0 ≤ s) :
    s < exitTime V hV z n ↔ s ∈ lifeSet V z ∧ s < n ∧
      ∀ r ∈ Icc (0 : ℝ) s, 1 / (n : ℝ) < ‖fPath V hV z r‖ ∧ ‖fPath V hV z r‖ < n := by
  constructor
  · intro hlt
    have hz : 0 < absorbingTime V z := by
      by_contra hz
      push Not at hz
      have h0' : absorbingTime V z = 0 := le_antisymm hz bot_le
      have : exitSet V hV z n = ∅ := by
        ext s'
        simp only [exitSet, Set.mem_ofPred_eq, mem_lifeSet, h0', mem_empty_iff_false, iff_false]
        rintro ⟨⟨-, hlt'⟩, -⟩
        exact not_lt_bot hlt'
      simp [exitTime, this] at hlt
      linarith
    have hsl : s ∈ lifeSet V z := mem_lifeSet_of_le (exitTime_mem_lifeSet hV hz n) hs hlt.le
    have hsn : s < n := (norm_fPath_mem_Ioo_of_lt_exitTime hV hs hlt).2
    refine ⟨hsl, hsn, fun r hr => ?_⟩
    exact (norm_fPath_mem_Ioo_of_lt_exitTime hV hr.1 (lt_of_le_of_lt hr.2 hlt)).1
  · rintro ⟨hsl, hsn, hr⟩
    have hz : 0 < absorbingTime V z :=
      zero_mem_lifeSet_iff.1 (mem_lifeSet_of_le hsl le_rfl hs)
    by_contra hle
    push Not at hle
    obtain ⟨hmem, hc⟩ := exitTime_mem_exitSet hV hz n
    have hτ0 := exitTime_nonneg hV hz n
    have := hr (exitTime V hV z n) ⟨hτ0, hle⟩
    have hτn : exitTime V hV z n < n := lt_of_le_of_lt hle hsn
    rcases hc with h | h | h
    · exact absurd this.1 (not_lt.2 h)
    · exact absurd this.2 (not_lt.2 h)
    · exact absurd hτn (not_lt.2 h)

/-- Testing `1/n < |f| < n` on `[0, s]` on a dense set of times. -/
theorem forall_Icc_iff_exists_forall_dense (hV : Continuous V) {z : ℂ} {s : ℝ}
    (hs : s ∈ lifeSet V z) {n : ℕ} {D : Set ℝ} (hD : D ⊆ Icc 0 s)
    (hdense : Icc 0 s ⊆ closure D) :
    (∀ r ∈ Icc (0 : ℝ) s, 1 / (n : ℝ) < ‖fPath V hV z r‖ ∧ ‖fPath V hV z r‖ < n) ↔
      ∃ k : ℕ, ∀ r ∈ D, 1 / (n : ℝ) + 1 / ((k : ℝ) + 1) ≤ ‖fPath V hV z r‖ ∧
        ‖fPath V hV z r‖ ≤ n - 1 / ((k : ℝ) + 1) := by
  have hcont : ContinuousOn (fun r => ‖fPath V hV z r‖) (Icc 0 s) :=
    (continuousOn_norm_fPath hV z).mono (Icc_subset_lifeSet hs)
  constructor
  · intro h
    obtain ⟨r₁, hr₁, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hs.1) hcont
    obtain ⟨r₂, hr₂, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hs.1) hcont
    have h1 := (h r₁ hr₁).1
    have h2 := (h r₂ hr₂).2
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (lt_min (sub_pos.2 h1) (sub_pos.2 h2))
    refine ⟨k, fun r hr => ?_⟩
    have hrI := hD hr
    have a1 : ‖fPath V hV z r₁‖ ≤ ‖fPath V hV z r‖ := hmin hrI
    have a2 : ‖fPath V hV z r‖ ≤ ‖fPath V hV z r₂‖ := hmax hrI
    have b1 := (lt_min_iff.1 hk).1
    have b2 := (lt_min_iff.1 hk).2
    constructor <;> linarith
  · rintro ⟨k, hk⟩
    have hk0 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hclosed : IsClosed (Icc (0 : ℝ) s ∩
        (fun r => ‖fPath V hV z r‖) ⁻¹' Icc (1 / (n : ℝ) + 1 / ((k : ℝ) + 1))
          (n - 1 / ((k : ℝ) + 1))) :=
      hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Icc
    have hDsub : D ⊆ Icc (0 : ℝ) s ∩
        (fun r => ‖fPath V hV z r‖) ⁻¹' Icc (1 / (n : ℝ) + 1 / ((k : ℝ) + 1))
          (n - 1 / ((k : ℝ) + 1)) := fun r hr => ⟨hD hr, hk r hr⟩
    intro r hr
    have := (closure_minimal hDsub hclosed) (hdense hr)
    obtain ⟨-, h1, h2⟩ := this
    constructor <;> linarith

end Deterministic

/-! ### Stopping times -/

variable {Ω : Type*} {m : MeasurableSpace Ω} {U : ℝ≥0 → Ω → ℂ} {ℱ : Filtration ℝ≥0 m}

/-- `{s < τ_n}` is `ℱ s`-measurable. -/
theorem measurableSet_lt_exitTime (hc : ∀ ω, Continuous fun t => U t ω) (had : Adapted ℱ U)
    (z : ℂ) (n : ℕ) (s : ℝ≥0) :
    MeasurableSet[ℱ s] {ω | (s : ℝ) < exitTime (fun r => U r ω) (hc ω) z n} := by
  classical
  obtain ⟨D', hD'c, hD'd⟩ := TopologicalSpace.exists_countable_dense (Icc (0 : ℝ) s)
  set D : Set ℝ := Subtype.val '' D' with hD
  have hDsub : D ⊆ Icc (0 : ℝ) s := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hDcl : Icc (0 : ℝ) s ⊆ closure D := by
    intro x hx
    have h1 : (⟨x, hx⟩ : Icc (0 : ℝ) s) ∈ closure D' := by rw [hD'd.closure_eq]; trivial
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image] at h1
    exact h1
  have hDc : D.Countable := hD'c.image _
  have key : {ω | (s : ℝ) < exitTime (fun r => U r ω) (hc ω) z n} =
      {ω | (s : ℝ) ∈ lifeSet (fun r => U r ω) z} ∩ ({ω | (s : ℝ) < n} ∩
        ⋃ k : ℕ, ⋂ r ∈ D, {ω | 1 / (n : ℝ) + 1 / ((k : ℝ) + 1) ≤
            ‖if (r.toNNReal : ℝ) ∈ lifeSet (fun s => U s ω) z then
              fPath (fun s => U s ω) (hc ω) z r.toNNReal else 0‖ ∧
          ‖if (r.toNNReal : ℝ) ∈ lifeSet (fun s => U s ω) z then
              fPath (fun s => U s ω) (hc ω) z r.toNNReal else 0‖ ≤ n - 1 / ((k : ℝ) + 1)}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_iInter]
    rw [lt_exitTime_iff (hc ω) s.coe_nonneg]
    constructor
    · rintro ⟨hsl, hsn, hr⟩
      refine ⟨hsl, hsn, ?_⟩
      obtain ⟨k, hk⟩ := (forall_Icc_iff_exists_forall_dense (hc ω) hsl hDsub hDcl).1 hr
      refine ⟨k, fun r hr' => ?_⟩
      have hrI := hDsub hr'
      have hrl : r ∈ lifeSet (fun s => U s ω) z := mem_lifeSet_of_le hsl hrI.1 hrI.2
      simp only [Real.coe_toNNReal r hrI.1, hrl, ↓reduceIte]
      exact hk r hr'
    · rintro ⟨hsl, hsn, k, hk⟩
      refine ⟨hsl, hsn, (forall_Icc_iff_exists_forall_dense (hc ω) hsl hDsub hDcl).2 ⟨k, ?_⟩⟩
      intro r hr'
      have hrI := hDsub hr'
      have hrl : r ∈ lifeSet (fun s => U s ω) z := mem_lifeSet_of_le hsl hrI.1 hrI.2
      have := hk r hr'
      simp only [Real.coe_toNNReal r hrI.1, hrl, ↓reduceIte] at this
      exact this
  rw [key]
  refine (measurableSet_mem_lifeSet hc had s z).inter ((MeasurableSet.const _).inter ?_)
  refine MeasurableSet.iUnion fun k => MeasurableSet.biInter hDc fun r hr => ?_
  have hF := (measurable_centeredPath hc had r.toNNReal z).mono
    (ℱ.mono (show r.toNNReal ≤ s by rw [Real.toNNReal_le_iff_le_coe]; exact (hDsub hr).2)) le_rfl
  have hFn : Measurable[ℱ s] fun ω => ‖if (r.toNNReal : ℝ) ∈ lifeSet (fun s => U s ω) z then
      fPath (fun s => U s ω) (hc ω) z r.toNNReal else 0‖ := measurable_norm.comp hF
  exact (hFn measurableSet_Ici).inter (hFn measurableSet_Iic)

/-- **`{τ_n ≤ s}` is `ℱ s`-measurable.** -/
theorem measurableSet_exitTime_le (hc : ∀ ω, Continuous fun t => U t ω) (had : Adapted ℱ U)
    (z : ℂ) (n : ℕ) (s : ℝ≥0) :
    MeasurableSet[ℱ s] {ω | exitTime (fun r => U r ω) (hc ω) z n ≤ s} := by
  have : {ω | exitTime (fun r => U r ω) (hc ω) z n ≤ s} =
      {ω | (s : ℝ) < exitTime (fun r => U r ω) (hc ω) z n}ᶜ := by
    ext ω; simp
  rw [this]
  exact (measurableSet_lt_exitTime hc had z n s).compl

/-- **The exit times `τ_n` are `ℱ`-stopping times.** -/
theorem isStoppingTime_exitTime (hc : ∀ ω, Continuous fun t => U t ω) (had : Adapted ℱ U)
    (z : ℂ) (n : ℕ) :
    IsStoppingTime ℱ fun ω => (((exitTime (fun r => U r ω) (hc ω) z n).toNNReal : ℝ≥0) :
      WithTop ℝ≥0) := by
  intro s
  have : {ω | (((exitTime (fun r => U r ω) (hc ω) z n).toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ s} =
      {ω | exitTime (fun r => U r ω) (hc ω) z n ≤ s} := by
    ext ω
    simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe]
    exact Real.toNNReal_le_iff_le_coe
  rw [this]
  exact measurableSet_exitTime_le hc had z n s

end ComplexSLE.Internal.Polar

end
