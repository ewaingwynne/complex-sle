/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Recurrence.HittingTime

/-!
# Hitting a closed set after a stopping time (M7/A5b, auxiliary)

`ComplexSLE.Recurrence.isStoppingTime_hittingAfter_of_isClosed` takes a deterministic starting
time. Here the start is a stopping time `ρ : Ω → WithTop ℝ≥0`:

* `hitAfterRand X F ρ ω`: the first time `t ≥ ρ(ω)` with `X_t(ω) ∈ F` (`⊤` if `ρ(ω) = ⊤` or if
  there is none);
* `hitAfterRand_le_iff`: for continuous paths and closed `F`, `R ≤ u` iff the path visits `F`
  during `[ρ, u]`;
* `isStoppingTime_hitAfterRand`: for `X` strongly adapted with everywhere continuous paths, `F`
  closed and `ρ` a stopping time, `R` is a stopping time. (The visit during `[ρ, u]` is detected on
  a countable dense set of times `j ≤ u` with `ρ ≤ j`, by the continuity of
  `t ↦ infDist (X t ω) F` and compactness of `[ρ, u]`.)

Source-independent.
-/

@[expose] public section

open scoped NNReal ENNReal Topology
open MeasureTheory Filter Set

namespace ComplexSLE.Recurrence

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {F : Set ℝ}

open Classical in
/-- The first time `t ≥ ρ(ω)` at which `X_t(ω) ∈ F` (`⊤` if `ρ(ω) = ⊤` or there is none). -/
noncomputable def hitAfterRand (X : ℝ≥0 → Ω → ℝ) (F : Set ℝ) (ρ : Ω → WithTop ℝ≥0) (ω : Ω) :
    WithTop ℝ≥0 :=
  if ρ ω = ⊤ then ⊤ else hittingAfter X F (ρ ω).untopA ω

theorem hitAfterRand_le_iff (hF : IsClosed F) (hXc : ∀ ω, Continuous fun t => X t ω)
    {ρ : Ω → WithTop ℝ≥0} {ω : Ω} {u : ℝ≥0} :
    hitAfterRand X F ρ ω ≤ u ↔
      ρ ω ≤ u ∧ ∃ j : ℝ≥0, (ρ ω).untopA ≤ j ∧ j ≤ u ∧ X j ω ∈ F := by
  by_cases hρ : ρ ω = ⊤
  · have h1 : ¬ ((⊤ : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0)) := WithTop.not_top_le_coe u
    have h2 : hitAfterRand X F ρ ω = ⊤ := by simp [hitAfterRand, hρ]
    rw [h2, hρ]
    exact ⟨fun h => absurd h h1, fun h => absurd h.1 h1⟩
  · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hρ
    have hρa : (ρ ω).untopA = a := by rw [← ha]; rfl
    simp only [hitAfterRand, hρ, ite_false, hρa]
    rw [hittingAfter_le_iff_exists hF (hXc ω)]
    constructor
    · rintro ⟨j, ⟨h1, h2⟩, h3⟩
      exact ⟨by rw [← ha]; exact_mod_cast h1.trans h2, j, h1, h2, h3⟩
    · rintro ⟨-, j, h1, h2, h3⟩
      exact ⟨j, ⟨h1, h2⟩, h3⟩

/-- `Icc a u ⊆ closure {j ∈ D ∪ {u} | a ≤ j}` for a set `D` dense in `Icc 0 u`. -/
theorem Icc_subset_closure_of_dense {a u : ℝ≥0} {D : Set ℝ≥0} (hau : a ≤ u)
    (hDd : Icc 0 u ⊆ closure D) :
    Icc a u ⊆ closure {j | j ∈ insert u D ∧ a ≤ j} := by
  rcases hau.lt_or_eq with hlt | rfl
  · -- `Ioo a u ⊆ closure (D ∩ Ioi a)` and `Icc a u = closure (Ioo a u)`
    have h1 : Ioo a u ⊆ closure {j | j ∈ insert u D ∧ a ≤ j} := by
      intro y hy
      rw [mem_closure_iff]
      intro V hV hyV
      have hy0 : y ∈ closure D := hDd ⟨zero_le, hy.2.le⟩
      obtain ⟨j, hjV, hjD⟩ := mem_closure_iff.1 hy0 (V ∩ Ioi a) (hV.inter isOpen_Ioi)
        ⟨hyV, hy.1⟩
      exact ⟨j, hjV.1, Or.inr hjD, hjV.2.le⟩
    have h2 : Icc a u ⊆ closure (Ioo a u) := by
      rw [closure_Ioo hlt.ne]
    exact h2.trans (closure_minimal h1 isClosed_closure)
  · intro x hx
    have : x = a := le_antisymm hx.2 hx.1
    subst this
    exact subset_closure ⟨Or.inl rfl, le_rfl⟩

/-- **Hitting a closed set after a stopping time is a stopping time** (continuous adapted
process). -/
theorem isStoppingTime_hitAfterRand {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
    (hX : StronglyAdapted ℱ X) (hXc : ∀ ω, Continuous fun t => X t ω) (hF : IsClosed F)
    {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime ℱ ρ) :
    IsStoppingTime ℱ (hitAfterRand X F ρ) := by
  rcases F.eq_empty_or_nonempty with rfl | hsne
  · intro i
    have : {ω : Ω | hitAfterRand X (∅ : Set ℝ) ρ ω ≤ (i : WithTop ℝ≥0)} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro h
      rw [hitAfterRand_le_iff hF hXc] at h
      obtain ⟨-, j, -, -, hj⟩ := h
      exact hj
    rw [this]; exact @MeasurableSet.empty _ (ℱ i)
  intro u
  obtain ⟨D, hDc, hD, hDd⟩ := TopologicalSpace.exists_countable_dense_subset (Icc (0 : ℝ≥0) u)
  set D' : Set ℝ≥0 := insert u D with hD'
  have hD'c : D'.Countable := hDc.insert u
  have hD'sub : D' ⊆ Icc 0 u := by
    intro j hj
    rcases hj with rfl | hj
    · exact ⟨zero_le, le_rfl⟩
    · exact hD hj
  have hset : {ω | hitAfterRand X F ρ ω ≤ (u : WithTop ℝ≥0)} =
      {ω | ρ ω ≤ (u : WithTop ℝ≥0)} ∩
        ⋂ k : ℕ, ⋃ j ∈ D', ({ω | ρ ω ≤ (j : WithTop ℝ≥0)} ∩
          {ω | Metric.infDist (X j ω) F < 1 / ((k : ℝ) + 1)}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_iUnion, exists_prop]
    rw [hitAfterRand_le_iff hF hXc]
    constructor
    · rintro ⟨hρu, j, hj1, hj2, hj3⟩
      refine ⟨hρu, ?_⟩
      obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hρu)
      have hρa : (ρ ω).untopA = a := by rw [← ha]; rfl
      rw [hρa] at hj1
      have hau : a ≤ u := by
        have : (a : WithTop ℝ≥0) ≤ u := by rw [ha]; exact hρu
        exact_mod_cast this
      have hD'' := Icc_subset_closure_of_dense (D := D) hau hDd
      have hex := (exists_mem_Icc_iff_forall_exists_infDist_lt hF hsne (hXc ω) (n := a) (i := u)
        (D := {j | j ∈ D' ∧ a ≤ j}) (fun j hj => ⟨hj.2, (hD'sub hj.1).2⟩) hD'').1
        ⟨j, ⟨hj1, hj2⟩, hj3⟩
      intro k
      obtain ⟨j', hj'1, hj'2⟩ := hex k
      refine ⟨j', hj'1.1, ?_, hj'2⟩
      rw [← ha]; exact_mod_cast hj'1.2
    · rintro ⟨hρu, h⟩
      refine ⟨hρu, ?_⟩
      obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hρu)
      have hρa : (ρ ω).untopA = a := by rw [← ha]; rfl
      rw [hρa]
      have hau : a ≤ u := by
        have : (a : WithTop ℝ≥0) ≤ u := by rw [ha]; exact hρu
        exact_mod_cast this
      have hD'' := Icc_subset_closure_of_dense (D := D) hau hDd
      have hex := (exists_mem_Icc_iff_forall_exists_infDist_lt hF hsne (hXc ω) (n := a) (i := u)
        (D := {j | j ∈ D' ∧ a ≤ j}) (fun j hj => ⟨hj.2, (hD'sub hj.1).2⟩) hD'').2
      obtain ⟨j, hj1, hj2⟩ := hex (fun k => by
        obtain ⟨j', hj'1, hj'2, hj'3⟩ := h k
        refine ⟨j', ⟨hj'1, ?_⟩, hj'3⟩
        rw [← ha] at hj'2; exact_mod_cast hj'2)
      exact ⟨j, hj1.1, hj1.2, hj2⟩
  rw [hset]
  refine (hρ u).inter (MeasurableSet.iInter fun k => MeasurableSet.biUnion hD'c fun j hj => ?_)
  have hju : j ≤ u := (hD'sub hj).2
  refine ((ℱ.mono hju _ (hρ j)).inter ?_)
  have hmeas : Measurable[ℱ j] (X j) := (hX j).measurable
  exact ℱ.mono hju _ (measurableSet_lt ((Metric.continuous_infDist_pt F).measurable.comp hmeas)
    measurable_const)

end ComplexSLE.Recurrence

end
