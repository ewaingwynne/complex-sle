/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Order.Compact

/-!
# Hitting times of closed sets by continuous processes on `ℝ≥0`

Mathlib proves that `hittingAfter` is a stopping time only for well-founded countable index sets.
For a process `X : ℝ≥0 → Ω → ℝ` with *every* path continuous and a closed target set `s`,

* `hittingAfter_mem_of_ne_top`: the hitting time is attained (`X_R ∈ s` when `R < ∞`);
* `hittingAfter_le_iff_exists`: `R ≤ i` iff the path visits `s` during `[n, i]`;
* `isStoppingTime_hittingAfter_of_isClosed`: `R` is a stopping time of any filtration to which
  `X` is strongly adapted (the visit set during `[n, i]` is detected on a countable dense set of
  times by the continuity of `t ↦ infDist (X t ω) s`);
* the exit time `R` of an open interval `(l, u)` from a start in `[l, u]`: `X_t ∈ [l, u]` for
  `t ≤ R`, and `X_R ∈ {l, u}` when `R < ∞`.

Source-independent; used for the exit times in the proof of Lemma 2.16 (`sec-recurrence`).
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory Filter Set

namespace ComplexSLE.Recurrence

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {s : Set ℝ} {n : ℝ≥0} {ω : Ω}

/-- On a continuous path the hitting time of a closed set, when finite, is attained. -/
theorem hittingAfter_mem_of_ne_top (hs : IsClosed s) (hXc : Continuous fun t => X t ω)
    (hR : hittingAfter X s n ω ≠ ⊤) :
    X (hittingAfter X s n ω).untopA ω ∈ s ∧ n ≤ (hittingAfter X s n ω).untopA := by
  classical
  have hex : ∃ j, n ≤ j ∧ X j ω ∈ s := by
    by_contra h
    exact hR (by simp [hittingAfter, h])
  have hclosed : IsClosed {i : ℝ≥0 | n ≤ i ∧ X i ω ∈ s} := by
    have : {i : ℝ≥0 | n ≤ i ∧ X i ω ∈ s} = Ici n ∩ (fun i => X i ω) ⁻¹' s := by
      ext i; simp [mem_Ici]
    rw [this]
    exact isClosed_Ici.inter (hs.preimage hXc)
  have hmem := hclosed.csInf_mem hex (OrderBot.bddBelow _)
  have heq : (hittingAfter X s n ω).untopA = sInf {i : ℝ≥0 | n ≤ i ∧ X i ω ∈ s} := by
    simp only [hittingAfter, hex, ite_true]
    rfl
  rw [heq]
  exact ⟨hmem.2, hmem.1⟩

/-- `R ≤ i` iff the path visits `s` during `[n, i]` (continuous path, closed set). -/
theorem hittingAfter_le_iff_exists (hs : IsClosed s) (hXc : Continuous fun t => X t ω) (i : ℝ≥0) :
    hittingAfter X s n ω ≤ i ↔ ∃ j ∈ Icc n i, X j ω ∈ s := by
  constructor
  · intro h
    have hne : hittingAfter X s n ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top h
    obtain ⟨hmem, hn⟩ := hittingAfter_mem_of_ne_top hs hXc hne
    refine ⟨(hittingAfter X s n ω).untopA, ⟨hn, ?_⟩, hmem⟩
    have := WithTop.untopA_le h
    simpa using this
  · rintro ⟨j, ⟨hnj, hji⟩, hj⟩
    exact (hittingAfter_le_of_mem hnj hj).trans (by exact_mod_cast hji)

/-- The visit set `{∃ j ∈ [n, i], X j ∈ s}` is detected on a countable dense set of times. -/
theorem exists_mem_Icc_iff_forall_exists_infDist_lt (hs : IsClosed s) (hsne : s.Nonempty)
    (hXc : Continuous fun t => X t ω) {i : ℝ≥0} {D : Set ℝ≥0} (hD : D ⊆ Icc n i)
    (hDd : Icc n i ⊆ closure D) :
    (∃ j ∈ Icc n i, X j ω ∈ s) ↔
      ∀ k : ℕ, ∃ j ∈ D, Metric.infDist (X j ω) s < 1 / ((k : ℝ) + 1) := by
  have hcont : Continuous fun t : ℝ≥0 => Metric.infDist (X t ω) s :=
    Metric.continuous_infDist_pt s |>.comp hXc
  constructor
  · rintro ⟨j, hj, hjs⟩ k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hU : IsOpen {t : ℝ≥0 | Metric.infDist (X t ω) s < 1 / ((k : ℝ) + 1)} :=
      isOpen_lt hcont continuous_const
    have hjU : j ∈ {t : ℝ≥0 | Metric.infDist (X t ω) s < 1 / ((k : ℝ) + 1)} := by
      simp only [mem_ofPred_eq, Metric.infDist_zero_of_mem hjs]
      exact hpos
    obtain ⟨j', hj'U, hj'D⟩ := mem_closure_iff.1 (hDd hj) _ hU hjU
    exact ⟨j', hj'D, hj'U⟩
  · intro h
    by_cases hni : n ≤ i
    · obtain ⟨j₀, hj₀, hmin⟩ := (isCompact_Icc (a := n) (b := i)).exists_isMinOn
        (nonempty_Icc.2 hni) hcont.continuousOn
      refine ⟨j₀, hj₀, ?_⟩
      rw [hs.mem_iff_infDist_zero hsne]
      by_contra hne
      have hpos : 0 < Metric.infDist (X j₀ ω) s :=
        lt_of_le_of_ne Metric.infDist_nonneg (Ne.symm hne)
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
      obtain ⟨j, hjD, hj⟩ := h k
      have h2 : Metric.infDist (X j₀ ω) s ≤ Metric.infDist (X j ω) s := hmin (hD hjD)
      linarith
    · obtain ⟨j, hjD, -⟩ := h 0
      exact absurd ((hD hjD).1.trans (hD hjD).2) hni

/-- **Hitting times of closed sets are stopping times** for processes with everywhere-continuous
paths, strongly adapted to `ℱ`. -/
theorem isStoppingTime_hittingAfter_of_isClosed {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
    (hX : StronglyAdapted ℱ X) (hXc : ∀ ω, Continuous fun t => X t ω) (hs : IsClosed s)
    (n : ℝ≥0) : IsStoppingTime ℱ (hittingAfter X s n) := by
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · rw [hittingAfter_empty]
    intro i
    have : {ω : Ω | (⊤ : WithTop ℝ≥0) ≤ (i : WithTop ℝ≥0)} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h => WithTop.coe_ne_top (top_le_iff.mp h)
    rw [this]; exact @MeasurableSet.empty _ (ℱ i)
  intro i
  obtain ⟨D, hDc, hD, hDd⟩ := TopologicalSpace.exists_countable_dense_subset (Icc n i)
  have hset : {ω | hittingAfter X s n ω ≤ i} =
      ⋂ k : ℕ, ⋃ j ∈ D, {ω | Metric.infDist (X j ω) s < 1 / ((k : ℝ) + 1)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, exists_prop]
    rw [hittingAfter_le_iff_exists hs (hXc ω),
      exists_mem_Icc_iff_forall_exists_infDist_lt hs hsne (hXc ω) hD hDd]
  rw [hset]
  refine MeasurableSet.iInter fun k => ?_
  refine MeasurableSet.biUnion hDc fun j hj => ?_
  have hji : j ≤ i := (hD hj).2
  refine ℱ.mono hji _ ?_
  have hmeas : Measurable[ℱ j] (X j) := (hX j).measurable
  exact measurableSet_lt ((Metric.continuous_infDist_pt s).measurable.comp hmeas) measurable_const

/-! ### Exit times of open intervals -/

variable {l u : ℝ}

/-- Before the exit time of `(l, u)` the path is in `(l, u)`. -/
theorem mem_Ioo_of_lt_exit {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) < hittingAfter X (Ioo l u)ᶜ 0 ω) :
    X t ω ∈ Ioo l u := by
  have := notMem_of_lt_hittingAfter ht (zero_le : (0 : ℝ≥0) ≤ t)
  simpa using this

/-- Up to and including the exit time of `(l, u)` (from a start in `[l, u]`), the path is in
`[l, u]`. -/
theorem mem_Icc_of_le_exit (hXc : Continuous fun t => X t ω) (h0 : X 0 ω ∈ Icc l u)
    {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) ≤ hittingAfter X (Ioo l u)ᶜ 0 ω) : X t ω ∈ Icc l u := by
  rcases ht.lt_or_eq with hlt | heq
  · exact Ioo_subset_Icc_self (mem_Ioo_of_lt_exit hlt)
  · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0t | hpos
    · rw [← h0t]; exact h0
    · -- `t > 0` is the exit time: it is a limit of times `< t` at which the path is in `(l, u)`
      have hclosed : IsClosed {r : ℝ≥0 | X r ω ∈ Icc l u} := isClosed_Icc.preimage hXc
      have hsub : Ico 0 t ⊆ {r : ℝ≥0 | X r ω ∈ Icc l u} := fun r hr =>
        Ioo_subset_Icc_self (mem_Ioo_of_lt_exit (heq ▸ (by exact_mod_cast hr.2)))
      have ht_cl : t ∈ closure (Ico 0 t) := by
        rw [closure_Ico hpos.ne]; exact ⟨(zero_le : (0 : ℝ≥0) ≤ t), le_rfl⟩
      exact hclosed.closure_subset_iff.2 hsub ht_cl

/-- At a finite exit time of `(l, u)` (from a start in `[l, u]`), the path is at `l` or at
`u`. -/
theorem stoppedValue_exit_mem (hXc : Continuous fun t => X t ω)
    (h0 : X 0 ω ∈ Icc l u) (hR : hittingAfter X (Ioo l u)ᶜ 0 ω ≠ ⊤) :
    stoppedValue X (hittingAfter X (Ioo l u)ᶜ 0) ω = l ∨
      stoppedValue X (hittingAfter X (Ioo l u)ᶜ 0) ω = u := by
  have hcl : IsClosed (Ioo l u)ᶜ := isOpen_Ioo.isClosed_compl
  obtain ⟨hmem, -⟩ := hittingAfter_mem_of_ne_top hcl hXc hR
  have hle : (((hittingAfter X (Ioo l u)ᶜ 0 ω).untopA : ℝ≥0) : WithTop ℝ≥0) ≤
      hittingAfter X (Ioo l u)ᶜ 0 ω := by
    rw [WithTop.untopA_eq_untop hR, WithTop.coe_untop]
  have hIcc := mem_Icc_of_le_exit hXc h0 hle
  simp only [stoppedValue, mem_compl_iff, mem_Ioo, not_and, not_lt] at hmem ⊢
  rcases hIcc with ⟨h1, h2⟩
  rcases h1.lt_or_eq with h1 | h1
  · exact Or.inr (le_antisymm h2 (hmem h1))
  · exact Or.inl h1.symm

/-- The exit time of `(l, u)` is a stopping time. -/
theorem isStoppingTime_exit {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
    (hX : StronglyAdapted ℱ X) (hXc : ∀ ω, Continuous fun t => X t ω) (l u : ℝ) :
    IsStoppingTime ℱ (hittingAfter X (Ioo l u)ᶜ 0) :=
  isStoppingTime_hittingAfter_of_isClosed hX hXc isOpen_Ioo.isClosed_compl 0

end ComplexSLE.Recurrence

end
