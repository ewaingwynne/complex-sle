/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
Ported from leobon12/lean-formalizations @31e7483,
QuantumZipper/Proofs/ItoLite/OptionalStopping.lean;
trimmed and adapted to Lean v4.36 and the module system.
-/
module

public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Hitting times of closed sets by continuous adapted processes (trimmed)

Only `ItoLite.isStoppingTime_hittingBtwn_of_isClosed` is kept from the upstream file: the hitting
time of a closed set by an everywhere continuous adapted process, capped at `T`, is a stopping
time. The optional-stopping parts of the upstream file are not needed (the project has its own
external-free versions in `ComplexSLE.Infrastructure.Stochastic.ContinuousOptionalStopping`).
-/

public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace QuantumZipper
namespace ItoLite

variable {Ω : Type*} {m : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 m}

/-- **Hitting times of closed sets.** The hitting time of a closed set by a continuous adapted
process, capped at `T`, is a stopping time. -/
theorem isStoppingTime_hittingBtwn_of_isClosed {β : Type*} [PseudoMetricSpace β]
    [MeasurableSpace β] [OpensMeasurableSpace β] {U : ℝ≥0 → Ω → β} (hU : Adapted 𝓕 U)
    (hc : ∀ ω, Continuous (U · ω)) {K : Set β} (hK : IsClosed K) (T : ℝ≥0) :
    IsStoppingTime 𝓕 (fun ω => ((hittingBtwn U K 0 T ω : ℝ≥0) : WithTop ℝ≥0)) := by
  intro u
  simp only [WithTop.coe_le_coe]
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp only [hittingBtwn_empty]
    exact MeasurableSet.const _
  by_cases hTu : T ≤ u
  · have : {ω | hittingBtwn U K 0 T ω ≤ u} = Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact (hittingBtwn_le ω).trans hTu
    rw [this]; exact MeasurableSet.univ
  have huT : u < T := lt_of_not_ge hTu
  -- step 1: `hit ≤ u` iff the path meets `K` during `[0, u]`
  have step1 : ∀ ω, hittingBtwn U K 0 T ω ≤ u ↔ ∃ j ∈ Set.Icc 0 u, U j ω ∈ K := by
    intro ω
    constructor
    · intro h
      by_cases hex : ∃ j ∈ Set.Icc 0 T, U j ω ∈ K
      · set S : Set ℝ≥0 := Set.Icc 0 T ∩ {i | U i ω ∈ K} with hS
        have hSc : IsClosed S := isClosed_Icc.inter (hK.preimage (hc ω))
        have hSne : S.Nonempty := by
          obtain ⟨j, hj, hjK⟩ := hex; exact ⟨j, hj, hjK⟩
        have hmem := hSc.csInf_mem hSne (OrderBot.bddBelow S)
        have heq : hittingBtwn U K 0 T ω = sInf S := by
          simp only [hittingBtwn, hex, ↓reduceIte, hS]
        rw [heq] at h
        exact ⟨sInf S, ⟨zero_le, h⟩, hmem.2⟩
      · have heq : hittingBtwn U K 0 T ω = T := by
          simp only [hittingBtwn, hex, ↓reduceIte]
        rw [heq] at h
        exact absurd h (not_le.mpr huT)
    · rintro ⟨j, hj, hjK⟩
      exact (hittingBtwn_le_of_mem hj.1 (hj.2.trans huT.le) hjK).trans hj.2
  -- step 2: a countable description
  obtain ⟨D, hDc, hDsub, hDdense⟩ :=
    TopologicalSpace.exists_countable_dense_subset (Set.Icc (0 : ℝ≥0) u)
  have step2 : ∀ ω, (∃ j ∈ Set.Icc 0 u, U j ω ∈ K) ↔
      ∀ k : ℕ, ∃ q ∈ D, Metric.infDist (U q ω) K < 1 / ((k : ℝ) + 1) := by
    intro ω
    constructor
    · rintro ⟨j, hj, hjK⟩ k
      have hε : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      obtain ⟨δ, hδ, hδU⟩ := Metric.continuous_iff.mp (hc ω) j _ hε
      obtain ⟨q, hqD, hq⟩ := Metric.mem_closure_iff.mp (hDdense hj) δ hδ
      refine ⟨q, hqD, ?_⟩
      calc Metric.infDist (U q ω) K ≤ dist (U q ω) (U j ω) := Metric.infDist_le_dist_of_mem hjK
        _ < _ := hδU q (by rw [dist_comm]; exact hq)
    · intro h
      choose q hqD hq using h
      obtain ⟨a, ha, φ, hφ, hlim⟩ :=
        (isCompact_Icc (a := (0 : ℝ≥0)) (b := u)).tendsto_subseq (fun n => hDsub (hqD n))
      have h1 : Tendsto (fun n => Metric.infDist (U (q (φ n)) ω) K) atTop
          (𝓝 (Metric.infDist (U a ω) K)) :=
        (((Metric.continuous_infDist_pt K).comp (hc ω)).tendsto a).comp hlim
      have h2 : Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
        (tendsto_one_div_add_atTop_nhds_zero_nat).comp hφ.tendsto_atTop
      have hle : Metric.infDist (U a ω) K ≤ 0 :=
        le_of_tendsto_of_tendsto' h1 h2 (fun n => (hq (φ n)).le)
      refine ⟨a, ha, ?_⟩
      rw [hK.mem_iff_infDist_zero hKne]
      exact le_antisymm hle Metric.infDist_nonneg
  have hset : {ω | hittingBtwn U K 0 T ω ≤ u} =
      ⋂ k : ℕ, ⋃ q ∈ D, {ω | Metric.infDist (U q ω) K < 1 / ((k : ℝ) + 1)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, exists_prop]
    exact (step1 ω).trans (step2 ω)
  rw [hset]
  refine MeasurableSet.iInter fun k => MeasurableSet.biUnion hDc fun q hq => ?_
  have hUq : Measurable[𝓕 u] (U q) := (hU q).mono (𝓕.mono (hDsub hq).2) le_rfl
  exact measurableSet_lt ((Metric.continuous_infDist_pt K).measurable.comp hUq) measurable_const

end ItoLite
end QuantumZipper
