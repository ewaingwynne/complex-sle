/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Data.NNRat.Encodable
public import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Data.NNRat.Floor
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Uniform oscillation of a continuous process over rational times

Source-independent probability. For a process `U : ℝ≥0 → Ω → ℂ` with measurable coordinates and
almost surely continuous paths, `oscSet U N h r` is the (measurable) event that some two rational
times in `[0, N]` at distance at most `h` have `‖U p - U q‖ > r`. Its probability tends to `0` as
`h → 0` (`exists_small_oscSet`): by uniform continuity of the paths on `[0, N]` the events decrease
to a null set. Also `le_of_forall_nnrat_le`: a continuous real function bounded at the rational
times `≤ h` is bounded at all times `≤ h`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ComplexSLE.Infrastructure.Support

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {U : ℝ≥0 → Ω → ℂ}

/-- Oscillation over rational times. -/
def oscSet (U : ℝ≥0 → Ω → ℂ) (N h : ℝ≥0) (r : ℝ) : Set Ω :=
  ⋃ (p : ℚ≥0) (q : ℚ≥0), {ω | (p : ℝ≥0) ≤ N ∧ (q : ℝ≥0) ≤ N ∧ (p : ℝ≥0) ≤ q + h ∧
    (q : ℝ≥0) ≤ p + h ∧ r < ‖U p ω - U q ω‖}

theorem measurableSet_oscSet (hm : ∀ s, Measurable (U s)) (N h : ℝ≥0) (r : ℝ) :
    MeasurableSet (oscSet U N h r) := by
  refine MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun q => ?_
  have : MeasurableSet {ω | r < ‖U p ω - U q ω‖} :=
    measurableSet_lt measurable_const (((hm _).sub (hm _)).norm)
  have h2 : {ω : Ω | (p : ℝ≥0) ≤ N ∧ (q : ℝ≥0) ≤ N ∧ (p : ℝ≥0) ≤ q + h ∧
      (q : ℝ≥0) ≤ p + h ∧ r < ‖U p ω - U q ω‖} =
      {ω : Ω | (p : ℝ≥0) ≤ N ∧ (q : ℝ≥0) ≤ N ∧ (p : ℝ≥0) ≤ q + h ∧ (q : ℝ≥0) ≤ p + h} ∩
        {ω | r < ‖U p ω - U q ω‖} := by
    ext ω; simp [and_assoc]
  rw [h2]
  exact (MeasurableSet.const _).inter this

theorem oscSet_mono {N h h' : ℝ≥0} (hh : h ≤ h') (r : ℝ) : oscSet U N h r ⊆ oscSet U N h' r := by
  intro ω hω
  simp only [oscSet, mem_iUnion] at hω ⊢
  obtain ⟨p, q, h1, h2, h3, h4, h5⟩ := hω
  exact ⟨p, q, h1, h2, h3.trans (by gcongr), h4.trans (by gcongr), h5⟩

theorem exists_small_oscSet (hm : ∀ s, Measurable (U s))
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => U t ω) (N : ℝ≥0) {r : ℝ} (hr : 0 < r)
    {γ : ℝ≥0∞} (hγ : 0 < γ) [IsFiniteMeasure P] :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ h : ℝ≥0, h ≤ η → P (oscSet U N h r) ≤ γ := by
  set A : ℕ → Set Ω := fun n => oscSet U N ((n : ℝ≥0) + 1)⁻¹ r with hA
  have hAnti : Antitone A := fun m n hmn => oscSet_mono (by
    exact inv_anti₀ (by positivity) (by gcongr)) r
  have hnull : P (⋂ n, A n) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hcont)
    intro ω hω hc
    simp only [mem_iInter] at hω
    have hcont' : ContinuousOn (fun t => U t ω) (Icc 0 N) := hc.continuousOn
    have huc := isCompact_Icc.uniformContinuousOn_of_continuous hcont'
    obtain ⟨η, hη, hηω⟩ := Metric.uniformContinuousOn_iff.1 huc r hr
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hη
    have hωn := hω n
    simp only [hA, oscSet, mem_iUnion, mem_ofPred_eq] at hωn
    obtain ⟨p, q, hpN, hqN, hpq, hqp, hrlt⟩ := hωn
    have hd : dist (p : ℝ≥0) (q : ℝ≥0) < η := by
      rw [NNReal.dist_eq, abs_lt]
      have h1 : ((p : ℝ≥0) : ℝ) ≤ (q : ℝ≥0) + (((n : ℝ≥0) + 1)⁻¹ : ℝ≥0) := by exact_mod_cast hpq
      have h2 : ((q : ℝ≥0) : ℝ) ≤ (p : ℝ≥0) + (((n : ℝ≥0) + 1)⁻¹ : ℝ≥0) := by exact_mod_cast hqp
      have h3 : (((n : ℝ≥0) + 1)⁻¹ : ℝ≥0) = 1 / ((n : ℝ) + 1) := by
        push_cast; simp
      rw [h3] at h1 h2
      constructor <;> linarith
    have := hηω p ⟨zero_le, hpN⟩ q ⟨zero_le, hqN⟩ hd
    rw [dist_eq_norm] at this
    linarith
  have hfin : ∃ i, P (A i) ≠ ∞ := ⟨0, measure_ne_top P _⟩
  have ht := tendsto_measure_iInter_atTop
    (fun n => (measurableSet_oscSet hm _ _ _).nullMeasurableSet) hAnti hfin
  rw [hnull] at ht
  have hev := (tendsto_order.1 ht).2 γ hγ
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hev
  refine ⟨((n₀ : ℝ≥0) + 1)⁻¹, by positivity, fun h hh => ?_⟩
  exact ((measure_mono (oscSet_mono hh r)).trans (hn₀ n₀ le_rfl).le : _)

/-- Rational times from below approximate every nonnegative real time. -/
theorem exists_nnrat_seq (s : ℝ≥0) : ∃ q : ℕ → ℚ≥0, (∀ i, ((q i : ℚ≥0) : ℝ≥0) ≤ s) ∧
    Filter.Tendsto (fun i => ((q i : ℚ≥0) : ℝ≥0)) Filter.atTop (𝓝 s) := by
  refine ⟨fun i => (⌊s * ((i : ℝ≥0) + 1)⌋₊ : ℚ≥0) / ((i : ℚ≥0) + 1), ?_, ?_⟩
  · intro i
    push_cast
    rw [div_le_iff₀ (by positivity)]
    exact Nat.floor_le (by positivity)
  · rw [← NNReal.tendsto_coe]
    have h1 : Tendsto (fun i : ℕ => (s : ℝ) - 1 / ((i : ℝ) + 1)) atTop (𝓝 ((s : ℝ) - 0)) :=
      tendsto_const_nhds.sub _root_.tendsto_one_div_add_atTop_nhds_zero_nat
    rw [sub_zero] at h1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds (fun i => ?_)
      (fun i => ?_)
    · have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      have h2 : s * ((i : ℝ≥0) + 1) < ⌊s * ((i : ℝ≥0) + 1)⌋₊ + 1 := Nat.lt_floor_add_one _
      have h3 : (s : ℝ) * ((i : ℝ) + 1) < (⌊s * ((i : ℝ≥0) + 1)⌋₊ : ℝ) + 1 := by exact_mod_cast h2
      push_cast
      have h4 : (s : ℝ) - 1 / ((i : ℝ) + 1) = ((s : ℝ) * ((i : ℝ) + 1) - 1) / ((i : ℝ) + 1) := by
        field_simp
      rw [h4]
      gcongr
      linarith
    · have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      have h2 : (⌊s * ((i : ℝ≥0) + 1)⌋₊ : ℝ≥0) ≤ s * ((i : ℝ≥0) + 1) := Nat.floor_le (by positivity)
      have h3 : (⌊s * ((i : ℝ≥0) + 1)⌋₊ : ℝ) ≤ (s : ℝ) * ((i : ℝ) + 1) := by exact_mod_cast h2
      push_cast
      rw [div_le_iff₀ hi]
      exact h3

/-- A continuous function bounded by `c` at all rational times `≤ h` is bounded by `c` at all
times `≤ h`. -/
theorem le_of_forall_nnrat_le {f : ℝ≥0 → ℝ} (hf : Continuous f) {h : ℝ≥0} {c : ℝ}
    (H : ∀ q : ℚ≥0, (q : ℝ≥0) ≤ h → f q ≤ c) : ∀ s ≤ h, f s ≤ c := by
  intro s hs
  obtain ⟨q, hqs, hq⟩ := exists_nnrat_seq s
  exact le_of_tendsto' ((hf.tendsto s).comp hq) fun i => H (q i) ((hqs i).trans hs)

end ComplexSLE.Infrastructure.Support

end
