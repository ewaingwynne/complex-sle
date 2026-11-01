/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Ergodic.SeparatedCount
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Recurrence of stationary sums (proof of the external input)

A complete proof of the exact statement of `ComplexSLE.External.recurrence_stationary`; this
module deliberately does not import `ComplexSLE.External.*`, the statement is a verbatim copy.

The argument is elementary and uses neither integrability of `ξ 0` nor ergodic decomposition.
Write `S n = ∑ k < n, ξ k` and, for `ε > 0`, let `E ε k` be the event that the shifted sums
`∑ i < n, ξ (i + k)` stay at distance at least `ε` from `0` for all `n ≥ 1`.

* If `ω ∈ E ε j` and `j < k` then `|S k - S j| ≥ ε`, so the indices `k < N` with `ω ∈ E ε k` give
  `ε`-separated values of `S`; since `S n / n → 0` almost surely, their proportion in `[0, N)`
  tends to `0` (`ComplexSLE.Infrastructure.Ergodic.tendsto_card_div_of_separated`).
* By stationarity `P (E ε k) = P (E ε 0)`, so the expected proportion is `P (E ε 0)` for every
  `N ≥ 1`; dominated convergence gives `P (E ε 0) = 0`.
* Hence almost surely every shifted sum series returns arbitrarily close to its start, which forces
  `|S n| < ε` infinitely often.
-/

public section

open scoped Topology ENNReal
open MeasureTheory Filter Set

namespace ComplexSLE.Internal.ExternalProofs

namespace RecurrenceStationaryAux

/-- The set of real sequences all of whose nonempty partial sums have absolute value at least
`ε`. -/
def farSeqs (ε : ℝ) : Set (ℕ → ℝ) :=
  {x | ∀ n : ℕ, 1 ≤ n → ε ≤ |∑ i ∈ Finset.range n, x i|}

/-- The event that the sums of the sequence shifted by `k` stay at distance at least `ε` from `0`
for all `n ≥ 1`. -/
def farEvent {Ω : Type} (ξ : ℕ → Ω → ℝ) (ε : ℝ) (k : ℕ) : Set Ω :=
  (fun ω (n : ℕ) => ξ (n + k) ω) ⁻¹' farSeqs ε

theorem mem_farEvent {Ω : Type} (ξ : ℕ → Ω → ℝ) (ε : ℝ) (k : ℕ) (ω : Ω) :
    ω ∈ farEvent ξ ε k ↔ ∀ n : ℕ, 1 ≤ n → ε ≤ |∑ i ∈ Finset.range n, ξ (i + k) ω| :=
  Iff.rfl

theorem measurableSet_farSeqs (ε : ℝ) : MeasurableSet (farSeqs ε) := by
  have : farSeqs ε = ⋂ n : ℕ, ⋂ (_ : 1 ≤ n), {x : ℕ → ℝ | ε ≤ |∑ i ∈ Finset.range n, x i|} := by
    ext x; simp [farSeqs]
  rw [this]
  refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ => ?_
  have hm : Measurable fun x : ℕ → ℝ => |∑ i ∈ Finset.range n, x i| :=
    continuous_abs.measurable.comp (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
  exact measurableSet_le measurable_const hm

/-- Partial sums over a shifted window. -/
theorem sum_range_add_sub (f : ℕ → ℝ) (j n : ℕ) :
    ∑ i ∈ Finset.range (j + n), f i - ∑ i ∈ Finset.range j, f i =
      ∑ i ∈ Finset.range n, f (i + j) := by
  rw [Finset.sum_range_add]
  simp [add_comm]

/-- Separation along the partial sums. -/
theorem sep_of_mem_farEvent {Ω : Type} {ξ : ℕ → Ω → ℝ} {ε : ℝ} {ω : Ω} {j k : ℕ} (hjk : j < k)
    (hω : ω ∈ farEvent ξ ε j) :
    ε ≤ |∑ i ∈ Finset.range k, ξ i ω - ∑ i ∈ Finset.range j, ξ i ω| := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hjk
  have := hω (n + 1) (by omega)
  rw [← sum_range_add_sub (fun i => ξ i ω) j (n + 1)] at this
  rw [show j + n + 1 = j + (n + 1) by omega]
  exact this

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : ℕ → Ω → ℝ}

theorem measurable_shift (hmeas : ∀ n, Measurable (ξ n)) (k : ℕ) :
    Measurable fun ω (n : ℕ) => ξ (n + k) ω :=
  measurable_pi_iff.2 fun _ => hmeas _

theorem measurableSet_farEvent (hmeas : ∀ n, Measurable (ξ n)) (ε : ℝ) (k : ℕ) :
    MeasurableSet (farEvent ξ ε k) :=
  (measurableSet_farSeqs ε).preimage (measurable_shift hmeas k)

/-- Stationarity: the far events all have the same probability. -/
theorem measure_farEvent_eq (hmeas : ∀ n, Measurable (ξ n))
    (hstat : ∀ k : ℕ, P.map (fun ω (n : ℕ) => ξ (n + k) ω) = P.map (fun ω (n : ℕ) => ξ n ω))
    (ε : ℝ) (k : ℕ) : P (farEvent ξ ε k) = P (farEvent ξ ε 0) := by
  have h0 : farEvent ξ ε 0 = (fun ω (n : ℕ) => ξ n ω) ⁻¹' farSeqs ε := rfl
  rw [h0, farEvent, ← Measure.map_apply (measurable_shift hmeas k) (measurableSet_farSeqs ε),
    ← Measure.map_apply (measurable_pi_iff.2 hmeas) (measurableSet_farSeqs ε), hstat k]

/-- The expected number of indices `k < N` with `ω ∈ farEvent ξ ε k` is `N P (farEvent ξ ε 0)`. -/
theorem integral_count (hmeas : ∀ n, Measurable (ξ n))
    (hstat : ∀ k : ℕ, P.map (fun ω (n : ℕ) => ξ (n + k) ω) = P.map (fun ω (n : ℕ) => ξ n ω))
    [IsProbabilityMeasure P] (ε : ℝ) (N : ℕ) :
    ∫ ω, ∑ k ∈ Finset.range N, (farEvent ξ ε k).indicator (fun _ => (1 : ℝ)) ω ∂P =
      N * (P (farEvent ξ ε 0)).toReal := by
  rw [integral_finsetSum _ fun k _ =>
    (integrable_const (1 : ℝ)).indicator (measurableSet_farEvent hmeas ε k)]
  have : ∀ k ∈ Finset.range N, ∫ ω, (farEvent ξ ε k).indicator (fun _ => (1 : ℝ)) ω ∂P =
      (P (farEvent ξ ε 0)).toReal := by
    intro k _
    rw [integral_indicator_const _ (measurableSet_farEvent hmeas ε k), smul_eq_mul, mul_one,
      Measure.real, measure_farEvent_eq hmeas hstat ε k]
  rw [Finset.sum_congr rfl this]
  simp

/-- **Step 1.** For `ε > 0`, almost surely there is a return to within `ε` of the start. -/
theorem measure_farEvent_zero [IsProbabilityMeasure P] (hmeas : ∀ n, Measurable (ξ n))
    (hstat : ∀ k : ℕ, P.map (fun ω (n : ℕ) => ξ (n + k) ω) = P.map (fun ω (n : ℕ) => ξ n ω))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, ξ k ω) / n) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) : P (farEvent ξ ε 0) = 0 := by
  classical
  set F : ℕ → Ω → ℝ := fun N ω =>
    (∑ k ∈ Finset.range N, (farEvent ξ ε k).indicator (fun _ => (1 : ℝ)) ω) / N with hF
  have hFmeas : ∀ N, AEStronglyMeasurable (F N) P := by
    intro N
    refine (Measurable.div_const ?_ _).aestronglyMeasurable
    exact Finset.measurable_sum _ fun k _ =>
      measurable_const.indicator (measurableSet_farEvent hmeas ε k)
  have hFbound : ∀ N, ∀ᵐ ω ∂P, ‖F N ω‖ ≤ (fun _ => (1 : ℝ)) ω := by
    intro N
    refine Eventually.of_forall fun ω => ?_
    simp only [hF, Real.norm_eq_abs]
    have hnn : 0 ≤ ∑ k ∈ Finset.range N, (farEvent ξ ε k).indicator (fun _ => (1 : ℝ)) ω :=
      Finset.sum_nonneg fun k _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hle : ∑ k ∈ Finset.range N, (farEvent ξ ε k).indicator (fun _ => (1 : ℝ)) ω ≤ N := by
      calc _ ≤ ∑ k ∈ Finset.range N, (1 : ℝ) :=
            Finset.sum_le_sum fun k _ => Set.indicator_le_self' (fun _ _ => zero_le_one) _
        _ = N := by simp
    rw [abs_of_nonneg (div_nonneg hnn (Nat.cast_nonneg N))]
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    · rw [div_le_one (by exact_mod_cast h)]; exact hle
  have hFlim : ∀ᵐ ω ∂P, Tendsto (fun N => F N ω) atTop (𝓝 ((fun _ => (0 : ℝ)) ω)) := by
    filter_upwards [hlim] with ω hω
    have hsep : ∀ j k, j < k → ω ∈ farEvent ξ ε j →
        ε ≤ |(∑ i ∈ Finset.range k, ξ i ω) - ∑ i ∈ Finset.range j, ξ i ω| :=
      fun j k hjk hj => sep_of_mem_farEvent hjk hj
    have := ComplexSLE.Infrastructure.Ergodic.tendsto_card_div_of_separated hε
      (fun n => ∑ i ∈ Finset.range n, ξ i ω) (fun k => ω ∈ farEvent ξ ε k) hω hsep
    refine this.congr fun N => ?_
    simp only [hF]
    simp only [Set.indicator_apply, Finset.sum_boole]
  have hlimint := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) hFmeas
    (integrable_const _) hFbound hFlim
  simp only [integral_zero] at hlimint
  have hconst : ∀ N : ℕ, 1 ≤ N → ∫ ω, F N ω ∂P = (P (farEvent ξ ε 0)).toReal := by
    intro N hN
    simp only [hF]
    rw [integral_div, integral_count hmeas hstat]
    have : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    field_simp
  have hlim2 : Tendsto (fun N : ℕ => ∫ ω, F N ω ∂P) atTop (𝓝 (P (farEvent ξ ε 0)).toReal) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact (hconst N hN).symm)
  have h0 : (P (farEvent ξ ε 0)).toReal = 0 := tendsto_nhds_unique hlim2 hlimint
  rcases (ENNReal.toReal_eq_zero_iff _).1 h0 with h | h
  · exact h
  · exact absurd h (measure_ne_top _ _)

/-- Deterministic step: arbitrarily good returns of the shifted sums force `|S n| < ε` infinitely
often. -/
theorem frequently_lt_of_returns (S : ℕ → ℝ) (hS0 : S 0 = 0)
    (hret : ∀ k : ℕ, ∀ δ : ℝ, 0 < δ → ∃ n : ℕ, 1 ≤ n ∧ |S (k + n) - S k| < δ)
    {ε : ℝ} (hε : 0 < ε) : ∃ᶠ n in atTop, |S n| < ε := by
  by_contra hcon
  rw [not_frequently, eventually_atTop] at hcon
  obtain ⟨N, hN⟩ := hcon
  have hP0 : |S 0| < ε := by rw [hS0]; simpa using hε
  classical
  set L := Nat.findGreatest (fun n => |S n| < ε) N with hL
  have hLN : L ≤ N := Nat.findGreatest_le N
  have hLspec : |S L| < ε := Nat.findGreatest_spec (P := fun n => |S n| < ε) (Nat.zero_le N) hP0
  obtain ⟨n, hn1, hn⟩ := hret L (ε - |S L|) (by linarith)
  have hlt : |S (L + n)| < ε := by
    have := abs_sub_abs_le_abs_sub (S (L + n)) (S L)
    linarith
  by_cases hle : L + n ≤ N
  · exact Nat.findGreatest_is_greatest (P := fun n => |S n| < ε) (by omega) hle hlt
  · have := hN (L + n) (by omega)
    linarith

end RecurrenceStationaryAux

open RecurrenceStationaryAux in
/-- **Recurrence of stationary sums with sublinear growth.** Same statement as
`ComplexSLE.External.recurrence_stationary`, proved. -/
theorem recurrence_stationary {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ξ : ℕ → Ω → ℝ) (hmeas : ∀ n, Measurable (ξ n))
    (hstat : ∀ k : ℕ, P.map (fun ω (n : ℕ) => ξ (n + k) ω) = P.map (fun ω (n : ℕ) => ξ n ω))
    (hint : Integrable (ξ 0) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, ξ k ω) / n) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∃ᶠ n in atTop, |∑ k ∈ Finset.range n, ξ k ω| < ε := by
  -- the proof uses neither integrability of `ξ 0` nor ergodic decomposition
  have _ := hint
  have hae : ∀ᵐ ω ∂P, ∀ k m : ℕ, ω ∉ farEvent ξ (1 / ((m : ℝ) + 1)) k := by
    rw [ae_all_iff]
    intro k
    rw [ae_all_iff]
    intro m
    refine measure_eq_zero_iff_ae_notMem.1 ?_
    rw [measure_farEvent_eq hmeas hstat]
    exact measure_farEvent_zero hmeas hstat hlim (by positivity)
  filter_upwards [hae] with ω hω ε hε
  refine frequently_lt_of_returns (fun n => ∑ k ∈ Finset.range n, ξ k ω) (by simp) ?_ hε
  intro k δ hδ
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  have h := hω k m
  rw [mem_farEvent] at h
  push Not at h
  obtain ⟨n, hn1, hn⟩ := h
  refine ⟨n, hn1, ?_⟩
  rw [sum_range_add_sub (fun i => ξ i ω) k n]
  exact hn.trans hm

end ComplexSLE.Internal.ExternalProofs

end
