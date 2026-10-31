/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Probability.BrownianMotion.Basic

import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# Brownian motion oscillates

Source-independent probability. No external input is used; only Mathlib.

For a standard real Brownian motion `B` (`IsBrownianReal B P`, or just `IsPreBrownianReal B P`,
since path continuity is not used):

* `ae_forall_exists_ge_of_isBrownianReal`: almost surely `limsup_{t → ∞} B t = +∞`, stated as
  `∀ M T, ∃ t ≥ T, B t ω ≥ M`;
* `ae_forall_exists_le_of_isBrownianReal`: almost surely `liminf_{t → ∞} B t = -∞`, stated as
  `∀ M T, ∃ t ≥ T, B t ω ≤ -M`;
* `ae_forall_exists_ge_of_timeChange`, `ae_forall_exists_le_of_timeChange`: the time-changed
  corollary. If `β` is Brownian, `A` has continuous paths with `A t → ∞` almost surely, and
  `N t = β (A t)` almost surely (the output shape of the Dambis–Dubins–Schwarz theorem), then
  `N` is almost surely unbounded above and below. This is a pure composition with the intermediate
  value theorem.

Route. Write `X k = B (k + 1) - B k`; these are independent (`HasIndepIncrements.nat`), and
`∑_{k<n} X k = B n - B 0` a.s. By Brownian scaling (`IsPreBrownianReal.smul`) `P (√n ≤ B n - B 0)`
equals the probability `q > 0` that a standard Gaussian is `≥ 1`, for every `n ≥ 1`. The event
`{limsup S n = +∞}` contains `limsup_n {√n ≤ S n}`, whose probability is `≥ q` (continuity from
above, a reverse Fatou argument); it is a tail event of the independent sequence `X`, so by
Kolmogorov's 0-1 law (`measure_zero_or_one_of_measurableSet_limsup_atTop`) it has probability `1`.
The `X k` are only a.e. measurable, so the argument is run on measurable versions
(`AEMeasurable.mk`).
The lower statement follows from `IsPreBrownianReal.neg`.
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Infrastructure

section RandomWalk

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The event that the partial sums of `X` are unbounded above is a tail event of the sequence. -/
theorem measurableSet_tail_unbounded (X : ℕ → Ω → ℝ) :
    MeasurableSet[limsup (fun k => MeasurableSpace.comap (X k) inferInstance) atTop]
      {ω | ∀ M N : ℕ, ∃ m, N ≤ m ∧ (M : ℝ) ≤ ∑ k ∈ Finset.range m, X k ω} := by
  rw [Filter.limsup_eq_iInf_iSup_of_nat, MeasurableSpace.measurableSet_iInf]
  intro n
  set m' : MeasurableSpace Ω := ⨆ i ≥ n, MeasurableSpace.comap (X i) inferInstance with hm'
  have hXm : ∀ k, n ≤ k → Measurable[m'] (X k) := fun k hk =>
    Measurable.of_comap_le
      (le_iSup₂ (f := fun i (_ : i ≥ n) => MeasurableSpace.comap (X i) inferInstance) k hk)
  have hY : ∀ m, Measurable[m'] (fun ω => ∑ k ∈ Finset.Ico n m, X k ω) := fun m =>
    Finset.measurable_sum _ (fun k hk => hXm k (Finset.mem_Ico.1 hk).1)
  have hEq : {ω | ∀ M N : ℕ, ∃ m, N ≤ m ∧ (M : ℝ) ≤ ∑ k ∈ Finset.range m, X k ω} =
      ⋂ M : ℕ, ⋂ N : ℕ, ⋃ m, ⋃ (_ : max N n ≤ m),
        {ω | (M : ℝ) ≤ ∑ k ∈ Finset.Ico n m, X k ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, mem_iInter, mem_iUnion, exists_prop]
    constructor
    · intro h M N
      obtain ⟨m, hm, hle⟩ := h ⌈(M : ℝ) + ∑ k ∈ Finset.range n, X k ω⌉₊ (max N n)
      refine ⟨m, hm, ?_⟩
      have hn : n ≤ m := (le_max_right _ _).trans hm
      have h1 := Nat.le_ceil ((M : ℝ) + ∑ k ∈ Finset.range n, X k ω)
      rw [← Finset.sum_range_add_sum_Ico _ hn] at hle
      linarith
    · intro h M N
      obtain ⟨m, hm, hle⟩ := h ⌈(M : ℝ) - ∑ k ∈ Finset.range n, X k ω⌉₊ N
      refine ⟨m, (le_max_left _ _).trans hm, ?_⟩
      have hn : n ≤ m := (le_max_right _ _).trans hm
      have h1 := Nat.le_ceil ((M : ℝ) - ∑ k ∈ Finset.range n, X k ω)
      rw [← Finset.sum_range_add_sum_Ico _ hn]
      linarith
  rw [hEq]
  refine MeasurableSet.iInter fun M => MeasurableSet.iInter fun N => MeasurableSet.iUnion fun m =>
    MeasurableSet.iUnion fun _ => ?_
  exact measurableSet_le measurable_const (hY m)

/-- **Oscillation of a random walk.** Let `X` be an independent sequence of random variables whose
partial sums `S n` satisfy `P (g n ≤ S n) ≥ c > 0` eventually, with `g n → ∞`.  Then almost surely
`S` is unbounded above.  (Reverse Fatou lemma and Kolmogorov's 0-1 law.) -/
theorem ae_forall_frequently_ge_of_iIndepFun [IsProbabilityMeasure P] (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X P) {g : ℕ → ℝ} (hg : Tendsto g atTop atTop) {c : ℝ≥0∞} (hc : c ≠ 0)
    (hP : ∀ᶠ n in atTop, c ≤ P {ω | g n ≤ ∑ k ∈ Finset.range n, X k ω}) :
    ∀ᵐ ω ∂P, ∀ M : ℝ, ∃ᶠ n in atTop, M ≤ ∑ k ∈ Finset.range n, X k ω := by
  set E : Set Ω := {ω | ∀ M N : ℕ, ∃ m, N ≤ m ∧ (M : ℝ) ≤ ∑ k ∈ Finset.range m, X k ω} with hE
  have hs : ∀ k, MeasurableSpace.comap (X k) inferInstance ≤ mΩ := fun k => (hX k).comap_le
  have hEtail := measurableSet_tail_unbounded X
  have hEm : MeasurableSet E := (limsup_le_iSup.trans (iSup_le hs)) E hEtail
  have h01 := measure_zero_or_one_of_measurableSet_limsup_atTop
    (s := fun k => MeasurableSpace.comap (X k) inferInstance) hs hind hEtail
  have hA : ∀ n, MeasurableSet {ω | g n ≤ ∑ k ∈ Finset.range n, X k ω} := fun n =>
    measurableSet_le measurable_const (Finset.measurable_sum _ fun k _ => hX k)
  set D : ℕ → Set Ω := fun N => ⋃ n, ⋃ _ : N ≤ n, {ω | g n ≤ ∑ k ∈ Finset.range n, X k ω}
    with hD
  have hDanti : Antitone D := by
    intro N N' h ω hω
    simp only [hD, mem_iUnion] at hω ⊢
    obtain ⟨n, hn, hn'⟩ := hω
    exact ⟨n, h.trans hn, hn'⟩
  have hDm : ∀ N, MeasurableSet (D N) := fun N =>
    MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ => hA n
  have hsub : ⋂ N, D N ⊆ E := by
    intro ω hω M N
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hg.eventually_ge_atTop (M : ℝ))
    have := mem_iInter.1 hω (max N N0)
    simp only [hD, mem_iUnion, Set.mem_ofPred_eq] at this
    obtain ⟨n, hn, hgn⟩ := this
    exact ⟨n, (le_max_left _ _).trans hn, (hN0 n ((le_max_right _ _).trans hn)).trans hgn⟩
  have hDc : ∀ N, c ≤ P (D N) := by
    intro N
    obtain ⟨n, hn, hNn⟩ := (hP.and (eventually_ge_atTop N)).exists
    exact hn.trans (measure_mono (subset_iUnion₂ (s := fun n (_ : N ≤ n) =>
      {ω | g n ≤ ∑ k ∈ Finset.range n, X k ω}) n hNn))
  have hpos : c ≤ P E := by
    refine le_trans ?_ (measure_mono hsub)
    rw [hDanti.measure_iInter (fun N => (hDm N).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
    exact le_iInf hDc
  have h1 : P E = 1 :=
    h01.resolve_left (ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 hc) hpos))
  have hae : ∀ᵐ ω ∂P, ω ∈ E := by
    rw [ae_iff]
    exact (prob_compl_eq_zero_iff hEm).2 h1
  filter_upwards [hae] with ω hω M
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨m, hm, h⟩ := hω ⌈M⌉₊ N
  exact ⟨m, hm, (Nat.le_ceil M).trans h⟩

end RandomWalk

section Brownian

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The probability that a standard Gaussian is at least `1` is positive. -/
theorem gaussianReal_Ici_one_ne_zero : gaussianReal 0 1 (Ici 1) ≠ 0 := by
  intro h
  have := gaussianReal_absolutelyContinuous' 0 (one_ne_zero (α := ℝ≥0)) h
  simp at this

/-- For `n ≥ 1`, `P (√n ≤ B n - B 0)` is the probability that a standard Gaussian is at least `1`
(Brownian scaling). -/
theorem measure_sqrt_le_sub_of_isPreBrownianReal (hB : IsPreBrownianReal B P) {n : ℕ}
    (hn : n ≠ 0) :
    P {ω | √(n : ℝ) ≤ B n ω - B 0 ω} = gaussianReal 0 1 (Ici 1) := by
  have hn' : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn
  have hpos : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hn)
  have hlaw := (hB.smul hn').hasLaw_sub 1 0
  have hset : {ω | √(n : ℝ) ≤ B n ω - B 0 ω} =
      {ω | 1 ≤ ((fun t ω => (√((n : ℝ≥0) : ℝ))⁻¹ * B (n * t) ω) 1 ω -
        (fun t ω => (√((n : ℝ≥0) : ℝ))⁻¹ * B (n * t) ω) 0 ω)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, NNReal.coe_natCast, mul_one, mul_zero]
    rw [← mul_sub, le_inv_mul_iff₀ hpos, mul_one]
  rw [hset]
  have h1 : nndist (1 : ℝ≥0).1 (0 : ℝ≥0).1 = 1 := by simp
  rw [h1] at hlaw
  exact hlaw.measure_eq (p := fun x => 1 ≤ x) (measurableSet_le measurable_const measurable_id)

/-- **Brownian motion is unbounded above** (`limsup_{t → ∞} B t = +∞` almost surely), for a
pre-Brownian motion. -/
theorem ae_forall_exists_ge_of_isPreBrownianReal (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ (M : ℝ) (T : ℝ≥0), ∃ t ≥ T, B t ω ≥ M := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hind := hB.hasIndepIncrements.nat (t := fun n : ℕ => (n : ℝ≥0))
    Nat.mono_cast
  set Y : ℕ → Ω → ℝ := fun k ω => B ((k + 1 : ℕ) : ℝ≥0) ω - B (k : ℝ≥0) ω with hY
  have hYae : ∀ k, AEMeasurable (Y k) P := fun k =>
    (hB.aemeasurable _).sub (hB.aemeasurable _)
  set X : ℕ → Ω → ℝ := fun k => (hYae k).mk (Y k) with hXdef
  have hXm : ∀ k, Measurable (X k) := fun k => (hYae k).measurable_mk
  have hXY : ∀ k, Y k =ᵐ[P] X k := fun k => (hYae k).ae_eq_mk
  have hindX : iIndepFun X P := hind.congr hXY
  have hS : ∀ᵐ ω ∂P, ∀ n : ℕ, ∑ k ∈ Finset.range n, X k ω = B (n : ℝ≥0) ω - B 0 ω := by
    filter_upwards [ae_all_iff.2 hXY] with ω hω n
    rw [← Finset.sum_congr rfl (fun k _ => hω k)]
    simpa [hY] using Finset.sum_range_sub (fun k : ℕ => B (k : ℝ≥0) ω) n
  have hP : ∀ᶠ n : ℕ in atTop, gaussianReal 0 1 (Ici 1) ≤
      P {ω | √(n : ℝ) ≤ ∑ k ∈ Finset.range n, X k ω} := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    refine le_of_eq ?_
    rw [← measure_sqrt_le_sub_of_isPreBrownianReal hB hn]
    refine (measure_congr ?_).symm
    filter_upwards [hS] with ω hω
    simp only [hω n]
  have hmain := ae_forall_frequently_ge_of_iIndepFun hXm hindX
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop) gaussianReal_Ici_one_ne_zero hP
  filter_upwards [hmain, hS, hB.eval_zero_ae_eq_zero] with ω h1 h2 h3 M T
  obtain ⟨n, hn, hle⟩ := (Filter.frequently_atTop.1 (h1 M)) ⌈T⌉₊
  refine ⟨n, ?_, ?_⟩
  · exact (Nat.le_ceil T).trans (by exact_mod_cast hn)
  · rw [h2 n, h3, sub_zero] at hle
    exact hle

/-- **Brownian motion is unbounded below** (`liminf_{t → ∞} B t = -∞` almost surely), for a
pre-Brownian motion. -/
theorem ae_forall_exists_le_of_isPreBrownianReal (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ (M : ℝ) (T : ℝ≥0), ∃ t ≥ T, B t ω ≤ -M := by
  filter_upwards [ae_forall_exists_ge_of_isPreBrownianReal hB.neg] with ω hω M T
  obtain ⟨t, ht, h⟩ := hω M T
  refine ⟨t, ht, ?_⟩
  simp only [Pi.neg_apply] at h
  linarith

/-- **Brownian motion is unbounded above**: almost surely `limsup_{t → ∞} B t = +∞`, stated as
`∀ M T, ∃ t ≥ T, B t ω ≥ M`. -/
theorem ae_forall_exists_ge_of_isBrownianReal (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ (M : ℝ) (T : ℝ≥0), ∃ t ≥ T, B t ω ≥ M :=
  ae_forall_exists_ge_of_isPreBrownianReal hB.toIsPreBrownianReal

/-- **Brownian motion is unbounded below**: almost surely `liminf_{t → ∞} B t = -∞`, stated as
`∀ M T, ∃ t ≥ T, B t ω ≤ -M`. -/
theorem ae_forall_exists_le_of_isBrownianReal (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ (M : ℝ) (T : ℝ≥0), ∃ t ≥ T, B t ω ≤ -M :=
  ae_forall_exists_le_of_isPreBrownianReal hB.toIsPreBrownianReal

section TimeChange

variable {N A : ℝ≥0 → Ω → ℝ}

/-- **Time-changed Brownian motion oscillates (above).** If `β` is a Brownian motion, `A` has
continuous paths with `A t → ∞` almost surely, and `N t = β (A t)` almost surely for all `t`
(as given by the Dambis–Dubins–Schwarz theorem), then almost surely `limsup_{t → ∞} N t = +∞`.
Continuity of `A` is needed: it makes every large time `s` of `β` an attained value of `A`. -/
theorem ae_forall_exists_ge_of_timeChange (hβ : IsBrownianReal B P)
    (hN : ∀ᵐ ω ∂P, ∀ t, N t ω = B (Real.toNNReal (A t ω)) ω)
    (hAc : ∀ᵐ ω ∂P, Continuous (fun t => A t ω))
    (hAtop : ∀ᵐ ω ∂P, Tendsto (fun t => A t ω) atTop atTop) :
    ∀ᵐ ω ∂P, ∀ (M : ℝ) (T : ℝ≥0), ∃ t ≥ T, N t ω ≥ M := by
  filter_upwards [ae_forall_exists_ge_of_isBrownianReal hβ, hN, hAc, hAtop] with ω h1 h2 h3 h4 M T
  obtain ⟨s, hs, hMs⟩ := h1 M (Real.toNNReal (A T ω))
  obtain ⟨t₁, hAt₁, hTt₁⟩ := ((h4.eventually_ge_atTop (s : ℝ)).and (eventually_ge_atTop T)).exists
  have hAT : A T ω ≤ (s : ℝ) := (Real.le_coe_toNNReal _).trans (by exact_mod_cast hs)
  obtain ⟨t, ht, hts⟩ := intermediate_value_Icc hTt₁ h3.continuousOn ⟨hAT, hAt₁⟩
  refine ⟨t, ht.1, ?_⟩
  have hts' : A t ω = (s : ℝ) := hts
  rw [h2 t, hts', Real.toNNReal_coe]
  exact hMs

/-- **Time-changed Brownian motion oscillates (below).** See `ae_forall_exists_ge_of_timeChange`:
almost surely `liminf_{t → ∞} N t = -∞`. -/
theorem ae_forall_exists_le_of_timeChange (hβ : IsBrownianReal B P)
    (hN : ∀ᵐ ω ∂P, ∀ t, N t ω = B (Real.toNNReal (A t ω)) ω)
    (hAc : ∀ᵐ ω ∂P, Continuous (fun t => A t ω))
    (hAtop : ∀ᵐ ω ∂P, Tendsto (fun t => A t ω) atTop atTop) :
    ∀ᵐ ω ∂P, ∀ (M : ℝ) (T : ℝ≥0), ∃ t ≥ T, N t ω ≤ -M := by
  have h := ae_forall_exists_ge_of_timeChange (N := fun t ω => - N t ω) (A := A) hβ.neg
    (by filter_upwards [hN] with ω hω t using by simp [hω t]) hAc hAtop
  filter_upwards [h] with ω hω M T
  obtain ⟨t, ht, h⟩ := hω M T
  exact ⟨t, ht, by linarith⟩

end TimeChange

end Brownian

end ComplexSLE.Infrastructure

end
