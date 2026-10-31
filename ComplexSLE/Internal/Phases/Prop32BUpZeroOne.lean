/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.Prop32BUpEvents
public import ComplexSLE.Internal.Phases.Prop32BUpMarkov
public import ComplexSLE.Internal.Phases.Lemma38Meas
public import ComplexSLE.Internal.Phases.KoebeHitSigma
public import Mathlib.Probability.Martingale.Convergence

/-!
# Proposition 3.2(b): the martingale 0-1 step (M7/E5, step 5 of the upgrade)

Source: paper.tex:L1811-1816. If `P(StaysAway(U, ξ)) ≥ q_* > 0` for every `ξ ≠ 0`, then
`StaysAway(U, z)` holds a.s., for every `z ≠ 0`.

* `ae_mem_of_forall_measureReal_le` (Lévy's upward theorem, generic): let `𝒢` be a filtration
  indexed by `ℕ` and `E` a `⨆ 𝒢_n`-measurable event with `P(A ∩ E) ≥ q_* P(A)` for all `A ∈ 𝒢_n`,
  all `n`; then `E` holds a.s. (`μ[1_E | 𝒢_n] ≥ q_*`, `μ[1_E | 𝒢_n] → 1_E`).
* `staysAway_iff_exists_forall_nat`: for a continuous driver `u` with `σ_z(n) < ∞` for all `n`,
  `StaysAway u z` iff `∃ k, ∀ n, 1/(k+1) < dist(z, L_{σ_z(n)})`.
* `measurableSet_hitSetN`: `{dist(z, L_{σ_z(n)}) ≤ r} ∈ 𝒢_n = ℱ_{σ_z(n)}` (it is
  `{hitTime ≤ σ_z(n)}`, for the stopping time `hitTime` of the level `r`).
* `ae_staysAway_of_lowerBound`: the conclusion; the lower bound
  `P(A ∩ StaysAway) = ∫_A q(f̂_n(z)) dP ≥ q_* P(A)` for `A ∈ 𝒢_n` is the Markov step at `σ_z(n)`
  (`measure_inter_event_eq_lintegral`).

Uses the EXTERNALs `strongMarkov_sleDriver` and `koebe_quarter`.
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Metric

namespace ComplexSLE.Internal

/-! ### Lévy's upward theorem -/

section Levy

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- If `P(A ∩ E) ≥ q_* P(A)` for `A ∈ 𝒢_n`, then `μ[1_E | 𝒢_n] ≥ q_*` a.e. -/
theorem ae_le_condExp_indicator (𝒢 : Filtration ℕ m0) {n : ℕ} {E : Set Ω}
    (hE : MeasurableSet E) {qs : ℝ}
    (h : ∀ A : Set Ω, MeasurableSet[𝒢 n] A → qs * μ.real A ≤ μ.real (A ∩ E)) :
    ∀ᵐ ω ∂μ, qs ≤ (μ[E.indicator (fun _ => (1 : ℝ)) | 𝒢 n]) ω := by
  set g : Ω → ℝ := E.indicator (fun _ => (1 : ℝ)) with hg
  have hle : 𝒢 n ≤ m0 := 𝒢.le n
  have hgint : Integrable g μ := (integrable_const (1 : ℝ)).indicator hE
  set f : Ω → ℝ := μ[g | 𝒢 n] with hf
  have hfm : StronglyMeasurable[𝒢 n] f := stronglyMeasurable_condExp
  have hfint : Integrable f μ := integrable_condExp
  have hkey : 0 ≤ᵐ[μ.trim hle] fun ω => f ω - qs := by
    refine @ae_nonneg_of_forall_setIntegral_nonneg Ω (𝒢 n) (μ.trim hle) _ ?_ ?_
    · exact (hfint.trim hle hfm).sub (integrable_const qs)
    · intro A hA _
      have hAm : MeasurableSet A := hle _ hA
      rw [← setIntegral_trim hle (f := fun ω => f ω - qs)
        (hfm.sub stronglyMeasurable_const : StronglyMeasurable[𝒢 n] (fun ω => f ω - qs)) hA]
      rw [integral_sub hfint.integrableOn (integrableOn_const (by simp))]
      rw [setIntegral_condExp hle hgint hA, setIntegral_const, hg,
        setIntegral_indicator hE, setIntegral_const]
      simp only [smul_eq_mul, mul_one]
      have := h A hA
      linarith
  filter_upwards [ae_of_ae_trim hle hkey] with ω hω
  exact sub_nonneg.1 hω

/-- **Martingale 0-1 step** (paper.tex:L1811-1816): if `E ∈ ⨆ 𝒢_n` and `P(A ∩ E) ≥ q_* P(A)` for
all `A ∈ 𝒢_n`, all `n`, with `q_* > 0`, then `E` holds a.s. -/
theorem ae_mem_of_forall_measureReal_le (𝒢 : Filtration ℕ m0) {E : Set Ω}
    (hE : MeasurableSet[⨆ n, 𝒢 n] E) {qs : ℝ} (hqs : 0 < qs)
    (h : ∀ n (A : Set Ω), MeasurableSet[𝒢 n] A → qs * μ.real A ≤ μ.real (A ∩ E)) :
    ∀ᵐ ω ∂μ, ω ∈ E := by
  have hEm : MeasurableSet E := (iSup_le fun n => 𝒢.le n) _ hE
  set g : Ω → ℝ := E.indicator (fun _ => (1 : ℝ)) with hg
  have hgint : Integrable g μ := (integrable_const (1 : ℝ)).indicator hEm
  have hgmeas : StronglyMeasurable[⨆ n, 𝒢 n] g :=
    (stronglyMeasurable_const.indicator hE : StronglyMeasurable[⨆ n, 𝒢 n] _)
  have hlevy := hgint.tendsto_ae_condExp hgmeas
  have hall : ∀ᵐ ω ∂μ, ∀ n, qs ≤ (μ[g | 𝒢 n]) ω :=
    ae_all_iff.2 fun n => ae_le_condExp_indicator 𝒢 hEm (h n)
  filter_upwards [hlevy, hall] with ω h1 h2
  have h3 : qs ≤ g ω := ge_of_tendsto' h1 h2
  by_contra hω
  rw [hg, Set.indicator_of_notMem hω] at h3
  linarith

end Levy

/-! ### `StaysAway` along the integer σ-times -/

section Deterministic

open Polar

variable {u : ℝ≥0 → ℂ}

theorem staysAway_iff_exists_forall_nat (hu : Continuous u) {z : ℂ}
    (hG : ∀ s : ℝ≥0, (s : ℝ) ∈ sigmaDom u hu z) :
    StaysAway u z ↔ ∃ k : ℕ, ∀ n : ℕ,
      1 / ((k : ℝ) + 1) <
        infDist z (leftHull u (sigmaTime u hu z ((n : ℝ≥0) : ℝ)).toNNReal) := by
  constructor
  · rintro ⟨ε, hε, h⟩
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    refine ⟨k, fun n => lt_of_lt_of_le hk (h _ ?_)⟩
    exact sigmaTime_toNNReal_lt_absorbingTime hu (hG n)
  · rintro ⟨k, hk⟩
    refine ⟨1 / ((k : ℝ) + 1), by positivity, fun t ht => ?_⟩
    have hlife : (t : ℝ) ∈ lifeSet u z := coe_mem_lifeSet_iff.2 (notMem_leftHull_iff.2 ht)
    set s0 : ℝ := clock u hu z t with hs0def
    have hs0 : s0 ∈ sigmaDom u hu z := clock_mem_sigmaDom hu hlife
    have hσ0 : sigmaTime u hu z s0 = t := sigmaTime_clock hu hlife
    set n : ℕ := ⌈s0⌉₊ with hn
    have hsn : s0 ≤ (((n : ℝ≥0)) : ℝ) := by
      rw [NNReal.coe_natCast]; exact Nat.le_ceil s0
    have hmon := sigmaTime_monotoneOn hu z hs0 (hG n) hsn
    rw [hσ0] at hmon
    have htτ : t ≤ (sigmaTime u hu z ((n : ℝ≥0) : ℝ)).toNNReal := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (sigmaTime_nonneg hu (hG n))]
      exact hmon
    have h1 : infDist z (leftHull u (sigmaTime u hu z ((n : ℝ≥0) : ℝ)).toNNReal) ≤
        infDist z (leftHull u t) :=
      infDist_le_infDist_of_subset (leftHull_mono htτ) (leftHull_nonempty u t)
    exact (hk n).le.trans h1

end Deterministic

/-! ### The events along the integer σ-times -/

section Events

open Polar

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- `{dist(z, L_{σ_z(n)}) ≤ r}`, written as `{hitTime_r ≤ σ_z(n)}`. -/
def hitSetN (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) (n : ℕ) (r : ℝ) : Set Ω :=
  {ω | hitTime (fun t => U t ω) z r ≤ sigmaTop hU z ((n : ℝ≥0)) ω}

theorem measurableSet_hitSetN (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) (n : ℕ) (r : ℝ) :
    MeasurableSet[sigmaFiltration hU z ((n : ℝ≥0))] (hitSetN hU z n r) :=
  IsStoppingTime.measurableSet_stopping_time_le (isStoppingTime_hitTime hU.cont hU.adapted z r)
    (isStoppingTime_sigmaTop hU z ((n : ℝ≥0)))

theorem mem_hitSetN_iff (hU : IsSLEDriverAdapted a b c U P ℱ) {z : ℂ} {n : ℕ} {r : ℝ} {ω : Ω}
    (hω : ((n : ℝ≥0) : ℝ) ∈ sigmaDom (fun t => U t ω) (hU.cont ω) z) :
    ω ∈ hitSetN hU z n r ↔
      infDist z (leftHull (fun t => U t ω) (sigmaTime (fun t => U t ω) (hU.cont ω) z
        ((n : ℝ≥0) : ℝ)).toNNReal) ≤ r := by
  unfold hitSetN
  rw [mem_ofPred_eq, sigmaTop_of_mem hU hω]
  exact hitTime_le_iff (hU.cont ω)

/-- The event `StaysAway` of the integer σ-times: `⋃_k ⋂_n {dist(z, L_{σ_z(n)}) > 1/(k+1)}`. -/
noncomputable def staysAwaySeq (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) : Set Ω :=
  ⋃ k : ℕ, ⋂ n : ℕ, (hitSetN hU z n (1 / ((k : ℝ) + 1)))ᶜ

theorem measurableSet_staysAwaySeq (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) :
    MeasurableSet[⨆ n : ℕ, sigmaFiltration hU z ((n : ℝ≥0))] (staysAwaySeq hU z) := by
  refine MeasurableSet.iUnion fun k => MeasurableSet.iInter fun n => ?_
  refine MeasurableSet.compl ?_
  exact (le_iSup (fun n : ℕ => sigmaFiltration hU z ((n : ℝ≥0))) n) _
    (measurableSet_hitSetN hU z n _)

theorem mem_staysAwaySeq_iff (hU : IsSLEDriverAdapted a b c U P ℱ) {z : ℂ} {ω : Ω}
    (hG : ∀ s : ℝ≥0, (s : ℝ) ∈ sigmaDom (fun t => U t ω) (hU.cont ω) z) :
    ω ∈ staysAwaySeq hU z ↔ StaysAway (fun t => U t ω) z := by
  rw [staysAway_iff_exists_forall_nat (hU.cont ω) hG]
  unfold staysAwaySeq
  simp only [mem_iUnion, mem_iInter, mem_compl_iff]
  refine exists_congr fun k => forall_congr' fun n => ?_
  rw [mem_hitSetN_iff hU (hG n), not_le]

end Events

/-! ### The conclusion -/

section Main

open Polar

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- **Paper.tex:L1811-1816.** If `q(ξ) = P(StaysAway(U, ξ)) ≥ q_* > 0` for every `ξ ≠ 0`, then
`StaysAway(U, z)` holds a.s. for every `z ≠ 0`. -/
theorem ae_staysAway_of_lowerBound [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hc : c ^ 2 ≤ a * b) {qs : ℝ}
    (hqs : 0 < qs) (hlow : ∀ ξ : ℂ, ξ ≠ 0 → ENNReal.ofReal qs ≤ evProb StaysAway P U ξ)
    {z : ℂ} (hz : z ≠ 0) : ∀ᵐ ω ∂P, StaysAway (fun t => U t ω) z := by
  have hgood := ae_thetaHat_eq_and_continuous hU ha hc hz
  obtain ⟨M, hMm, hM⟩ := measurableEvents_staysAway
  -- the filtration `𝒢_n = ℱ_{σ_z(n)}`
  let 𝒢 : Filtration ℕ m :=
    { seq := fun n => sigmaFiltration hU z ((n : ℝ≥0))
      mono' := fun i j hij => (sigmaFiltration hU z).mono (by exact_mod_cast hij)
      le' := fun n => (sigmaFiltration hU z).le _ }
  have hE : MeasurableSet[⨆ n, 𝒢 n] (staysAwaySeq hU z) := measurableSet_staysAwaySeq hU z
  -- `E' = StaysAway` almost surely
  have hset : ∀ A : Set Ω, (A ∩ staysAwaySeq hU z : Set Ω) =ᵐ[P]
      (A ∩ {ω | StaysAway (fun t => U t ω) z} : Set Ω) := fun A => by
    filter_upwards [hgood] with ω hω
    exact propext (and_congr_right fun _ => mem_staysAwaySeq_iff hU hω.1)
  -- the lower bound on `𝒢_n`-sets
  have hbound : ∀ n (A : Set Ω), MeasurableSet[𝒢 n] A →
      qs * P.real A ≤ P.real (A ∩ staysAwaySeq hU z) := by
    intro n A hA
    have hmark := measure_inter_event_eq_lintegral hU ha hc futureDependentEvents_staysAway hMm
      hM hz ((n : ℝ≥0)) hA
    have hAm : MeasurableSet A := (𝒢.le n) _ hA
    have hne : ∀ᵐ ω ∂P, fHat hU z ((n : ℝ≥0)) ω ≠ 0 := by
      filter_upwards [hgood] with ω hω
      have hmem := hω.1 n
      rw [fHat_of_mem hU hmem]
      exact fPath_ne_zero (hU.cont ω) (sigmaTime_mem_lifeSet (hU.cont ω) hmem)
    have hlow' : ∀ᵐ ω ∂P, ENNReal.ofReal qs ≤ evProb StaysAway P U (fHat hU z ((n : ℝ≥0)) ω) := by
      filter_upwards [hne] with ω hω using hlow _ hω
    have h1 : ENNReal.ofReal qs * P A ≤ P (A ∩ staysAwaySeq hU z) := by
      rw [measure_congr (hset A), hmark, ← setLIntegral_const]
      exact lintegral_mono_ae (ae_restrict_of_ae hlow')
    have h2 : (ENNReal.ofReal qs * P A).toReal ≤ (P (A ∩ staysAwaySeq hU z)).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hqs.le] at h2
    exact h2
  have := ae_mem_of_forall_measureReal_le 𝒢 hE hqs hbound
  filter_upwards [this, hgood] with ω h1 hω
  exact (mem_staysAwaySeq_iff hU hω.1).1 h1

end Main

end ComplexSLE.Internal

end
