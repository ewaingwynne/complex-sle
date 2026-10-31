/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Disconnect.Thm110AMarkov
public import ComplexSLE.Internal.Phases.Prop32BUpZeroOne

/-!
# Theorem 1.10(a), upgrade step: the uniform bound and the martingale 0-1 step (M8/T5b)

Source: paper.tex:L2199-2217 (as the proof of Proposition 3.2(b), paper.tex:L1808-1816).

* `exists_lowerBound_disc`: if `q(z) = P(Disc(U, z)) > 0` for every `z ≠ 0`, then `q ≥ q_* > 0`
  on `ℂ ∖ {0}`. Here `q` is lower semicontinuous (`lowerSemicontinuous_evProb_disc`), so it
  attains its minimum on the compact unit circle (no Koebe ball is needed), and `q(ξ) = q(ξ/|ξ|)`.
* `discSeq hU z`: the event `⋃_{q ∈ ℚ>0} ⋃_n ({DiscAt(U, z, q)} ∩ {q ≤ σ_z(n)})`. It lies in
  `⨆_n 𝒢_n`, for `𝒢_n = ℱ_{σ_z(n)}` (`measurableSet_discSeq`: `{DiscAt at q} ∈ ℱ_q` by
  `measurableSet_setOf_discAt` and `B ∈ ℱ_q ⇒ B ∩ {q ≤ σ} ∈ ℱ_σ`), and for a continuous driver
  with all `σ_z(n) < ∞` it is equivalent to `Disc(U, z)` (`mem_discSeq_iff`: if `DiscAt` at `q`,
  then `q < T_z`, so `q ≤ σ_z(n)` for some `n`, as `σ_z(n) ↑ T_z`).
* `ae_disc_of_lowerBound`: the conclusion. For `A ∈ 𝒢_n`, the restart inequality at `σ_z(n)` gives
  `q_* P(A) ≤ ∫_A q(f̂_n(z)) dP ≤ P(A ∩ Disc(U, z))`; Lévy's upward theorem
  (`ae_mem_of_forall_measureReal_le`) yields `P(Disc(U, z)) = 1`.

Consumes the EXTERNAL `strongMarkov_sleDriver`.
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Metric

namespace ComplexSLE.Internal

open Polar

section LowerBound

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- **Lower semicontinuity and compactness** (paper.tex:L2212): if `q(z) > 0` for every `z ≠ 0`,
then `q ≥ q_* > 0` on `ℂ ∖ {0}`. -/
theorem exists_lowerBound_disc [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ)
    (hpos : ∀ z : ℂ, z ≠ 0 → 0 < evProb Disc P U z) :
    ∃ qs : ℝ, 0 < qs ∧ ∀ ξ : ℂ, ξ ≠ 0 → ENNReal.ofReal qs ≤ evProb Disc P U ξ := by
  obtain ⟨M, hMm, hM⟩ := measurableEvents_disc
  have hsph : ∀ z ∈ sphere (0 : ℂ) 1, z ≠ 0 := fun z hz h => by
    rw [mem_sphere_zero_iff_norm, h, norm_zero] at hz
    exact zero_ne_one hz
  have hone : (1 : ℂ) ∈ sphere (0 : ℂ) 1 := by simp
  obtain ⟨x, hxS, hx⟩ := (lowerSemicontinuous_evProb_disc hU).lowerSemicontinuousOn
    (sphere (0 : ℂ) 1) |>.exists_isMinOn ⟨1, hone⟩ (isCompact_sphere (0 : ℂ) 1)
  set qm : ℝ≥0∞ := evProb Disc P U x with hqm
  have hqm0 : 0 < qm := hpos x (hsph x hxS)
  have hqmtop : qm ≠ ⊤ := measure_ne_top _ _
  refine ⟨qm.toReal, ENNReal.toReal_pos hqm0.ne' hqmtop, fun ξ hξ => ?_⟩
  rw [ENNReal.ofReal_toReal hqmtop, evProb_eq_unit hU scaleInvariantEvents_disc hMm hM hξ]
  refine hx ?_
  rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, norm_norm,
    div_self (norm_ne_zero_iff.2 hξ)]

end LowerBound

section ZeroOne

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- `B ∈ ℱ_q ⇒ B ∩ {q ≤ σ_z(s)} ∈ ℱ_{σ_z(s)}`. -/
theorem measurableSet_inter_le_sigmaTop (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ)
    (s q : ℝ≥0) {B : Set Ω} (hB : MeasurableSet[ℱ q] B) :
    MeasurableSet[sigmaFiltration hU z s]
      (B ∩ {ω | (q : WithTop ℝ≥0) ≤ sigmaTop hU z s ω}) := by
  have hτ := isStoppingTime_const ℱ q
  have hπ := isStoppingTime_sigmaTop hU z s
  have hB' : MeasurableSet[hτ.measurableSpace] B := by
    rw [IsStoppingTime.measurableSpace_const]; exact hB
  have h1 := hτ.measurableSet_inter_le hπ B hB'
  exact IsStoppingTime.measurableSpace_mono (hτ.min hπ) hπ (fun ω => min_le_right _ _) _ h1

/-- The event `⋃_{q ∈ ℚ>0} ⋃_n ({DiscAt(U, z, q)} ∩ {q ≤ σ_z(n)})`. -/
noncomputable def discSeq (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) : Set Ω :=
  ⋃ q : ℚ, ⋃ (_ : 0 < q), ⋃ n : ℕ,
    {ω | DiscAt (fun t => U t ω) z (q : ℝ).toNNReal} ∩
      {ω | (((q : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ sigmaTop hU z ((n : ℝ≥0)) ω}

theorem measurableSet_discSeq (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) :
    MeasurableSet[⨆ n : ℕ, sigmaFiltration hU z ((n : ℝ≥0))] (discSeq hU z) := by
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iUnion fun n => ?_
  exact (le_iSup (fun n : ℕ => sigmaFiltration hU z ((n : ℝ≥0))) n) _
    (measurableSet_inter_le_sigmaTop hU z _ _ (measurableSet_setOf_discAt hU z _))

theorem mem_discSeq_iff (hU : IsSLEDriverAdapted a b c U P ℱ) {z : ℂ} {ω : Ω}
    (hG : ∀ s : ℝ≥0, (s : ℝ) ∈ sigmaDom (fun t => U t ω) (hU.cont ω) z) :
    ω ∈ discSeq hU z ↔ Disc (fun t => U t ω) z := by
  rw [disc_iff_exists_rat]
  unfold discSeq
  simp only [mem_iUnion, mem_inter_iff, exists_prop, mem_ofPred_eq]
  constructor
  · rintro ⟨q, hq, n, hd, -⟩
    exact ⟨q, hq, hd⟩
  · rintro ⟨q, hq, hd⟩
    refine ⟨q, hq, ?_⟩
    set t : ℝ≥0 := (q : ℝ).toNNReal with ht
    set u : ℝ≥0 → ℂ := fun s => U s ω with hu
    have hlife : (t : ℝ) ∈ lifeSet u z := coe_mem_lifeSet_iff.2 hd.1
    set s0 : ℝ := clock u (hU.cont ω) z t with hs0def
    have hs0 : s0 ∈ sigmaDom u (hU.cont ω) z := clock_mem_sigmaDom (hU.cont ω) hlife
    have hσ0 : sigmaTime u (hU.cont ω) z s0 = t := sigmaTime_clock (hU.cont ω) hlife
    set n : ℕ := ⌈s0⌉₊ with hn
    have hsn : s0 ≤ (((n : ℝ≥0)) : ℝ) := by
      rw [NNReal.coe_natCast]; exact Nat.le_ceil s0
    have hmon := sigmaTime_monotoneOn (hU.cont ω) z hs0 (hG n) hsn
    rw [hσ0] at hmon
    refine ⟨n, hd, ?_⟩
    rw [sigmaTop_of_mem hU (hG n), WithTop.coe_le_coe, ← NNReal.coe_le_coe,
      Real.coe_toNNReal _ (sigmaTime_nonneg (hU.cont ω) (hG n))]
    exact hmon

/-- **The martingale 0-1 step for `Disc`** (paper.tex:L2212-2217, as paper.tex:L1811-1816). If
`q(ξ) = P(Disc(U, ξ)) ≥ q_* > 0` for every `ξ ≠ 0`, then `Disc(U, z)` holds a.s. for every
`z ≠ 0`. -/
theorem ae_disc_of_lowerBound [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hc : c ^ 2 ≤ a * b) {qs : ℝ}
    (hqs : 0 < qs) (hlow : ∀ ξ : ℂ, ξ ≠ 0 → ENNReal.ofReal qs ≤ evProb Disc P U ξ)
    {z : ℂ} (hz : z ≠ 0) : ∀ᵐ ω ∂P, Disc (fun t => U t ω) z := by
  have hgood := ae_thetaHat_eq_and_continuous hU ha hc hz
  obtain ⟨M, hMm, hM⟩ := measurableEvents_disc
  -- the filtration `𝒢_n = ℱ_{σ_z(n)}`
  let 𝒢 : Filtration ℕ m :=
    { seq := fun n => sigmaFiltration hU z ((n : ℝ≥0))
      mono' := fun i j hij => (sigmaFiltration hU z).mono (by exact_mod_cast hij)
      le' := fun n => (sigmaFiltration hU z).le _ }
  have hE : MeasurableSet[⨆ n, 𝒢 n] (discSeq hU z) := measurableSet_discSeq hU z
  -- `discSeq = Disc` almost surely
  have hset : ∀ A : Set Ω, (A ∩ discSeq hU z : Set Ω) =ᵐ[P]
      (A ∩ {ω | Disc (fun t => U t ω) z} : Set Ω) := fun A => by
    filter_upwards [hgood] with ω hω
    exact propext (and_congr_right fun _ => mem_discSeq_iff hU hω.1)
  -- the lower bound on `𝒢_n`-sets
  have hbound : ∀ n (A : Set Ω), MeasurableSet[𝒢 n] A →
      qs * P.real A ≤ P.real (A ∩ discSeq hU z) := by
    intro n A hA
    have hmark := lintegral_evProb_fHat_le hU ha hc restartImpliesEvents_disc hMm hM hz
      ((n : ℝ≥0)) hA
    have hne : ∀ᵐ ω ∂P, fHat hU z ((n : ℝ≥0)) ω ≠ 0 := by
      filter_upwards [hgood] with ω hω
      have hmem := hω.1 n
      rw [fHat_of_mem hU hmem]
      exact fPath_ne_zero (hU.cont ω) (sigmaTime_mem_lifeSet (hU.cont ω) hmem)
    have hlow' : ∀ᵐ ω ∂P, ENNReal.ofReal qs ≤ evProb Disc P U (fHat hU z ((n : ℝ≥0)) ω) := by
      filter_upwards [hne] with ω hω using hlow _ hω
    have h1 : ENNReal.ofReal qs * P A ≤ P (A ∩ discSeq hU z) := by
      rw [measure_congr (hset A)]
      refine le_trans ?_ hmark
      rw [← setLIntegral_const]
      exact lintegral_mono_ae (ae_restrict_of_ae hlow')
    have h2 : (ENNReal.ofReal qs * P A).toReal ≤ (P (A ∩ discSeq hU z)).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hqs.le] at h2
    exact h2
  have := ae_mem_of_forall_measureReal_le 𝒢 hE hqs hbound
  filter_upwards [this, hgood] with ω h1 hω
  exact (mem_discSeq_iff hU hω.1).1 h1

end ZeroOne

end ComplexSLE.Internal

end
