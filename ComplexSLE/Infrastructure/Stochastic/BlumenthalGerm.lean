/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Stochastic.AeSigma
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Blumenthal 0-1 law for a process with independent increments (measurable coordinates)

Source-independent probability. No external input is used; only Mathlib.

Let `U : ℝ≥0 → Ω → ℂ` have measurable coordinates, almost surely continuous paths with `U 0 = 0`
almost surely, and suppose that for every `t` the restarted path `s ↦ U (s + t) - U t` is
independent of the past `(U r)_{r ≤ t}` (outer measure semantics, as in
`IsSLEDriver.indep_shift_past`). Write `ℱ ε = σ(U s : s ≤ ε)`. If `A` is any set such that for every
`ε > 0` there is `B ∈ ℱ ε` with `P (A ∆ B) = 0`, then `P A = 0 ∨ P A = 1`
(`blumenthal_of_measurable`).

Route. Put `ε n = 1 / (n + 1)` and `𝒥 n = σ(U (s + ε n) - U (ε n) : s)`. Let `E ∈ ℱ 1` with
`P (A ∆ E) = 0`. Since `E` agrees a.e. with a set of `ℱ (ε n)`, which is independent of `𝒥 n`,
`E` is independent of each `𝒥 n`, hence of `⨆ n, 𝒥 n` (the `𝒥 n` increase,
`indep_iSup_of_directed_le`).
Every coordinate `U s` agrees a.e. with a `⨆ n, 𝒥 n`-measurable function, the limit of the
`𝒥 n`-measurable variables `U s - U (ε n)` (path continuity at `0` and `U 0 = 0`), so `E` agrees
a.e. with a set `G` of `⨆ n, 𝒥 n` (`aeSigma`), and `P E = P (E ∩ G) = P E * P G = (P E)^2`.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology symmDiff

namespace ComplexSLE.Infrastructure.Blumenthal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {U : ℝ≥0 → Ω → ℂ}

/-- The decreasing sequence of times `1 / (n + 1)`. -/
@[expose] noncomputable def epsSeq (n : ℕ) : ℝ≥0 := ((n : ℝ≥0) + 1)⁻¹

theorem epsSeq_pos (n : ℕ) : 0 < epsSeq n := by
  unfold epsSeq; positivity

theorem epsSeq_antitone : Antitone epsSeq := fun m n h => by
  unfold epsSeq
  exact inv_anti₀ (by positivity) (by gcongr)

theorem tendsto_epsSeq : Tendsto epsSeq atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ≥0) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => le_add_of_nonneg_right zero_le_one) tendsto_natCast_atTop_atTop
  exact tendsto_inv_atTop_zero.comp h1

/-- The σ-algebra of the path up to time `ε`. -/
noncomputable abbrev pastSigma (U : ℝ≥0 → Ω → ℂ) (ε : ℝ≥0) : MeasurableSpace Ω :=
  ⨆ (s : ℝ≥0) (_ : s ≤ ε), MeasurableSpace.comap (U s) inferInstance

/-- The σ-algebra of the path restarted at time `ε`. -/
noncomputable abbrev futureSigma (U : ℝ≥0 → Ω → ℂ) (ε : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (s : ℝ≥0) => U (s + ε) ω - U ε ω) MeasurableSpace.pi

theorem pastSigma_le (hm : ∀ s, Measurable (U s)) (ε : ℝ≥0) : pastSigma U ε ≤ mΩ :=
  iSup₂_le fun s _ => (hm s).comap_le

theorem futureSigma_le (hm : ∀ s, Measurable (U s)) (ε : ℝ≥0) : futureSigma U ε ≤ mΩ :=
  Measurable.comap_le (measurable_pi_iff.2 fun _ => (hm _).sub (hm _))

theorem pastSigma_le_comap (ε : ℝ≥0) : pastSigma U ε ≤
    MeasurableSpace.comap (fun ω (r : Set.Iic ε) => U (r : ℝ≥0) ω) MeasurableSpace.pi := by
  refine iSup₂_le fun s hs => ?_
  have : Measurable[MeasurableSpace.comap (fun ω (r : Set.Iic ε) => U (r : ℝ≥0) ω)
      MeasurableSpace.pi] (U s) :=
    (measurable_pi_apply (⟨s, hs⟩ : Set.Iic ε)).comp
      (comap_measurable (fun ω (r : Set.Iic ε) => U (r : ℝ≥0) ω))
  exact this.comap_le

theorem futureSigma_mono {ε ε' : ℝ≥0} (h : ε' ≤ ε) : futureSigma U ε ≤ futureSigma U ε' := by
  have hcoord : ∀ r : ℝ≥0, Measurable[futureSigma U ε'] (fun ω => U (r + ε') ω - U ε' ω) :=
    fun r => (measurable_pi_apply r).comp
      (comap_measurable (fun ω (s : ℝ≥0) => U (s + ε') ω - U ε' ω))
  have key : ∀ s : ℝ≥0, Measurable[futureSigma U ε'] (fun ω => U (s + ε) ω - U ε ω) := by
    intro s
    have := (hcoord (s + (ε - ε'))).sub (hcoord (ε - ε'))
    convert this using 1
    ext ω
    simp only [Pi.sub_apply, add_assoc, tsub_add_cancel_of_le h]
    ring
  refine Measurable.comap_le ?_
  exact (@measurable_pi_iff _ _ _ (futureSigma U ε') _ _).2 key

/-- Every coordinate agrees a.e. with a measurable function of the restarted paths at the times
`ε n`, `n ∈ ℕ` (the limit of `U s - U (ε n)`). -/
theorem exists_measurable_ae_eq
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => U t ω) (hzero : ∀ᵐ ω ∂P, U 0 ω = 0) (s : ℝ≥0) :
    ∃ W : Ω → ℂ, Measurable[⨆ n : ℕ, futureSigma U (epsSeq n)] W ∧ U s =ᵐ[P] W := by
  set Y : ℕ → Ω → ℂ := fun n ω => U ((s - epsSeq n) + epsSeq n) ω - U (epsSeq n) ω with hY
  have hYm : ∀ n, Measurable[⨆ n : ℕ, futureSigma U (epsSeq n)] (Y n) := fun n => by
    have h1 : Measurable[futureSigma U (epsSeq n)] (Y n) :=
      (measurable_pi_apply (s - epsSeq n)).comp
        (comap_measurable (fun ω (r : ℝ≥0) => U (r + epsSeq n) ω - U (epsSeq n) ω))
    exact h1.mono (le_iSup (fun n : ℕ => futureSigma U (epsSeq n)) n) le_rfl
  let _ : MeasurableSpace Ω := ⨆ n : ℕ, futureSigma U (epsSeq n)
  have hW : StronglyMeasurable fun ω => limUnder atTop (fun n => Y n ω) :=
    StronglyMeasurable.limUnder (fun n => (hYm n).stronglyMeasurable)
  refine ⟨_, hW.measurable, ?_⟩
  filter_upwards [hcont, hzero] with ω hc h0
  have h1 : Tendsto (fun n => (s - epsSeq n) + epsSeq n) atTop (𝓝 s) := by
    have := (tendsto_const_nhds (x := s)).sub tendsto_epsSeq |>.add tendsto_epsSeq
    simpa using this
  have h2 : Tendsto (fun n => Y n ω) atTop (𝓝 (U s ω - 0)) := by
    refine ((hc.tendsto s).comp h1).sub ?_
    have := (hc.tendsto 0).comp tendsto_epsSeq
    rw [h0] at this
    exact this
  rw [sub_zero] at h2
  exact h2.limUnder_eq.symm

/-- Up to null sets, the past up to time `1` is contained in the σ-algebra generated by the
restarted paths at the times `ε n`. -/
theorem pastSigma_one_le_aeSigma (hcont : ∀ᵐ ω ∂P, Continuous fun t => U t ω)
    (hzero : ∀ᵐ ω ∂P, U 0 ω = 0) :
    pastSigma U 1 ≤ aeSigma P (⨆ n : ℕ, futureSigma U (epsSeq n)) :=
  iSup₂_le fun s _ => by
    obtain ⟨W, hW, hae⟩ := exists_measurable_ae_eq hcont hzero s
    exact (measurable_aeSigma hW hae).comap_le

/-- **Blumenthal 0-1 law for a measurable process with independent increments.** -/
theorem blumenthal_of_measurable [IsProbabilityMeasure P] (hm : ∀ s, Measurable (U s))
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => U t ω) (hzero : ∀ᵐ ω ∂P, U 0 ω = 0)
    (hind : ∀ t : ℝ≥0, Indep (futureSigma U t)
      (MeasurableSpace.comap (fun ω (r : Set.Iic t) => U (r : ℝ≥0) ω) MeasurableSpace.pi) P)
    (A : Set Ω)
    (hA : ∀ ε : ℝ≥0, 0 < ε → ∃ B : Set Ω, MeasurableSet[pastSigma U ε] B ∧ P (A ∆ B) = 0) :
    P A = 0 ∨ P A = 1 := by
  obtain ⟨E, hEm, hAE⟩ := hA 1 one_pos
  have hEmeas : MeasurableSet E := pastSigma_le hm 1 _ hEm
  have hB : ∀ n, ∃ B : Set Ω, MeasurableSet[pastSigma U (epsSeq n)] B ∧ P (E ∆ B) = 0 := fun n => by
    obtain ⟨B, hBm, hAB⟩ := hA (epsSeq n) (epsSeq_pos n)
    refine ⟨B, hBm, measure_mono_null (symmDiff_triangle E A B) ?_⟩
    rw [symmDiff_comm E A]
    exact measure_union_null hAE hAB
  have hgen : MeasurableSpace.generateFrom {E} ≤ mΩ :=
    MeasurableSpace.generateFrom_le fun t ht => by rw [mem_singleton_iff.1 ht]; exact hEmeas
  have hIndE : ∀ n, Indep (futureSigma U (epsSeq n)) (MeasurableSpace.generateFrom {E}) P := by
    intro n
    obtain ⟨B, hBm, hEB⟩ := hB n
    have hEB' : E =ᵐ[P] B := measure_symmDiff_eq_zero_iff.1 hEB
    have hind' : Indep (futureSigma U (epsSeq n)) (pastSigma U (epsSeq n)) P :=
      indep_of_indep_of_le_right (hind (epsSeq n)) (pastSigma_le_comap _)
    refine IndepSets.indep (futureSigma_le hm _) hgen
      (p1 := {F | MeasurableSet[futureSigma U (epsSeq n)] F}) (p2 := {E})
      (@MeasurableSpace.isPiSystem_measurableSet _ (futureSigma U (epsSeq n)))
      (IsPiSystem.singleton E)
      (@MeasurableSpace.generateFrom_measurableSet _ (futureSigma U (epsSeq n))).symm rfl ?_
    refine (IndepSets_iff _ _ _).2 fun F E' hF hE' => ?_
    rw [mem_singleton_iff.1 hE']
    have h1 := (Indep_iff _ _ _).1 hind' F B hF hBm
    rw [measure_congr (EventuallyEqSet.inter EventuallyEq.rfl hEB'), h1, measure_congr hEB']
  have hdir : Directed (· ≤ ·) (fun n : ℕ => futureSigma U (epsSeq n)) :=
    Monotone.directed_le fun n m h => futureSigma_mono (epsSeq_antitone h)
  have hIndAll := indep_iSup_of_directed_le hIndE (fun n => futureSigma_le hm _) hgen hdir
  obtain ⟨G, hG, hEG⟩ := pastSigma_one_le_aeSigma hcont hzero E hEm
  have hGE : G =ᵐ[P] E := (measure_symmDiff_eq_zero_iff.1 (by rwa [symmDiff_comm] at hEG))
  have h1 := (Indep_iff _ _ _).1 hIndAll G E hG (MeasurableSpace.measurableSet_generateFrom rfl)
  rw [measure_congr (EventuallyEqSet.inter hGE EventuallyEq.rfl), inter_self,
    measure_congr hGE] at h1
  have hPA : P A = P E := measure_congr (measure_symmDiff_eq_zero_iff.1 hAE)
  rw [hPA]
  by_cases h0 : P E = 0
  · exact Or.inl h0
  · right
    have h2 : P E * 1 = P E * P E := by rwa [mul_one]
    exact (ENNReal.mul_right_inj h0 (measure_ne_top P E)).1 h2 |>.symm

end ComplexSLE.Infrastructure.Blumenthal

end
