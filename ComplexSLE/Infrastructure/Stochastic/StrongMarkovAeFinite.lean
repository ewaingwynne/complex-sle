/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Stochastic.StrongMarkovCore

import ComplexSLE.Infrastructure.Stochastic.TimeChangeOptionalSampling
import Mathlib.MeasureTheory.Measure.Continuity

/-!
# Strong Markov property, step 3: almost surely finite stopping times

Source-independent probability. No external input is used; only Mathlib.

`StrongMarkovCore` handles `ℝ≥0`-valued stopping times. Here `τ : Ω → WithTop ℝ≥0` is a stopping
time with `τ ≠ ⊤` almost surely, and the restarted path is `smPath U (fun ω => (τ ω).untopA)`
(`untopA` sends `⊤` to a junk value, on a null set). For `A ∈ ℱ_τ`, the truncated times `τ ∧ n`
are `ℝ≥0`-valued stopping times, `A ∩ {τ ≤ n} ∈ ℱ_{τ ∧ n}`, and on `{τ ≤ n}` the restarted paths
at `τ` and `τ ∧ n` agree, so that

* `map_restrict_smPath_eq_aeFinite`:
  `(P|_A).map (smPath U τ) = P A • P.map (smPath U (fun _ => 0))`,

by continuity of the measure along `{τ ≤ n} ↑ {τ < ⊤}` (the same truncation argument as
`BouRabeeGwynne.standardBrownianLaw_aeFiniteStopping_map_restrict`, leobon12/lean-formalizations
@31e7483). Corollaries: `map_smPath_aeFinite` (take `A = univ`) and `indep_smPath_aeFinite`.
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Infrastructure.StrongMarkov

variable {Ω E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {U : ℝ≥0 → Ω → E}

/-- Truncation: `P (X ∩ {τ ≤ n}) → P X` when `τ` is a.s. finite. -/
theorem tendsto_measure_inter_le_nat {τ : Ω → WithTop ℝ≥0} (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤)
    (X : Set Ω) :
    Tendsto (fun n : ℕ => P (X ∩ {ω | τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)})) atTop (𝓝 (P X)) := by
  have hmono : Monotone (fun n : ℕ => X ∩ {ω | τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}) := by
    intro n m hnm ω hω
    refine ⟨hω.1, ?_⟩
    have : ((n : ℝ≥0) : WithTop ℝ≥0) ≤ ((m : ℝ≥0) : WithTop ℝ≥0) := by
      exact_mod_cast (Nat.cast_le.2 hnm : (n : ℝ≥0) ≤ m)
    exact hω.2.trans this
  have hunion : (⋃ n : ℕ, X ∩ {ω | τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}) =ᵐ[P] X := by
    filter_upwards [hfin] with ω hω
    apply propext
    constructor
    · intro h
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
      exact hn.1
    · intro hX
      obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hω
      obtain ⟨n, hn⟩ := exists_nat_ge a
      refine Set.mem_iUnion.mpr ⟨n, hX, ?_⟩
      change τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)
      rw [← ha]
      exact_mod_cast hn
  simpa only [measure_congr hunion, Function.comp_def] using
    (tendsto_measure_iUnion_atTop (μ := P) hmono)

/-- The truncated time `τ ∧ n` as an `ℝ≥0`-valued stopping time. -/
theorem isStoppingTime_untopA_min {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) (n : ℝ≥0) :
    IsStoppingTime ℱ fun ω => (((min (τ ω) (n : WithTop ℝ≥0)).untopA : ℝ≥0) : WithTop ℝ≥0) := by
  have h : (fun ω => (((min (τ ω) (n : WithTop ℝ≥0)).untopA : ℝ≥0) : WithTop ℝ≥0)) =
      fun ω => min (τ ω) (n : WithTop ℝ≥0) := by
    funext ω
    have hne : min (τ ω) (n : WithTop ℝ≥0) ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)
    rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop]
  rw [h]
  exact hτ.min_const n

/-- **Strong Markov property at an a.s. finite stopping time, law form.** `T = (τ).untopA` sends
the value `⊤` to a junk value; this happens only on a null set. -/
theorem map_restrict_smPath_eq_aeFinite [IsProbabilityMeasure P]
    (hUc : ∀ ω, Continuous fun t => U t ω) (hUm : ∀ t, Measurable (U t))
    (hM : SimpleMarkov U P ℱ) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (P.restrict A).map (smPath U fun ω => (τ ω).untopA) =
      P A • P.map (smPath U (fun _ => 0)) := by
  have hTm : Measurable fun ω => (τ ω).untopA := hτ.measurable'.untopA
  have hsm := measurable_smPath hUc hUm hTm
  ext S hS
  rw [Measure.map_apply hsm hS, Measure.restrict_apply (hsm hS), Measure.smul_apply, smul_eq_mul]
  have heq : ∀ n : ℕ, P ((smPath U (fun ω => (τ ω).untopA) ⁻¹' S ∩ A) ∩
      {ω | τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}) =
      P.map (smPath U (fun _ => 0)) S * P (A ∩ {ω | τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}) := by
    intro n
    set τn : Ω → ℝ≥0 := fun ω => (min (τ ω) ((n : ℝ≥0) : WithTop ℝ≥0)).untopA with hτn
    have hstop : IsStoppingTime ℱ fun ω => (τn ω : WithTop ℝ≥0) :=
      isStoppingTime_untopA_min hτ n
    set An : Set Ω := A ∩ {ω | τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} with hAn
    have hAn_meas : MeasurableSet[hstop.measurableSpace] An := by
      have h1 : MeasurableSet[hτ.measurableSpace] An :=
        hA.inter (hτ.measurableSet_le' (n : ℝ≥0))
      have h2 := (hτ.measurableSet_inter_le_const_iff A (n : ℝ≥0)).1 h1
      have hcongr := measurableSpace_congr_fun (hτ.min_const (n : ℝ≥0)) hstop (by
        funext ω
        have hne : min (τ ω) ((n : ℝ≥0) : WithTop ℝ≥0) ≠ ⊤ :=
          ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)
        simp only [hτn]
        rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop])
      rwa [hcongr] at h2
    have hlaw := map_restrict_smPath_eq hUc hUm hM hstop hAn_meas
    have hmτn : Measurable (smPath U τn) :=
      measurable_smPath hUc hUm (measurable_of_isStoppingTime hstop)
    have heval := congrArg (fun ρ : Measure (ℝ≥0 → E) => ρ S) hlaw
    simp only [Measure.map_apply hmτn hS, Measure.restrict_apply (hmτn hS), Measure.smul_apply,
      smul_eq_mul] at heval
    have hsets : smPath U τn ⁻¹' S ∩ An =
        (smPath U (fun ω => (τ ω).untopA) ⁻¹' S ∩ A) ∩
          {ω | τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      by_cases h : τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)
      · have : τn ω = (τ ω).untopA := by simp only [hτn, min_eq_left h]
        have hp : smPath U τn ω = smPath U (fun ω => (τ ω).untopA) ω := by
          funext s; simp only [smPath, smShift, this]
        simp only [Set.mem_inter_iff, Set.mem_preimage, hAn, Set.mem_ofPred_eq, h, and_true, hp]
      · simp only [Set.mem_inter_iff, hAn, Set.mem_ofPred_eq, h, and_false]
    rw [hsets] at heval
    exact heval.trans (mul_comm _ _)
  have hleft := tendsto_measure_inter_le_nat hfin (smPath U (fun ω => (τ ω).untopA) ⁻¹' S ∩ A)
  have hright := ((ENNReal.continuous_const_mul
    (measure_ne_top (P.map (smPath U fun _ => 0)) S)).tendsto (P A)).comp
    (tendsto_measure_inter_le_nat hfin A)
  have hevent := tendsto_nhds_unique hleft (hright.congr fun n => (heq n).symm)
  exact hevent.trans (mul_comm _ _)

/-- **Strong Markov property at an a.s. finite stopping time, unconditional law.** -/
theorem map_smPath_aeFinite [IsProbabilityMeasure P]
    (hUc : ∀ ω, Continuous fun t => U t ω) (hUm : ∀ t, Measurable (U t))
    (hM : SimpleMarkov U P ℱ) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    P.map (smPath U fun ω => (τ ω).untopA) = P.map (smPath U (fun _ => 0)) := by
  have h := map_restrict_smPath_eq_aeFinite hUc hUm hM hτ hfin
    (@MeasurableSet.univ _ hτ.measurableSpace)
  rwa [Measure.restrict_univ, measure_univ, one_smul] at h

/-- **Strong Markov property at an a.s. finite stopping time, independence.** The restarted path
is independent of `ℱ_τ`. -/
theorem indep_smPath_aeFinite [IsProbabilityMeasure P]
    (hUc : ∀ ω, Continuous fun t => U t ω) (hUm : ∀ t, Measurable (U t))
    (hM : SimpleMarkov U P ℱ) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    Indep hτ.measurableSpace
      (MeasurableSpace.comap (smPath U fun ω => (τ ω).untopA) MeasurableSpace.pi) P :=
  indep_comap_of_map_restrict_eq
    (measurable_smPath hUc hUm hτ.measurable'.untopA)
    (fun _ hA => map_restrict_smPath_eq_aeFinite hUc hUm hM hτ hfin hA)

end ComplexSLE.Infrastructure.StrongMarkov

end
