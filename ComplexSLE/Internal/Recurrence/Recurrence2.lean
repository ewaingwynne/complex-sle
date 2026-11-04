/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

import all ComplexSLE.Internal.Recurrence.Renewal
public import ComplexSLE.Internal.Recurrence.SLE
public import ComplexSLE.Internal.Recurrence.CondDiffusion

/-!
# Lemma 2.16: the Markov transport of (2.45) to deterministic times

`sle_markov_transport` is the Markov transport of claim (2.45) (`sle_angle_hit_unif`,
`ComplexSLE/Internal/Recurrence/SLE.lean`) to deterministic times, the form of the hypothesis
`hren` of the renewal argument (`ae_frequently_mem_latticeSet`, `Renewal.lean`). It is proved from
the conditioning lemma `isDiffusionSolution_cond_shift` (the Markov property at a fixed time,
martingale form) and `π`-periodicity: splitting `A ∩ {X_s ∈ C_ε}` by the integer `n` with
`X_s ∈ [x + nπ, x + nπ + π - ε]`, the shifted process `X_{s+·} - nπ` solves the same martingale
problem under `P[|A ∩ {X_s ∈ I_n}]`, started in `[x, x + π - ε]`, so the uniform bound (2.45)
applies on every piece, and the pieces are summed.
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
open ComplexSLE.Internal

namespace ComplexSLE.Recurrence

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ≥0 mΩ}

/-! ### Real and extended-real forms of a ratio bound -/

theorem ofReal_mul_measure_le {δ : ℝ} (hδ : 0 ≤ δ) {S S' : Set Ω}
    (h : δ * P.real S ≤ P.real S') : ENNReal.ofReal δ * P S ≤ P S' := by
  calc ENNReal.ofReal δ * P S = ENNReal.ofReal δ * ENNReal.ofReal (P.real S) := by
        rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ = ENNReal.ofReal (δ * P.real S) := (ENNReal.ofReal_mul hδ).symm
    _ ≤ ENNReal.ofReal (P.real S') := ENNReal.ofReal_le_ofReal h
    _ = P S' := by rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem real_mul_measureReal_le {δ : ℝ} (hδ : 0 ≤ δ) {S S' : Set Ω}
    (h : ENNReal.ofReal δ * P S ≤ P S') : δ * P.real S ≤ P.real S' := by
  have := ENNReal.toReal_mono (measure_ne_top P S') h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ] at this

/-! ### The Markov transport of (2.45) to deterministic times -/

/-- **Markov transport at a fixed time.** For continuous `π`-periodic coefficients, a solution `X`
with everywhere-continuous paths, and a uniform bound `δ ≤ P'(∃ t ≤ T, X'_t = x)` valid for all
solutions started in `[x, x + π - ε]` (on any probability space), one has
`δ P(A ∩ {X_s ∈ C_ε}) ≤ P(A ∩ {X_s ∈ C_ε} ∩ {∃ t ≤ T, X_{s+t} ∈ x + πℤ})` for all `s` and
`A ∈ ℱ_s`. -/
theorem sle_markov_transport {α β : ℝ → ℝ} (hα : Continuous α) (hβ : Continuous β)
    (hαper : Function.Periodic α π) (hβper : ∀ v, β (v + π) ^ 2 = β v ^ 2)
    {X : ℝ≥0 → Ω → ℝ} (hX : IsDiffusionSolution ℱ α β X P)
    (hXc : ∀ ω, Continuous fun t => X t ω) (x : ℝ) {ε : ℝ} {T : ℝ≥0} {δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ)
    (h245 : ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (ℱ' : Filtration ℝ≥0 ‹_›) (X' : ℝ≥0 → Ω' → ℝ), IsDiffusionSolution ℱ' α β X' P' →
        (∀ ω, Continuous fun t => X' t ω) → (∀ᵐ ω ∂P', X' 0 ω ∈ Icc x (x + π - ε)) →
        δ ≤ P'.real {ω | ∃ t : ℝ≥0, t ≤ T ∧ X' t ω = x})
    (s : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[ℱ s] A) :
    δ * P.real (A ∩ {ω | X s ω ∈ goodSet x ε}) ≤
      P.real (A ∩ {ω | X s ω ∈ goodSet x ε} ∩ {ω | ∃ t ≤ T, X (s + t) ω ∈ latticeSet x}) := by
  -- the pieces `G n = {X_s ∈ [x + nπ, x + nπ + π - ε]}` and the window event
  set G : ℤ → Set Ω := fun n =>
    {ω | X s ω ∈ Icc (x + n * π) (x + n * π + π - ε)} with hG
  set W : Set Ω := {ω | ∃ t ≤ T, X (s + t) ω ∈ latticeSet x} with hW
  have hXs : Measurable[ℱ s] (X s) := (hX.1.stronglyAdapted s).measurable
  have hGmeas : ∀ n, MeasurableSet[ℱ s] (G n) := fun n => hXs measurableSet_Icc
  have hWmeas : MeasurableSet W :=
    ℱ.le _ _ (measurableSet_window (x := x) hX.1.stronglyAdapted hXc s T)
  have hAm : MeasurableSet A := ℱ.le s _ hA
  have hGunion : A ∩ {ω | X s ω ∈ goodSet x ε} = ⋃ n, A ∩ G n := by
    ext ω
    simp only [goodSet, hG, mem_inter_iff, mem_ofPred_eq, mem_iUnion]
    exact exists_and_left.symm
  have hGdisj : Pairwise (Function.onFun Disjoint fun n => A ∩ G n) := by
    intro n k hnk
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨-, h1⟩ ⟨-, h2⟩
    simp only [hG, mem_ofPred_eq, mem_Icc] at h1 h2
    rcases lt_or_gt_of_ne hnk with h | h
    · have : (n : ℝ) + 1 ≤ k := by exact_mod_cast h
      nlinarith [Real.pi_pos]
    · have : (k : ℝ) + 1 ≤ n := by exact_mod_cast h
      nlinarith [Real.pi_pos]
  -- the claim on each piece, in `ℝ≥0∞`
  have hpiece : ∀ n : ℤ, ENNReal.ofReal δ * P (A ∩ G n) ≤ P (A ∩ G n ∩ W) := by
    intro n
    by_cases h0 : P (A ∩ G n) = 0
    · rw [h0, mul_zero]; exact zero_le
    have hB : MeasurableSet[ℱ s] (A ∩ G n) := hA.inter (hGmeas n)
    have hBm : MeasurableSet (A ∩ G n) := ℱ.le s _ hB
    have : IsProbabilityMeasure P[|A ∩ G n] := cond_isProbabilityMeasure h0
    have hY := isDiffusionSolution_cond_shift hα hβ hX hXc s hB h0
    have hper_α : ∀ v, α (v - n * π) = α v := fun v => hαper.sub_int_mul_eq n
    have hper_β : ∀ v, β (v - n * π) ^ 2 = β v ^ 2 := fun v =>
      (Function.Periodic.sub_int_mul_eq (f := fun v => β v ^ 2) (c := π)
        (fun v => hβper v) n :)
    have hZ := isDiffusionSolution_sub_const (n * π) hper_α hper_β hY
    have key := h245 Ω P[|A ∩ G n] (shiftFiltration ℱ s) (fun t ω => X (s + t) ω - n * π) hZ
      (fun ω => ((hXc ω).comp (continuous_const.add continuous_id)).sub continuous_const)
      (by
        refine ae_cond_of_forall_mem hBm fun ω hω => ?_
        obtain ⟨-, hω⟩ := hω
        simp only [hG, mem_ofPred_eq, mem_Icc] at hω
        simp only [add_zero, mem_Icc]
        constructor <;> linarith [hω.1, hω.2])
    -- transport back to `P`
    have hsub : {ω | ∃ t : ℝ≥0, t ≤ T ∧ X (s + t) ω - n * π = x} ⊆ W := by
      rintro ω ⟨t, htT, ht⟩
      refine ⟨t, htT, mem_latticeSet_iff.2 ⟨n, by linarith⟩⟩
    have hcond : P[|A ∩ G n].real W = (P.real (A ∩ G n))⁻¹ * P.real (A ∩ G n ∩ W) := by
      simp only [Measure.real, cond_apply hBm, ENNReal.toReal_mul, ENNReal.toReal_inv]
    have hpos : 0 < P.real (A ∩ G n) := ENNReal.toReal_pos h0 (measure_ne_top _ _)
    have hle : δ ≤ (P.real (A ∩ G n))⁻¹ * P.real (A ∩ G n ∩ W) := by
      rw [← hcond]
      exact key.trans (measureReal_mono hsub)
    exact ofReal_mul_measure_le hδ.le (by
      have := (le_inv_mul_iff₀ hpos).1 hle
      linarith)
  -- sum over the pieces
  have hmeasA : ∀ n, MeasurableSet (A ∩ G n) := fun n => hAm.inter (ℱ.le s _ (hGmeas n))
  have hdisjW : Pairwise (Function.onFun Disjoint fun n => A ∩ G n ∩ W) := fun n k hnk =>
    (hGdisj hnk).mono inter_subset_left inter_subset_left
  have hU1 : P (A ∩ {ω | X s ω ∈ goodSet x ε}) = ∑' n, P (A ∩ G n) := by
    rw [hGunion]; exact measure_iUnion hGdisj hmeasA
  have hU2 : P (A ∩ {ω | X s ω ∈ goodSet x ε} ∩ W) = ∑' n, P (A ∩ G n ∩ W) := by
    rw [hGunion, iUnion_inter]
    exact measure_iUnion hdisjW fun n => (hmeasA n).inter hWmeas
  refine real_mul_measureReal_le hδ.le ?_
  rw [hU1, hU2, ← ENNReal.tsum_mul_left]
  exact tsum_le_tsum hpiece

/-! ### Lemma 2.16 without the Markov hypothesis -/

variable {a b c : ℝ} {β : ℝ → ℝ}

end ComplexSLE.Recurrence

end
