/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

import all ComplexSLE.Internal.Recurrence.Renewal
public import ComplexSLE.Internal.Recurrence.SLE
public import ComplexSLE.Internal.Recurrence.CondDiffusion

/-!
# Lemma 2.16 without the Markov hypothesis, and the case `c ≤ 0`

`sle_markov_transport` discharges the hypothesis `hMarkov` of `sle_recurrence`
(`ComplexSLE/Internal/Recurrence/SLE.lean`) from the conditioning lemma
`isDiffusionSolution_cond_shift` (the Markov property at a fixed time, martingale form) and
`π`-periodicity: splitting `A ∩ {X_s ∈ C_ε}` by the integer `n` with
`X_s ∈ [x + nπ, x + nπ + π - ε]`, the shifted process `X_{s+·} - nπ` solves the same martingale
problem under `P[|A ∩ {X_s ∈ I_n}]`, started in `[x, x + π - ε]`, so the uniform bound (2.45)
applies on every piece, and the pieces are summed.

* `sle_recurrence'`: Lemma 2.16 for `c ≥ 0` with only the stationarity input `hstat`;
* `sle_recurrence_nonpos`: Lemma 2.16 for `c ≤ 0`, by reflection `X ↦ -X`
  (`step:wlog-c-nonneg-arg`): the recurrence point for `X` is the reflected one.
  Stationarity enters through the reflected process `-X` and the reflected point `-x`.

Everything uses `ito_formula` (through `sle_angle_hit_unif`), proved in-project.
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

/-- **Lemma 2.16 (recurrence), `c ≥ 0`, without the Markov hypothesis.** Let `X` solve the
`θ̂`-SDE (martingale form) with everywhere-continuous paths, and assume the stationarity input
`hstat` (for every `η > 0` some `ε > 0` has `P(X_t ∉ C_ε) ≤ η` for all `t`). Then a.s. there are
arbitrarily large `t` with `e^{2iX_t} = e^{2ix}`. This is `sle_recurrence` with the Markov
transport `hMarkov` proved (`sle_markov_transport`, from the conditioning lemma
`isDiffusionSolution_cond_shift`). -/
theorem sle_recurrence' (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b) (hc0 : 0 ≤ c)
    (hβc : Continuous β) (hβ2 : ∀ v, β v ^ 2 = 2 * diffusionD a b c v)
    {X : ℝ≥0 → Ω → ℝ} (hX : IsDiffusionSolution ℱ (mu a b c) β X P)
    (hXc : ∀ ω, Continuous fun t => X t ω) (x : ℝ)
    (hstat : ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ≥0, P.real {ω | X t ω ∉ goodSet x ε} ≤ η) :
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0, ∃ t : ℝ≥0, s ≤ t ∧
      Complex.exp (2 * Complex.I * X t ω) = Complex.exp (2 * Complex.I * x) :=
  sle_recurrence ha hb hc hc0 hβc hβ2 hX hXc x hstat
    fun _ _ _ hε _ hδ h245 s A hA =>
      sle_markov_transport (continuous_mu a b c) hβc (mu_periodic a b c)
        (sq_periodic_of_sq_eq_two_mul_diffusionD hβ2) hX hXc x hε hδ h245 s A hA

/-! ### The case `c ≤ 0`: reflection -/

/-- `-v ∈ C_ε(-x)` iff `v ∈ ⋃ₙ [x + nπ + ε, x + nπ + π]`: the form of the good set of the
reflected process in terms of the original one. -/
theorem neg_mem_goodSet_neg_iff {x ε v : ℝ} :
    -v ∈ goodSet (-x) ε ↔ ∃ n : ℤ, x + n * π + ε ≤ v ∧ v ≤ x + n * π + π := by
  simp only [goodSet, mem_iUnion, mem_Icc]
  constructor
  · rintro ⟨k, h1, h2⟩
    refine ⟨-k - 1, ?_, ?_⟩ <;> push_cast <;> linarith
  · rintro ⟨n, h1, h2⟩
    refine ⟨-n - 1, ?_, ?_⟩ <;> push_cast <;> linarith

/-- **Lemma 2.16 (recurrence), `c ≤ 0`** (`step:wlog-c-nonneg-arg`, ERRATA R19), by the reflection
`X ↦ -X`, `c ↦ -c`, `β ↦ β(-·)`. The reflected process `-X` solves the `c ≥ 0` problem, so it
recurs to the lattice `-x + πℤ` for every `x`, i.e. `X` recurs to `x + πℤ`; in the critical case
`c = -√(ab)` one may take `x` with `tan x = sgn(c) √(b/a)` (R19).

The stationarity input is the one of the reflected process `-X` and the reflected point `-x`:
`P(-X_t ∉ C_ε(-x)) ≤ η`, where `-v ∈ C_ε(-x)` iff
`v ∈ ⋃ₙ [x + nπ + ε, x + nπ + π]` (the points whose representative in `(x, x+π]` lies in
`[x + ε, x + π]`). -/
theorem sle_recurrence_nonpos (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b) (hc0 : c ≤ 0)
    (hβc : Continuous β) (hβ2 : ∀ v, β v ^ 2 = 2 * diffusionD a b c v)
    {X : ℝ≥0 → Ω → ℝ} (hX : IsDiffusionSolution ℱ (mu a b c) β X P)
    (hXc : ∀ ω, Continuous fun t => X t ω) (x : ℝ)
    (hstat : ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧
      ∀ t : ℝ≥0, P.real {ω | -X t ω ∉ goodSet (-x) ε} ≤ η) :
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0, ∃ t : ℝ≥0, s ≤ t ∧
      Complex.exp (2 * Complex.I * X t ω) = Complex.exp (2 * Complex.I * x) := by
  have hc' : (-c) ^ 2 ≤ a * b := by rwa [neg_sq]
  have hβ2' : ∀ v, β (-v) ^ 2 = 2 * diffusionD a b (-c) v := fun v => by
    rw [diffusionD_neg_c, hβ2]
  have hX' : IsDiffusionSolution ℱ (mu a b (-c)) (fun v => β (-v)) (fun t ω => -X t ω) P := by
    have := isDiffusionSolution_neg hX
    have e : (fun v => -mu a b c (-v)) = mu a b (-c) := funext fun v => (mu_neg_c a b c v).symm
    rwa [e] at this
  have h := sle_recurrence' ha hb hc' (neg_nonneg.2 hc0) (hβc.comp continuous_neg) hβ2' hX'
    (fun ω => (hXc ω).neg) (-x) hstat
  filter_upwards [h] with ω hω s
  obtain ⟨t, hst, ht⟩ := hω s
  refine ⟨t, hst, ?_⟩
  have e1 : Complex.exp (2 * Complex.I * ((-X t ω : ℝ) : ℂ)) =
      (Complex.exp (2 * Complex.I * (X t ω : ℂ)))⁻¹ := by
    rw [← Complex.exp_neg]; congr 1; push_cast; ring
  have e2 : Complex.exp (2 * Complex.I * ((-x : ℝ) : ℂ)) =
      (Complex.exp (2 * Complex.I * (x : ℂ)))⁻¹ := by
    rw [← Complex.exp_neg]; congr 1; push_cast; ring
  rw [e1, e2] at ht
  exact inv_injective ht

end ComplexSLE.Recurrence

end
