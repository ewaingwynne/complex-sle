/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Recurrence.Renewal
import all ComplexSLE.Internal.Recurrence.Renewal
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Lemma 2.16: from a stationary law with no atoms to the recurrence input `hstat`

The renewal argument (`ae_frequently_mem_latticeSet`, `sle_recurrence'`) takes as input the uniform
smallness `hstat`: for every `η > 0` there is `ε > 0` with `P(X_t ∉ C_ε) ≤ η` for all `t`, where
`C_ε = goodSet x ε`. The stationarity layer (`map_addCircle_eq_of_markov`) provides the law of
`X_t mod π`, as a random variable in `AddCircle π`, independently of `t`. This file bridges the two:

* `hstat_of_map_eq`: if `P.map (X_t mod π) = μ` for all `t` and `μ` has no atoms, then `hstat`
  holds. The point is that `X_t ∉ C_ε` forces `X_t mod π` into an arc of length `ε` ending at
  `x mod π`, and `μ` of such arcs tends to `0` (outer regularity of the finite measure `μ` at the
  null set `{x mod π}`; no condition beyond `NullSingletonClass μ` is needed).
* `hstat_neg_of_map_eq`: the reflected form used by `sle_recurrence_nonpos` (the process `-X`, the
  point `-x`), under the same hypotheses.
* `nullSingletonClass_map_addCircle_of_absolutelyContinuous`,
  `nullSingletonClass_map_addCircle_of_withDensity`: the law of `X_0 mod π` has no atoms
  (`NullSingletonClass`, the current name of `NoAtoms`) when the law of `X_0` is absolutely
  continuous, in particular when it is `p₀(u) 1_{[0,π]}(u) du`.
* `hstat_of_map_eq_density`, `hstat_neg_of_map_eq_density`: the two combined, with the stationarity
  hypothesis in exactly the form `∀ t, law(X_t mod π) = law(X_0 mod π)` produced by
  `map_addCircle_eq_of_markov` (Stationary layer).

No external input is used; this file does not import the Stationary layer.
-/

public section

open scoped NNReal ENNReal
open MeasureTheory Set Filter

namespace ComplexSLE.Recurrence

open Real

/-! ### Small arcs around `x` -/

/-- Translating by an integer multiple of `π` does not change the class in `AddCircle π`. -/
theorem coe_sub_intCast_mul_pi (v : ℝ) (n : ℤ) :
    (((v - n * π : ℝ)) : AddCircle π) = (v : AddCircle π) := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff]
  exact ⟨n, by simp⟩

/-- If `U ⊆ AddCircle π` is an open neighbourhood of `x mod π`, then for some `ε > 0` every real
`v` outside `C_ε = goodSet x ε` has `v mod π ∈ U`. -/
theorem exists_eps_forall_not_mem_goodSet {U : Set (AddCircle π)} (hU : IsOpen U) {x : ℝ}
    (hx : (x : AddCircle π) ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v : ℝ, v ∉ goodSet x ε → (v : AddCircle π) ∈ U := by
  have : Fact (0 < π) := ⟨pi_pos⟩
  have hopen : IsOpen (((↑) : ℝ → AddCircle π) ⁻¹' U) :=
    hU.preimage (continuous_quotient_mk')
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen x hx
  refine ⟨δ, hδ, fun v hv => ?_⟩
  -- the representative `w = v - nπ` of `v` in `(x - π, x]`
  set n : ℤ := ⌈(v - x) / π⌉ with hn
  have h1 : (v - x) / π ≤ n := Int.le_ceil _
  have h2 : (n : ℝ) < (v - x) / π + 1 := Int.ceil_lt_add_one _
  have h1' : v - x ≤ n * π := by
    have := (div_le_iff₀ pi_pos).1 h1
    linarith
  have h2' : (n : ℝ) * π < v - x + π := by
    have := (lt_div_iff₀ pi_pos).mp (by linarith : (n : ℝ) - 1 < (v - x) / π)
    linarith
  have hw : v - n * π ∈ Metric.ball x δ := by
    rw [Real.ball_eq_Ioo, mem_Ioo]
    refine ⟨?_, by linarith⟩
    by_contra hcon
    push Not at hcon
    refine hv ?_
    simp only [goodSet, mem_iUnion, mem_Icc]
    refine ⟨n - 1, ?_, ?_⟩ <;> push_cast <;> linarith
  have := hball hw
  rwa [mem_preimage, coe_sub_intCast_mul_pi] at this

/-- The reflected form of `exists_eps_forall_not_mem_goodSet`: for some `ε > 0` every real `v` with
`-v ∉ C_ε(-x)` has `v mod π ∈ U`. -/
theorem exists_eps_forall_neg_not_mem_goodSet {U : Set (AddCircle π)} (hU : IsOpen U) {x : ℝ}
    (hx : (x : AddCircle π) ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v : ℝ, -v ∉ goodSet (-x) ε → (v : AddCircle π) ∈ U := by
  have hU' : IsOpen ((fun y : AddCircle π => -y) ⁻¹' U) := hU.preimage continuous_neg
  have hx' : ((-x : ℝ) : AddCircle π) ∈ (fun y : AddCircle π => -y) ⁻¹' U := by
    rw [mem_preimage, AddCircle.coe_neg, neg_neg]
    exact hx
  obtain ⟨ε, hε, h⟩ := exists_eps_forall_not_mem_goodSet hU' hx'
  refine ⟨ε, hε, fun v hv => ?_⟩
  have := h (-v) hv
  rwa [mem_preimage, AddCircle.coe_neg, neg_neg] at this

/-! ### Measures without atoms on the circle -/

/-- A finite measure on the circle without atoms gives every point a neighbourhood of arbitrarily
small mass. -/
theorem exists_isOpen_measureReal_lt (μ : Measure (AddCircle π)) [IsFiniteMeasure μ]
    [NullSingletonClass μ] (a : AddCircle π) {η : ℝ} (hη : 0 < η) :
    ∃ U : Set (AddCircle π), IsOpen U ∧ a ∈ U ∧ μ.real U < η := by
  have : Fact (0 < π) := ⟨pi_pos⟩
  have h0 : μ {a} < ENNReal.ofReal η := by
    rw [measure_singleton]
    exact ENNReal.ofReal_pos.2 hη
  obtain ⟨U, hsub, hU, hlt⟩ := Set.exists_isOpen_lt_of_lt {a} (ENNReal.ofReal η) h0
  exact ⟨U, hU, hsub rfl, ENNReal.toReal_lt_of_lt_ofReal hlt⟩

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- If the law of `Y mod π` is `μ` and `Y ∈ S` forces `Y mod π ∈ U`, then `P(Y ∈ S) ≤ μ(U)`. -/
theorem measureReal_preimage_le_of_map_eq [IsFiniteMeasure P] {Y : Ω → ℝ} (hY : Measurable Y)
    {μ : Measure (AddCircle π)} [IsFiniteMeasure μ]
    (hμ : P.map (fun ω => ((Y ω : ℝ) : AddCircle π)) = μ) {U : Set (AddCircle π)} {S : Set ℝ}
    (hS : ∀ v ∈ S, (v : AddCircle π) ∈ U) : P.real {ω | Y ω ∈ S} ≤ μ.real U := by
  have : Fact (0 < π) := ⟨pi_pos⟩
  have hc : Continuous (((↑) : ℝ → AddCircle π)) := continuous_quotient_mk'
  have hmk : Measurable (((↑) : ℝ → AddCircle π)) := hc.measurable
  have hle : P {ω | Y ω ∈ S} ≤ μ U := by
    calc P {ω | Y ω ∈ S}
        ≤ P ((fun ω => ((Y ω : ℝ) : AddCircle π)) ⁻¹' U) :=
          measure_mono fun ω hω => hS _ hω
      _ ≤ (P.map (fun ω => ((Y ω : ℝ) : AddCircle π))) U :=
          Measure.le_map_apply (hmk.comp hY).aemeasurable U
      _ = μ U := by rw [hμ]
  exact ENNReal.toReal_mono (measure_ne_top μ U) hle

/-! ### `hstat` from a time-independent law without atoms -/

variable {X : ℝ≥0 → Ω → ℝ}

/-- **Bridge to `hstat`.** If the law of `X_t mod π` (as a random variable in `AddCircle π`) is the
same measure `μ` for all `t`, and `μ` has no atoms, then for every `η > 0` there is `ε > 0` with
`P(X_t ∉ C_ε) ≤ η` for all `t`. This is the input `hstat` of `sle_recurrence'`; its hypotheses
compose with the conclusion of `map_addCircle_eq_of_markov` (take `μ = P.map (X_0 mod π)`). -/
theorem hstat_of_map_eq (hX : ∀ t, Measurable (X t)) {μ : Measure (AddCircle π)}
    [NullSingletonClass μ]
    (hμ : ∀ t, P.map (fun ω => ((X t ω : ℝ) : AddCircle π)) = μ) (x : ℝ) :
    ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ≥0, P.real {ω | X t ω ∉ goodSet x ε} ≤ η := by
  have : IsFiniteMeasure μ := by rw [← hμ 0]; infer_instance
  intro η hη
  obtain ⟨U, hU, hxU, hμU⟩ := exists_isOpen_measureReal_lt μ (x : AddCircle π) hη
  obtain ⟨ε, hε, hεU⟩ := exists_eps_forall_not_mem_goodSet hU hxU
  refine ⟨ε, hε, fun t => ?_⟩
  have := measureReal_preimage_le_of_map_eq (P := P) (hX t) (hμ t)
    (S := {v | v ∉ goodSet x ε}) hεU
  exact this.trans hμU.le

/-- **Bridge to the reflected `hstat`** (the input of `sle_recurrence_nonpos`): under the
hypotheses of `hstat_of_map_eq`, for every `η > 0` there is `ε > 0` with
`P(-X_t ∉ C_ε(-x)) ≤ η` for all `t`. -/
theorem hstat_neg_of_map_eq (hX : ∀ t, Measurable (X t)) {μ : Measure (AddCircle π)}
    [NullSingletonClass μ]
    (hμ : ∀ t, P.map (fun ω => ((X t ω : ℝ) : AddCircle π)) = μ) (x : ℝ) :
    ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧
      ∀ t : ℝ≥0, P.real {ω | -X t ω ∉ goodSet (-x) ε} ≤ η := by
  have : IsFiniteMeasure μ := by rw [← hμ 0]; infer_instance
  intro η hη
  obtain ⟨U, hU, hxU, hμU⟩ := exists_isOpen_measureReal_lt μ (x : AddCircle π) hη
  obtain ⟨ε, hε, hεU⟩ := exists_eps_forall_neg_not_mem_goodSet hU hxU
  refine ⟨ε, hε, fun t => ?_⟩
  have := measureReal_preimage_le_of_map_eq (P := P) (hX t) (hμ t)
    (S := {v | -v ∉ goodSet (-x) ε}) hεU
  exact this.trans hμU.le

/-! ### The law of `X_0 mod π` has no atoms when the law of `X_0` has a density -/

omit [IsProbabilityMeasure P] in
/-- If the law of `X₀` is absolutely continuous with respect to Lebesgue measure, then the law of
`X₀ mod π` has no atoms: the preimage of a point of the circle is a countable coset of `πℤ`. -/
theorem nullSingletonClass_map_addCircle_of_absolutelyContinuous {X₀ : Ω → ℝ} (hX₀ : Measurable X₀)
    (hac : P.map X₀ ≪ volume) : NullSingletonClass (P.map fun ω => ((X₀ ω : ℝ) : AddCircle π)) := by
  have : Fact (0 < π) := ⟨pi_pos⟩
  have hc : Continuous (((↑) : ℝ → AddCircle π)) := continuous_quotient_mk'
  have hmk : Measurable (((↑) : ℝ → AddCircle π)) := hc.measurable
  refine ⟨fun a => ?_⟩
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective a
  have e : (fun ω => ((X₀ ω : ℝ) : AddCircle π)) = ((↑) : ℝ → AddCircle π) ∘ X₀ := rfl
  rw [e, ← Measure.map_map hmk hX₀, Measure.map_apply hmk (measurableSet_singleton _)]
  have hcount : (((↑) : ℝ → AddCircle π) ⁻¹' {(v : AddCircle π)}).Countable := by
    refine (Set.countable_range (fun n : ℤ => v + n * π)).mono fun u hu => ?_
    simp only [mem_preimage, mem_singleton_iff] at hu
    rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff] at hu
    obtain ⟨k, hk⟩ := hu
    refine ⟨-k, ?_⟩
    simp only [zsmul_eq_mul] at hk
    push_cast
    linarith
  exact hac (hcount.measure_zero volume)

omit [IsProbabilityMeasure P] in
/-- The law of `X₀ mod π` has no atoms when the law of `X₀` is `p₀(u) 1_{[0,π]}(u) du`. -/
theorem nullSingletonClass_map_addCircle_of_withDensity {X₀ : Ω → ℝ} (hX₀ : Measurable X₀)
    {p₀ : ℝ → ℝ}
    (hlaw : P.map X₀ = (volume.restrict (Icc 0 π)).withDensity fun v => ENNReal.ofReal (p₀ v)) :
    NullSingletonClass (P.map fun ω => ((X₀ ω : ℝ) : AddCircle π)) := by
  refine nullSingletonClass_map_addCircle_of_absolutelyContinuous hX₀ ?_
  rw [hlaw]
  exact (withDensity_absolutelyContinuous _ _).trans Measure.restrict_le_self.absolutelyContinuous

/-- **`hstat` from the stationary law with density `p₀`.** If `law(X_0) = p₀(u) 1_{[0,π]}(u) du`
and `law(X_t mod π) = law(X_0 mod π)` for all `t` (the conclusion of `map_addCircle_eq_of_markov`),
then for every `η > 0` there is `ε > 0` with `P(X_t ∉ C_ε) ≤ η` for all `t`: the input `hstat` of
`sle_recurrence'`. -/
theorem hstat_of_map_eq_density (hX : ∀ t, Measurable (X t)) {p₀ : ℝ → ℝ}
    (hlaw : P.map (X 0) = (volume.restrict (Icc 0 π)).withDensity fun v => ENNReal.ofReal (p₀ v))
    (hstat : ∀ t : ℝ≥0, P.map (fun ω => ((X t ω : ℝ) : AddCircle π)) =
      P.map (fun ω => ((X 0 ω : ℝ) : AddCircle π))) (x : ℝ) :
    ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ≥0, P.real {ω | X t ω ∉ goodSet x ε} ≤ η :=
  haveI := nullSingletonClass_map_addCircle_of_withDensity (hX 0) hlaw
  hstat_of_map_eq hX hstat x

/-- **Reflected `hstat` from the stationary law with density `p₀`**: the input of
`sle_recurrence_nonpos` under the hypotheses of `hstat_of_map_eq_density`. -/
theorem hstat_neg_of_map_eq_density (hX : ∀ t, Measurable (X t)) {p₀ : ℝ → ℝ}
    (hlaw : P.map (X 0) = (volume.restrict (Icc 0 π)).withDensity fun v => ENNReal.ofReal (p₀ v))
    (hstat : ∀ t : ℝ≥0, P.map (fun ω => ((X t ω : ℝ) : AddCircle π)) =
      P.map (fun ω => ((X 0 ω : ℝ) : AddCircle π))) (x : ℝ) :
    ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧
      ∀ t : ℝ≥0, P.real {ω | -X t ω ∉ goodSet (-x) ε} ≤ η :=
  haveI := nullSingletonClass_map_addCircle_of_withDensity (hX 0) hlaw
  hstat_neg_of_map_eq hX hstat x

end ComplexSLE.Recurrence

end
