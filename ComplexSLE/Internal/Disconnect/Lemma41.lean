/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Disconnect.Lemma41Core
public import ComplexSLE.Frozen.Defs.IsSLEDriver
import ComplexSLE.Internal.Disconnect.Lemma41Meas
import ComplexSLE.External.SupportSLEDriver
import ComplexSLE.Internal.Driver.Shift
import ComplexSLE.Internal.Driver.Transform
import ComplexSLE.Internal.Driver.BridgeVersion
import ComplexSLE.Frozen.Reflection_LeftHull
import ComplexSLE.Infrastructure.Planar.Disconnect

/-!
# Lemma 4.1 (probabilistic assembly)

arXiv:2203.07313v4, Lemma 4.1 (`lem-disconnect-2`, paper.tex:L1960-1963), proof L2159-2195.

For an `SLE_Σ` driver `U` (`0 < a, b`, `c² ≤ a b`) there are a bounded open nonempty set `V` and a
time `t > 0` such that with positive probability `L_t` is disjoint from `V` and disconnects `V` from
infinity.

Proof (`c ≥ 0`): pass to an everywhere-continuous version `U'` of `U` (a.s. equal). The
deterministic core `lemma41_core` shows that on `E₁ ∩ E₂₃ ∩ E₄` one of two balls is disconnected
by `L_{K+2+T}`, where `E₁ = {sup_{[0,T]} |U'| < η₁}`, `E₂₃ = {sup_{[0,2]} |W - φ| < η₂}` for the
shift `W` at `T`, and `E₄ = {sup_{[0,K]} |W'| < η₃}` for the shift `W'` of `W` at `2`. Each event
has positive probability by the support theorem (the classical input `support_sleDriver`), and the
events are independent by the Markov property at deterministic times (`IsSLEDriver.indep_shift_past`
applied to `U'` at `T` and to `W` at `2`). For `c < 0` apply the case `c ≥ 0` to the conjugate
driver (reflection property).
-/

public section

open scoped NNReal ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory Set Metric ComplexSLE

namespace ComplexSLE.Internal

/-- The σ-algebra of the shifted process is contained in that of the process. -/
theorem comap_shift_le {Ω : Type*} (Y : ℝ≥0 → Ω → ℂ) (t : ℝ≥0) :
    MeasurableSpace.comap (fun ω (s : ℝ≥0) => Y (s + t) ω - Y t ω) MeasurableSpace.pi ≤
      MeasurableSpace.comap (fun ω (s : ℝ≥0) => Y s ω) MeasurableSpace.pi := by
  have : (fun ω (s : ℝ≥0) => Y (s + t) ω - Y t ω) =
      (fun f : ℝ≥0 → ℂ => fun s => f (s + t) - f t) ∘ (fun ω s => Y s ω) := rfl
  rw [this, ← MeasurableSpace.comap_comp]
  have hm : Measurable (fun f : ℝ≥0 → ℂ => fun s => f (s + t) - f t) :=
    measurable_pi_iff.2 fun s => (measurable_pi_apply (s + t)).sub (measurable_pi_apply t)
  exact MeasurableSpace.comap_mono hm.comap_le

/-- The σ-algebra of the process up to time `T` is contained in that of the whole process. -/
theorem comap_Iic_le {Ω : Type*} (Y : ℝ≥0 → Ω → ℂ) (T : ℝ≥0) :
    MeasurableSpace.comap (fun ω (r : Set.Iic T) => Y r ω) MeasurableSpace.pi ≤
      MeasurableSpace.comap (fun ω (s : ℝ≥0) => Y s ω) MeasurableSpace.pi := by
  have : (fun ω (r : Set.Iic T) => Y r ω) =
      (fun f : ℝ≥0 → ℂ => fun r : Set.Iic T => f r) ∘ (fun ω s => Y s ω) := rfl
  rw [this, ← MeasurableSpace.comap_comp]
  have hm : Measurable (fun f : ℝ≥0 → ℂ => fun r : Set.Iic T => f r) :=
    measurable_pi_iff.2 fun r => measurable_pi_apply (r : ℝ≥0)
  exact MeasurableSpace.comap_mono hm.comap_le

/-- **Lemma 4.1 for `c ≥ 0`.** -/
theorem lemma41_nonneg (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc0 : 0 ≤ c) (hc : c ^ 2 ≤ a * b)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ℝ≥0 → Ω → ℂ) (hU : IsSLEDriver a b c U P) :
    ∃ (V : Set ℂ) (t : ℝ≥0), IsOpen V ∧ Bornology.IsBounded V ∧ V.Nonempty ∧ 0 < t ∧
      0 < P {ω | Disjoint V (leftHull (U · ω) t) ∧
        DisconnectsFromInfinity (leftHull (U · ω) t) V} := by
  obtain ⟨φ, T, K, η₁, η₂, η₃, r, p₁, p₂, hφc, hφ0, hφS, hη₁, hη₂, hη₃, hr, hcore⟩ :=
    lemma41_core a b c ha hb hc0 hc
  obtain ⟨N, V, hNm, hN0, hout, -, hcont, -, -, hV⟩ := hU.exists_measurable_version
  set W1 : ℝ≥0 → Ω → ℂ := fun s ω => V (s + T) ω - V T ω with hW1def
  set W2 : ℝ≥0 → Ω → ℂ := fun s ω => W1 (s + 2) ω - W1 2 ω with hW2def
  have hW1 : IsSLEDriver a b c W1 P := hV.shift T
  have hW2 : IsSLEDriver a b c W2 P := hW1.shift 2
  have hcont1 : ∀ ω, Continuous fun t => W1 t ω := fun ω =>
    ((hcont ω).comp (continuous_id.add continuous_const)).sub continuous_const
  have hcont2 : ∀ ω, Continuous fun t => W2 t ω := fun ω =>
    ((hcont1 ω).comp (continuous_id.add continuous_const)).sub continuous_const
  have hφS0 : ∀ t : ℝ≥0, ∃ v : Fin 2 → ℝ,
      (covMatrix a b c).mulVec v 0 = (((fun _ => (0 : ℂ)) t)).re ∧
      (covMatrix a b c).mulVec v 1 = (((fun _ => (0 : ℂ)) t)).im := fun t => ⟨0, by simp⟩
  -- the three events
  set E1 : Set Ω := {ω | ∀ t ≤ T, ‖V t ω - (fun _ => (0 : ℂ)) t‖ < η₁} with hE1
  set E23 : Set Ω := {ω | ∀ t ≤ 2, ‖W1 t ω - φ t‖ < η₂} with hE23
  set E4 : Set Ω := {ω | ∀ t ≤ K, ‖W2 t ω - (fun _ => (0 : ℂ)) t‖ < η₃} with hE4
  have hP1 : 0 < P E1 := External.support_sleDriver a b c ha.le hb.le hc V hV (fun _ => 0)
    continuous_const rfl hφS0 T η₁ hη₁
  have hP23 : 0 < P E23 := External.support_sleDriver a b c ha.le hb.le hc W1 hW1 φ hφc hφ0 hφS
    2 η₂ hη₂
  have hP4 : 0 < P E4 := External.support_sleDriver a b c ha.le hb.le hc W2 hW2 (fun _ => 0)
    continuous_const rfl hφS0 K η₃ hη₃
  -- measurability
  have hE1m := measurableSet_forall_norm_sub_lt V (fun _ => 0) continuous_const hcont T η₁
  have hE23m := measurableSet_forall_norm_sub_lt W1 φ hφc hcont1 2 η₂
  have hE4m := measurableSet_forall_norm_sub_lt W2 (fun _ => 0) continuous_const hcont2 K η₃
  -- independence
  have hind1 := hV.indep_shift_past T
  have hind2 := hW1.indep_shift_past 2
  have hE4' : MeasurableSet[MeasurableSpace.comap (fun ω (s : ℝ≥0) => W1 s ω) MeasurableSpace.pi]
      E4 := comap_shift_le W1 2 _ (comap_Iic_le W2 K _ hE4m)
  have hE23' : MeasurableSet[MeasurableSpace.comap (fun ω (s : ℝ≥0) => W1 s ω) MeasurableSpace.pi]
      E23 := comap_Iic_le W1 2 _ hE23m
  have hprod1 : P (E4 ∩ E23) = P E4 * P E23 :=
    (Indep_iff _ _ _).1 hind2 E4 E23 (comap_Iic_le W2 K _ hE4m) hE23m
  have hprod2 : P (E4 ∩ E23 ∩ E1) = P (E4 ∩ E23) * P E1 :=
    (Indep_iff _ _ _).1 hind1 (E4 ∩ E23) E1 (hE4'.inter hE23') hE1m
  have hpos : 0 < P (E4 ∩ E23 ∩ E1) := by
    rw [hprod2, hprod1]
    exact ENNReal.mul_pos (ENNReal.mul_pos hP4.ne' hP23.ne').ne' hP1.ne'
  -- the deterministic core
  set S : ℂ → Set Ω := fun p => {ω | Disjoint (ball p r) (leftHull (fun t => V t ω) (K + 2 + T)) ∧
    DisconnectsFromInfinity (leftHull (fun t => V t ω) (K + 2 + T)) (ball p r)} with hSdef
  have hsub : E4 ∩ E23 ∩ E1 ⊆ S p₁ ∪ S p₂ := by
    rintro ω ⟨⟨h4, h23⟩, h1⟩
    refine hcore (fun t => V t ω) (hcont ω) (fun t ht => by simpa using h1 t ht) h23
      (fun t ht => ?_)
    have e : W2 t ω = V (t + (2 + T)) ω - V (2 + T) ω := by
      simp only [hW2def, hW1def]
      rw [add_assoc]
      ring
    have := h4 t ht
    simp only [sub_zero] at this
    rwa [e] at this
  have hpos' : 0 < P (S p₁ ∪ S p₂) := lt_of_lt_of_le hpos (measure_mono hsub)
  have hone : 0 < P (S p₁) ∨ 0 < P (S p₂) := by
    by_contra h
    rw [not_or] at h
    simp only [not_lt, nonpos_iff_eq_zero] at h
    exact hpos'.ne' (measure_union_null h.1 h.2)
  have hae : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  have hSU : ∀ p : ℂ, P (S p) ≤ P {ω | Disjoint (ball p r) (leftHull (U · ω) (K + 2 + T)) ∧
      DisconnectsFromInfinity (leftHull (U · ω) (K + 2 + T)) (ball p r)} := by
    intro p
    refine measure_mono_ae (hae.mono fun ω hω hmem => ?_)
    have hmem' : Disjoint (ball p r) (leftHull (fun t => V t ω) (K + 2 + T)) ∧
        DisconnectsFromInfinity (leftHull (fun t => V t ω) (K + 2 + T)) (ball p r) := hmem
    have e : (fun t => V t ω) = fun t => U t ω := funext (hout ω hω)
    rw [e] at hmem'
    exact hmem'
  have hTpos : 0 < K + 2 + T := by positivity
  rcases hone with h | h
  · exact ⟨ball p₁ r, K + 2 + T, isOpen_ball, Metric.isBounded_ball, ⟨p₁, mem_ball_self hr⟩,
      hTpos, lt_of_lt_of_le h (hSU p₁)⟩
  · exact ⟨ball p₂ r, K + 2 + T, isOpen_ball, Metric.isBounded_ball, ⟨p₂, mem_ball_self hr⟩,
      hTpos, lt_of_lt_of_le h (hSU p₂)⟩

/-- **Lemma 4.1** (paper.tex:L1960-1963): for an `SLE_Σ` driver there are a bounded open nonempty
set `V` and a time `t > 0` such that, with positive probability, `L_t` is disjoint from `V` and
disconnects `V` from infinity. -/
theorem lemma_4_1 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ℝ≥0 → Ω → ℂ) (hU : IsSLEDriver a b c U P) :
    ∃ (V : Set ℂ) (t : ℝ≥0), IsOpen V ∧ Bornology.IsBounded V ∧ V.Nonempty ∧ 0 < t ∧
      0 < P {ω | Disjoint V (leftHull (U · ω) t) ∧
        DisconnectsFromInfinity (leftHull (U · ω) t) V} := by
  rcases le_or_gt 0 c with hc0 | hc0
  · exact lemma41_nonneg a b c ha hb hc0 hc Ω P U hU
  · obtain ⟨V, t, hVo, hVb, hVn, ht, hpos⟩ := lemma41_nonneg a b (-c) ha hb (by linarith)
      (by rw [neg_sq]; exact hc) Ω P (fun s ω => conj (U s ω)) hU.conjugate
    have hVV : (starRingEnd ℂ) '' ((starRingEnd ℂ) '' V) = V := by
      rw [Set.image_image]
      simp
    refine ⟨(starRingEnd ℂ) '' V, t, ?_, ?_, hVn.image _, ht, lt_of_lt_of_le hpos ?_⟩
    · exact Complex.conjCLE.toHomeomorph.isOpenMap V hVo
    · exact Planar.isBounded_image_of_norm_le zero_le_one (fun z => by simp) hVb
    · refine measure_mono_ae (hU.cont.mono fun ω hωc hmem => ?_)
      have hmem' : Disjoint V (leftHull (fun s => conj (U s ω)) t) ∧
          DisconnectsFromInfinity (leftHull (fun s => conj (U s ω)) t) V := hmem
      have e := (reflection_leftHull (fun s => U s ω) hωc t).1
      rw [e] at hmem'
      obtain ⟨h1, h2⟩ := hmem'
      refine ⟨?_, ?_⟩
      · rw [← hVV] at h1
        exact (Set.disjoint_image_iff (starRingEnd ℂ).injective).1 h1
      · refine (Planar.disconnectsFromInfinity_conj _ ((starRingEnd ℂ) '' V)).1 ?_
        rw [hVV]
        exact h2

end ComplexSLE.Internal

end
