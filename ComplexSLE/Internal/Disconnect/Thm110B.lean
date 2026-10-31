/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsSLEDriver
public import ComplexSLE.Frozen.Defs.IsSLEDriverAdapted
public import ComplexSLE.Frozen.Defs.LeftHull
public import ComplexSLE.Frozen.Defs.DisconnectsFromInfinity
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import ComplexSLE.External.BlumenthalSLEDriver
public import ComplexSLE.Internal.Disconnect.Thm110BEvent
import ComplexSLE.Internal.Phases.AllZDriverLaw

/-!
# Theorem 1.10(b) from Lemma 4.1: scaling, Blumenthal, monotonicity (M8/T6)

`theorem_1_10_b_of_lemma41` has exactly the binders and the conclusion of the frozen anchor
`ComplexSLE.theorem_1_10_b` (paper.tex:L502-509: a.s., for every `t > 0`, the set of points
disconnected from `∞` by `L_t` has nonempty interior), plus one extra explicit hypothesis `hL41`
(placed after `hc`): Lemma 4.1 (paper.tex:L1938-2224), in the internal form of
`review/plans/M8.md`.

Proof (paper.tex:L2220-2224), with `G_s = {ω | GEvent (U' · ω) s}` (`L_s` disconnects some ball
from `∞` and misses it; `Thm110BEvent.lean`):

1. Pass to the adapted everywhere-continuous version `U'` of `U` (`IsSLEDriver.exists_adapted`).
2. `P(G_s)` does not depend on `s > 0` (`measure_gEvent_scale`, `measure_gEvent_eq`): the driver
   `r U'(·/r²)` is an `SLE_Σ` driver (`IsSLEDriver.scale`) with the same path law
   (`IsSLEDriver.measure_path_preimage_eq`), and its `G_s` is `G_{s/r²}` of `U'`
   (`gEvent_scale`). By Lemma 4.1, `P(G_{t₀}) > 0`.
3. `A_n = ⋃_{k ≥ n} G_{1/(k+1)}` has `P(A_n) ≥ p = P(G_1) > 0`, and `A = ⋂_n A_n` has
   `P(A) ≥ p` (continuity from above). `A = ⋂_{n ≥ N} A_n` is measurable for
   `σ(U'_r : r ≤ ε)` for every `ε > 0`, so Blumenthal's 0-1 law gives `P(A) = 1`
   (`ae_exists_small_gEvent`, the EXTERNAL `blumenthal_sleDriver`).
4. On `A`, for every `t > 0` there is `s ≤ t` with `G_s`; left hulls are monotone, so `L_t`
   disconnects the same ball (`exists_ball_subset_interior_of_gEvent`).

Consumes the EXTERNAL `blumenthal_sleDriver`.
-/

public section

open scoped NNReal ENNReal
open MeasureTheory Filter Set

namespace ComplexSLE.Internal

section Scale

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- **Scale invariance of `P(G_s)`.** `P(G_{s/r²}) = P(G_s)` for `r > 0`. -/
theorem measure_gEvent_scale (hU : IsSLEDriverAdapted a b c U P ℱ) (r : ℝ≥0) (hr : 0 < r)
    (s : ℝ≥0) :
    P {ω | GEvent (fun t => U t ω) (s / r ^ 2)} = P {ω | GEvent (fun t => U t ω) s} := by
  have hUm : ∀ t, Measurable (U t) := fun t => hU.adapted.measurable
  set U' : ℝ≥0 → Ω → ℂ := fun s ω => (r : ℂ) * U (s / r ^ 2) ω with hU'
  have hscaled : IsSLEDriver a b c U' P := hU.toIsSLEDriver.scale r hr
  have hU'm : ∀ t, Measurable (U' t) := fun t => measurable_const.mul (hUm _)
  obtain ⟨S, hS, hGS⟩ := exists_measurableSet_gEvent s
  have hlaw := hscaled.measure_path_preimage_eq hU.toIsSLEDriver hU'm hUm hS
  have hcont' : ∀ ω, Continuous fun t => U' t ω := fun ω =>
    continuous_const.mul ((hU.cont ω).comp (continuous_id.div_const _))
  have e1 : {ω | GEvent (fun t => U t ω) (s / r ^ 2)} = {ω | GEvent (fun t => U' t ω) s} := by
    ext ω
    exact (gEvent_scale (hU.cont ω) r hr s).symm
  have e2 : {ω | GEvent (fun t => U' t ω) s} = {ω | (fun t => U' t ω) ∈ S} := by
    ext ω
    exact hGS _ (hcont' ω)
  have e3 : {ω | GEvent (fun t => U t ω) s} = {ω | (fun t => U t ω) ∈ S} := by
    ext ω
    exact hGS _ (hU.cont ω)
  rw [e1, e2, e3, hlaw]

/-- `P(G_s)` does not depend on `s > 0`. -/
theorem measure_gEvent_eq (hU : IsSLEDriverAdapted a b c U P ℱ) {s s' : ℝ≥0} (hs : 0 < s)
    (hs' : 0 < s') :
    P {ω | GEvent (fun t => U t ω) s'} = P {ω | GEvent (fun t => U t ω) s} := by
  set r : ℝ≥0 := NNReal.sqrt (s / s') with hr
  have hss : 0 < s / s' := div_pos hs hs'
  have hr0 : 0 < r := NNReal.sqrt_pos.2 hss
  have hr2 : r ^ 2 = s / s' := NNReal.sq_sqrt _
  have h := measure_gEvent_scale hU r hr0 s
  rw [hr2, div_div_cancel₀ hs.ne'] at h
  exact h

/-- Lemma 4.1 gives `P(G_{t₀}) > 0`: a ball inside the open set `V` is disconnected. -/
theorem measure_gEvent_pos_of_lemma41
    (hL : ∃ (V : Set ℂ) (t : ℝ≥0), IsOpen V ∧ Bornology.IsBounded V ∧ V.Nonempty ∧ 0 < t ∧
      0 < P {ω | Disjoint V (leftHull (fun s => U s ω) t) ∧
        DisconnectsFromInfinity (leftHull (fun s => U s ω) t) V}) :
    ∃ t : ℝ≥0, 0 < t ∧ 0 < P {ω | GEvent (fun s => U s ω) t} := by
  obtain ⟨V, t, hVo, -, ⟨z, hz⟩, ht, hS⟩ := hL
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hVo z hz
  refine ⟨t, ht, lt_of_lt_of_le hS (measure_mono fun ω hω => ?_)⟩
  exact ⟨z, ρ, hρ, hω.1.mono_left hball, disconnectsFromInfinity_mono_right hω.2 hball⟩

end Scale

section Blumenthal

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- The times `s_k = 1/(k+1)`. -/
noncomputable def invTime (k : ℕ) : ℝ≥0 := 1 / ((k : ℝ≥0) + 1)

theorem invTime_pos (k : ℕ) : 0 < invTime k := by
  unfold invTime
  positivity

theorem invTime_antitone : Antitone invTime := by
  intro i j hij
  unfold invTime
  gcongr

theorem exists_invTime_lt {ε : ℝ≥0} (hε : 0 < ε) : ∃ n : ℕ, invTime n < ε := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < ε from hε)
  refine ⟨n, ?_⟩
  rw [← NNReal.coe_lt_coe]
  simpa [invTime] using hn

/-- **Blumenthal step** (paper.tex:L2223): if `P(G_s) > 0` for some `s > 0`, then almost surely
`G_s` occurs for arbitrarily small `s`. -/
theorem ae_exists_small_gEvent [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) {t₀ : ℝ≥0} (ht₀ : 0 < t₀)
    (hpos : 0 < P {ω | GEvent (fun s => U s ω) t₀}) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ∃ s : ℝ≥0, s ≤ t ∧ GEvent (fun r => U r ω) s := by
  have hm : ∀ t, Measurable[m] (U t) := fun t => hU.adapted.measurable
  set ℱn : Filtration ℝ≥0 m := Filtration.natural U (fun t => (hm t).stronglyMeasurable) with hℱn
  have hUn : IsSLEDriverAdapted a b c U P ℱn :=
    ⟨hU.toIsSLEDriver, hU.cont,
      fun t => (Filtration.stronglyAdapted_natural (β := fun _ => ℂ)
        (fun t => (hm t).stronglyMeasurable) t).measurable,
      fun s t hst => IsSLEDriver.indep_increment_natural hU.toIsSLEDriver hm hst⟩
  -- the sets
  set G : ℕ → Set Ω := fun k => {ω | GEvent (fun r => U r ω) (invTime k)} with hG
  set An : ℕ → Set Ω := fun n => ⋃ k : ℕ, ⋃ (_ : n ≤ k), G k with hAn
  set A : Set Ω := ⋂ n, An n with hA
  have hGmeas : ∀ k, MeasurableSet[ℱn (invTime k)] (G k) := fun k =>
    measurableSet_setOf_gEvent hUn (invTime k)
  have hGle : ∀ k {ε : ℝ≥0}, invTime k ≤ ε → MeasurableSet[ℱn ε] (G k) := fun k ε hk =>
    ℱn.mono hk _ (hGmeas k)
  have hAnmeas : ∀ n {ε : ℝ≥0}, invTime n ≤ ε → MeasurableSet[ℱn ε] (An n) := by
    intro n ε hn
    exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun hk =>
      hGle k ((invTime_antitone hk).trans hn)
  have hAnanti : Antitone An := fun i j hij => by
    refine iUnion₂_mono' fun k hk => ⟨k, hij.trans hk, subset_rfl⟩
  have hAnm : ∀ n, MeasurableSet (An n) := fun n =>
    ℱn.le _ _ (hAnmeas n le_rfl)
  -- the measure of `G k` is constant
  have hconst : ∀ k, P (G k) = P (G 0) := fun k =>
    measure_gEvent_eq hU (invTime_pos 0) (invTime_pos k)
  have hp : 0 < P (G 0) := by
    rw [← measure_gEvent_eq hU ht₀ (invTime_pos 0)] at hpos
    exact hpos
  -- `P A ≥ P (G 0) > 0`
  have hPA : P (G 0) ≤ P A := by
    rw [hA, Antitone.measure_iInter hAnanti (fun n => (hAnm n).nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩]
    refine le_iInf fun n => ?_
    rw [← hconst n]
    exact measure_mono fun ω hω => mem_iUnion₂.2 ⟨n, le_rfl, hω⟩
  -- `A` is germ-measurable
  have hgerm : ∀ ε : ℝ≥0, 0 < ε → ∃ B : Set Ω,
      MeasurableSet[⨆ (s : ℝ≥0) (_ : s ≤ ε), MeasurableSpace.comap (U s) inferInstance] B ∧
        P (symmDiff A B) = 0 := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_invTime_lt hε
    refine ⟨A, ?_, by simp⟩
    have hA' : A = ⋂ j, An (j + N) := by
      rw [hA, hAnanti.iInter_nat_add N]
    rw [hA']
    exact MeasurableSet.iInter fun j =>
      hAnmeas (j + N) ((invTime_antitone (Nat.le_add_left N j)).trans hN.le)
  have h01 := External.blumenthal_sleDriver hU.toIsSLEDriver A hgerm
  have hA1 : P A = 1 := h01.resolve_left (ne_of_gt (lt_of_lt_of_le hp hPA))
  have hae : ∀ᵐ ω ∂P, ω ∈ A := by
    have hAm : MeasurableSet A := MeasurableSet.iInter hAnm
    have h1 : P Aᶜ = 0 := by
      rw [measure_compl hAm (measure_ne_top P A), hA1, measure_univ, tsub_self]
    rw [ae_iff]
    exact h1
  filter_upwards [hae] with ω hω t ht
  obtain ⟨n, hn⟩ := exists_invTime_lt ht
  obtain ⟨k, hk, hωk⟩ := mem_iUnion₂.1 (mem_iInter.1 hω n)
  exact ⟨invTime k, ((invTime_antitone hk).trans hn.le), hωk⟩

end Blumenthal

/-- **Theorem 1.10(b) from Lemma 4.1** (paper.tex:L2220-2224). Same binders and conclusion as the
frozen `ComplexSLE.theorem_1_10_b`, plus the explicit hypothesis `hL41` (Lemma 4.1): for every
`SLE_Σ` driver on every probability space, some bounded open nonempty `V` is, for some `t > 0` and
with positive probability, disjoint from `L_t` and disconnected from `∞` by `L_t`. -/
theorem theorem_1_10_b_of_lemma41 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (hL41 : ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (U' : ℝ≥0 → Ω' → ℂ), IsSLEDriver a b c U' P' →
      ∃ (V : Set ℂ) (t : ℝ≥0), IsOpen V ∧ Bornology.IsBounded V ∧ V.Nonempty ∧ 0 < t ∧
        0 < P' {ω | Disjoint V (leftHull (U' · ω) t) ∧
          DisconnectsFromInfinity (leftHull (U' · ω) t) V})
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ℝ≥0 → Ω → ℂ) (hU : IsSLEDriver a b c U P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      (interior {w | DisconnectsFromInfinity (leftHull (U · ω) t) {w}}).Nonempty := by
  obtain ⟨ℱ, U', hUU', -, -, hU'⟩ := hU.exists_adapted
  obtain ⟨t₀, ht₀, hpos⟩ := measure_gEvent_pos_of_lemma41 (hL41 Ω P U' hU'.toIsSLEDriver)
  have hsmall := ae_exists_small_gEvent hU' ht₀ hpos
  filter_upwards [hsmall, hUU'] with ω h1 h2 t ht
  obtain ⟨s, hs, hG⟩ := h1 t ht
  have e : (fun t => U' t ω) = fun t => U t ω := funext h2
  rw [e] at hG
  exact exists_ball_subset_interior_of_gEvent hG hs

end ComplexSLE.Internal

end
