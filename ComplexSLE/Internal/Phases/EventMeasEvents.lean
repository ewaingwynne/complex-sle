/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.EventMeasDist

/-!
# `MeasurableEvents` for the event families of §3 (M7/B2)

The event families of Lemma 3.3 (`lem-all-z`) that the §3 roots use are jointly measurable in
(driver path, point), in the sense of `MeasurableEvents` (`AllZEvents.lean`):

* (a) `T_z < ∞` and `T_z = ∞` (`measurableEvents_absorbingTime_lt_top`, `_eq_top`);
* (b) the R14 ε-forms of Proposition 3.2: `∀ ε > 0, ∃ t < T_z, dist(z, L_t) < ε` and its negation
  `∃ ε > 0, ∀ t < T_z, ε ≤ dist(z, L_t)` (`measurableEvents_hull_approach`,
  `measurableEvents_hull_stays_away`).

The proof reduces the uncountable quantifier `∃ t` to a countable dense set of times using the
monotonicity of `t ↦ L_t` (`measurableSet_approach`), and uses the joint measurability of `T_z(u)`
(`measurable_absorbingTime`) and of `dist(z, L_t(u))` (`measurable_infDist_leftHull`).
-/

public section

open scoped NNReal ENNReal
open Set MeasureTheory Metric

namespace ComplexSLE.Internal

/-! ### The approach set -/

/-- For a measurable bound `B`, the set of (path, point) pairs such that `dist(z, L_t(u))` is
arbitrarily small for `t < B` is measurable. -/
theorem measurableSet_approach (B : ContPath × ℂ → ℝ≥0∞) (hB : Measurable B) :
    MeasurableSet {p : ContPath × ℂ | ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < B p ∧
      infDist p.2 (leftHull p.1.1 t) < ε} := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have h : {p : ContPath × ℂ | ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < B p ∧
      infDist p.2 (leftHull p.1.1 t) < ε} =
      ⋂ n : ℕ, ⋃ q ∈ D, ({p : ContPath × ℂ | (q : ℝ≥0∞) < B p} ∩
        {p : ContPath × ℂ | infDist p.2 (leftHull p.1.1 q) < 1 / ((n : ℝ) + 1)}) := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, mem_inter_iff, exists_prop]
    constructor
    · intro hp n
      obtain ⟨t, htB, htd⟩ := hp (1 / ((n : ℝ) + 1)) (by positivity)
      obtain ⟨r, htr, hrB⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 htB
      obtain ⟨q, hqD, hqt, hqr⟩ := hDd.exists_between (ENNReal.coe_lt_coe.1 htr)
      refine ⟨q, hqD, lt_trans (ENNReal.coe_lt_coe.2 hqr) hrB, lt_of_le_of_lt ?_ htd⟩
      exact infDist_le_infDist_of_subset (leftHull_mono hqt.le) (leftHull_nonempty _ _)
    · intro hp ε hε
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      obtain ⟨q, -, hqB, hqd⟩ := hp n
      exact ⟨q, hqB, hqd.trans hn⟩
  rw [h]
  refine MeasurableSet.iInter fun n => MeasurableSet.biUnion hDc fun q _ => ?_
  exact (measurableSet_lt measurable_const hB).inter
    (measurableSet_lt (measurable_infDist_leftHull q) measurable_const)

/-! ### (a) `T_z < ∞` and `T_z = ∞` -/

theorem measurableEvents_absorbingTime_lt_top :
    MeasurableEvents fun u z => absorbingTime u z < ⊤ :=
  MeasurableEvents.of_measurableSet
    (S := {p : ContPath × ℂ | absorbingTime p.1.1 p.2 < ⊤})
    (measurableSet_lt measurable_absorbingTime measurable_const) fun _ _ _ => Iff.rfl

theorem measurableEvents_absorbingTime_eq_top :
    MeasurableEvents fun u z => absorbingTime u z = ⊤ :=
  measurableEvents_absorbingTime_lt_top.not.congr fun _ _ _ => by simp

/-! ### (b) The ε-forms of Proposition 3.2 -/

/-- `∀ ε > 0, ∃ t < T_z, dist(z, L_t) < ε` (the event of Proposition 3.2(a)). -/
theorem measurableEvents_hull_approach :
    MeasurableEvents fun u z => ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < absorbingTime u z ∧
      infDist z (leftHull u t) < ε :=
  MeasurableEvents.of_measurableSet
    (S := {p : ContPath × ℂ | ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < absorbingTime p.1.1 p.2 ∧
      infDist p.2 (leftHull p.1.1 t) < ε})
    (measurableSet_approach _ measurable_absorbingTime) fun _ _ _ => Iff.rfl

/-- `∃ ε > 0, ∀ t < T_z, ε ≤ dist(z, L_t)` (the event of Proposition 3.2(b)). -/
theorem measurableEvents_hull_stays_away :
    MeasurableEvents fun u z => ∃ ε > 0, ∀ t : ℝ≥0, (t : ℝ≥0∞) < absorbingTime u z →
      ε ≤ infDist z (leftHull u t) :=
  measurableEvents_hull_approach.not.congr fun _ _ _ => by
    push Not
    rfl

end ComplexSLE.Internal

end
