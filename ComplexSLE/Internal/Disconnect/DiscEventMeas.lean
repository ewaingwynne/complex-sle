/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Disconnect.DiscEvent
public import ComplexSLE.Internal.Disconnect.DiscEventCrit
public import ComplexSLE.Internal.Phases.EventMeasDist
public import ComplexSLE.Internal.Polar.Measurability

/-!
# Measurability of the disconnection event

For each time `t`, the set `discJoint t ⊆ C([0, t], ℂ) × ℂ` of (path on `[0, t]`, point) pairs
`(g, z)` such that the left hull `L_t(g)` of the extension of `g` satisfies the countable criterion
`discCrit` of `DiscEventCrit.lean` is measurable (`measurableSet_discJoint`): the infimum distance
`g ↦ dist(a, L_t(g))` is measurable for each `a` (`measurable_infDist_hullSet`). By
`discAt_iff_discCrit`, for a continuous driver `u`,
`DiscAt u z t ↔ (u|[0, t], z) ∈ discJoint t` (`discAt_iff_mem_discJoint`).

Consequences:

* `measurableSet_discAtSet`: a measurable set `M_t ⊆ ContPath × ℂ` with
  `DiscAt u z t ↔ (u, z) ∈ M_t`, depending on `u` only through `restrictPath t u`;
* `measurableEvents_disc`, `measurableEvents_discAt`: `MeasurableEvents Disc` (rational times,
  `disc_iff_exists_rat`);
* `scaleInvariantEvents_disc`: `ScaleInvariantEvents Disc`;
* `measurableSet_setOf_discAt`, `measurableSet_setOf_ballDiscAt`: for an adapted driver, the events
  `{DiscAt (U · ω) z t}` and `{BallDiscAt (U · ω) c r t}` are `ℱ t`-measurable.
-/

public section

open scoped NNReal ENNReal
open Set Metric MeasureTheory

namespace ComplexSLE.Internal

/-! ### The measurable set of (path on `[0, t]`, point) pairs -/

/-- The set of pairs `(g, z)` with `discCrit (L_t(g)) z`. -/
@[expose] def discJoint (t : ℝ≥0) : Set (C(Icc (0 : ℝ) t, ℂ) × ℂ) :=
  {p | discCrit (hullSet t p.1) p.2}

theorem measurable_infDist_hullSet_left (t : ℝ≥0) (a : ℂ) :
    Measurable fun g : C(Icc (0 : ℝ) t, ℂ) => infDist a (hullSet t g) := by
  have h := measurable_infDist_hullSet t
  have h2 : Measurable fun g : C(Icc (0 : ℝ) t, ℂ) => (g, a) :=
    measurable_id.prodMk measurable_const
  have h3 := h.comp h2
  exact h3

theorem measurableSet_discJoint (t : ℝ≥0) : MeasurableSet (discJoint t) :=
  measurableSet_discCrit (K := hullSet t) (measurable_infDist_hullSet_left t)

/-- For a continuous driver, `DiscAt u z t` iff `(u|[0, t], z) ∈ discJoint t`. -/
theorem discAt_iff_mem_discJoint {u : ℝ≥0 → ℂ} (hu : Continuous u) (z : ℂ) (t : ℝ≥0) :
    DiscAt u z t ↔ (restrictPath t ⟨u, hu⟩, z) ∈ discJoint t := by
  have h := discAt_iff_discCrit (leftHull_nonempty u t) (isClosed_leftHull' hu t) z
  have e : leftHull u t = hullSet t (restrictPath t ⟨u, hu⟩) := leftHull_eq_hullSet t ⟨u, hu⟩
  unfold DiscAt
  change _ ↔ discCrit (hullSet t (restrictPath t ⟨u, hu⟩)) z
  rw [← e]
  exact h

/-- The measurable set `M_t ⊆ ContPath × ℂ` of the event `DiscAt`. -/
@[expose] def discAtSet (t : ℝ≥0) : Set (ContPath × ℂ) :=
  Prod.map (restrictPath t) id ⁻¹' discJoint t

theorem measurableSet_discAtSet (t : ℝ≥0) : MeasurableSet (discAtSet t) :=
  (((measurable_restrictPath t).comp measurable_fst).prodMk measurable_snd)
    (measurableSet_discJoint t)

theorem discAt_iff_mem_discAtSet {u : ℝ≥0 → ℂ} (hu : Continuous u) (z : ℂ) (t : ℝ≥0) :
    DiscAt u z t ↔ ((⟨u, hu⟩ : ContPath), z) ∈ discAtSet t :=
  discAt_iff_mem_discJoint hu z t

/-- `DiscAt` at time `t` depends on a continuous driver only through its restriction to `[0, t]`. -/
theorem discAt_congr_restrictPath {u v : ℝ≥0 → ℂ} (hu : Continuous u) (hv : Continuous v)
    (z : ℂ) (t : ℝ≥0) (h : restrictPath t ⟨u, hu⟩ = restrictPath t ⟨v, hv⟩) :
    DiscAt u z t ↔ DiscAt v z t := by
  rw [discAt_iff_mem_discJoint hu, discAt_iff_mem_discJoint hv, h]

/-! ### `MeasurableEvents` and scale invariance -/

theorem measurableEvents_discAt (t : ℝ≥0) : MeasurableEvents fun u z => DiscAt u z t :=
  MeasurableEvents.of_measurableSet (measurableSet_discAtSet t) fun _ hu z =>
    discAt_iff_mem_discAtSet hu z t

theorem measurableEvents_disc : MeasurableEvents Disc := by
  refine MeasurableEvents.of_measurableSet
    (S := ⋃ q : ℚ, ⋃ _ : 0 < q, discAtSet (q : ℝ).toNNReal)
    (MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ => measurableSet_discAtSet _)
    fun u hu z => ?_
  rw [disc_iff_exists_rat]
  simp only [mem_iUnion, exists_prop]
  refine exists_congr fun q => and_congr_right fun _ => ?_
  exact discAt_iff_mem_discAtSet hu z _

theorem scaleInvariantEvents_disc : ScaleInvariantEvents Disc :=
  fun _ hu r hr z => disc_scale hu r hr z

/-! ### `ℱ_t`-measurability for an adapted driver -/

section Adapted

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

theorem leftHull_eq_hullSet_driverPath (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) (ω : Ω) :
    leftHull (fun s => U s ω) t = hullSet t (Polar.driverPath U hU.cont t ω) :=
  leftHull_eq_hullSet t ⟨fun s => U s ω, hU.cont ω⟩

/-- For an adapted driver, `{DiscAt (U · ω) z t}` is `ℱ t`-measurable. -/
theorem measurableSet_setOf_discAt (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) (t : ℝ≥0) :
    MeasurableSet[ℱ t] {ω | DiscAt (fun s => U s ω) z t} := by
  have h : {ω | DiscAt (fun s => U s ω) z t} =
      (fun ω => (Polar.driverPath U hU.cont t ω, z)) ⁻¹' discJoint t := by
    ext ω
    exact discAt_iff_mem_discJoint (hU.cont ω) z t
  rw [h]
  let _ : MeasurableSpace Ω := ℱ t
  have h1 := Polar.measurable_driverPath hU.cont hU.adapted t
  have h2 : Measurable fun ω => (Polar.driverPath U hU.cont t ω, z) :=
    h1.prodMk measurable_const
  exact h2 (measurableSet_discJoint t)

/-- For an adapted driver, `{BallDiscAt (U · ω) c r t}` is `ℱ t`-measurable. -/
theorem measurableSet_setOf_ballDiscAt (hU : IsSLEDriverAdapted a b c U P ℱ) (x : ℂ) (r : ℝ)
    (t : ℝ≥0) : MeasurableSet[ℱ t] {ω | BallDiscAt (fun s => U s ω) x r t} := by
  by_cases hr : 0 < r
  · have h : {ω | BallDiscAt (fun s => U s ω) x r t} =
        {ω | r ≤ infDist x (hullSet t (Polar.driverPath U hU.cont t ω))} ∩
          {ω | DiscAt (fun s => U s ω) x t} := by
      ext ω
      rw [mem_inter_iff, mem_ofPred_eq, mem_ofPred_eq, mem_ofPred_eq,
        ballDiscAt_iff hr, leftHull_eq_hullSet_driverPath hU]
    rw [h]
    refine MeasurableSet.inter ?_ (measurableSet_setOf_discAt hU x t)
    let _ : MeasurableSpace Ω := ℱ t
    have h1 := Polar.measurable_driverPath hU.cont hU.adapted t
    have h2 := (measurable_infDist_hullSet_left t x).comp h1
    exact measurableSet_le measurable_const h2
  · have h : {ω | BallDiscAt (fun s => U s ω) x r t} = univ := by
      ext ω
      have hb : ball x r = ∅ := ball_eq_empty.2 (not_lt.1 hr)
      simp only [mem_ofPred_eq, mem_univ, iff_true, BallDiscAt, hb]
      exact ⟨Set.empty_disjoint _, fun y _ _ => Set.empty_disjoint _⟩
    rw [h]
    exact MeasurableSet.univ

/-- For an adapted driver, `{Disc (U · ω) z}` is measurable. -/
theorem measurableSet_setOf_disc (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) :
    MeasurableSet {ω | Disc (fun s => U s ω) z} := by
  have h : {ω | Disc (fun s => U s ω) z} =
      ⋃ q : ℚ, ⋃ _ : 0 < q, {ω | DiscAt (fun s => U s ω) z (q : ℝ).toNNReal} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
    exact disc_iff_exists_rat
  rw [h]
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
    ℱ.le _ _ (measurableSet_setOf_discAt hU z _)

end Adapted

end ComplexSLE.Internal

end
