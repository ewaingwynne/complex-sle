/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.Lemma38Step
public import ComplexSLE.Internal.Phases.EventMeasDist
public import ComplexSLE.Internal.Polar.PolarItoState
public import ComplexSLE.Internal.Polar.PolarTimeSigma

/-!
# Lemma 3.10, adaptedness (M7/E2)

For an adapted driver `U` (continuous paths) and a point `z`:

* `measurable_infDist_leftHull_omega`: `ω ↦ dist(z, L_t(U(ω)))` is `ℱ t`-measurable;
* `isStoppingTime_hitTime`: `ω ↦ hitTime (U ω) z r` is an `ℱ`-stopping time (right-continuity of
  `t ↦ dist(z, L_t)`, `Lemma38Hull.lean`, gives `{τ ≤ t} = {dist(z, L_t) ≤ r}`);
* `clockOrZero` (the clock `A_t(z)` on `{t < T_z}`, `0` elsewhere) is progressively measurable, so
  its value at a stopping time is measurable for the σ-algebra of that stopping time.
-/

public section

open scoped NNReal ENNReal Topology
open Set Metric Filter MeasureTheory

namespace ComplexSLE.Internal.Polar

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m} {U : ℝ≥0 → Ω → ℂ}

theorem measurable_infDist_leftHull_omega (hc : ∀ ω, Continuous fun t => U t ω)
    (had : Adapted ℱ U) (t : ℝ≥0) (z : ℂ) :
    Measurable[ℱ t] fun ω => infDist z (leftHull (fun s => U s ω) t) := by
  have h : (fun ω => infDist z (leftHull (fun s => U s ω) t)) =
      (fun p : C(Icc (0 : ℝ) t, ℂ) × ℂ => infDist p.2 (hullSet t p.1)) ∘
        (fun ω => (driverPath U hc t ω, z)) := by
    funext ω
    simp only [Function.comp]
    exact congrArg (infDist z) (leftHull_eq_hullSet t ⟨fun s => U s ω, hc ω⟩)
  rw [h]
  exact (measurable_infDist_hullSet t).comp
    ((measurable_driverPath hc had t).prodMk measurable_const)

/-- **The hitting time of `{dist(z, L_t) ≤ r}` is an `ℱ`-stopping time.** -/
theorem isStoppingTime_hitTime (hc : ∀ ω, Continuous fun t => U t ω) (had : Adapted ℱ U)
    (z : ℂ) (r : ℝ) :
    IsStoppingTime ℱ fun ω => hitTime (fun s => U s ω) z r := by
  intro i
  have h : {ω | hitTime (fun s => U s ω) z r ≤ (i : WithTop ℝ≥0)} =
      {ω | infDist z (leftHull (fun s => U s ω) i) ≤ r} := by
    ext ω
    exact hitTime_le_iff (hc ω)
  change MeasurableSet[ℱ i] {ω | hitTime (fun s => U s ω) z r ≤ (i : WithTop ℝ≥0)}
  rw [h]
  exact measurableSet_le (measurable_infDist_leftHull_omega hc had i z) measurable_const

open Classical in
/-- The clock `A_t(z)` on `{t < T_z}`, and `0` elsewhere. -/
@[expose] noncomputable def clockOrZero (U : ℝ≥0 → Ω → ℂ) (hc : ∀ ω, Continuous fun t => U t ω)
    (z : ℂ) (r : ℝ≥0) (ω : Ω) : ℝ :=
  if (r : ℝ) ∈ lifeSet (fun s => U s ω) z then clock (fun s => U s ω) (hc ω) z r else 0

theorem continuousWithinAt_clockOrZero (hc : ∀ ω, Continuous fun t => U t ω) (z : ℂ) (ω : Ω)
    (r : ℝ≥0) : ContinuousWithinAt (fun t => clockOrZero U hc z t ω) (Ici r) r := by
  by_cases hr : (r : ℝ) ∈ lifeSet (fun s => U s ω) z
  · have hcont : ContinuousAt (fun t : ℝ≥0 => clock (fun s => U s ω) (hc ω) z t) r := by
      have h1 : ContinuousWithinAt (clock (fun s => U s ω) (hc ω) z) (Ici 0) (r : ℝ) :=
        continuousWithinAt_clock_Ici (hc ω) hr
      have h2 : ContinuousWithinAt (fun t : ℝ≥0 => (t : ℝ)) univ r :=
        NNReal.continuous_coe.continuousWithinAt
      have := h1.comp h2 (fun t _ => NNReal.coe_nonneg t)
      rwa [continuousWithinAt_univ] at this
    refine (hcont.congr_of_eventuallyEq ?_).continuousWithinAt
    filter_upwards [coe_mem_lifeSet_mem_nhds hr] with t ht
    simp [clockOrZero, ht]
  · refine (continuousWithinAt_const (b := (0 : ℝ))).congr (fun t ht => ?_) ?_
    · have : (t : ℝ) ∉ lifeSet (fun s => U s ω) z := fun h =>
        hr (mem_lifeSet_of_le h (NNReal.coe_nonneg r) (NNReal.coe_le_coe.2 ht))
      simp [clockOrZero, this]
    · simp [clockOrZero, hr]

theorem stronglyAdapted_clockOrZero (hc : ∀ ω, Continuous fun t => U t ω)
    (had : Adapted ℱ U) (z : ℂ) : StronglyAdapted ℱ (clockOrZero U hc z) := fun r =>
  (measurable_clock hc had r z).stronglyMeasurable

theorem isStronglyProgressive_clockOrZero (hc : ∀ ω, Continuous fun t => U t ω)
    (had : Adapted ℱ U) (z : ℂ) : IsStronglyProgressive ℱ (clockOrZero U hc z) :=
  (stronglyAdapted_clockOrZero hc had z).isStronglyProgressive_of_rightContinuous
    fun ω r => continuousWithinAt_clockOrZero hc z ω r

end ComplexSLE.Internal.Polar

end
