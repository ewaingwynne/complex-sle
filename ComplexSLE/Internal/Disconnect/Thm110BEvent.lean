/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Disconnect.DiscEventMeas
public import ComplexSLE.Internal.Driver.BridgeAdapted

/-!
# Theorem 1.10(b): the event `G_s` of a disconnected ball (M8/T6)

Source: paper.tex:L2220-2224. For a driver path `u` and a time `s` let

  `GEvent u s` :⟺ `∃ c r, 0 < r ∧ BallDiscAt u c r s`,

i.e. `L_s` disconnects some ball from `∞` (and misses it). This file proves the deterministic and
measurability facts about `GEvent` used by `Thm110B.lean`:

* `gEvent_iff_dense`: `GEvent u s` iff `BallDiscAt u (e n) (1/(k+1)) s` for some `n, k : ℕ`, where
  `e` is the fixed dense sequence of `ℂ` (a rational sub-ball);
* `gEvent_scale`: `GEvent (r u(·/r²)) t ↔ GEvent u (t/r²)` for a continuous `u` (scaling of left
  hulls and of disconnection);
* `exists_measurableSet_gEvent`: a measurable set `S` of paths with `GEvent u s ↔ u ∈ S` for
  continuous `u`;
* `measurableSet_setOf_gEvent`: for a driver adapted to a filtration, `{GEvent (U · ω) s}` is
  `ℱ s`-measurable;
* `exists_ball_subset_interior_of_gEvent`: monotonicity. If `GEvent u s` and `s ≤ t`, then the
  set of points disconnected from `∞` by `L_t` has nonempty interior (paper.tex:L2224: left hulls
  are non-decreasing, so `L_t` disconnects the same ball).
-/

public section

open scoped NNReal ENNReal
open Set Metric MeasureTheory
open scoped Pointwise

namespace ComplexSLE.Internal

/-- `L_s` is disjoint from some ball and disconnects it from `∞`. -/
@[expose] def GEvent (u : ℝ≥0 → ℂ) (s : ℝ≥0) : Prop :=
  ∃ (c : ℂ) (r : ℝ), 0 < r ∧ BallDiscAt u c r s

/-! ### Deterministic facts -/

/-- `BallDiscAt` passes to sub-balls. -/
theorem BallDiscAt.mono_ball {u : ℝ≥0 → ℂ} {c c' : ℂ} {r r' : ℝ} {t : ℝ≥0}
    (h : BallDiscAt u c r t) (hsub : ball c' r' ⊆ ball c r) : BallDiscAt u c' r' t :=
  ⟨h.1.mono_left hsub, disconnectsFromInfinity_mono_right h.2 hsub⟩

/-- A ball in the sense of `GEvent` may be taken with a dense center and radius `1/(k+1)`. -/
theorem gEvent_iff_dense {u : ℝ≥0 → ℂ} {s : ℝ≥0} :
    GEvent u s ↔ ∃ n k : ℕ, BallDiscAt u (denseSeqC n) (1 / ((k : ℝ) + 1)) s := by
  constructor
  · rintro ⟨c, r, hr, h⟩
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hr)
    obtain ⟨n, hn⟩ := denseRange_denseSeqC.exists_dist_lt c (half_pos hr)
    rw [dist_comm] at hn
    refine ⟨n, k, h.mono_ball fun x hx => ?_⟩
    rw [mem_ball] at hx ⊢
    calc dist x c ≤ dist x (denseSeqC n) + dist (denseSeqC n) c := dist_triangle _ _ _
      _ < 1 / ((k : ℝ) + 1) + r / 2 := add_lt_add hx hn
      _ < r / 2 + r / 2 := by linarith
      _ = r := add_halves r
  · rintro ⟨n, k, h⟩
    exact ⟨denseSeqC n, 1 / ((k : ℝ) + 1), by positivity, h⟩

/-- Scaling of `BallDiscAt`: the driver `r u(·/r²)` disconnects `B(r c, r ρ)` at time `t` iff `u`
disconnects `B(c, ρ)` at time `t / r²`. -/
theorem ballDiscAt_scale {u : ℝ≥0 → ℂ} (hu : Continuous u) (r : ℝ≥0) (hr : 0 < r) (c : ℂ)
    (ρ : ℝ) (t : ℝ≥0) :
    BallDiscAt (fun s => (r : ℂ) * u (s / r ^ 2)) ((r : ℂ) * c) ((r : ℝ) * ρ) t ↔
      BallDiscAt u c ρ (t / r ^ 2) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hball : ball ((r : ℂ) * c) ((r : ℝ) * ρ) = (fun w => (r : ℂ) * w) '' ball c ρ := by
    have h1 := smul_ball hr0 c ρ
    have h2 : ‖(r : ℂ)‖ = (r : ℝ) := by simp
    rw [h2] at h1
    have h3 : (fun w : ℂ => (r : ℂ) * w) '' ball c ρ = (r : ℂ) • ball c ρ := by
      simp only [← smul_eq_mul]
      exact Set.image_smul
    rw [h3, h1]
    simp
  unfold BallDiscAt
  rw [scaling_leftHull u hu r hr t, hball, Set.disjoint_image_iff (mul_right_injective₀ hr0),
    Planar.disconnectsFromInfinity_mul hr0]

/-- Scaling of `GEvent`. -/
theorem gEvent_scale {u : ℝ≥0 → ℂ} (hu : Continuous u) (r : ℝ≥0) (hr : 0 < r) (t : ℝ≥0) :
    GEvent (fun s => (r : ℂ) * u (s / r ^ 2)) t ↔ GEvent u (t / r ^ 2) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  constructor
  · rintro ⟨c', ρ', hρ', h⟩
    refine ⟨c' / r, ρ' / r, div_pos hρ' hr', ?_⟩
    rw [← ballDiscAt_scale hu r hr]
    rwa [mul_div_cancel₀ _ hr0, mul_div_cancel₀ _ hr'.ne']
  · rintro ⟨c, ρ, hρ, h⟩
    exact ⟨(r : ℂ) * c, (r : ℝ) * ρ, mul_pos hr' hρ, (ballDiscAt_scale hu r hr c ρ t).2 h⟩

/-- **Monotonicity** (paper.tex:L2224): if `L_s` disconnects a ball from `∞` and `s ≤ t`, then the
set of points disconnected from `∞` by `L_t` has nonempty interior. -/
theorem exists_ball_subset_interior_of_gEvent {u : ℝ≥0 → ℂ} {s t : ℝ≥0} (h : GEvent u s)
    (hst : s ≤ t) :
    (interior {w | DisconnectsFromInfinity (leftHull u t) {w}}).Nonempty := by
  obtain ⟨c, r, hr, hb⟩ := h
  have hdis : DisconnectsFromInfinity (leftHull u t) (ball c r) :=
    Planar.disconnectsFromInfinity_mono (leftHull_mono hst) hb.2
  refine ⟨c, ?_⟩
  have hsub : ball c r ⊆ {w | DisconnectsFromInfinity (leftHull u t) {w}} := fun w hw =>
    disconnectsFromInfinity_mono_right hdis (singleton_subset_iff.2 hw)
  exact interior_maximal hsub isOpen_ball (mem_ball_self hr)

/-! ### Measurability -/

/-- The set of continuous paths `u` with `BallDiscAt u c r t` (for `r > 0`). -/
def ballDiscSet (c : ℂ) (r : ℝ) (t : ℝ≥0) : Set ContPath :=
  {u | (u, c) ∈ discAtSet t ∧ r ≤ infDist c (hullSet t (restrictPath t u))}

theorem measurableSet_ballDiscSet (c : ℂ) (r : ℝ) (t : ℝ≥0) :
    MeasurableSet (ballDiscSet c r t) := by
  have h1 : MeasurableSet {u : ContPath | (u, c) ∈ discAtSet t} :=
    measurable_prodMk_right (measurableSet_discAtSet t)
  have h2 : Measurable fun u : ContPath => infDist c (hullSet t (restrictPath t u)) :=
    (measurable_infDist_hullSet_left t c).comp (measurable_restrictPath t)
  exact h1.inter (measurableSet_le measurable_const h2)

theorem ballDiscAt_iff_mem_ballDiscSet {u : ℝ≥0 → ℂ} (hu : Continuous u) {c : ℂ} {r : ℝ}
    (hr : 0 < r) (t : ℝ≥0) :
    BallDiscAt u c r t ↔ (⟨u, hu⟩ : ContPath) ∈ ballDiscSet c r t := by
  rw [ballDiscAt_iff hr, and_comm]
  have e : leftHull u t = hullSet t (restrictPath t ⟨u, hu⟩) := leftHull_eq_hullSet t ⟨u, hu⟩
  rw [e, discAt_iff_mem_discAtSet hu]
  rfl

/-- The set of continuous paths with `GEvent`. -/
noncomputable def gSet (t : ℝ≥0) : Set ContPath :=
  ⋃ n : ℕ, ⋃ k : ℕ, ballDiscSet (denseSeqC n) (1 / ((k : ℝ) + 1)) t

theorem measurableSet_gSet (t : ℝ≥0) : MeasurableSet (gSet t) :=
  MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => measurableSet_ballDiscSet _ _ _

theorem gEvent_iff_mem_gSet {u : ℝ≥0 → ℂ} (hu : Continuous u) (t : ℝ≥0) :
    GEvent u t ↔ (⟨u, hu⟩ : ContPath) ∈ gSet t := by
  rw [gEvent_iff_dense]
  simp only [gSet, mem_iUnion]
  refine exists_congr fun n => exists_congr fun k => ?_
  exact ballDiscAt_iff_mem_ballDiscSet hu (by positivity) t

/-- `GEvent` is a measurable event on continuous paths. -/
theorem measurableEvents_gEvent (t : ℝ≥0) : MeasurableEvents fun u (_ : ℂ) => GEvent u t :=
  MeasurableEvents.of_measurableSet (S := gSet t ×ˢ univ)
    ((measurableSet_gSet t).prod MeasurableSet.univ) fun u hu z => by
      rw [gEvent_iff_mem_gSet hu]
      simp

/-- A measurable set `S` of paths on which `GEvent · t` is the indicator (for continuous paths). -/
theorem exists_measurableSet_gEvent (t : ℝ≥0) :
    ∃ S : Set (ℝ≥0 → ℂ), MeasurableSet S ∧
      ∀ u : ℝ≥0 → ℂ, Continuous u → (GEvent u t ↔ u ∈ S) := by
  obtain ⟨M, hM, hE⟩ := measurableEvents_gEvent t
  refine ⟨(fun v : ℝ≥0 → ℂ => (v, (0 : ℂ))) ⁻¹' M, measurable_prodMk_right hM, fun u hu => ?_⟩
  exact hE u 0 hu

section Adapted

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- For an adapted driver, `{GEvent (U · ω) s}` is `ℱ s`-measurable. -/
theorem measurableSet_setOf_gEvent (hU : IsSLEDriverAdapted a b c U P ℱ) (s : ℝ≥0) :
    MeasurableSet[ℱ s] {ω | GEvent (fun t => U t ω) s} := by
  have h : {ω | GEvent (fun t => U t ω) s} =
      ⋃ n : ℕ, ⋃ k : ℕ, {ω | BallDiscAt (fun t => U t ω) (denseSeqC n) (1 / ((k : ℝ) + 1)) s} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    exact gEvent_iff_dense
  rw [h]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun k =>
    measurableSet_setOf_ballDiscAt hU _ _ s

end Adapted

end ComplexSLE.Internal

end
