/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.EventMeasPath

/-!
# Joint measurability of `dist(z, L_t)` in (driver path, point) (M7/B2)

For a path `g ∈ C([0, t], ℂ)` (extended by its final value) let `H_g = L_t(g) = {w : T_w ≤ t}`.
The graph `{(g, w) : w ∈ H_g}` is the complement of the jointly open set `aliveJoint t`, hence
closed; every `H_g` contains the starting point `g(0)`, so is nonempty, and local compactness of
`ℂ` turns closedness of the graph into joint lower semicontinuity of `(g, z) ↦ dist(z, H_g)`
(`lowerSemicontinuous_infDist_hullSet`). A lower semicontinuous function is Borel measurable, and
for continuous paths `L_t(u) = H_{u|[0, t]}`, so `(u, z) ↦ dist(z, L_t(u))` is measurable on
`ContPath × ℂ` (`measurable_infDist_leftHull`).
-/

public section

open scoped NNReal ENNReal Topology
open Set MeasureTheory Filter Metric

namespace ComplexSLE.Internal

/-- The left hull `L_t` of the extension of a path `g ∈ C([0, t], ℂ)`. -/
@[expose] noncomputable def hullSet (t : ℝ≥0) (g : C(Icc (0 : ℝ) t, ℂ)) : Set ℂ :=
  leftHull (Polar.extendDriver t g) t

theorem mem_hullSet_iff {t : ℝ≥0} {g : C(Icc (0 : ℝ) t, ℂ)} {w : ℂ} :
    w ∈ hullSet t g ↔ (g, w) ∉ aliveJoint t := by
  have : (g, w) ∈ aliveJoint t ↔ w ∈ (leftHull (Polar.extendDriver t g) t)ᶜ :=
    Polar.coe_mem_lifeSet_iff
  rw [this, mem_compl_iff, not_not]
  rfl

theorem isClosed_graph_hullSet (t : ℝ≥0) :
    IsClosed {p : C(Icc (0 : ℝ) t, ℂ) × ℂ | p.2 ∈ hullSet t p.1} := by
  have : {p : C(Icc (0 : ℝ) t, ℂ) × ℂ | p.2 ∈ hullSet t p.1} = (aliveJoint t)ᶜ := by
    ext p; exact mem_hullSet_iff
  rw [this]
  exact (isOpen_aliveJoint t).isClosed_compl

theorem isClosed_hullSet (t : ℝ≥0) (g : C(Icc (0 : ℝ) t, ℂ)) : IsClosed (hullSet t g) :=
  (isClosed_graph_hullSet t).preimage (Continuous.prodMk_right g)

theorem hullSet_nonempty (t : ℝ≥0) (g : C(Icc (0 : ℝ) t, ℂ)) : (hullSet t g).Nonempty :=
  leftHull_nonempty _ _

/-- **Joint lower semicontinuity of the distance to the left hull.** -/
theorem lowerSemicontinuous_infDist_hullSet (t : ℝ≥0) :
    LowerSemicontinuous fun p : C(Icc (0 : ℝ) t, ℂ) × ℂ => infDist p.2 (hullSet t p.1) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro c
  refine IsSeqClosed.isClosed ?_
  intro x p hx hxp
  obtain ⟨g, z⟩ := p
  simp only [mem_preimage, mem_Iic] at hx ⊢
  -- nearest points
  have hex : ∀ n, ∃ w ∈ hullSet t (x n).1, infDist (x n).2 (hullSet t (x n).1) = dist (x n).2 w :=
    fun n => (isClosed_hullSet t (x n).1).exists_infDist_eq_dist (hullSet_nonempty t _) _
  choose w hwmem hwdist using hex
  have hz : Tendsto (fun n => (x n).2) atTop (𝓝 z) := (continuous_snd.tendsto _).comp hxp
  have hg : Tendsto (fun n => (x n).1) atTop (𝓝 g) := (continuous_fst.tendsto _).comp hxp
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ hz)
  have hwb : ∀ n, w n ∈ closedBall (0 : ℂ) (R + c) := by
    intro n
    rw [mem_closedBall, dist_zero_right]
    have h1 : ‖(x n).2‖ ≤ R := hR _ ⟨n, rfl⟩
    have h2 : dist (x n).2 (w n) ≤ c := by rw [← hwdist n]; exact hx n
    have h3 : ‖w n‖ ≤ ‖(x n).2‖ + dist (x n).2 (w n) := by
      rw [dist_eq_norm]
      calc ‖w n‖ = ‖(x n).2 - ((x n).2 - w n)‖ := by congr 1; ring
        _ ≤ ‖(x n).2‖ + ‖(x n).2 - w n‖ := norm_sub_le _ _
    linarith
  obtain ⟨a, -, φ, hφ, hwa⟩ := (isCompact_closedBall (0 : ℂ) (R + c)).tendsto_subseq hwb
  have hga : Tendsto (fun n => ((x (φ n)).1, w (φ n))) atTop (𝓝 (g, a)) :=
    ((hg.comp hφ.tendsto_atTop).prodMk_nhds hwa)
  have ha : a ∈ hullSet t g :=
    (isClosed_graph_hullSet t).mem_of_tendsto hga (Eventually.of_forall fun n => hwmem (φ n))
  have hd : Tendsto (fun n => dist (x (φ n)).2 (w (φ n))) atTop (𝓝 (dist z a)) :=
    (hz.comp hφ.tendsto_atTop).dist hwa
  have hle : dist z a ≤ c :=
    le_of_tendsto hd (Eventually.of_forall fun n => by rw [← hwdist (φ n)]; exact hx (φ n))
  exact (infDist_le_dist_of_mem ha).trans hle

theorem measurable_infDist_hullSet (t : ℝ≥0) :
    Measurable fun p : C(Icc (0 : ℝ) t, ℂ) × ℂ => infDist p.2 (hullSet t p.1) :=
  (lowerSemicontinuous_infDist_hullSet t).measurable

theorem leftHull_eq_hullSet (t : ℝ≥0) (u : ContPath) :
    leftHull u.1 t = hullSet t (restrictPath t u) := by
  ext w
  rw [mem_hullSet_iff, ← mem_lifeSet_iff_restrictPath, Polar.coe_mem_lifeSet_iff,
    mem_compl_iff, not_not]

/-- **`(u, z) ↦ dist(z, L_t(u))` is measurable on `ContPath × ℂ`.** -/
theorem measurable_infDist_leftHull (t : ℝ≥0) :
    Measurable fun p : ContPath × ℂ => infDist p.2 (leftHull p.1.1 t) := by
  have h : (fun p : ContPath × ℂ => infDist p.2 (leftHull p.1.1 t)) =
      (fun q : C(Icc (0 : ℝ) t, ℂ) × ℂ => infDist q.2 (hullSet t q.1)) ∘
        Prod.map (restrictPath t) id := by
    funext p
    simp only [Function.comp, Prod.map_fst, Prod.map_snd, id, leftHull_eq_hullSet]
  rw [h]
  exact (measurable_infDist_hullSet t).comp
    (((measurable_restrictPath t).comp measurable_fst).prodMk measurable_snd)

end ComplexSLE.Internal

end
