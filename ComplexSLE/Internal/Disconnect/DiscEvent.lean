/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.LeftHull
public import ComplexSLE.Frozen.Defs.DisconnectsFromInfinity
public import ComplexSLE.Frozen.Defs.CenteredLoewnerMap
public import ComplexSLE.Frozen.Defs.RightHull
public import ComplexSLE.Frozen.Scaling_LeftHull
public import ComplexSLE.Frozen.Concatenation_LeftHull
public import ComplexSLE.Infrastructure.Planar.Disconnect
public import ComplexSLE.Infrastructure.Planar.Pullback
public import ComplexSLE.Internal.Disconnect.Growth
public import ComplexSLE.Internal.Hull.ConnectedNoExt
public import ComplexSLE.Internal.Hull.Basic

/-!
# The disconnection event of Theorem 1.10(a): deterministic layer

For a driver path `u`, a point `z` and a time `t`:

* `DiscAt u z t`: `z ∉ L_t` and `L_t` disconnects `z` from `∞`;
* `Disc u z`: `DiscAt u z t` for some `t > 0` (the event of Theorem 1.10(a), paper.tex:L502-507);
* `BallDiscAt u c r t`: the ball `B(c, r)` is disjoint from `L_t` and disconnected from `∞` by it.

This file proves the deterministic facts used by the proof of Theorem 1.10(a)
(paper.tex:L2199-2217):

* monotonicity in `t` and the reduction to rational times (`DiscAt.mono`, `disc_iff_exists_rat`);
* the ball version (`ballDiscAt_iff`) and its monotonicity;
* openness in `z` for a continuous driver (`isOpen_setOf_discAt`, `isOpen_setOf_disc`);
* scale invariance (`disc_scale`), from the scaling property of left hulls;
* the restart implication (`disc_of_disc_restart`): if the restarted driver
  `u(· + s) - u s` has `Disc` at `f_s(z)`, then `u` has `Disc` at `z` (the pullback lemma and the
  concatenation property; the converse is false).
-/

@[expose] public section

open scoped NNReal ENNReal
open Set Metric

namespace ComplexSLE.Internal

/-- `L_t` disconnects `z` from `∞` without containing it. -/
def DiscAt (u : ℝ≥0 → ℂ) (z : ℂ) (t : ℝ≥0) : Prop :=
  z ∉ leftHull u t ∧ DisconnectsFromInfinity (leftHull u t) {z}

/-- The event of Theorem 1.10(a): some `L_t`, `t > 0`, disconnects `z` from `∞` without
containing it. -/
def Disc (u : ℝ≥0 → ℂ) (z : ℂ) : Prop :=
  ∃ t : ℝ≥0, 0 < t ∧ DiscAt u z t

/-- The ball `B(c, r)` is disjoint from `L_t` and disconnected from `∞` by it. -/
def BallDiscAt (u : ℝ≥0 → ℂ) (c : ℂ) (r : ℝ) (t : ℝ≥0) : Prop :=
  Disjoint (ball c r) (leftHull u t) ∧ DisconnectsFromInfinity (leftHull u t) (ball c r)

/-! ### Monotonicity -/

/-- Monotonicity of disconnection in the set to be disconnected. -/
theorem disconnectsFromInfinity_mono_right {K W W' : Set ℂ}
    (h : DisconnectsFromInfinity K W) (hW : W' ⊆ W) : DisconnectsFromInfinity K W' :=
  fun x hx hxu => (h x hx hxu).mono_left hW

/-- `DiscAt` is monotone in `t` as long as the point stays outside the hull. -/
theorem DiscAt.mono {u : ℝ≥0 → ℂ} {z : ℂ} {t t' : ℝ≥0} (h : DiscAt u z t) (htt : t ≤ t')
    (hz : z ∉ leftHull u t') : DiscAt u z t' :=
  ⟨hz, Planar.disconnectsFromInfinity_mono (leftHull_mono htt) h.2⟩

/-- `Disc` may be tested at rational times. -/
theorem disc_iff_exists_rat {u : ℝ≥0 → ℂ} {z : ℂ} :
    Disc u z ↔ ∃ q : ℚ, 0 < q ∧ DiscAt u z (q : ℝ).toNNReal := by
  constructor
  · rintro ⟨t, ht, h⟩
    have hlt : (t : ℝ≥0∞) < absorbingTime u z := notMem_leftHull_iff.1 h.1
    obtain ⟨r, htr, hrT⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
    have htr' : (t : ℝ) < r := by exact_mod_cast ENNReal.coe_lt_coe.1 htr
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn htr'
    have hq0 : (0 : ℝ) < q := lt_of_le_of_lt t.2 hq1
    have hqpos : 0 < q := by exact_mod_cast hq0
    have hq3 : (q : ℝ).toNNReal ≤ r := by
      rw [Real.toNNReal_le_iff_le_coe]; exact hq2.le
    have htq : t ≤ (q : ℝ).toNNReal := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0.le]; exact hq1.le
    refine ⟨q, hqpos, h.mono htq ?_⟩
    rw [notMem_leftHull_iff]
    exact lt_of_le_of_lt (by exact_mod_cast hq3) hrT
  · rintro ⟨q, hq, h⟩
    refine ⟨(q : ℝ).toNNReal, ?_, h⟩
    rw [Real.toNNReal_pos]
    exact_mod_cast hq

/-! ### The ball version -/

/-- For `r > 0`, `B(c, r)` is disconnected from `∞` by `L_t` iff `r ≤ dist(c, L_t)` and `c` is. -/
theorem ballDiscAt_iff {u : ℝ≥0 → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r) {t : ℝ≥0} :
    BallDiscAt u c r t ↔ r ≤ infDist c (leftHull u t) ∧ DiscAt u c t := by
  have hne := leftHull_nonempty u t
  have hdis : Disjoint (ball c r) (leftHull u t) ↔ r ≤ infDist c (leftHull u t) := by
    rw [le_infDist hne, Set.disjoint_left]
    constructor
    · intro h y hy
      by_contra hlt
      exact h (mem_ball_comm.1 (not_le.1 hlt)) hy
    · intro h y hy hyL
      exact absurd (h hyL) (not_le.2 (mem_ball_comm.1 hy))
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hdis.1 h1, ?_, disconnectsFromInfinity_mono_right h2 (singleton_subset_iff.2
      (mem_ball_self hr))⟩
    exact fun hc => Set.disjoint_left.1 h1 (mem_ball_self hr) hc
  · rintro ⟨h1, h2, h3⟩
    have h4 := hdis.2 h1
    exact ⟨h4, Planar.disconnectsFromInfinity_of_preconnected (convex_ball c r).isPreconnected h4
      (mem_ball_self hr) h3⟩

/-! ### Openness -/

/-- For a continuous driver, `{z | DiscAt u z t}` is open. -/
theorem isOpen_setOf_discAt {u : ℝ≥0 → ℂ} (hu : Continuous u) (t : ℝ≥0) :
    IsOpen {z | DiscAt u z t} := by
  rw [Metric.isOpen_iff]
  intro z hz
  obtain ⟨r, hr, hball, hdis⟩ :=
    Planar.exists_ball_disconnectsFromInfinity (isClosed_leftHull' hu t) hz.1 hz.2
  refine ⟨r, hr, fun w hw => ⟨fun hwL => hball hw hwL, ?_⟩⟩
  exact disconnectsFromInfinity_mono_right hdis (singleton_subset_iff.2 hw)

/-- For a continuous driver, `{z | Disc u z}` is open. -/
theorem isOpen_setOf_disc {u : ℝ≥0 → ℂ} (hu : Continuous u) : IsOpen {z | Disc u z} := by
  have : {z | Disc u z} = ⋃ t : ℝ≥0, ⋃ _ : 0 < t, {z | DiscAt u z t} := by
    ext z; simp [Disc]
  rw [this]
  exact isOpen_iUnion fun t => isOpen_iUnion fun _ => isOpen_setOf_discAt hu t

/-! ### Scale invariance -/

/-- Scaling: `DiscAt` for the driver `r u(·/r²)` at the point `r z` and time `t` is `DiscAt` for
`u` at `z` and time `t / r²`. -/
theorem discAt_scale {u : ℝ≥0 → ℂ} (hu : Continuous u) (r : ℝ≥0) (hr : 0 < r) (z : ℂ)
    (t : ℝ≥0) :
    DiscAt (fun s => (r : ℂ) * u (s / r ^ 2)) ((r : ℂ) * z) t ↔ DiscAt u z (t / r ^ 2) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold DiscAt
  rw [scaling_leftHull u hu r hr t]
  have hmem : (r : ℂ) * z ∈ (fun w => (r : ℂ) * w) '' leftHull u (t / r ^ 2) ↔
      z ∈ leftHull u (t / r ^ 2) :=
    (mul_right_injective₀ hr0).mem_set_image
  have hsing : ({(r : ℂ) * z} : Set ℂ) = (fun w => (r : ℂ) * w) '' {z} :=
    (Set.image_singleton).symm
  rw [hmem, hsing, Planar.disconnectsFromInfinity_mul hr0]

/-- `Disc` is invariant under scaling. -/
theorem disc_scale {u : ℝ≥0 → ℂ} (hu : Continuous u) (r : ℝ≥0) (hr : 0 < r) (z : ℂ) :
    Disc u z ↔ Disc (fun s => (r : ℂ) * u (s / r ^ 2)) ((r : ℂ) * z) := by
  have hr2 : (r ^ 2 : ℝ≥0) ≠ 0 := pow_ne_zero 2 hr.ne'
  constructor
  · rintro ⟨t, ht, h⟩
    refine ⟨t * r ^ 2, mul_pos ht (pow_pos hr 2), ?_⟩
    rw [discAt_scale hu r hr, mul_div_cancel_right₀ _ hr2]
    exact h
  · rintro ⟨t, ht, h⟩
    refine ⟨t / r ^ 2, div_pos ht (pow_pos hr 2), ?_⟩
    exact (discAt_scale hu r hr z t).1 h

/-! ### Restart (one direction) -/

/-- **Restart.** If the restarted driver `u(· + s) - u s` has `Disc` at `f_s(z)`, then `u` has
`Disc` at `z` (for `z ∉ L_s`). The converse is false in general. -/
theorem disc_of_disc_restart {u : ℝ≥0 → ℂ} (hu : Continuous u) (s : ℝ≥0) (z : ℂ)
    (hz : z ∉ leftHull u s)
    (h : Disc (fun r => u (r + s) - u s) (centeredLoewnerMap u hu s ⟨z, hz⟩)) : Disc u z := by
  obtain ⟨t, ht, hzt, hdis⟩ := h
  refine ⟨t + s, lt_of_lt_of_le ht le_self_add, ?_, ?_⟩
  · rw [concatenation_leftHull u hu t s]
    rintro (h1 | ⟨h2, h3, -⟩)
    · exact hz h1
    · exact hzt h3
  · have hpull := Planar.disconnectsFromInfinity_pullback
      (L := leftHull u s) (R := rightHull u hu s)
      (L' := leftHull (fun r => u (r + s) - u s) t) (F := centeredLoewnerMap u hu s)
      (continuous_centeredLoewnerMap hu s) (fun w h => h ⟨w, rfl⟩)
      (fun M => (centeredLoewnerMap_norm_ge hu s M).imp fun M' hM' w hw => hM' w w.2 hw)
      (V := {z}) ?_
    · rw [concatenation_leftHull u hu t s]
      exact hpull
    · refine Planar.disconnectsFromInfinity_mono (Set.subset_union_right) ?_
      refine disconnectsFromInfinity_mono_right hdis ?_
      rintro _ ⟨⟨x, hx⟩, hxz, rfl⟩
      have : x = z := hxz
      subst this
      rfl

end ComplexSLE.Internal

end
