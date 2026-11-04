/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.AllZEvents
public import ComplexSLE.Internal.Polar.PolarDerivShift
public import ComplexSLE.Internal.Polar.PathSpace
public import ComplexSLE.Internal.Hull.Basic

/-!
# Joint measurability of `{t < T_z}` in (driver path, point) (M7/B2)

`ContPath` is the space of continuous driver paths `ℝ≥0 → ℂ` with the σ-algebra induced from the
product σ-algebra of `ℝ≥0 → ℂ` (the cylinder σ-algebra: Mathlib's `Subtype.instMeasurableSpace`).
For a fixed time `t`, restriction to `[0, t]` is a measurable map `ContPath → C([0, t], ℂ)` (into
the Borel σ-algebra of the sup norm, `ContinuousMap.measurable_iff_eval`), and the set of pairs
(path, point) with `t < T_z` is the preimage of a jointly open subset of
`C([0, t], ℂ) × ℂ` (`isOpen_aliveJoint`: Grönwall stability `exists_stability` combined with the
shift of the initial point by a constant driver, `lifeSet_sub_const`). Hence `T_z(u)` is a
measurable function of `(u, z) ∈ ContPath × ℂ` (`measurable_absorbingTime`).

`MeasurableEvents.of_measurableSet` converts a cylinder-measurable set of `ContPath × ℂ` into the
`MeasurableEvents` of `AllZEvents.lean` (a set of the product `(ℝ≥0 → ℂ) × ℂ`), and
`MeasurableEvents.not/and/or` are the closure properties.
-/

public section

open scoped NNReal ENNReal
open Set MeasureTheory

namespace ComplexSLE.Internal

/-- Continuous driver paths, with the cylinder σ-algebra (induced from `ℝ≥0 → ℂ`). -/
abbrev ContPath : Type := {u : ℝ≥0 → ℂ // Continuous u}

/-! ### From cylinder-measurable sets to `MeasurableEvents` -/

theorem measurableSpace_contPath_prod :
    (inferInstance : MeasurableSpace (ContPath × ℂ)) =
      MeasurableSpace.comap (Prod.map (Subtype.val : ContPath → ℝ≥0 → ℂ) (id : ℂ → ℂ))
        (MeasurableSpace.prod (inferInstance : MeasurableSpace (ℝ≥0 → ℂ))
          (inferInstance : MeasurableSpace ℂ)) := by
  rw [MeasurableSpace.comap_prodMap, MeasurableSpace.comap_id]
  rfl

/-- A cylinder-measurable set of (continuous path, point) pairs yields `MeasurableEvents`. -/
theorem MeasurableEvents.of_measurableSet {E : (ℝ≥0 → ℂ) → ℂ → Prop} {S : Set (ContPath × ℂ)}
    (hS : MeasurableSet S) (h : ∀ (u : ℝ≥0 → ℂ) (hu : Continuous u) (z : ℂ),
      E u z ↔ ((⟨u, hu⟩ : ContPath), z) ∈ S) : MeasurableEvents E := by
  have hS' : MeasurableSet[MeasurableSpace.comap
      (Prod.map (Subtype.val : ContPath → ℝ≥0 → ℂ) (id : ℂ → ℂ))
      (MeasurableSpace.prod (inferInstance : MeasurableSpace (ℝ≥0 → ℂ))
        (inferInstance : MeasurableSpace ℂ))] S := by
    rw [← measurableSpace_contPath_prod]; exact hS
  obtain ⟨M, hM, hMS⟩ := MeasurableSpace.measurableSet_comap.1 hS'
  refine ⟨M, hM, fun u z hu => ?_⟩
  rw [h u hu z, ← hMS]
  rfl

theorem MeasurableEvents.not {E : (ℝ≥0 → ℂ) → ℂ → Prop} (h : MeasurableEvents E) :
    MeasurableEvents fun u z => ¬ E u z := by
  obtain ⟨M, hM, hE⟩ := h
  exact ⟨Mᶜ, hM.compl, fun u z hu => by
    beta_reduce; rw [hE u z hu]; rfl⟩

theorem MeasurableEvents.congr {E F : (ℝ≥0 → ℂ) → ℂ → Prop} (hE : MeasurableEvents E)
    (h : ∀ (u : ℝ≥0 → ℂ), Continuous u → ∀ z, E u z ↔ F u z) : MeasurableEvents F := by
  obtain ⟨M, hM, hME⟩ := hE
  exact ⟨M, hM, fun u z hu => by rw [← h u hu z, hME u z hu]⟩

/-! ### Restriction to `[0, t]` -/

/-- The restriction of a continuous path to `[0, t]`. -/
@[expose] def restrictPath (t : ℝ≥0) (u : ContPath) : C(Icc (0 : ℝ) t, ℂ) :=
  Polar.restrictDriver t u.1 u.2

theorem measurable_restrictPath (t : ℝ≥0) : Measurable (restrictPath t) := by
  refine ContinuousMap.measurable_iff_eval.2 fun x => ?_
  change Measurable fun a : ContPath => a.1 (x : ℝ).toNNReal
  exact (measurable_pi_apply _).comp measurable_subtype_coe

/-! ### Joint openness of the alive set -/

/-- The pairs (path on `[0, t]`, point) such that `t < T_z` for the extended path. -/
@[expose] def aliveJoint (t : ℝ≥0) : Set (C(Icc (0 : ℝ) t, ℂ) × ℂ) :=
  {p | p.1 ∈ Polar.alive t p.2}

theorem isOpen_aliveJoint (t : ℝ≥0) : IsOpen (aliveJoint t) := by
  rw [Metric.isOpen_iff]
  rintro ⟨g₀, z₀⟩ hg₀
  obtain ⟨ρ, hρ, C, -, hC⟩ := Polar.exists_stability (Polar.continuous_extendDriver t g₀)
    (show (t : ℝ) ∈ Polar.lifeSet (Polar.extendDriver t g₀) z₀ from hg₀)
  refine ⟨ρ / 2, by positivity, ?_⟩
  rintro ⟨g, w⟩ hgw
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hgw
  obtain ⟨h1, h2⟩ := hgw
  simp only at h1 h2
  set c : ℂ := w - z₀ with hc
  have hU' : Continuous fun s => Polar.extendDriver t g s - c :=
    (Polar.continuous_extendDriver t g).sub continuous_const
  have hε : ‖g - g₀‖ + ‖c‖ < ρ := by rw [hc]; linarith
  obtain ⟨hlife, -⟩ := hC _ hU' (‖g - g₀‖ + ‖c‖) hε (fun s _ => by
    have h3 := Polar.norm_extendDriver_sub_le t g₀ g s.toNNReal
    have h4 : ‖g₀ - g‖ = ‖g - g₀‖ := norm_sub_rev _ _
    calc ‖Polar.extendDriver t g₀ s.toNNReal - (Polar.extendDriver t g s.toNNReal - c)‖
        = ‖(Polar.extendDriver t g₀ s.toNNReal - Polar.extendDriver t g s.toNNReal) + c‖ := by
          congr 1; ring
      _ ≤ ‖Polar.extendDriver t g₀ s.toNNReal - Polar.extendDriver t g s.toNNReal‖ + ‖c‖ :=
          norm_add_le _ _
      _ ≤ ‖g - g₀‖ + ‖c‖ := by
          have := h3.trans h4.le
          linarith)
  have hlife' := Polar.lifeSet_sub_const (U := Polar.extendDriver t g) w c
  rw [show w - c = z₀ by rw [hc]; ring] at hlife'
  change (t : ℝ) ∈ Polar.lifeSet (Polar.extendDriver t g) w
  rw [← hlife']
  exact hlife

/-! ### `{t < T_z}` and `T_z` are measurable on `ContPath × ℂ` -/

theorem mem_lifeSet_iff_restrictPath (t : ℝ≥0) (u : ContPath) (z : ℂ) :
    (t : ℝ) ∈ Polar.lifeSet u.1 z ↔ (restrictPath t u, z) ∈ aliveJoint t :=
  Polar.mem_lifeSet_congr u.2 (Polar.continuous_extendDriver _ _) fun _ hs =>
    (Polar.extendDriver_restrictDriver t u.1 u.2 hs).symm

theorem measurableSet_lt_absorbingTime (t : ℝ≥0) :
    MeasurableSet {p : ContPath × ℂ | (t : ℝ≥0∞) < absorbingTime p.1.1 p.2} := by
  have h : {p : ContPath × ℂ | (t : ℝ≥0∞) < absorbingTime p.1.1 p.2} =
      Prod.map (restrictPath t) id ⁻¹' aliveJoint t := by
    ext p
    change _ ↔ (restrictPath t p.1, p.2) ∈ aliveJoint t
    rw [← mem_lifeSet_iff_restrictPath, Polar.mem_lifeSet, ENNReal.ofReal_coe_nnreal]
    simp
  rw [h]
  exact ((measurable_restrictPath t).comp measurable_fst).prodMk measurable_snd
    (isOpen_aliveJoint t).measurableSet

theorem measurableSet_absorbingTime_le (t : ℝ≥0) :
    MeasurableSet {p : ContPath × ℂ | absorbingTime p.1.1 p.2 ≤ t} := by
  have := (measurableSet_lt_absorbingTime t).compl
  simpa [compl_ofPred, not_lt] using this

/-- `(u, z) ↦ T_z(u)` is measurable on `ContPath × ℂ`. -/
theorem measurable_absorbingTime : Measurable fun p : ContPath × ℂ => absorbingTime p.1.1 p.2 := by
  refine measurable_of_Iic fun x => ?_
  induction x using ENNReal.recTopCoe with
  | top => simp
  | coe t => exact measurableSet_absorbingTime_le t

end ComplexSLE.Internal

end
