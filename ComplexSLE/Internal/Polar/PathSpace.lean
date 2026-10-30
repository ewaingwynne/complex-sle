/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.Stability
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# The Loewner solution as a functional on the path space `C([0, t], ℂ)`

For `t : ℝ≥0` the set `C([0, t], ℂ)` of continuous functions on the compact interval `[0, t]`,
with the sup-norm topology and its Borel σ-algebra (Mathlib's `ContinuousMap.measurableSpace`), is
the path space of drivers on `[0, t]`. A path `g` is extended to a continuous driver on `ℝ≥0` by
the constant `g t` after time `t` (`extendDriver`). By `Stability.lean`:

* the set `alive t z` of paths `g` with `t < T_z(extendDriver t g)` is open,
* the value `f_t(z)` (`centeredValue t z`, zero off `alive t z`) is continuous on `alive t z`,

hence `centeredValue t z` is Borel measurable on `C([0, t], ℂ)`. By locality
(`mem_lifeSet_congr`, `fPath_congr`) these describe the original driver on `[0, t]`.
-/

public section

open scoped NNReal ENNReal
open Set MeasureTheory

namespace ComplexSLE.Internal.Polar

/-- The driver restricted to `[0, t]`, as a continuous function on the compact interval. -/
@[expose] def restrictDriver (t : ℝ≥0) (U : ℝ≥0 → ℂ) (hU : Continuous U) :
    C(Icc (0 : ℝ) t, ℂ) :=
  ⟨fun s => U (s : ℝ).toNNReal,
    hU.comp (continuous_real_toNNReal.comp continuous_subtype_val)⟩

/-- A path on `[0, t]` extended by its final value to a driver on `ℝ≥0`. -/
@[expose] noncomputable def extendDriver (t : ℝ≥0) (g : C(Icc (0 : ℝ) t, ℂ)) : ℝ≥0 → ℂ :=
  fun s => g (projIcc 0 (t : ℝ) t.coe_nonneg (s : ℝ))

theorem continuous_extendDriver (t : ℝ≥0) (g : C(Icc (0 : ℝ) t, ℂ)) :
    Continuous (extendDriver t g) :=
  g.continuous.comp (continuous_projIcc.comp NNReal.continuous_coe)

theorem extendDriver_toNNReal (t : ℝ≥0) (g : C(Icc (0 : ℝ) t, ℂ)) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) t) : extendDriver t g s.toNNReal = g ⟨s, hs⟩ := by
  unfold extendDriver
  rw [Real.coe_toNNReal s hs.1, projIcc_of_mem _ hs]

theorem extendDriver_restrictDriver (t : ℝ≥0) (U : ℝ≥0 → ℂ) (hU : Continuous U) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) t) :
    extendDriver t (restrictDriver t U hU) s.toNNReal = U s.toNNReal := by
  rw [extendDriver_toNNReal t _ hs]
  rfl

theorem norm_extendDriver_sub_le (t : ℝ≥0) (g g' : C(Icc (0 : ℝ) t, ℂ)) (s : ℝ≥0) :
    ‖extendDriver t g s - extendDriver t g' s‖ ≤ ‖g - g'‖ := by
  have := (g - g').norm_coe_le_norm (projIcc 0 (t : ℝ) t.coe_nonneg (s : ℝ))
  simpa [extendDriver] using this

/-- The set of paths `g` on `[0, t]` for which `t` lies in the life set `[0, T_z)` of the extended
driver. -/
@[expose] def alive (t : ℝ≥0) (z : ℂ) : Set C(Icc (0 : ℝ) t, ℂ) :=
  {g | (t : ℝ) ∈ lifeSet (extendDriver t g) z}

open Classical in
/-- The value `f_t(z)` of the centered Loewner path at time `t`, for the extended driver; `0` if
`t` is not in the life set. -/
@[expose] noncomputable def centeredValue (t : ℝ≥0) (z : ℂ) (g : C(Icc (0 : ℝ) t, ℂ)) : ℂ :=
  if (t : ℝ) ∈ lifeSet (extendDriver t g) z then
    fPath (extendDriver t g) (continuous_extendDriver t g) z t
  else 0

/-- Local stability: around a path in `alive t z` there is a ball inside `alive t z` on which
`centeredValue t z` is Lipschitz. -/
theorem exists_ball_alive (t : ℝ≥0) (z : ℂ) {g₀ : C(Icc (0 : ℝ) t, ℂ)} (hg₀ : g₀ ∈ alive t z) :
    ∃ ρ > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : C(Icc (0 : ℝ) t, ℂ), ‖g - g₀‖ < ρ →
      g ∈ alive t z ∧ ‖centeredValue t z g - centeredValue t z g₀‖ ≤ C * ‖g - g₀‖ := by
  obtain ⟨ρ, hρ, C, hC0, hC⟩ := exists_stability (continuous_extendDriver t g₀) hg₀
  refine ⟨ρ, hρ, C, hC0, fun g hg => ?_⟩
  have hd : ∀ s ∈ Icc (0 : ℝ) t,
      ‖extendDriver t g₀ s.toNNReal - extendDriver t g s.toNNReal‖ ≤ ‖g - g₀‖ := fun s _ => by
    rw [norm_sub_rev g g₀]
    exact norm_extendDriver_sub_le t g₀ g _
  obtain ⟨h1, h2⟩ := hC (extendDriver t g) (continuous_extendDriver t g) ‖g - g₀‖ hg hd
  refine ⟨h1, ?_⟩
  have h3 := h2 t ⟨t.coe_nonneg, le_rfl⟩
  have h1' : (t : ℝ) ∈ lifeSet (extendDriver t g) z := h1
  have h0' : (t : ℝ) ∈ lifeSet (extendDriver t g₀) z := hg₀
  simpa [centeredValue, h1', h0'] using h3

theorem isOpen_alive (t : ℝ≥0) (z : ℂ) : IsOpen (alive t z) := by
  refine Metric.isOpen_iff.2 fun g₀ hg₀ => ?_
  obtain ⟨ρ, hρ, C, -, hC⟩ := exists_ball_alive t z hg₀
  exact ⟨ρ, hρ, fun g hg => (hC g (by simpa [dist_eq_norm] using hg)).1⟩

theorem continuousOn_centeredValue (t : ℝ≥0) (z : ℂ) :
    ContinuousOn (centeredValue t z) (alive t z) := by
  intro g₀ hg₀
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨ρ, hρ, C, hC0, hC⟩ := exists_ball_alive t z hg₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨min ρ (ε / (C + 1)), lt_min hρ (by positivity), fun g hg => ?_⟩
  have hgρ : ‖g - g₀‖ < ρ := by
    have := lt_of_lt_of_le hg (min_le_left _ _)
    simpa [dist_eq_norm] using this
  have hgε : ‖g - g₀‖ < ε / (C + 1) := by
    have := lt_of_lt_of_le hg (min_le_right _ _)
    simpa [dist_eq_norm] using this
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (hC g hgρ).2 ?_
  calc C * ‖g - g₀‖ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hgε.le hC0
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

/-- `centeredValue t z` is Borel measurable on the path space `C([0, t], ℂ)`. -/
theorem measurable_centeredValue (t : ℝ≥0) (z : ℂ) : Measurable (centeredValue t z) := by
  classical
  have h : centeredValue t z = (alive t z).piecewise (centeredValue t z) (fun _ => 0) := by
    funext g
    by_cases hg : g ∈ alive t z
    · simp [Set.piecewise, hg]
    · have : (t : ℝ) ∉ lifeSet (extendDriver t g) z := hg
      simp [Set.piecewise, hg, centeredValue, this]
  rw [h]
  exact ContinuousOn.measurable_piecewise (continuousOn_centeredValue t z) continuousOn_const
    (isOpen_alive t z).measurableSet

end ComplexSLE.Internal.Polar

end
