/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.PathSpace
public import ComplexSLE.Frozen.Defs.IsSLEDriverAdapted

/-!
# Measurability of the Loewner objects in `ω` (M6/S6)

Let `U : ℝ≥0 → Ω → ℂ` be a driver with continuous paths, adapted to a filtration `ℱ`. We prove that
the objects of the deterministic polar layer are `ℱ`-measurable / adapted functionals of `U`:

* `measurable_centeredPath`, `measurableSet_mem_lifeSet`: for fixed `t`, the value `f_t(z)` on the
  event `{t < T_z}`, and that event, are `ℱ t`-measurable.

The proof sends `ω` to the stopped path `U(ω)|[0, t] ∈ C([0, t], ℂ)`, which is `ℱ t`-measurable
(`measurable_driverPath`, from Mathlib's `ContinuousMap.measurable_iff_eval`) and composes with the
Borel functionals `alive`, `centeredValue` of `PathSpace.lean` (Grönwall stability of the Loewner
solution under sup-norm perturbations of the driver, `Stability.lean`).
-/

public section

open scoped NNReal ENNReal
open Set MeasureTheory

namespace ComplexSLE.Internal.Polar

variable {Ω : Type*} {m : MeasurableSpace Ω} {U : ℝ≥0 → Ω → ℂ} {ℱ : Filtration ℝ≥0 m}

/-- The driver on `[0, t]`, as a random element of `C([0, t], ℂ)`. -/
@[expose] noncomputable def driverPath (U : ℝ≥0 → Ω → ℂ) (hc : ∀ ω, Continuous fun t => U t ω)
    (t : ℝ≥0) (ω : Ω) : C(Icc (0 : ℝ) t, ℂ) :=
  restrictDriver t (fun s => U s ω) (hc ω)

/-- The stopped driver `U|[0, t]` is `ℱ t`-measurable as a random element of `C([0, t], ℂ)`. -/
theorem measurable_driverPath (hc : ∀ ω, Continuous fun t => U t ω) (had : Adapted ℱ U)
    (t : ℝ≥0) : Measurable[ℱ t] (driverPath U hc t) := by
  let _ : MeasurableSpace Ω := ℱ t
  refine ContinuousMap.measurable_iff_eval.2 fun x => ?_
  have hx : (x : ℝ).toNNReal ≤ t := by
    rw [Real.toNNReal_le_iff_le_coe]; exact x.2.2
  have h1 : Measurable[ℱ (x : ℝ).toNNReal] (U (x : ℝ).toNNReal) := had _
  exact h1.mono (ℱ.mono hx) le_rfl

theorem extendDriver_driverPath (hc : ∀ ω, Continuous fun t => U t ω) (t : ℝ≥0) (ω : Ω) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) t) :
    extendDriver t (driverPath U hc t ω) s.toNNReal = U s.toNNReal ω :=
  extendDriver_restrictDriver t (fun s => U s ω) (hc ω) hs

theorem mem_lifeSet_iff_driverPath (hc : ∀ ω, Continuous fun t => U t ω) (t : ℝ≥0) (z : ℂ)
    (ω : Ω) : (t : ℝ) ∈ lifeSet (fun s => U s ω) z ↔ driverPath U hc t ω ∈ alive t z :=
  mem_lifeSet_congr (hc ω) (continuous_extendDriver _ _) fun _ hs =>
    (extendDriver_driverPath hc t ω hs).symm

/-- The event `{t < T_z}` is `ℱ t`-measurable. -/
theorem measurableSet_mem_lifeSet (hc : ∀ ω, Continuous fun t => U t ω) (had : Adapted ℱ U)
    (t : ℝ≥0) (z : ℂ) : MeasurableSet[ℱ t] {ω | (t : ℝ) ∈ lifeSet (fun s => U s ω) z} := by
  have : {ω | (t : ℝ) ∈ lifeSet (fun s => U s ω) z} = driverPath U hc t ⁻¹' alive t z := by
    ext ω; exact mem_lifeSet_iff_driverPath hc t z ω
  rw [this]
  exact measurable_driverPath hc had t (isOpen_alive t z).measurableSet

open Classical in
/-- **`f_t(z)` is `ℱ t`-measurable** (on `{t < T_z}`; `0` elsewhere). -/
theorem measurable_centeredPath (hc : ∀ ω, Continuous fun t => U t ω) (had : Adapted ℱ U)
    (t : ℝ≥0) (z : ℂ) :
    Measurable[ℱ t] fun ω =>
      if (t : ℝ) ∈ lifeSet (fun s => U s ω) z then fPath (fun s => U s ω) (hc ω) z t else 0 := by
  have : (fun ω => if (t : ℝ) ∈ lifeSet (fun s => U s ω) z then
      fPath (fun s => U s ω) (hc ω) z t else 0) = centeredValue t z ∘ driverPath U hc t := by
    funext ω
    simp only [Function.comp, centeredValue]
    by_cases h : (t : ℝ) ∈ lifeSet (fun s => U s ω) z
    · have h' : (t : ℝ) ∈ lifeSet (extendDriver t (driverPath U hc t ω)) z :=
        (mem_lifeSet_iff_driverPath hc t z ω).1 h
      simp only [h, h', ite_true]
      exact fPath_congr (hc ω) (continuous_extendDriver _ _) h
        (fun s hs => (extendDriver_driverPath hc t ω hs).symm) ⟨t.coe_nonneg, le_rfl⟩
    · have h' : (t : ℝ) ∉ lifeSet (extendDriver t (driverPath U hc t ω)) z :=
        fun h'' => h ((mem_lifeSet_iff_driverPath hc t z ω).2 h'')
      simp [h, h']
  rw [this]
  exact (measurable_centeredValue t z).comp (measurable_driverPath hc had t)

end ComplexSLE.Internal.Polar

end
