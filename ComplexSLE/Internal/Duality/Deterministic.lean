/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Duality.Locality
public import ComplexSLE.Internal.Loewner.Transform
import all ComplexSLE.Internal.Loewner.Duality

/-!
# Deterministic duality for a continuous driver

For a continuous driver `u : ℝ≥0 → ℂ` with `u 0 = 0` and `t : ℝ≥0` put
`ũ s = i (u (t - s) - u t) + i (u (max s t) - u t)` (`dualDriver u t`). On `[0, t]` this is the
reversed driver `revDriver u t`, and `revDriver ũ t = -u` on `[0, t]`. Together with the locality of
hulls and maps (`ComplexSLE.Internal.Duality.Locality`) and the duality
`R_t^u = (-i) L_t^{revDriver u t}` (`rightHull_eq_image_leftHull_revDriver`) this gives

* `L̃_t = i R_t` (`leftHull_dualDriver`),
* `R̃_t = i L_t` (`rightHull_dualDriver`, uses `u 0 = 0`),
* `f̃_t (w) = i z` where `f_t z = -i w` (`centeredLoewnerMap_dualDriver`, uses `u 0 = 0`).
-/

public section

open scoped NNReal ENNReal
open Set

namespace ComplexSLE.Internal

/-- The dual driver `ũ s = i (u (t - s) - u t) + i (u (max s t) - u t)` of Prop 1.5. -/
@[expose] noncomputable def dualDriver (u : ℝ≥0 → ℂ) (t : ℝ≥0) : ℝ≥0 → ℂ :=
  fun s => Complex.I * (u (t - s) - u t) + Complex.I * (u (max s t) - u t)

variable {u : ℝ≥0 → ℂ}

theorem continuous_dualDriver (hu : Continuous u) (t : ℝ≥0) : Continuous (dualDriver u t) := by
  unfold dualDriver
  fun_prop

theorem dualDriver_eq_revDriver (u : ℝ≥0 → ℂ) {t s : ℝ≥0} (hs : s ≤ t) :
    dualDriver u t s = revDriver u t s := by
  simp only [dualDriver, revDriver, max_eq_right hs, sub_self, mul_zero, add_zero]
  rw [NNReal.sub_def]

theorem dualDriver_sub (u : ℝ≥0 → ℂ) {t s : ℝ≥0} (hs : s ≤ t) :
    dualDriver u t (t - s) = Complex.I * (u s - u t) := by
  simp only [dualDriver, max_eq_right (tsub_le_self : t - s ≤ t), tsub_tsub_cancel_of_le hs,
    sub_self, mul_zero, add_zero]

theorem dualDriver_self (hu0 : u 0 = 0) (t : ℝ≥0) :
    dualDriver u t t = -Complex.I * u t := by
  simp only [dualDriver, tsub_self, max_self, hu0, sub_self, mul_zero, add_zero, zero_sub,
    mul_neg, neg_mul]

/-- `L̃_t = i R_t`. -/
theorem leftHull_dualDriver (hu : Continuous u) (t : ℝ≥0) :
    leftHull (dualDriver u t) t = (fun z => Complex.I * z) '' rightHull u hu t := by
  rw [leftHull_congr (continuous_dualDriver hu t) (continuous_revDriver hu t)
      (fun s hs => dualDriver_eq_revDriver u hs),
    rightHull_eq_image_leftHull_revDriver hu t, Set.image_image]
  have : (fun x : ℂ => Complex.I * (-Complex.I * x)) = id := by
    funext x
    simp only [id]
    linear_combination (-x) * Complex.I_mul_I
  rw [this, Set.image_id]

/-- `R̃_t = i L_t` (uses `u 0 = 0`). -/
theorem rightHull_dualDriver (hu : Continuous u) (hu0 : u 0 = 0) (t : ℝ≥0) :
    rightHull (dualDriver u t) (continuous_dualDriver hu t) t =
      (fun z => Complex.I * z) '' leftHull u t := by
  have hneg : ∀ s ≤ t, revDriver (dualDriver u t) t s = (fun s => -u s) s := by
    intro s hs
    have h1 : revDriver (dualDriver u t) t s =
        Complex.I * (dualDriver u t (t - s) - dualDriver u t t) := by
      simp only [revDriver]
      rw [← NNReal.sub_def]
    rw [h1, dualDriver_sub u hs, dualDriver_self hu0]
    linear_combination (u s) * Complex.I_mul_I
  rw [rightHull_eq_image_leftHull_revDriver (continuous_dualDriver hu t) t,
    leftHull_congr (continuous_revDriver (continuous_dualDriver hu t) t)
      (by fun_prop : Continuous fun s => -u s) hneg,
    leftHull_neg, Set.image_image]
  refine Set.image_congr fun x _ => ?_
  simp

/-- `f̃_t (w) = i z` for the point `z` with `f_t z = -i w` (uses `u 0 = 0`). -/
theorem centeredLoewnerMap_dualDriver (hu : Continuous u) (hu0 : u 0 = 0) (t : ℝ≥0) (w : ℂ)
    (hw : w ∈ (leftHull (dualDriver u t) t)ᶜ) :
    ∃ z : ↥(leftHull u t)ᶜ, centeredLoewnerMap u hu t z = -Complex.I * w ∧
      centeredLoewnerMap (dualDriver u t) (continuous_dualDriver hu t) t ⟨w, hw⟩ =
        Complex.I * z := by
  have hD := continuous_dualDriver hu t
  obtain ⟨γ, hγ0, hγ⟩ := (notMem_leftHull_iff_exists_closedSol hD t w).1 hw
  have hf : centeredLoewnerMap (dualDriver u t) hD t ⟨w, hw⟩ = γ t - dualDriver u t t :=
    centeredLoewnerMap_eq_of_closedSol hD hγ0 hγ hw
  have hDt := dualDriver_self hu0 t
  have hII : (-Complex.I) * (-Complex.I) = -1 := by
    linear_combination Complex.I_mul_I
  have hk : ClosedSol (fun s => u s.toNNReal) t
      (fun s => -Complex.I * (γ (t - s) - dualDriver u t t)) := by
    refine closedSol_reverse (W := fun s => dualDriver u t s.toNNReal) (a := -Complex.I)
      (c := dualDriver u t t) hII hγ ?_
    intro s hs
    obtain ⟨s', rfl⟩ : ∃ s' : ℝ≥0, (s' : ℝ) = s := ⟨s.toNNReal, Real.coe_toNNReal _ hs.1⟩
    have hs' : s' ≤ t := NNReal.coe_le_coe.1 hs.2
    have e1 : Real.toNNReal ((t : ℝ) - s') = t - s' := (NNReal.sub_def).symm
    simp only [Real.toNNReal_coe, e1, dualDriver_sub u hs', hDt]
    linear_combination (u s') * Complex.I_mul_I
  have hz0 : -Complex.I * (γ t - dualDriver u t t) ∈ (leftHull u t)ᶜ :=
    (notMem_leftHull_iff_exists_closedSol hu t _).2 ⟨_, by simp, hk⟩
  refine ⟨⟨_, hz0⟩, ?_, ?_⟩
  · rw [centeredLoewnerMap_eq_of_closedSol hu
      (γ := fun s => -Complex.I * (γ (t - s) - dualDriver u t t)) (by simp) hk hz0]
    simp only [sub_self, hγ0, hDt]
    linear_combination (-u t) * Complex.I_mul_I
  · rw [hf]
    change _ = Complex.I * (-Complex.I * _)
    linear_combination (γ t - dualDriver u t t) * Complex.I_mul_I

end ComplexSLE.Internal

end
