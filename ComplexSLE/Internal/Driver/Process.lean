/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsSLEDriver
import ComplexSLE.Infrastructure.Gaussian.MapProd

/-!
# The linear map from two Brownian coordinates to the SLE_Σ driver

For `a > 0`, `c² ≤ a b`, the real-linear map `L = driverCLM a b c : ℝ × ℝ →L[ℝ] ℂ`,
`L (x, y) = x • (√a + (c/√a) i) + y • (√(b - c²/a) i)`, has matrix `A = driverMatrix a b c` in
the coordinates `(re, im)` with `A Aᵀ = covMatrix a b c`. If `X` is `N(0, v)` then
`L (X ω₁, X ω₂)` has law `complexGaussian (v • covMatrix a b c)` under `P ⊗ P`
(`hasLaw_driverCLM_pair`). The driver `U t (ω₁, ω₂) = L (B t ω₁, B t ω₂)` for a real Brownian
motion `B` is assembled in `ComplexSLE.Internal.ExistsSLEDriver`.
-/

public section

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

namespace ComplexSLE.Internal

/-- The real-linear map `ℝ × ℝ → ℂ` sending the two independent Brownian coordinates to the
complex driver: `(x, y) ↦ x (√a + (c/√a) i) + y √(b - c²/a) i`. -/
noncomputable def driverCLM (a b c : ℝ) : ℝ × ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
      ((Real.sqrt a : ℂ) + ((c / Real.sqrt a : ℝ) : ℂ) * Complex.I) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
      (((Real.sqrt (b - c ^ 2 / a) : ℝ) : ℂ) * Complex.I)

/-- The matrix of `driverCLM` in the coordinates `(re, im)`. -/
noncomputable def driverMatrix (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.sqrt a, 0; c / Real.sqrt a, Real.sqrt (b - c ^ 2 / a)]

theorem driverCLM_apply (a b c : ℝ) (p : ℝ × ℝ) :
    driverCLM a b c p =
      (((driverMatrix a b c 0 0 * p.1 + driverMatrix a b c 0 1 * p.2 : ℝ)) : ℂ) +
        ((driverMatrix a b c 1 0 * p.1 + driverMatrix a b c 1 1 * p.2 : ℝ) : ℂ) * Complex.I := by
  simp [driverCLM, driverMatrix, Complex.real_smul]
  ring

theorem driverMatrix_mul_transpose (a b c : ℝ) (ha : 0 < a) (hc : c ^ 2 ≤ a * b) :
    driverMatrix a b c * (driverMatrix a b c)ᵀ = ComplexSLE.covMatrix a b c := by
  have hb' : 0 ≤ b - c ^ 2 / a := by
    rw [sub_nonneg, div_le_iff₀ ha]; linarith
  have h1 : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
  have h2 : Real.sqrt (b - c ^ 2 / a) * Real.sqrt (b - c ^ 2 / a) = b - c ^ 2 / a :=
    Real.mul_self_sqrt hb'
  have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have h3 : (c / Real.sqrt a) * (c / Real.sqrt a) = c ^ 2 / a := by
    rw [div_mul_div_comm, h1]; ring
  have h4 : Real.sqrt a * (c / Real.sqrt a) = c := by field_simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [driverMatrix, ComplexSLE.covMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination h1
  · linear_combination h4
  · linear_combination h4
  · linear_combination h3 + h2

/-- If `X` is `N(0, v)` under `P`, then `L (X ω₁, X ω₂)` has the law `complexGaussian (v • Σ)`
under `P ⊗ P`. -/
theorem hasLaw_driverCLM_pair {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) P)
    (a b c : ℝ) (ha : 0 < a) (hc : c ^ 2 ≤ a * b) :
    HasLaw (fun ω : Ω × Ω => driverCLM a b c (X ω.1, X ω.2))
      (complexGaussian ((v : ℝ) • covMatrix a b c)) (P.prod P) := by
  have mX := hX.aemeasurable
  have hpair : AEMeasurable (fun ω : Ω × Ω => (X ω.1, X ω.2)) (P.prod P) := by fun_prop
  have hL : Measurable (driverCLM a b c) := (driverCLM a b c).continuous.measurable
  refine ⟨hL.comp_aemeasurable hpair, ?_⟩
  have e1 : (P.prod P).map (fun ω : Ω × Ω => (X ω.1, X ω.2)) =
      (gaussianReal 0 v).prod (gaussianReal 0 v) := by
    rw [← hX.map_eq]
    exact (Measure.map_prod_map_of_aemeasurable P P mX mX).symm
  have e2 : (fun ω : Ω × Ω => driverCLM a b c (X ω.1, X ω.2)) =
      (driverCLM a b c) ∘ (fun ω : Ω × Ω => (X ω.1, X ω.2)) := rfl
  have hf : Measurable fun x : EuclideanSpace ℝ (Fin 2) => (x 0 : ℂ) + (x 1 : ℂ) * Complex.I := by
    fun_prop
  have e3 : ⇑(driverCLM a b c) = (fun x : EuclideanSpace ℝ (Fin 2) =>
      (x 0 : ℂ) + (x 1 : ℂ) * Complex.I) ∘ Infrastructure.matrixApplyPair (driverMatrix a b c) := by
    funext p
    rw [driverCLM_apply]
    simp
  rw [e2, ← AEMeasurable.map_map_of_aemeasurable hL.aemeasurable hpair, e1, e3,
    ← Measure.map_map hf (Infrastructure.measurable_matrixApplyPair _),
    Infrastructure.map_prod_gaussianReal_matrixApplyPair, driverMatrix_mul_transpose a b c ha hc]
  rfl

end ComplexSLE.Internal

end
