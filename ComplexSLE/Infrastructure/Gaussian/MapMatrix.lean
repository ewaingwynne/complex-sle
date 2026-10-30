/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Linear images of two-dimensional centered Gaussians

Source-independent Gaussian fact. If `S` is a positive semidefinite real `2 × 2` matrix and `M` is
any real `2 × 2` matrix, then the image of `multivariateGaussian 0 S` under `x ↦ M x` is
`multivariateGaussian 0 (M * S * Mᵀ)` (`map_matrixApply_multivariateGaussian`). When `M` is
invertible the statement also holds without positivity
(`map_matrixApply_multivariateGaussian_of_isUnit`), because both sides are then the Dirac mass
at `0`.
-/

public section

open MeasureTheory ProbabilityTheory Matrix

namespace ComplexSLE.Infrastructure

/-- The linear map `x ↦ M x` on `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def matrixApply (M : Matrix (Fin 2) (Fin 2) ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![M 0 0 * x 0 + M 0 1 * x 1, M 1 0 * x 0 + M 1 1 * x 1]

@[simp] theorem matrixApply_apply_zero (M : Matrix (Fin 2) (Fin 2) ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    matrixApply M x 0 = M 0 0 * x 0 + M 0 1 * x 1 := by
  simp [matrixApply]

@[simp] theorem matrixApply_apply_one (M : Matrix (Fin 2) (Fin 2) ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    matrixApply M x 1 = M 1 0 * x 0 + M 1 1 * x 1 := by
  simp [matrixApply]

theorem measurable_matrixApply (M : Matrix (Fin 2) (Fin 2) ℝ) : Measurable (matrixApply M) := by
  unfold matrixApply
  fun_prop

@[simp] theorem matrixApply_zero (M : Matrix (Fin 2) (Fin 2) ℝ) : matrixApply M 0 = 0 := by
  ext i
  fin_cases i <;> simp

/-- **Linear image of a centered 2-dimensional Gaussian (positive semidefinite case).** -/
theorem map_matrixApply_multivariateGaussian (M : Matrix (Fin 2) (Fin 2) ℝ)
    {S : Matrix (Fin 2) (Fin 2) ℝ} (hS : S.PosSemidef) :
    (multivariateGaussian 0 S).map (matrixApply M) = multivariateGaussian 0 (M * S * Mᵀ) := by
  have hS' : (M * S * Mᵀ).PosSemidef := by
    have h := hS.mul_mul_conjTranspose_same M
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hm := measurable_matrixApply M
  apply Measure.ext_of_charFun
  ext ξ
  rw [charFun_multivariateGaussian hS', charFun_apply, integral_map hm.aemeasurable (by fun_prop)]
  set η : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 ![M 0 0 * ξ 0 + M 1 0 * ξ 1, M 0 1 * ξ 0 + M 1 1 * ξ 1] with hη
  have h1 : ∀ x : EuclideanSpace ℝ (Fin 2),
      Complex.exp (↑(inner ℝ (matrixApply M x) ξ) * Complex.I) =
        Complex.exp (↑(inner ℝ x η) * Complex.I) := by
    intro x
    congr 2
    simp only [PiLp.inner_apply, Fin.sum_univ_two, matrixApply_apply_zero, matrixApply_apply_one,
      hη]
    simp
    ring
  simp_rw [h1]
  rw [← charFun_apply, charFun_multivariateGaussian hS]
  have h2 : η.ofLp ⬝ᵥ S *ᵥ η.ofLp = ξ.ofLp ⬝ᵥ (M * S * Mᵀ) *ᵥ ξ.ofLp := by
    simp only [dotProduct, Fin.sum_univ_two, Matrix.mulVec, Matrix.mul_apply,
      Matrix.transpose_apply, hη]
    simp
    ring
  rw [h2]
  simp

/-- **Linear image of a centered 2-dimensional Gaussian, invertible case.** For invertible `M` the
positivity hypothesis is not needed: if `S` is not positive semidefinite then neither is
`M * S * Mᵀ`, and both sides are the Dirac mass at `0`. -/
theorem map_matrixApply_multivariateGaussian_of_isUnit (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : IsUnit M.det) (S : Matrix (Fin 2) (Fin 2) ℝ) :
    (multivariateGaussian 0 S).map (matrixApply M) = multivariateGaussian 0 (M * S * Mᵀ) := by
  by_cases hS : S.PosSemidef
  · exact map_matrixApply_multivariateGaussian M hS
  · have hS' : ¬ (M * S * Mᵀ).PosSemidef := by
      intro h
      apply hS
      have hMt : IsUnit (Mᵀ).det := by rwa [Matrix.det_transpose]
      have h1 := h.mul_mul_conjTranspose_same M⁻¹
      rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h1
      have h2 : M⁻¹ * (M * S * Mᵀ) * (M⁻¹)ᵀ = S := by
        have e1 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hM
        have e2 : Mᵀ * (M⁻¹)ᵀ = 1 := by
          rw [← Matrix.transpose_mul, e1, Matrix.transpose_one]
        calc M⁻¹ * (M * S * Mᵀ) * (M⁻¹)ᵀ = (M⁻¹ * M) * S * (Mᵀ * (M⁻¹)ᵀ) := by
              simp only [Matrix.mul_assoc]
          _ = S := by rw [e1, e2]; simp
      rwa [h2] at h1
    rw [multivariateGaussian_of_not_posSemidef _ hS, multivariateGaussian_of_not_posSemidef _ hS',
      Measure.map_dirac' (measurable_matrixApply M), matrixApply_zero]

end ComplexSLE.Infrastructure

end
