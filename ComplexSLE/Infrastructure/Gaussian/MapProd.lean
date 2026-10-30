/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Linear images of product Gaussians

Source-independent Gaussian fact. If `ξ₁, ξ₂` are independent `N(0, v)` real variables and
`A` is a real `2 × 2` matrix, then `A (ξ₁, ξ₂)` has the multivariate Gaussian law
`N(0, v • (A * Aᵀ))` on `EuclideanSpace ℝ (Fin 2)`.
-/

public section

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

namespace ComplexSLE.Infrastructure

/-- The linear map `(x, y) ↦ A (x, y)` from `ℝ × ℝ` to `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def matrixApplyPair (A : Matrix (Fin 2) (Fin 2) ℝ) (p : ℝ × ℝ) :
    EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![A 0 0 * p.1 + A 0 1 * p.2, A 1 0 * p.1 + A 1 1 * p.2]

@[simp] theorem matrixApplyPair_apply_zero (A : Matrix (Fin 2) (Fin 2) ℝ) (p : ℝ × ℝ) :
    matrixApplyPair A p 0 = A 0 0 * p.1 + A 0 1 * p.2 := by
  simp [matrixApplyPair]

@[simp] theorem matrixApplyPair_apply_one (A : Matrix (Fin 2) (Fin 2) ℝ) (p : ℝ × ℝ) :
    matrixApplyPair A p 1 = A 1 0 * p.1 + A 1 1 * p.2 := by
  simp [matrixApplyPair]

theorem measurable_matrixApplyPair (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Measurable (matrixApplyPair A) := by
  unfold matrixApplyPair
  fun_prop

/-- **Linear image of a product of two `N(0, v)` laws.** The image of
`gaussianReal 0 v ⊗ gaussianReal 0 v` under `p ↦ A p` is the multivariate Gaussian
`N(0, v • (A * Aᵀ))`. -/
theorem map_prod_gaussianReal_matrixApplyPair (v : ℝ≥0) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ((gaussianReal 0 v).prod (gaussianReal 0 v)).map (matrixApplyPair A) =
      multivariateGaussian 0 ((v : ℝ) • (A * Aᵀ)) := by
  have hS : ((v : ℝ) • (A * Aᵀ)).PosSemidef := by
    have h := Matrix.posSemidef_self_mul_conjTranspose A
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h.smul v.2
  have hm := measurable_matrixApplyPair A
  apply Measure.ext_of_charFun
  ext ξ
  rw [charFun_multivariateGaussian hS, charFun_apply, integral_map hm.aemeasurable (by fun_prop)]
  set u : ℝ := ξ 0 * A 0 0 + ξ 1 * A 1 0 with hu
  set w : ℝ := ξ 0 * A 0 1 + ξ 1 * A 1 1 with hw
  have h1 : ∀ p : ℝ × ℝ, Complex.exp (↑(inner ℝ (matrixApplyPair A p) ξ) * Complex.I) =
      Complex.exp (↑u * ↑p.1 * Complex.I) * Complex.exp (↑w * ↑p.2 * Complex.I) := by
    intro p
    rw [← Complex.exp_add]
    congr 1
    simp only [matrixApplyPair, PiLp.inner_apply, Fin.sum_univ_two, hu, hw]
    simp
    ring
  simp_rw [h1]
  rw [integral_prod_mul (fun x : ℝ => Complex.exp (↑u * ↑x * Complex.I))
    (fun x : ℝ => Complex.exp (↑w * ↑x * Complex.I))]
  rw [← charFun_apply_real, ← charFun_apply_real, charFun_gaussianReal, charFun_gaussianReal]
  rw [← Complex.exp_add]
  have h2 : ξ.ofLp ⬝ᵥ ((v : ℝ) • (A * Aᵀ)) *ᵥ ξ.ofLp = (v : ℝ) * (u ^ 2 + w ^ 2) := by
    simp only [dotProduct, Fin.sum_univ_two, Matrix.mulVec, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.transpose_apply, hu, hw, smul_eq_mul]
    ring
  rw [h2]
  congr 1
  simp
  ring

end ComplexSLE.Infrastructure

end
