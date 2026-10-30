/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.ComplexGaussian
public import Mathlib.Probability.HasLaw
import ComplexSLE.Infrastructure.Gaussian.MapMatrix

/-!
# Real-linear images of `complexGaussian`

If `L : ℂ → ℂ` is the real-linear map with invertible real matrix `M` in the coordinates
`(re, im)`, then the image of `complexGaussian S` under `L` is `complexGaussian (M * S * Mᵀ)`
(`map_complexGaussian_of_isUnit`; no positivity of `S` is needed). This is the common core of the
scaling and symmetry lemmas for the driver of `SLE_Σ`.
-/

public section

open MeasureTheory ProbabilityTheory Matrix

namespace ComplexSLE.Internal

instance isProbabilityMeasure_complexGaussian (S : Matrix (Fin 2) (Fin 2) ℝ) :
    IsProbabilityMeasure (complexGaussian S) := by
  unfold complexGaussian
  infer_instance

/-- The image of `complexGaussian S` under a real-linear map `L` with invertible matrix `M`
(in the coordinates `(re, im)`) is `complexGaussian (M * S * Mᵀ)`. -/
theorem map_complexGaussian_of_isUnit (S M : Matrix (Fin 2) (Fin 2) ℝ) (hM : IsUnit M.det)
    (L : ℂ → ℂ) (hL : Measurable L)
    (hLM : ∀ x y : ℝ, L (x + y * Complex.I) =
      ((M 0 0 * x + M 0 1 * y : ℝ) : ℂ) + ((M 1 0 * x + M 1 1 * y : ℝ) : ℂ) * Complex.I) :
    (complexGaussian S).map L = complexGaussian (M * S * Mᵀ) := by
  have he : Measurable fun x : EuclideanSpace ℝ (Fin 2) => (x 0 : ℂ) + (x 1 : ℂ) * Complex.I := by
    fun_prop
  have hcomp : L ∘ (fun x : EuclideanSpace ℝ (Fin 2) => (x 0 : ℂ) + (x 1 : ℂ) * Complex.I) =
      (fun x : EuclideanSpace ℝ (Fin 2) => (x 0 : ℂ) + (x 1 : ℂ) * Complex.I) ∘
        Infrastructure.matrixApply M := by
    funext x
    simp [hLM]
  unfold complexGaussian
  rw [Measure.map_map hL he, hcomp, ← Measure.map_map he (Infrastructure.measurable_matrixApply M),
    Infrastructure.map_matrixApply_multivariateGaussian_of_isUnit M hM]

/-- Transport of a `complexGaussian` law along a real-linear map with invertible matrix. -/
theorem _root_.ProbabilityTheory.HasLaw.map_complexGaussian {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℂ} {S : Matrix (Fin 2) (Fin 2) ℝ} (hX : HasLaw X (complexGaussian S) P)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : IsUnit M.det) (L : ℂ → ℂ) (hL : Measurable L)
    (hLM : ∀ x y : ℝ, L (x + y * Complex.I) =
      ((M 0 0 * x + M 0 1 * y : ℝ) : ℂ) + ((M 1 0 * x + M 1 1 * y : ℝ) : ℂ) * Complex.I) :
    HasLaw (fun ω => L (X ω)) (complexGaussian (M * S * Mᵀ)) P := by
  refine ⟨hL.comp_aemeasurable hX.aemeasurable, ?_⟩
  rw [← map_complexGaussian_of_isUnit S M hM L hL hLM, ← hX.map_eq]
  exact (AEMeasurable.map_map_of_aemeasurable hL.aemeasurable hX.aemeasurable).symm

/-- Negation preserves every `complexGaussian` law (`-1` has matrix `-I`, and
`(-I) S (-I)ᵀ = S`). -/
theorem _root_.ProbabilityTheory.HasLaw.neg_complexGaussian {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℂ} {S : Matrix (Fin 2) (Fin 2) ℝ}
    (hX : HasLaw X (complexGaussian S) P) : HasLaw (fun ω => - X ω) (complexGaussian S) P := by
  have h := hX.map_complexGaussian (-1 : Matrix (Fin 2) (Fin 2) ℝ)
    (by simp [Matrix.det_neg]) (fun z => -z) measurable_neg (by intro x y; simp; ring)
  have hS : (-1 : Matrix (Fin 2) (Fin 2) ℝ) * S * (-1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = S := by
    simp
  rwa [hS] at h

end ComplexSLE.Internal

end
