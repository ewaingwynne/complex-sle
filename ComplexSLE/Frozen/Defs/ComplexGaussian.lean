/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.Complex.Basic

/-!
# Centered Gaussian laws on the complex plane
-/

@[expose] public section

open MeasureTheory ProbabilityTheory


namespace ComplexSLE

/-- The centered Gaussian law on `ℂ ≅ ℝ²` (coordinates `(re, im)`) with covariance matrix `S`
(used for Def 1.4 under ruling R6). -/
noncomputable def complexGaussian (S : Matrix (Fin 2) (Fin 2) ℝ) : Measure ℂ :=
  (multivariateGaussian 0 S).map fun x : EuclideanSpace ℝ (Fin 2) =>
    (x 0 : ℂ) + (x 1 : ℂ) * Complex.I

end ComplexSLE

end
