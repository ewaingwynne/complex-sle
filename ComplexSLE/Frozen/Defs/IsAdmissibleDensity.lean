/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.Mu
public import ComplexSLE.Frozen.Defs.DiffusionD
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Algebra.Ring.Periodic

/-!
# Admissible stationary densities
-/

@[expose] public section

open Real


namespace ComplexSLE

/-- `p` satisfies the hypotheses of Lemma 2.14 (paper.tex:L963-966, ruling R7): continuous,
non-negative, π-periodic, `∫₀^{2π} p = 1`, and for some `x`, `p` is `C²` off `x + πℤ` and
solves `-(µ p)' + (D p)'' = 0` there, while `D p` is `C¹` on `ℝ`. -/
def IsAdmissibleDensity (a b c : ℝ) (p : ℝ → ℝ) : Prop :=
  Continuous p ∧ (∀ u, 0 ≤ p u) ∧ Function.Periodic p π ∧ ∫ u in (0)..(2 * π), p u = 1 ∧
    ∃ x : ℝ,
      ContDiffOn ℝ 2 p {u | ∀ n : ℤ, u ≠ x + n * π} ∧
      (∀ u, (∀ n : ℤ, u ≠ x + n * π) →
        -deriv (fun v => mu a b c v * p v) u +
          deriv (deriv fun v => diffusionD a b c v * p v) u = 0) ∧
      ContDiff ℝ 1 (fun u => diffusionD a b c u * p u)

end ComplexSLE

end
