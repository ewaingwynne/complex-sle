/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Basic.ENNReal.Real

/-!
# Solutions of the Loewner initial value problem
-/

@[expose] public section

open scoped NNReal ENNReal

namespace ComplexSLE

/-- `γ` solves the Loewner initial value problem `γ' = 2/(γ - U)`, `γ 0 = z`, on `[0, τ)`
(Def 1.1, paper.tex:L251-263). Times are real `t ≥ 0`; `U` is read at `t.toNNReal`. -/
def IsLoewnerSolution (U : ℝ≥0 → ℂ) (z : ℂ) (τ : ℝ≥0∞) (γ : ℝ → ℂ) : Prop :=
  γ 0 = z ∧ ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < τ →
    γ t ≠ U t.toNNReal ∧
      HasDerivWithinAt γ (2 / (γ t - U t.toNNReal)) (Set.Ici 0) t

end ComplexSLE

end
