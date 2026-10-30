/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsLoewnerSolution
public import Mathlib.Order.CompleteLattice.Basic

/-!
# The absorbing time
-/

@[expose] public section

open scoped NNReal ENNReal

namespace ComplexSLE

/-- The absorbing time `T_z ∈ [0, ∞]`: the supremum of the times up to which the Loewner
initial value problem started at `z` has a solution (paper.tex:L268). -/
noncomputable def absorbingTime (U : ℝ≥0 → ℂ) (z : ℂ) : ℝ≥0∞ :=
  sSup {τ | ∃ γ, IsLoewnerSolution U z τ γ}

end ComplexSLE

end
