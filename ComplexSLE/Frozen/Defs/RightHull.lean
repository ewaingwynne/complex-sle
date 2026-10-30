/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.CenteredLoewnerMap

/-!
# The right hull
-/

@[expose] public section

open scoped NNReal

namespace ComplexSLE

/-- The right hull `R_t = ℂ ∖ f_t(ℂ ∖ L_t)` (Def 1.2, paper.tex:L271-277). -/
noncomputable def rightHull (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) : Set ℂ :=
  (Set.range (centeredLoewnerMap U hU t))ᶜ

end ComplexSLE

end
