/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsAdmissibleDensity
public import ComplexSLE.Internal.Density.Regular
public import ComplexSLE.Internal.Density.Degenerate

/-!
# Provider for `ComplexSLE.exists_admissibleDensity`

Implementation module for the frozen anchor `ComplexSLE/Frozen/Lemma_2_13_Exists.lean`.
The anchor is SEALED: it is proved by this module.

The proof splits on `c² < ab` (Case 1, `ComplexSLE/Internal/Density/Regular.lean`) and
`c² = ab` (Case 2, `ComplexSLE/Internal/Density/Degenerate.lean`); the latter treats
`c = √(ab)` directly and `c = -√(ab)` by the symmetry `u ↦ -u` (paper.tex:L1000-1105).
-/

public section

namespace ComplexSLE.Internal

/-- **Lemma 2.13, existence part** (paper.tex:L941-955; rulings R5, R7, R19). -/
theorem exists_admissibleDensity (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b) :
    ∃ p, IsAdmissibleDensity a b c p := by
  rcases hc.lt_or_eq with hlt | heq
  · exact exists_admissibleDensity_of_sq_lt ha hb hlt
  · exact exists_admissibleDensity_of_sq_eq ha hb heq

end ComplexSLE.Internal

end
