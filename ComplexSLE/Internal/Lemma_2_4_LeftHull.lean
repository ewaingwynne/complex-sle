/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.LeftHull
import ComplexSLE.Internal.Hull.ConnectedNoExt

/-!
# Provider for `ComplexSLE.lemma_2_4_leftHull`

Implementation module for the frozen anchor `ComplexSLE/Frozen/Lemma_2_4_LeftHull.lean`.

`L_t` is nonempty (`U 0 ∈ L_t`), closed and bounded, and `g_t` extends holomorphically to
`ℂ ∖ L_t`; all of this is proved in-project, with no external input. If `L_t` were not
preconnected it would split as `L_t = A ⊔ B` with `A`, `B` disjoint, closed and nonempty;
the part not containing `U 0` is empty by `leftHull_separation_eq_empty'`
(`Hull/ConnectedNoExt.lean`; a maximum-principle argument replacing the paper's
loop/homotopy sketch, paper.tex:L658-666).
-/

public section

open scoped NNReal
open Set

namespace ComplexSLE.Internal

/-- See `ComplexSLE.lemma_2_4_leftHull`. -/
theorem lemma_2_4_leftHull (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) :
    IsConnected (leftHull U t) :=
  lemma_2_4_leftHull' U hU t

end ComplexSLE.Internal

end
