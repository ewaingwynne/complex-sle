/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.RightHull
public import ComplexSLE.Internal.Hull.ConnectedNoExt

/-!
# Provider for `ComplexSLE.lemma_2_4_rightHull`

Implementation module for the frozen anchor `ComplexSLE/Frozen/Lemma_2_4_RightHull.lean`.
The anchor is SEALED: it is proved by this module.

By the duality property (2.4) (`ComplexSLE.Internal.rightHull_eq_image_leftHull_revDriver`),
`R_t^U = (-i) L_t^V` for the continuous reversed driver `V(s) = i (U(t - s) - U_t)`; the left
hull `L_t^V` is connected by `lemma_2_4_leftHull'` (external-free), and multiplication by `-i` is
continuous.
-/

public section

open scoped NNReal

namespace ComplexSLE.Internal

/-- See `ComplexSLE.lemma_2_4_rightHull`. -/
theorem lemma_2_4_rightHull (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) :
    IsConnected (rightHull U hU t) :=
  lemma_2_4_rightHull' U hU t

end ComplexSLE.Internal

end
