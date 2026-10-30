/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Mathlib.Probability.BrownianMotion.Basic

/-!
# EXTERNAL input: Existence of Brownian motion

Author-approved classical input (ERRATA.md R23). Assumed, not proved: its body is a permanent
`sorry`, and every result that uses it is reported `PROVED_REL`.
-/

public section

open scoped NNReal
open MeasureTheory ProbabilityTheory

namespace ComplexSLE.External

/-- **E-BM (existence of Brownian motion).** Some probability space carries a standard real
Brownian motion (Mathlib's `IsBrownianReal`: Brownian finite-dimensional laws and a.s. continuous
paths). Classical (Wiener; Kolmogorov extension + Kolmogorov–Chentsov). -/
theorem exists_isBrownianReal :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE.External

end
-- FROZEN_ANCHOR_SUFFIX_END
