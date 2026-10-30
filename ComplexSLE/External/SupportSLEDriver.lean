/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.IsSLEDriver

/-!
# EXTERNAL input: Support theorem for the planar driver

Author-approved classical input (ERRATA.md R23). Assumed, not proved: its body is a permanent
`sorry`, and every result that uses it is reported `PROVED_REL`.
-/

public section

open scoped NNReal
open MeasureTheory ProbabilityTheory

namespace ComplexSLE.External

/-- **E13 (support theorem).** A planar Brownian motion with covariance `Σ = covMatrix a b c`
(`Σ` positive semidefinite) stays uniformly within `δ` of any continuous path `φ` with `φ 0 = 0`
taking values in the range of `Σ`, on `[0, T]`, with positive probability. Used in Lemmas 4.2 and
4.4 (paper.tex:L2023, L2093-2101), stated there without proof. -/
theorem support_sleDriver {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c ^ 2 ≤ a * b) (U : ℝ≥0 → Ω → ℂ)
    (hU : IsSLEDriver a b c U P) (φ : ℝ≥0 → ℂ) (hφ : Continuous φ) (hφ0 : φ 0 = 0)
    (hφS : ∀ t, ∃ v : Fin 2 → ℝ, (covMatrix a b c).mulVec v 0 = (φ t).re ∧
      (covMatrix a b c).mulVec v 1 = (φ t).im)
    (T : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    0 < P {ω | ∀ t ≤ T, ‖U t ω - φ t‖ < δ} :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE.External

end
-- FROZEN_ANCHOR_SUFFIX_END
