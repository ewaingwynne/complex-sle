/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.IsSLEDriverAdapted
public import ComplexSLE.Frozen.Defs.IsDiffusionSolution
public import ComplexSLE.Frozen.Defs.DiffusionD
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# EXTERNAL input: `hormander_oneDim`

Author-approved classical input (ERRATA.md R24, R25). Assumed, not proved: its body is a permanent
`sorry`, and every result that uses it is reported `PROVED_REL`.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.External

/-- **E8 (one-dimensional Hörmander theorem; [Hai11, Thm 1.3] with Stroock–Varadhan
uniqueness).** Let `α, β` be smooth with `α` and `β²` `π`-periodic and, at every `u`,
`β(u) ≠ 0` or `β'(u) α(u) ≠ 0` (the paper's (A.2); it is the parabolic Hörmander condition for
the Stratonovich form, and bounded derivatives of all orders follow from periodicity). Then
there is a transition density `p t u v`, smooth in `(u, v)` for `t > 0`, such that
`u ↦ ∫ f(v) p t u v dv` is smooth for every bounded measurable `f`, and every solution `X` of
`dX = α(X) dt + β(X) dB` (martingale form, any filtered probability space) started at `u` has
`law(X_t) = p t u (·) dv` for `t > 0`. The last clause packages uniqueness in law of the
martingale problem (`β` Lipschitz). Serves `step:horm-apply-hairer` and hence Lemma A.2
(`T_s f` smooth, the law of `X_t` has a density; `t > 0`, the paper's `t ≥ 0` is a slip at
`t = 0`). -/
theorem hormander_oneDim (α β : ℝ → ℝ) (hα : ContDiff ℝ (⊤ : ℕ∞) α) (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hαper : ∀ u, α (u + Real.pi) = α u) (hβper : ∀ u, β (u + Real.pi) ^ 2 = β u ^ 2)
    (hH : ∀ u, β u ≠ 0 ∨ deriv β u * α u ≠ 0) :
    ∃ p : ℝ≥0 → ℝ → ℝ → ℝ,
      (∀ t : ℝ≥0, 0 < t → ContDiff ℝ (⊤ : ℕ∞) fun uv : ℝ × ℝ => p t uv.1 uv.2) ∧
      (∀ t u v, 0 ≤ p t u v) ∧
      (∀ t : ℝ≥0, 0 < t → ∀ f : ℝ → ℝ, Measurable f → (∃ C : ℝ, ∀ v, |f v| ≤ C) →
        ContDiff ℝ (⊤ : ℕ∞) fun u => ∫ v, f v * p t u v) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ≥0 ‹_›) (X : ℝ≥0 → Ω → ℝ) (u : ℝ),
        IsDiffusionSolution ℱ α β X P → (∀ᵐ ω ∂P, X 0 ω = u) →
          ∀ t : ℝ≥0, 0 < t →
            P.map (X t) = volume.withDensity fun v => ENNReal.ofReal (p t u v) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE.External

end
-- FROZEN_ANCHOR_SUFFIX_END
