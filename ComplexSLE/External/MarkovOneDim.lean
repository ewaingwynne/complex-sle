/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.IsDiffusionSolution

/-!
# EXTERNAL input: `markov_oneDim`

Author-approved classical input (ERRATA.md R29; Stroock–Varadhan 6.2.2, Ethier–Kurtz 4.4.2). Assumed, not proved: its
body is a permanent `sorry`, and every result that uses it is reported `PROVED_REL`.
-/

public section

open scoped NNReal
open MeasureTheory ProbabilityTheory

namespace ComplexSLE.External

/-- **Markov property of a one-dimensional diffusion with smooth periodic coefficients satisfying the Hörmander
condition** (Stroock–Varadhan Thm 6.2.2; Ethier–Kurtz Thm 4.4.2), relative to a transition kernel `p` that represents
the time-`t` law of every solution started at a point. Also: `p` is π-equivariant. -/
theorem markov_oneDim (α β : ℝ → ℝ) (hα : ContDiff ℝ (⊤ : ℕ∞) α) (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hαper : ∀ u, α (u + Real.pi) = α u) (hβper : ∀ u, β (u + Real.pi) ^ 2 = β u ^ 2)
    (hH : ∀ u, β u ≠ 0 ∨ deriv β u * α u ≠ 0)
    (p : ℝ≥0 → ℝ → ℝ → ℝ) (hp0 : ∀ t u v, 0 ≤ p t u v)
    (hpc : ∀ t : ℝ≥0, 0 < t → ∀ u, Continuous (p t u))
    (hp : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ≥0 ‹_›) (X : ℝ≥0 → Ω → ℝ) (u : ℝ),
      IsDiffusionSolution ℱ α β X P → (∀ᵐ ω ∂P, X 0 ω = u) →
        ∀ t : ℝ≥0, 0 < t → P.map (X t) = volume.withDensity fun v => ENNReal.ofReal (p t u v)) :
    (∀ t : ℝ≥0, 0 < t → ∀ u v, p t (u + Real.pi) (v + Real.pi) = p t u v) ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ≥0 ‹_›) (X : ℝ≥0 → Ω → ℝ), IsDiffusionSolution ℱ α β X P →
        ∀ t s : ℝ≥0, 0 < s → ∀ f : ℝ → ℝ, Measurable f → (∃ C : ℝ, ∀ v, |f v| ≤ C) →
          P[fun ω => f (X (t + s) ω) | ℱ t] =ᵐ[P] fun ω => ∫ v, f v * p s (X t ω) v :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE.External

end
-- FROZEN_ANCHOR_SUFFIX_END
