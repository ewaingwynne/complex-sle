/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.CovMatrix
public import ComplexSLE.Frozen.Defs.ComplexGaussian
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Mathlib.Probability.HasLaw

/-!
# The driving process of SLE_Σ
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped NNReal

namespace ComplexSLE

/-- `U` is a complex Brownian motion with infinitesimal covariance `Σ = covMatrix a b c`:
a.s. continuous paths, `U 0 = 0` a.s., independent increments, and
`U t - U s ∼ N(0, (t - s) Σ)` on `ℂ ≅ ℝ²` for `s ≤ t` (Def 1.4, paper.tex:L301-308, ruling R6).
Positive semidefiniteness of `Σ` is a standing assumption of the theorems, not a field. -/
structure IsSLEDriver {Ω : Type*} [MeasurableSpace Ω] (a b c : ℝ) (U : ℝ≥0 → Ω → ℂ)
    (P : Measure Ω) : Prop where
  cont : ∀ᵐ ω ∂P, Continuous fun t => U t ω
  zero : ∀ᵐ ω ∂P, U 0 ω = 0
  indepIncrements : HasIndepIncrements U P
  law_increment : ∀ s t : ℝ≥0, s ≤ t →
    HasLaw (fun ω => U t ω - U s ω) (complexGaussian (((t : ℝ) - s) • covMatrix a b c)) P

end ComplexSLE

end
