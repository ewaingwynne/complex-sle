/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsSLEDriver
public import ComplexSLE.Frozen.Defs.LeftHull
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# The dense phase
-/

@[expose] public section

open MeasureTheory Real

open scoped NNReal

namespace ComplexSLE

/-- Dense phase: for each `z ≠ 0`, a.s. `z ∈ closure (⋃ L_t) \ ⋃ L_t`
(Def 1.7, paper.tex:L415).
Meaningful only for positive semidefinite `Σ`; every theorem using it assumes this.
Rulings R4 (`z ≠ 0`) and R12 (all probability spaces in `Type`). -/
def IsDensePhase (a b c : ℝ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ℝ≥0 → Ω → ℂ), IsSLEDriver a b c U P → ∀ z : ℂ, z ≠ 0 →
      ∀ᵐ ω ∂P, z ∈ closure (⋃ t : ℝ≥0, leftHull (U · ω) t) \
        ⋃ t : ℝ≥0, leftHull (U · ω) t

end ComplexSLE

end
