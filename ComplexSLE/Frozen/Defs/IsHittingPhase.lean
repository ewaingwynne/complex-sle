/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsSLEDriver
public import ComplexSLE.Frozen.Defs.LeftHull
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# The hitting phase
-/

@[expose] public section

open MeasureTheory Real

open scoped NNReal ENNReal

namespace ComplexSLE

/-- Hitting phase: for each `z ≠ 0`, a.s. `T_z < ∞` and `z ∈ closure (⋃_{t < T_z} L_t)`
(Def 1.7, paper.tex:L414).
Meaningful only for positive semidefinite `Σ`; every theorem using it assumes this.
Rulings R4 (`z ≠ 0`) and R12 (all probability spaces in `Type`). -/
def IsHittingPhase (a b c : ℝ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ℝ≥0 → Ω → ℂ), IsSLEDriver a b c U P → ∀ z : ℂ, z ≠ 0 →
      ∀ᵐ ω ∂P, absorbingTime (U · ω) z < ∞ ∧
        z ∈ closure (⋃ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < absorbingTime (U · ω) z),
          leftHull (U · ω) t)

end ComplexSLE

end
