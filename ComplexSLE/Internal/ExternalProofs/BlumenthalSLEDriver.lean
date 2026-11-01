/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsSLEDriver
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

import ComplexSLE.Infrastructure.Stochastic.BlumenthalGerm
import ComplexSLE.Internal.Driver.Shift

/-!
# Blumenthal 0-1 law for the SLE_Σ driver (proof of the external input)

A complete proof of the exact statement of `ComplexSLE.External.blumenthal_sleDriver`
(E5, Revuz–Yor III.2.15); this module deliberately does not import `ComplexSLE.External.*`, the
statement is a verbatim copy.

Route.

1. Each coordinate `U s` is only a.e.-measurable, so the σ-algebras `σ(U s : s ≤ ε)` of the
   statement need not lie in the ambient σ-algebra and `P` is applied as an outer measure. Pass to
   the completion `P.completion` on `NullMeasurableSpace Ω P`, which has the same values on every
   set and for which every `U s` is measurable, and in which the a.e. data (`U` continuous,
   `U 0 = 0`) and the independence of the restarted path from the past
   (`IsSLEDriver.indep_shift_past`, a statement about values of `P` on sets) are unchanged.
2. `Infrastructure.Stochastic.BlumenthalGerm.blumenthal_of_measurable` proves the 0-1 law for a
   process with measurable coordinates, a.s. continuous paths with `U 0 = 0` a.s., and restarted
   paths independent of the past at every deterministic time.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Internal.ExternalProofs

/-- **Blumenthal 0-1 law for the driver (E5).** Same statement as
`ComplexSLE.External.blumenthal_sleDriver`, proved. -/
theorem blumenthal_sleDriver {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ} (hU : IsSLEDriver a b c U P)
    (A : Set Ω)
    (hA : ∀ ε : ℝ≥0, 0 < ε → ∃ B : Set Ω,
      MeasurableSet[⨆ (s : ℝ≥0) (_ : s ≤ ε), MeasurableSpace.comap (U s) inferInstance] B ∧
        P (symmDiff A B) = 0) :
    P A = 0 ∨ P A = 1 := by
  have : IsProbabilityMeasure P.completion :=
    ⟨(Measure.completion_apply P univ).trans measure_univ⟩
  have hm : ∀ s, @Measurable (NullMeasurableSpace Ω P) ℂ _ _ (U s) := fun s =>
    (hU.aemeasurable s).nullMeasurable
  have hind : ∀ t : ℝ≥0, Indep
      (MeasurableSpace.comap (fun ω (s : ℝ≥0) => U (s + t) ω - U t ω) MeasurableSpace.pi)
      (MeasurableSpace.comap (fun ω (r : Set.Iic t) => U (r : ℝ≥0) ω) MeasurableSpace.pi)
      P.completion := fun t =>
    (Indep_iff _ _ _).2 ((Indep_iff _ _ _).1 (hU.indep_shift_past t))
  exact ComplexSLE.Infrastructure.Blumenthal.blumenthal_of_measurable
    (Ω := NullMeasurableSpace Ω P) (P := P.completion) (U := U) hm hU.cont hU.zero hind A hA

end ComplexSLE.Internal.ExternalProofs

end
