/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsSLEDriver
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

import ComplexSLE.Infrastructure.Stochastic.SupportMeasurable
import ComplexSLE.Internal.Driver.Shift

/-!
# Support theorem for the SLE_Σ driver (proof of the external input)

A complete proof of the exact statement of `ComplexSLE.External.support_sleDriver` (E13); this
module deliberately does not import `ComplexSLE.External.*`, the statement is a verbatim copy.

Route.

1. Each coordinate `U s` is only a.e.-measurable and the target set is an arbitrary set, with `P`
   applied as an outer measure. Pass to the completion `P.completion` on `NullMeasurableSpace Ω P`,
   which has the same values on every set, for which every `U s` is measurable, and in which the
   a.e. data (`U` continuous, `U 0 = 0`), the independence of the restarted path from the past
   (`IsSLEDriver.indepFun_shift_past`, a statement about values of `P` on sets) and the laws of the
   increments are unchanged.
2. `Infrastructure.Support.support_of_measurableDriver` proves the support theorem for a process
   with measurable coordinates by chaining over a fine grid (no Cameron–Martin): see its module
   docstring. The range of `Σ` in the statement is `Infrastructure.SupportGaussian.covRange Σ`
   (`mem_covRange_iff`), and `Σ` is positive semidefinite for `a, b ≥ 0`, `c² ≤ a b`.
-/

public section

open scoped NNReal
open MeasureTheory ProbabilityTheory

namespace ComplexSLE.Internal.ExternalProofs

/-- **Support theorem for the driver (E13).** Same statement as
`ComplexSLE.External.support_sleDriver`, proved. -/
theorem support_sleDriver {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c ^ 2 ≤ a * b) (U : ℝ≥0 → Ω → ℂ)
    (hU : IsSLEDriver a b c U P) (φ : ℝ≥0 → ℂ) (hφ : Continuous φ) (hφ0 : φ 0 = 0)
    (hφS : ∀ t, ∃ v : Fin 2 → ℝ, (covMatrix a b c).mulVec v 0 = (φ t).re ∧
      (covMatrix a b c).mulVec v 1 = (φ t).im)
    (T : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    0 < P {ω | ∀ t ≤ T, ‖U t ω - φ t‖ < δ} := by
  have : IsProbabilityMeasure P.completion :=
    ⟨(Measure.completion_apply P Set.univ).trans measure_univ⟩
  have hm : ∀ s, @Measurable (NullMeasurableSpace Ω P) ℂ _ _ (U s) := fun s =>
    (hU.aemeasurable s).nullMeasurable
  have hdrv : Infrastructure.Support.MeasurableDriver (covMatrix a b c)
      (Ω := NullMeasurableSpace Ω P) U P.completion := by
    refine ⟨hm, hU.zero, hU.cont, fun t => ?_, fun s t hst => ?_⟩
    · exact (IndepFun_iff_Indep _ _ _).2 ((Indep_iff _ _ _).2
        ((Indep_iff _ _ _).1 ((IndepFun_iff_Indep _ _ _).1 (hU.indepFun_shift_past t))))
    · have h := hU.law_increment s t hst
      have hX : @Measurable (NullMeasurableSpace Ω P) ℂ _ _ (fun ω => U t ω - U s ω) :=
        (hm t).sub (hm s)
      refine Measure.ext fun B hB => ?_
      rw [Measure.map_apply hX hB]
      change P ((fun ω => U t ω - U s ω) ⁻¹' B) = _
      rw [← h.map_eq, Measure.map_apply_of_aemeasurable h.aemeasurable hB]
  have hS := Infrastructure.SupportGaussian.covMatrix_posSemidef' ha hb hc
  have hφS' : ∀ t, φ t ∈ Infrastructure.SupportGaussian.covRange (covMatrix a b c) := fun t =>
    (Infrastructure.SupportGaussian.mem_covRange_iff _ _).2 (hφS t)
  have key := Infrastructure.Support.support_of_measurableDriver hS hdrv hφ hφ0 hφS' T hδ
  exact key

end ComplexSLE.Internal.ExternalProofs

end
