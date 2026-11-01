/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.MeasureTheory.Measure.Basic

/-!
# The σ-algebra of sets that agree almost everywhere with a set of a given σ-algebra

Source-independent measure theory. For a measure `P` on `Ω` and a σ-algebra `m'` on `Ω` (not
necessarily contained in the ambient one), `aeSigma P m'` is the σ-algebra of the sets `B` such that
`P (B ∆ G) = 0` for some `G` measurable for `m'`; `P` is applied as an outer measure, so `B` and `G`
need not be measurable for the ambient σ-algebra.

* `measurable_aeSigma`: a function that agrees `P`-a.e. with an `m'`-measurable function is
  measurable for `aeSigma P m'`.
-/

public section

open MeasureTheory Set
open scoped symmDiff

namespace ComplexSLE.Infrastructure.Blumenthal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The σ-algebra of sets `B` with `P (B ∆ G) = 0` for some `G` measurable for `m'` (`P` applied as
an outer measure). -/
@[expose, instance_reducible] def aeSigma (P : Measure Ω) (m' : MeasurableSpace Ω) :
    MeasurableSpace Ω where
  MeasurableSet' B := ∃ G : Set Ω, MeasurableSet[m'] G ∧ P (B ∆ G) = 0
  measurableSet_empty := ⟨∅, @MeasurableSet.empty _ m', by simp⟩
  measurableSet_compl := by
    rintro B ⟨G, hG, h⟩
    exact ⟨Gᶜ, @MeasurableSet.compl _ _ m' hG, by rwa [compl_symmDiff_compl]⟩
  measurableSet_iUnion := by
    intro f hf
    choose G hG h using hf
    exact ⟨⋃ n, G n, @MeasurableSet.iUnion _ _ m' _ _ hG,
      measure_mono_null iUnion_symmDiff_iUnion_subset (measure_iUnion_null h)⟩

/-- A function that agrees `P`-a.e. with an `m'`-measurable function is
`aeSigma P m'`-measurable. -/
theorem measurable_aeSigma {β : Type*} [MeasurableSpace β] {P : Measure Ω}
    {m' : MeasurableSpace Ω} {f g : Ω → β} (hg : Measurable[m'] g) (hfg : f =ᵐ[P] g) :
    Measurable[aeSigma P m'] f := by
  intro O hO
  refine ⟨g ⁻¹' O, hg hO, measure_mono_null ?_ (ae_iff.1 hfg)⟩
  intro ω hω heq
  rcases mem_symmDiff.1 hω with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h2 (by simpa [heq] using h1)
  · exact h2 (by simpa [heq] using h1)

end ComplexSLE.Infrastructure.Blumenthal

end
