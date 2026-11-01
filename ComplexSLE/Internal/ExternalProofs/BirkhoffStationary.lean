/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Ergodic.PointwiseErgodicTheorem
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Birkhoff's ergodic theorem for stationary sequences (proof of the external input)

A complete proof of the exact statement of `ComplexSLE.External.birkhoff_stationary`; this module
deliberately does not import `ComplexSLE.External.*`, the statement is a verbatim copy.

The sequence `ξ` is transported to the canonical space `ℕ → ℝ`: the law `ν` of
`ω ↦ (n ↦ ξ n ω)` is invariant under the shift `x ↦ (n ↦ x (n + 1))` by stationarity (`hstat 1`).
Birkhoff's pointwise ergodic theorem
(`ComplexSLE.Infrastructure.Ergodic.birkhoff_pointwise`) for the shift and the coordinate `x ↦ x 0`
gives an integrable limit `L̄` on `ℕ → ℝ`; then `L = L̄ ∘ (ω ↦ (n ↦ ξ n ω))`, and the almost sure
statement and the integrals pull back along the measurable map.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Internal.ExternalProofs

theorem birkhoff_stationary {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ξ : ℕ → Ω → ℝ) (hmeas : ∀ n, Measurable (ξ n))
    (hstat : ∀ k : ℕ, P.map (fun ω (n : ℕ) => ξ (n + k) ω) = P.map (fun ω (n : ℕ) => ξ n ω))
    (hint : Integrable (ξ 0) P) :
    ∃ L : Ω → ℝ, Integrable L P ∧ ∫ ω, L ω ∂P = ∫ ω, ξ 0 ω ∂P ∧
      ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, ξ k ω) / n) atTop (𝓝 (L ω)) := by
  set X : Ω → (ℕ → ℝ) := fun ω n => ξ n ω with hX
  have hXm : Measurable X := Measurable.of_eval hmeas
  set ν : Measure (ℕ → ℝ) := P.map X with hν
  have : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  set σ : (ℕ → ℝ) → (ℕ → ℝ) := fun x n => x (n + 1) with hσdef
  have hσm : Measurable σ := Measurable.of_eval fun n => measurable_pi_apply (n + 1)
  have hσ : MeasurePreserving σ ν ν := by
    refine ⟨hσm, ?_⟩
    rw [hν, Measure.map_map hσm hXm]
    exact hstat 1
  set f0 : (ℕ → ℝ) → ℝ := fun x => x 0 with hf0
  have hf0m : Measurable f0 := measurable_pi_apply 0
  have hf0i : Integrable f0 ν :=
    (integrable_map_measure hf0m.aestronglyMeasurable hXm.aemeasurable).2 hint
  have hshift : ∀ (k : ℕ) (x : ℕ → ℝ), f0 (σ^[k] x) = x k := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih => intro x; rw [Function.iterate_succ_apply, ih]
  obtain ⟨L', hL'i, hL'int, hL'ae⟩ := ComplexSLE.Infrastructure.Ergodic.birkhoff_pointwise hσ hf0m
    hf0i
  refine ⟨fun ω => L' (X ω), ?_, ?_, ?_⟩
  · exact (integrable_map_measure hL'i.aestronglyMeasurable hXm.aemeasurable).1 hL'i
  · have h1 := integral_map (μ := P) hXm.aemeasurable hL'i.aestronglyMeasurable
    have h2 := integral_map (μ := P) hXm.aemeasurable hf0m.aestronglyMeasurable
    rw [← h1, hL'int, h2]
  · refine ae_of_ae_map hXm.aemeasurable (p := fun x => Tendsto
      (fun n : ℕ => (∑ k ∈ Finset.range n, x k) / n) atTop (𝓝 (L' x))) ?_
    filter_upwards [hL'ae] with x hx
    simpa only [hshift] using hx

end ComplexSLE.Internal.ExternalProofs

end
