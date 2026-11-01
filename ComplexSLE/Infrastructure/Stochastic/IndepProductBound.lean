/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# A conditional lower bound for independent pairs

Source-independent probability. If `F` and `Y` are independent measurable maps, `g` is a measurable
set of values of `F`, `S` a measurable set of pairs, and `P (Y ∈ S_a) ≥ q` for every `a ∈ g`
(`S_a` the section of `S` at `a`), then `P (F ∈ g, (F, Y) ∈ S) ≥ q * P (F ∈ g)`
(`mul_measure_le_of_indepFun`). This is Fubini's theorem for the law
`P.map (F, Y) = P.map F ⊗ P.map Y`.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ComplexSLE.Infrastructure.Support

/-- **Conditional lower bound under independence (Fubini).** -/
theorem mul_measure_le_of_indepFun {Ω α β : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace α]
    [MeasurableSpace β] {P : Measure Ω} [IsProbabilityMeasure P] {F : Ω → α} {Y : Ω → β}
    (hF : Measurable F) (hY : Measurable Y) (hind : IndepFun F Y P) {S : Set (α × β)}
    (hS : MeasurableSet S) {g : Set α} (hg : MeasurableSet g) {q : ℝ≥0∞}
    (hq : ∀ a ∈ g, q ≤ P (Y ⁻¹' {b | (a, b) ∈ S})) :
    q * P (F ⁻¹' g) ≤ P {ω | F ω ∈ g ∧ (F ω, Y ω) ∈ S} := by
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hF.aemeasurable hY.aemeasurable).1 hind
  have hFY : Measurable fun ω => (F ω, Y ω) := hF.prodMk hY
  have hT : MeasurableSet ((g ×ˢ (univ : Set β)) ∩ S) := (hg.prod MeasurableSet.univ).inter hS
  have e1 : {ω | F ω ∈ g ∧ (F ω, Y ω) ∈ S} =
      (fun ω => (F ω, Y ω)) ⁻¹' ((g ×ˢ (univ : Set β)) ∩ S) := by
    ext ω; simp
  rw [e1, ← Measure.map_apply hFY hT, hprod, Measure.prod_apply hT]
  have e2 : ∀ a, (P.map Y) (Prod.mk a ⁻¹' ((g ×ˢ (univ : Set β)) ∩ S)) =
      g.indicator (fun a => P (Y ⁻¹' {b | (a, b) ∈ S})) a := by
    intro a
    by_cases ha : a ∈ g
    · have : Prod.mk a ⁻¹' ((g ×ˢ (univ : Set β)) ∩ S) = {b | (a, b) ∈ S} := by
        ext b; simp [ha]
      have hSa : MeasurableSet {b | (a, b) ∈ S} := measurable_prodMk_left hS
      rw [this, indicator_of_mem ha, Measure.map_apply hY hSa]
    · have : Prod.mk a ⁻¹' ((g ×ˢ (univ : Set β)) ∩ S) = ∅ := by
        ext b; simp [ha]
      rw [this, indicator_of_notMem ha]; simp
  simp_rw [e2]
  calc q * P (F ⁻¹' g) = ∫⁻ a, g.indicator (fun _ => q) a ∂(P.map F) := by
        rw [lintegral_indicator_const hg, Measure.map_apply hF hg]
    _ ≤ _ := by
        refine lintegral_mono fun a => ?_
        by_cases ha : a ∈ g
        · rw [indicator_of_mem ha, indicator_of_mem ha]; exact hq a ha
        · simp [indicator_of_notMem ha]

end ComplexSLE.Infrastructure.Support

end
