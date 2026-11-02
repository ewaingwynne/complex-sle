/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.OccupationCritical

/-!
# Occupation of null sets by a diffusion (M10-R5a)

**Main result** (`ae_volume_occupation_null`). Let `0 < a`, `0 < b`, `c² ≤ ab`, and let `X` be an
everywhere-continuous solution of the martingale problem for `(µ, β)` (`IsDiffusionSolution`), `β`
continuous with `β² = 2D`. Then for every Lebesgue-null `N ⊆ ℝ` and every `T`, almost surely

  `Leb {t ∈ [0, T] : X_t ∈ N} = 0`.

This replaces the Lebesgue density of `law θ̂_1(z)` (Hörmander) by the weaker fact that suffices
for Lemma 3.3. Route:

1. **Dynkin bound** (`OccupationBound`): `∫ ψ β² dρ ≤ K ∫₀^π ψ` for the occupation measure
   `ρ = occupation X P T` and `π`-periodic continuous `ψ ≥ 0`;
2. **Null sets** (`OccupationNullSets`): hence `ρ (N ∩ {β² ≠ 0}) = 0`;
3. **Zero set** of `β²`: empty if `c² < ab`; if `c² = ab` it is the lattice `x₀ + πℤ`, of
   `ρ`-measure zero (`OccupationCritical`, using `µ(x₀) ≠ 0`);
4. so `ρ N = 0`, i.e. `(P ⊗ Leb|_{(0,T]}) {(ω, s) : X_s(ω) ∈ N} = 0`, and Fubini.

The only classical input is `External.ito_formula` (through `ItoReal.lean`).
-/

public section

open scoped NNReal ENNReal Topology Real
open MeasureTheory ProbabilityTheory Filter Set Function

namespace ComplexSLE.Internal

section Main

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ≥0 mΩ} {a b c : ℝ} {β : ℝ → ℝ} {X : ℝ≥0 → Ω → ℝ}

/-- The occupation measure of a Lebesgue-null set vanishes. -/
theorem occupation_eq_zero_of_volume_eq_zero (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (hX : IsDiffusionSolution ℱ (mu a b c) β X P) (hXc : ∀ ω, Continuous fun t => X t ω)
    (hβc : Continuous β) (hβsq : ∀ v, β v ^ 2 = 2 * diffusionD a b c v) (T : ℝ≥0) {N : Set ℝ}
    (hN : volume N = 0) : occupation X P T N = 0 := by
  have h1 := occupation_inter_ne_zero_eq_zero hX hXc hβc hβsq T hN
  have h2 : occupation X P T {x | β x ^ 2 = 0} = 0 := by
    rcases hc.lt_or_eq with hlt | heq
    · have : {x | β x ^ 2 = 0} = ∅ := by
        ext x
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rw [hβsq x]
        have := diffusionD_pos ha hb hlt x
        positivity
      rw [this, measure_empty]
    · exact occupation_zeroSet_eq_zero ha hb heq hX hXc hβc hβsq T
  refine measure_mono_null (t := (N ∩ {x | β x ^ 2 ≠ 0}) ∪ {x | β x ^ 2 = 0}) ?_ ?_
  · intro x hx
    by_cases h : β x ^ 2 = 0
    · exact Or.inr h
    · exact Or.inl ⟨hx, h⟩
  · exact measure_union_null h1 h2

/-- **Occupation of null sets.** An everywhere-continuous solution `X` of the martingale problem
for `(µ, β)` (`β² = 2D`, `0 < a`, `0 < b`, `c² ≤ ab`) a.s. spends Lebesgue-zero time in a
Lebesgue-null set `N`: `Leb {t ∈ [0, T] : X_t ∈ N} = 0`. -/
theorem ae_volume_occupation_null (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (hX : IsDiffusionSolution ℱ (mu a b c) β X P) (hXc : ∀ ω, Continuous fun t => X t ω)
    (hβc : Continuous β) (hβsq : ∀ v, β v ^ 2 = 2 * diffusionD a b c v) {N : Set ℝ}
    (hN : volume N = 0) (T : ℝ) :
    ∀ᵐ ω ∂P, volume {t : ℝ | t ∈ Set.Icc 0 T ∧ X t.toNNReal ω ∈ N} = 0 := by
  have hXm : ∀ t, Measurable (X t) := IsDiffusionSolution.measurable hX
  set N₁ := toMeasurable volume N with hN₁
  have hN₁m : MeasurableSet N₁ := measurableSet_toMeasurable _ _
  have hN₁0 : volume N₁ = 0 := by rw [hN₁, measure_toMeasurable]; exact hN
  set T' : ℝ≥0 := T.toNNReal with hT'
  have hρ := occupation_eq_zero_of_volume_eq_zero ha hb hc hX hXc hβc hβsq T' hN₁0
  -- the set in `Ω × ℝ`
  have hmeas := measurable_pathMap hXc hXm
  have hS : MeasurableSet (pathMap X ⁻¹' N₁) := hmeas hN₁m
  unfold occupation at hρ
  rw [Measure.map_apply hmeas hN₁m] at hρ
  have hfib := (Measure.measure_prod_null hS).1 hρ
  filter_upwards [hfib] with ω hω
  have hω' : (volume.restrict (Ioc (0 : ℝ) T')) (Prod.mk ω ⁻¹' (pathMap X ⁻¹' N₁)) = 0 := hω
  have hcm : Measurable fun s : ℝ => X s.toNNReal ω :=
    (hXc ω).measurable.comp measurable_real_toNNReal
  have hmeasS : MeasurableSet {s : ℝ | X s.toNNReal ω ∈ N₁} := hcm hN₁m
  have e : Prod.mk ω ⁻¹' (pathMap X ⁻¹' N₁) = {s : ℝ | X s.toNNReal ω ∈ N₁} := rfl
  rw [e, Measure.restrict_apply hmeasS] at hω'
  refine measure_mono_null (t := {s : ℝ | X s.toNNReal ω ∈ N₁} ∩ Ioc 0 T' ∪ {0}) ?_
    (measure_union_null hω' (Real.volume_singleton))
  intro t ⟨ht, htN⟩
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · exact Or.inr h0.symm
  · left
    refine ⟨subset_toMeasurable _ _ htN, hpos, ?_⟩
    rw [hT', Real.coe_toNNReal _ (ht.1.trans ht.2)]
    exact ht.2

end Main

end ComplexSLE.Internal

end
