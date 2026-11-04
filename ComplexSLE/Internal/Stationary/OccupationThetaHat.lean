/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.Occupation
public import ComplexSLE.Internal.Stationary.ThetaHatSolution
public import ComplexSLE.Infrastructure.Stochastic.ContinuousModification

/-!
# `θ̂(z)` spends no time in a null set (M10-R5a)

The occupation estimate for the concrete process `θ̂ = θ̂(z)`
(`Occupation.ae_volume_occupation_null`) and its Fubini corollary, which replaces the Lebesgue
density of `law θ̂_1(z)` (Hörmander) in Lemma 3.3:

* `exists_continuous_version_thetaHat`: an everywhere-continuous version of `θ̂(z)` for the
  completed filtration (`IsDiffusionSolution.exists_continuous_version`), solving the martingale
  problem for `(µ, √(2D))`;
* `exists_pos_measure_thetaHat_preimage_eq_zero`: for `0 < a`, `0 < b`, `c² ≤ ab`, `z ≠ 0` and a
  Lebesgue-null `N`, there is `t ∈ [1, 2]`, in particular `t > 0`, with `P (θ̂_t(z) ∈ N) = 0`
  (Fubini on `Ω × [1, 2]`).
-/

public section

open scoped NNReal ENNReal Topology Real
open MeasureTheory ProbabilityTheory Filter Set Function

namespace ComplexSLE.Internal

open Polar

section ThetaHat

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ≥0 m} {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- An everywhere-continuous version `X` of `θ̂(z)`, solving the martingale problem
for `(µ, √(2D))` on the completed filtration. -/
theorem exists_continuous_version_thetaHat (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a)
    (hc : c ^ 2 ≤ a * b) {z : ℂ} (hz : z ≠ 0) :
    ∃ (𝒢 : Filtration ℝ≥0 m) (X : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t, X t ω = thetaHat hU z t ω) ∧ (∀ ω, Continuous fun t => X t ω) ∧
        IsDiffusionSolution 𝒢 (mu a b c) (fun u => √(2 * diffusionD a b c u)) X P := by
  have hsol := isDiffusionSolution_thetaHat hU ha hc hz
  let 𝒢 : Filtration ℝ≥0 m :=
    { seq := fun s => sigmaFiltration hU z s ⊔
        MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet[m] N ∧ P N = 0}
      mono' := fun _ _ hst => sup_le_sup_right ((sigmaFiltration hU z).mono hst) _
      le' := fun s => sup_le ((sigmaFiltration hU z).le s)
        (MeasurableSpace.generateFrom_le fun _ hN => hN.1) }
  obtain ⟨X, hae, hXc, hX⟩ := hsol.exists_continuous_version 𝒢 fun s => rfl
  exact ⟨𝒢, X, hae, hXc, hX⟩

/-- **`θ̂(z)` at a good positive time.** For a Lebesgue-null `N` there is `t > 0` with
`P (θ̂_t(z) ∈ N) = 0` (indeed some `t ∈ [1, 2]`, by Fubini on `Ω × [1, 2]`). -/
theorem exists_pos_measure_thetaHat_preimage_eq_zero (hU : IsSLEDriverAdapted a b c U P ℱ)
    (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b) {z : ℂ} (hz : z ≠ 0) {N : Set ℝ}
    (hN : volume N = 0) : ∃ t : ℝ≥0, 0 < t ∧ P ((thetaHat hU z t) ⁻¹' N) = 0 := by
  obtain ⟨𝒢, X, hae, hXc, hX⟩ := exists_continuous_version_thetaHat hU ha hc hz
  have hβc : Continuous fun u => √(2 * diffusionD a b c u) :=
    (continuous_const.mul (continuous_diffusionD a b c)).sqrt
  have hXm : ∀ s, Measurable (X s) := IsDiffusionSolution.measurable hX
  set N₁ := toMeasurable volume N with hN₁
  have hN₁m : MeasurableSet N₁ := measurableSet_toMeasurable _ _
  have hN₁0 : volume N₁ = 0 := by rw [hN₁, measure_toMeasurable]; exact hN
  have h2 := ae_volume_occupation_null ha hb hc hX hXc hβc
    (fun u => sq_sqrt_two_mul_diffusionD ha hb hc u) hN₁0 2
  -- the set `A ⊆ Ω × ℝ`
  have hmeas : Measurable (pathMap X) := measurable_pathMap hXc hXm
  set A : Set (Ω × ℝ) := pathMap X ⁻¹' N₁ ∩ (univ ×ˢ Icc 1 2) with hA
  have hAm : MeasurableSet A :=
    (hmeas hN₁m).inter (MeasurableSet.univ.prod measurableSet_Icc)
  have hAnull : (P.prod volume) A = 0 := by
    rw [Measure.prod_apply hAm]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [h2] with ω hω
    refine measure_mono_null (fun t ht => ?_) hω
    exact ⟨⟨zero_le_one.trans ht.2.2.1, ht.2.2.2.trans (by norm_num)⟩, ht.1⟩
  -- Fubini the other way
  rw [Measure.prod_apply_symm hAm] at hAnull
  have hmf : Measurable fun t : ℝ => P ((fun ω => (ω, t)) ⁻¹' A) :=
    measurable_measure_prodMk_right hAm
  have hf0 : (fun t : ℝ => P ((fun ω => (ω, t)) ⁻¹' A)) =ᵐ[volume] 0 :=
    (lintegral_eq_zero_iff hmf).1 hAnull
  -- some `t ∈ [1, 2]` is good
  have hex : ∃ t ∈ Icc (1 : ℝ) 2, P ((fun ω => (ω, t)) ⁻¹' A) = 0 := by
    by_contra hcon
    push Not at hcon
    have hsub : Icc (1 : ℝ) 2 ⊆ {t : ℝ | ¬ (P ((fun ω => (ω, t)) ⁻¹' A) = (0 : ℝ → ℝ≥0∞) t)} :=
      fun t ht => hcon t ht
    have := measure_mono_null hsub (ae_iff.1 hf0)
    rw [Real.volume_Icc] at this
    norm_num at this
  obtain ⟨t₀, ht₀, hP⟩ := hex
  refine ⟨t₀.toNNReal, ?_, ?_⟩
  · rw [Real.toNNReal_pos]; linarith [ht₀.1]
  · have hsubset : thetaHat hU z t₀.toNNReal ⁻¹' N ⊆
        (fun ω => (ω, t₀)) ⁻¹' A ∪ {ω | ¬ ∀ s, X s ω = thetaHat hU z s ω} := by
      intro ω hω
      by_cases h : ∀ s, X s ω = thetaHat hU z s ω
      · left
        refine ⟨?_, trivial, ht₀⟩
        change X t₀.toNNReal ω ∈ N₁
        rw [h]
        exact subset_toMeasurable _ _ hω
      · right; exact h
    exact measure_mono_null hsubset (measure_union_null hP (ae_iff.1 hae))

end ThetaHat

end ComplexSLE.Internal

end
