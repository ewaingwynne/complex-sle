/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsLoewnerSolution
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Backward control of the distance to the driver

A solution of the Loewner equation `γ' = 2/(γ - U)` which is at distance `≥ 2η` from the driver
at a time `b` stays at distance `≥ η` on a short interval `[a, b]` before `b`: as long as the
distance is `≥ η` the speed is `≤ 2/η`, so neither `γ` nor `U` can move far on `[a, b]`.
-/

public section

open scoped NNReal
open Set

namespace ComplexSLE.Internal

variable {U : ℝ≥0 → ℂ}

/-- **Backward bound.** Let `γ` solve the Loewner equation on `[a, b]` (derivative within
`[a, b]`), with `‖γ b - U b‖ ≥ 2η`, `‖U u - U b‖ ≤ η/4` on `[a, b]` and `8 (b - a) ≤ η²`.
Then `‖γ u - U u‖ ≥ η` for all `u ∈ [a, b]`. -/
theorem norm_sub_driver_ge_of_Icc (hU : Continuous U) {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : ∀ u ∈ Icc a b, HasDerivWithinAt γ (2 / (γ u - U u.toNNReal)) (Icc a b) u)
    {η : ℝ} (hη : 0 < η) (hb : 2 * η ≤ ‖γ b - U b.toNNReal‖)
    (hUmod : ∀ u ∈ Icc a b, ‖U u.toNNReal - U b.toNNReal‖ ≤ η / 4)
    (hlen : 8 * (b - a) ≤ η ^ 2) :
    ∀ u ∈ Icc a b, η ≤ ‖γ u - U u.toNNReal‖ := by
  set V : ℝ → ℂ := fun s => U s.toNNReal with hV
  have hVc : Continuous V := hU.comp continuous_real_toNNReal
  have hγcont : ContinuousOn γ (Icc a b) := HasDerivWithinAt.continuousOn hγ
  have hfcont : ContinuousOn (fun u => ‖γ u - V u‖) (Icc a b) :=
    (hγcont.sub hVc.continuousOn).norm
  by_contra hcon
  push Not at hcon
  obtain ⟨u₁, hu₁, hlt⟩ := hcon
  have hlt' : ‖γ u₁ - V u₁‖ < η := hlt
  -- `W`: times in `[u₁, b]` where the distance to the driver is `≤ η`
  set W := Icc u₁ b ∩ (fun u => ‖γ u - V u‖) ⁻¹' Iic η with hW
  have hWclosed : IsClosed W :=
    (hfcont.mono (Icc_subset_Icc hu₁.1 le_rfl)).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_Iic
  have hWne : W.Nonempty := ⟨u₁, ⟨le_rfl, hu₁.2⟩, hlt'.le⟩
  have hWbdd : BddAbove W := ⟨b, fun u hu => hu.1.2⟩
  set u₀ := sSup W with hu₀
  have hu₀W : u₀ ∈ W := hWclosed.csSup_mem hWne hWbdd
  have hu₀le : ‖γ u₀ - V u₀‖ ≤ η := hu₀W.2
  have hb' : 2 * η ≤ ‖γ b - V b‖ := hb
  have hu₀b : u₀ < b := by
    refine lt_of_le_of_ne hu₀W.1.2 fun h => ?_
    rw [h] at hu₀le
    linarith
  have hu₀ab : u₀ ∈ Icc a b := ⟨hu₁.1.trans hu₀W.1.1, hu₀W.1.2⟩
  -- beyond `u₀` the distance exceeds `η`
  have hgt : ∀ u ∈ Ioc u₀ b, η < ‖γ u - V u‖ := by
    intro u hu
    by_contra h
    push Not at h
    have hmem : u ∈ W := ⟨⟨hu₀W.1.1.trans hu.1.le, hu.2⟩, h⟩
    exact absurd (le_csSup hWbdd hmem) (not_le.2 hu.1)
  -- by closedness, the distance is `≥ η` on `[u₀, b]`
  have hge : ∀ u ∈ Icc u₀ b, η ≤ ‖γ u - V u‖ := by
    have hC : IsClosed (Icc a b ∩ (fun u => ‖γ u - V u‖) ⁻¹' Ici η) :=
      hfcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hsub : Ioc u₀ b ⊆ Icc a b ∩ (fun u => ‖γ u - V u‖) ⁻¹' Ici η :=
      fun u hu => ⟨⟨hu₀ab.1.trans hu.1.le, hu.2⟩, (hgt u hu).le⟩
    have := hC.closure_subset_iff.2 hsub
    rw [closure_Ioc hu₀b.ne] at this
    exact fun u hu => (this hu).2
  -- speed bound on `[u₀, b]`
  have hderiv : ∀ u ∈ Icc u₀ b, HasDerivWithinAt γ (2 / (γ u - V u)) (Icc u₀ b) u :=
    fun u hu => (hγ u ⟨hu₀ab.1.trans hu.1, hu.2⟩).mono (Icc_subset_Icc hu₀ab.1 le_rfl)
  have hbound : ∀ u ∈ Icc u₀ b, ‖2 / (γ u - V u)‖ ≤ 2 / η := by
    intro u hu
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
    exact div_le_div_of_nonneg_left (by norm_num) hη (hge u hu)
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_Icc _ _)
    (⟨le_rfl, hu₀b.le⟩ : u₀ ∈ Icc u₀ b) (⟨hu₀b.le, le_rfl⟩ : b ∈ Icc u₀ b)
  have h1 : ‖γ b - γ u₀‖ ≤ η / 4 := by
    have hnorm : ‖b - u₀‖ = b - u₀ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    rw [hnorm] at hmvt
    calc ‖γ b - γ u₀‖ ≤ 2 / η * (b - u₀) := hmvt
      _ ≤ 2 / η * (b - a) := by gcongr; exact hu₀ab.1
      _ ≤ η / 4 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hη (by norm_num)]
        nlinarith
  have h2 : ‖V u₀ - V b‖ ≤ η / 4 := hUmod u₀ hu₀ab
  have h3 : ‖γ b - V b‖ ≤ ‖γ u₀ - V u₀‖ + ‖γ b - γ u₀‖ + ‖V u₀ - V b‖ := by
    calc ‖γ b - V b‖ = ‖(γ u₀ - V u₀) + (γ b - γ u₀) + (V u₀ - V b)‖ := by ring_nf
      _ ≤ ‖(γ u₀ - V u₀) + (γ b - γ u₀)‖ + ‖V u₀ - V b‖ := norm_add_le _ _
      _ ≤ _ := by gcongr; exact norm_add_le _ _
  linarith

end ComplexSLE.Internal

end
