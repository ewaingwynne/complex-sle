/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Disconnect.ZeroDriver
public import ComplexSLE.External.LoewnerMapTendstoUniformly

/-!
# Lemma 4.3 (first bullet) for small drivers: the `ε`-`ρ` form

arXiv:2203.07313v4, Lemma 4.3 (`lem-haus`, paper.tex:L1998-2019). The classical input E12
(`ComplexSLE.External.loewnerMap_tendstoUniformly`) is stated for sequences of drivers converging
locally uniformly. Here it is turned into the quantitative statement
`exists_small_driver_approx`: if a continuous driver `V` is uniformly small on `[0, T]`, then
`f^V_T` is uniformly close to the explicit map `zeroMap T` away from the slit `slitI T`.

This file uses the classical input `loewnerMap_tendstoUniformly` (proved in-project,
`Internal/ExternalProofs/`).
-/

public section

open scoped NNReal ENNReal Topology
open Set Filter

namespace ComplexSLE.Internal

/-- **Lemma 4.3, first bullet, in `ε`-`ρ` form** (paper.tex:L1999-2003). For every `T`, `ε > 0` and
`η > 0` there is `ρ > 0` such that for every continuous driver `V` with `|V t| < ρ` on `[0, T]`,
every point `z` at distance `≥ ε` from the zero-driver hull `L⁰_T = slitI T` lies outside `L^V_T`
and `|f^V_T (z) - f⁰_T (z)| < η`, where `f⁰_T = zeroMap T`.

The proof is by contradiction. A violating sequence `V n` with `|V n| < 1/(n+1)` on `[0, T]` is
truncated to `V n (min · T)`, which does not change `L_T` or `f_T`
(`leftHull_congr`, `centeredLoewnerMap_congr`) and converges uniformly to `0`; the classical input
`loewnerMap_tendstoUniformly` (E12) then contradicts the violation. -/
theorem exists_small_driver_approx (T : ℝ≥0) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ ρ > 0, ∀ (V : ℝ≥0 → ℂ) (hV : Continuous V), (∀ t ≤ T, ‖V t‖ < ρ) →
      ∀ z : ℂ, ε ≤ Metric.infDist z (slitI T) →
        ∃ h : z ∈ (leftHull V T)ᶜ,
          ‖centeredLoewnerMap V hV T ⟨z, h⟩ - zeroMap T z‖ < η := by
  by_contra hneg
  push Not at hneg
  choose V hV hsmall z hz hbad using fun n : ℕ => hneg (1 / ((n : ℝ) + 1)) (by positivity)
  set W : ℕ → ℝ≥0 → ℂ := fun n t => V n (min t T) with hW
  have hWc : ∀ n, Continuous (W n) := fun n =>
    (hV n).comp (continuous_id.min continuous_const)
  have hWsmall : ∀ n t, ‖W n t‖ < 1 / ((n : ℝ) + 1) := fun n t => hsmall n _ (min_le_right _ _)
  have hconv : TendstoLocallyUniformly W (fun _ => (0 : ℂ)) atTop := by
    refine TendstoUniformly.tendstoLocallyUniformly ?_
    rw [Metric.tendstoUniformly_iff]
    intro e he
    filter_upwards [(tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds he)] with n hn x
    rw [dist_eq_norm, zero_sub, norm_neg]
    exact (hWsmall n x).trans hn
  have hE := External.loewnerMap_tendstoUniformly (fun _ : ℝ≥0 => (0 : ℂ)) continuous_const W hWc
    hconv T ε hε (η / 2) (half_pos hη)
  obtain ⟨n, hn1, hn2⟩ := (hE.and ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (gt_mem_nhds (half_pos hη)))).exists
  have hzn := hz n
  rw [← leftHull_zero T] at hzn
  obtain ⟨h₁, h₂, hlt⟩ := hn1 T le_rfl (z n) hzn
  have hcong : ∀ s ≤ T, V n s = W n s := fun s hs => by simp [hW, min_eq_left hs]
  have hL : leftHull (V n) T = leftHull (W n) T := leftHull_congr (hV n) (hWc n) hcong
  have h₃ : z n ∈ (leftHull (V n) T)ᶜ := by rw [hL]; exact h₁
  have hb := hbad n h₃
  have hz0 : z n ∉ slitI T := by
    rw [← leftHull_zero T]; exact h₂
  have e1 : centeredLoewnerMap (V n) (hV n) T ⟨z n, h₃⟩ =
      centeredLoewnerMap (W n) (hWc n) T ⟨z n, h₁⟩ :=
    centeredLoewnerMap_congr (hV n) (hWc n) hcong h₃ h₁
  have e2 : zeroMap T (z n) = loewnerMap (fun _ : ℝ≥0 => (0 : ℂ)) continuous_const T ⟨z n, h₂⟩ := by
    rw [← centeredLoewnerMap_zero hz0 h₂]
    simp [centeredLoewnerMap]
  rw [e1, e2] at hb
  have e3 : centeredLoewnerMap (W n) (hWc n) T ⟨z n, h₁⟩ - loewnerMap (fun _ : ℝ≥0 => (0 : ℂ))
      continuous_const T ⟨z n, h₂⟩ =
      (loewnerMap (W n) (hWc n) T ⟨z n, h₁⟩ - loewnerMap (fun _ : ℝ≥0 => (0 : ℂ))
        continuous_const T ⟨z n, h₂⟩) - W n T := by
    simp [centeredLoewnerMap]
    ring
  rw [e3] at hb
  have := norm_sub_le (loewnerMap (W n) (hWc n) T ⟨z n, h₁⟩ - loewnerMap (fun _ : ℝ≥0 => (0 : ℂ))
        continuous_const T ⟨z n, h₂⟩) (W n T)
  have := hWsmall n T
  linarith

end ComplexSLE.Internal

end
