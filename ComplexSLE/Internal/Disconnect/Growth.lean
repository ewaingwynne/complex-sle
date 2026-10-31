/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Duality.Locality
public import ComplexSLE.Internal.Hull.ConnectedNoExt
import all ComplexSLE.Internal.Loewner.Duality

/-!
# Growth of the centered Loewner map at infinity

For a continuous driver `U` and a time `t`, `‖f_t(z)‖ → ∞` as `‖z‖ → ∞` (`z ∉ L_t`). The proof
follows the Loewner solution `γ` from `z` on `[0, t]`: as long as `‖γ - U‖ ≥ 1` the speed of `γ`
is at most `2`, so `γ` stays within `2t` of `z`, and `f_t(z) = γ(t) - U_t`.
-/

public section

open scoped NNReal ENNReal
open Set Metric

namespace ComplexSLE.Internal

variable {U : ℝ≥0 → ℂ}

/-- **Growth of the centered Loewner map**: for every `M` there is `M'` such that
`M ≤ ‖f_t(z)‖` whenever `z ∉ L_t` and `M' ≤ ‖z‖`. -/
theorem centeredLoewnerMap_norm_ge (hU : Continuous U) (t : ℝ≥0) (M : ℝ) :
    ∃ M' : ℝ, ∀ (z : ℂ) (h : z ∈ (leftHull U t)ᶜ), M' ≤ ‖z‖ →
      M ≤ ‖centeredLoewnerMap U hU t ⟨z, h⟩‖ := by
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := (t : ℝ))).exists_bound_of_continuousOn
    (f := fun u : ℝ => U u.toNNReal) (hU.comp continuous_real_toNNReal).continuousOn
  refine ⟨M₀ + 2 + 2 * t + |M|, fun z hz hzM => ?_⟩
  obtain ⟨γ, h0, hcs⟩ := (notMem_leftHull_iff_exists_closedSol hU t z).1 hz
  rw [centeredLoewnerMap_eq_of_closedSol hU h0 hcs hz]
  have ht0 : (0 : ℝ) ≤ t := t.2
  have hUt : ‖U t‖ ≤ M₀ := by
    simpa using hM₀ t ⟨ht0, le_rfl⟩
  -- the solution moves by at most `2 t`
  have hmove : ‖γ t - z‖ ≤ 2 * t := by
    rcases eq_or_ne t 0 with rfl | ht
    · simp [h0]
    have htpos : (0 : ℝ) < t := by exact_mod_cast pos_iff_ne_zero.2 ht
    have hγ' : ∀ u ∈ Ico 0 (t : ℝ), γ u ≠ U u.toNNReal ∧
        HasDerivWithinAt γ (2 / (γ u - U u.toNNReal)) (Ici 0) u := by
      intro u hu
      obtain ⟨h1, h2⟩ := hcs u ⟨hu.1, hu.2.le⟩
      refine ⟨h1, h2.mono_of_mem_nhdsWithin ?_⟩
      exact mem_nhdsWithin.2 ⟨Iio t, isOpen_Iio, hu.2, fun x hx => ⟨hx.2, hx.1.le⟩⟩
    have hMτ : ∀ u ∈ Ico 0 (t : ℝ), ‖U u.toNNReal‖ ≤ M₀ := fun u hu => hM₀ u ⟨hu.1, hu.2.le⟩
    have hfar := one_le_norm_sub_driver_of_far hU h0 hγ' hMτ
      (by linarith [abs_nonneg M])
    have hVc : Continuous fun s : ℝ => U s.toNNReal := hU.comp continuous_real_toNNReal
    have hγc : ContinuousOn γ (Icc 0 (t : ℝ)) := fun s hs => (hcs s hs).2.continuousWithinAt
    have hC : IsClosed (Icc 0 (t : ℝ) ∩ (fun u => ‖γ u - U u.toNNReal‖) ⁻¹' Ici 1) :=
      ((hγc.sub hVc.continuousOn).norm).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hsub : Ico 0 (t : ℝ) ⊆ Icc 0 (t : ℝ) ∩ (fun u => ‖γ u - U u.toNNReal‖) ⁻¹' Ici 1 :=
      fun u hu => ⟨⟨hu.1, hu.2.le⟩, hfar u hu⟩
    have hclos := hC.closure_subset_iff.2 hsub
    rw [closure_Ico htpos.ne] at hclos
    have hbound : ∀ u ∈ Icc 0 (t : ℝ), ‖2 / (γ u - U u.toNNReal)‖ ≤ 2 := by
      intro u hu
      have h1 : 1 ≤ ‖γ u - U u.toNNReal‖ := (hclos hu).2
      rw [norm_div, show ‖(2 : ℂ)‖ = 2 by simp, div_le_iff₀ (by linarith)]
      nlinarith
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := γ) (f' := fun u => 2 / (γ u - U u.toNNReal)) (s := Icc 0 (t : ℝ))
      (fun u hu => (hcs u hu).2) hbound (convex_Icc 0 (t : ℝ))
      (⟨le_rfl, ht0⟩ : (0 : ℝ) ∈ Icc 0 (t : ℝ)) (⟨ht0, le_rfl⟩ : (t : ℝ) ∈ Icc 0 (t : ℝ))
    rw [h0, Real.norm_eq_abs, sub_zero, abs_of_nonneg ht0] at hmvt
    exact hmvt
  have h3 : ‖z‖ ≤ ‖γ t - z‖ + ‖γ t - U t‖ + ‖U t‖ := by
    calc ‖z‖ = ‖-(γ t - z) + (γ t - U t) + U t‖ := by congr 1; ring
      _ ≤ ‖-(γ t - z) + (γ t - U t)‖ + ‖U t‖ := norm_add_le _ _
      _ ≤ ‖-(γ t - z)‖ + ‖γ t - U t‖ + ‖U t‖ := by gcongr; exact norm_add_le _ _
      _ = ‖γ t - z‖ + ‖γ t - U t‖ + ‖U t‖ := by rw [norm_neg]
  linarith [le_abs_self M]

/-- The centered Loewner map is continuous on `ℂ ∖ L_t` (it is the restriction of a holomorphic
function). -/
theorem continuous_centeredLoewnerMap (hU : Continuous U) (t : ℝ≥0) :
    Continuous (centeredLoewnerMap U hU t) := by
  obtain ⟨G, hG, hd⟩ := exists_differentiableOn_extension_loewnerMap hU t
  have h1 : Continuous fun z : ↥(leftHull U t)ᶜ => G z := by
    have := hd.continuousOn
    rw [continuousOn_iff_continuous_domRestrict] at this
    exact this
  have h2 : centeredLoewnerMap U hU t = fun z : ↥(leftHull U t)ᶜ => G z - U t := by
    funext z
    simp only [centeredLoewnerMap, hG z]
  rw [h2]
  exact h1.sub continuous_const

end ComplexSLE.Internal

end
