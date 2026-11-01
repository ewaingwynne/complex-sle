/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Disconnect.Growth

/-!
# Far-field estimates for the Loewner flow

For a continuous driver `U` bounded by `M` on `[0, t]` and a Loewner solution `γ` on `[0, t]`
started at `z` with `‖z‖ ≥ M + 2 + 2 t`, the solution stays at distance `≥ 1` from the driver,
moves by at most `2 s` up to time `s ≤ t`, and `z (γ t - z) = 2 t + O(1/‖z‖)`.
-/

public section

open scoped NNReal ENNReal
open Set Metric

namespace ComplexSLE.Internal.ExternalProofs

variable {U : ℝ≥0 → ℂ}

/-- **Far solutions move slowly.** If `‖U‖ ≤ M` on `[0, t]`, `γ` solves the Loewner equation on
`[0, t]` from `z`, and `M + 2 + 2 t ≤ ‖z‖`, then for all `s ∈ [0, t]` we have `‖γ s - z‖ ≤ 2 s` and
`‖z‖ - M - 2 s ≤ ‖γ s - U s‖`. -/
theorem far_closedSol (hU : Continuous U) {t : ℝ≥0} {M : ℝ} {z : ℂ} {γ : ℝ → ℂ}
    (h0 : γ 0 = z)
    (hcs : ∀ s ∈ Icc (0 : ℝ) t, γ s ≠ U s.toNNReal ∧
      HasDerivWithinAt γ (2 / (γ s - U s.toNNReal)) (Icc 0 (t : ℝ)) s)
    (hM : ∀ u ∈ Icc (0 : ℝ) t, ‖U u.toNNReal‖ ≤ M) (hz : M + 2 + 2 * t ≤ ‖z‖) :
    ∀ s ∈ Icc (0 : ℝ) t, ‖γ s - z‖ ≤ 2 * s ∧ ‖z‖ - M - 2 * s ≤ ‖γ s - U s.toNNReal‖ := by
  have ht0 : (0 : ℝ) ≤ t := t.2
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, ht0⟩)
  -- the speed bound and the movement bound at each time
  have key : (∀ u ∈ Icc (0 : ℝ) t, 1 ≤ ‖γ u - U u.toNNReal‖) →
      ∀ s ∈ Icc (0 : ℝ) t, ‖γ s - z‖ ≤ 2 * s ∧ ‖z‖ - M - 2 * s ≤ ‖γ s - U s.toNNReal‖ := by
    intro hfar s hs
    have hbound : ∀ u ∈ Icc 0 (t : ℝ), ‖2 / (γ u - U u.toNNReal)‖ ≤ 2 := by
      intro u hu
      have h1 : 1 ≤ ‖γ u - U u.toNNReal‖ := hfar u hu
      rw [norm_div, show ‖(2 : ℂ)‖ = 2 by simp, div_le_iff₀ (by linarith)]
      nlinarith
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := γ) (f' := fun u => 2 / (γ u - U u.toNNReal)) (s := Icc 0 (t : ℝ))
      (fun u hu => (hcs u hu).2) hbound (convex_Icc 0 (t : ℝ))
      (⟨le_rfl, ht0⟩ : (0 : ℝ) ∈ Icc 0 (t : ℝ)) hs
    rw [h0, Real.norm_eq_abs, sub_zero, abs_of_nonneg hs.1] at hmvt
    refine ⟨hmvt, ?_⟩
    have hMs : ‖U s.toNNReal‖ ≤ M := hM s hs
    have h3 : ‖z‖ ≤ ‖γ s - U s.toNNReal‖ + ‖γ s - z‖ + ‖U s.toNNReal‖ := by
      calc ‖z‖ = ‖(γ s - U s.toNNReal) - (γ s - z) + U s.toNNReal‖ := by congr 1; ring
        _ ≤ ‖(γ s - U s.toNNReal) - (γ s - z)‖ + ‖U s.toNNReal‖ := norm_add_le _ _
        _ ≤ ‖γ s - U s.toNNReal‖ + ‖γ s - z‖ + ‖U s.toNNReal‖ := by
          gcongr; exact norm_sub_le _ _
    linarith
  apply key
  rcases eq_or_ne t 0 with rfl | ht
  · intro u hu
    have hu0 : u = 0 := by simpa using hu
    subst hu0
    have h1 : ‖z‖ ≤ ‖γ 0 - U (0 : ℝ).toNNReal‖ + ‖U (0 : ℝ).toNNReal‖ := by
      rw [h0]
      calc ‖z‖ = ‖(z - U (0 : ℝ).toNNReal) + U (0 : ℝ).toNNReal‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    have := hM 0 ⟨le_rfl, le_rfl⟩
    simp only [NNReal.coe_zero] at hz
    linarith
  · have htpos : (0 : ℝ) < t := by exact_mod_cast pos_iff_ne_zero.2 ht
    have hγ' : ∀ u ∈ Ico 0 (t : ℝ), γ u ≠ U u.toNNReal ∧
        HasDerivWithinAt γ (2 / (γ u - U u.toNNReal)) (Ici 0) u := by
      intro u hu
      obtain ⟨h1, h2⟩ := hcs u ⟨hu.1, hu.2.le⟩
      refine ⟨h1, h2.mono_of_mem_nhdsWithin ?_⟩
      exact mem_nhdsWithin.2 ⟨Iio t, isOpen_Iio, hu.2, fun x hx => ⟨hx.2, hx.1.le⟩⟩
    have hMτ : ∀ u ∈ Ico 0 (t : ℝ), ‖U u.toNNReal‖ ≤ M := fun u hu => hM u ⟨hu.1, hu.2.le⟩
    have hfar := one_le_norm_sub_driver_of_far hU h0 hγ' hMτ hz
    have hVc : Continuous fun s : ℝ => U s.toNNReal := hU.comp continuous_real_toNNReal
    have hγc : ContinuousOn γ (Icc 0 (t : ℝ)) := fun s hs => (hcs s hs).2.continuousWithinAt
    have hC : IsClosed (Icc 0 (t : ℝ) ∩ (fun u => ‖γ u - U u.toNNReal‖) ⁻¹' Ici 1) :=
      ((hγc.sub hVc.continuousOn).norm).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hsub : Ico 0 (t : ℝ) ⊆ Icc 0 (t : ℝ) ∩ (fun u => ‖γ u - U u.toNNReal‖) ⁻¹' Ici 1 :=
      fun u hu => ⟨⟨hu.1, hu.2.le⟩, hfar u hu⟩
    have hclos := hC.closure_subset_iff.2 hsub
    rw [closure_Ico htpos.ne] at hclos
    exact fun u hu => (hclos hu).2

/-- **Asymptotics of a far solution at time `t`.** Under the hypotheses of `far_closedSol`,
`‖z (γ t - z) - 2 t‖ ≤ 2 (2 t + M) / (‖z‖ - M - 2 t) * t`. -/
theorem norm_mul_sub_sub_two_mul_le (hU : Continuous U) {t : ℝ≥0} {M : ℝ} {z : ℂ} {γ : ℝ → ℂ}
    (h0 : γ 0 = z)
    (hcs : ∀ s ∈ Icc (0 : ℝ) t, γ s ≠ U s.toNNReal ∧
      HasDerivWithinAt γ (2 / (γ s - U s.toNNReal)) (Icc 0 (t : ℝ)) s)
    (hM : ∀ u ∈ Icc (0 : ℝ) t, ‖U u.toNNReal‖ ≤ M) (hz : M + 2 + 2 * t ≤ ‖z‖) :
    ‖z * (γ t - z) - 2 * (t : ℂ)‖ ≤ 2 * (2 * t + M) / (‖z‖ - M - 2 * t) * t := by
  have ht0 : (0 : ℝ) ≤ t := t.2
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, ht0⟩)
  have hfar := far_closedSol hU h0 hcs hM hz
  set D : ℝ := ‖z‖ - M - 2 * t with hD
  have hD2 : 2 ≤ D := by rw [hD]; linarith
  have hDpos : 0 < D := by linarith
  set B : ℝ := 2 * (2 * t + M) / D with hB
  set h : ℝ → ℂ := fun s => z * (γ s - z) - 2 * (s : ℂ) with hh
  have hderiv : ∀ s ∈ Icc (0 : ℝ) t,
      HasDerivWithinAt h (z * (2 / (γ s - U s.toNNReal)) - 2) (Icc 0 (t : ℝ)) s := by
    intro s hs
    have h1 := ((hcs s hs).2.sub_const z).const_mul z
    have h2 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 s := (hasDerivAt_id s).ofReal_comp
    have h3 : HasDerivWithinAt (fun x : ℝ => 2 * (x : ℂ)) 2 (Icc 0 (t : ℝ)) s := by
      simpa using (h2.const_mul (2 : ℂ)).hasDerivWithinAt (s := Icc 0 (t : ℝ))
    exact h1.sub h3
  have hbound : ∀ s ∈ Icc (0 : ℝ) t, ‖z * (2 / (γ s - U s.toNNReal)) - 2‖ ≤ B := by
    intro s hs
    obtain ⟨hmove, hlow⟩ := hfar s hs
    set w : ℂ := γ s - U s.toNNReal with hw
    have hwD : D ≤ ‖w‖ := by
      have : ‖z‖ - M - 2 * s ≤ ‖w‖ := hlow
      rw [hD]; linarith [hs.2]
    have hw0 : w ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hDpos hwD)
    have hzw : ‖z - w‖ ≤ 2 * t + M := by
      have e : z - w = -(γ s - z) + U s.toNNReal := by rw [hw]; ring
      rw [e]
      calc ‖-(γ s - z) + U s.toNNReal‖ ≤ ‖-(γ s - z)‖ + ‖U s.toNNReal‖ := norm_add_le _ _
        _ ≤ 2 * t + M := by
          rw [norm_neg]; linarith [hM s hs, hs.2]
    have e : z * (2 / w) - 2 = 2 * (z - w) / w := by field_simp
    rw [e, norm_div, norm_mul, show ‖(2 : ℂ)‖ = 2 by simp, hB]
    have hwpos : 0 < ‖w‖ := lt_of_lt_of_le hDpos hwD
    calc 2 * ‖z - w‖ / ‖w‖ ≤ 2 * (2 * t + M) / ‖w‖ := by gcongr
      _ ≤ 2 * (2 * t + M) / D := by gcongr
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := h) (f' := fun s => z * (2 / (γ s - U s.toNNReal)) - 2) (s := Icc 0 (t : ℝ))
    hderiv hbound (convex_Icc 0 (t : ℝ))
    (⟨le_rfl, ht0⟩ : (0 : ℝ) ∈ Icc 0 (t : ℝ)) (⟨ht0, le_rfl⟩ : (t : ℝ) ∈ Icc 0 (t : ℝ))
  have hh0 : h 0 = 0 := by simp [hh, h0]
  rw [hh0, sub_zero, Real.norm_eq_abs, sub_zero, abs_of_nonneg ht0] at hmvt
  simpa [hh, hB, hD, mul_comm, mul_left_comm, mul_assoc] using hmvt

end ComplexSLE.Internal.ExternalProofs

end
