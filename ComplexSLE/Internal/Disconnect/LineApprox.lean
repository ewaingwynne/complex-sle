/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Disconnect.LineApproxKoebe
public import ComplexSLE.Internal.Duality.Deterministic

/-!
# Lemmas 4.2 and 4.3 in deterministic form: small drivers have hulls near the zero-driver slits

arXiv:2203.07313v4, Lemma 4.2 (`lem-line-approx`, paper.tex:L1991-1993, proof L2021-2025) and
Lemma 4.3 (`lem-haus`, L1998-2019). The probabilistic input (`U` is uniformly small on `[0, T]`
with positive probability) is not used here; the statement is purely deterministic.

`lineApprox`: for `T > 0` and `δ > 0` there is `η > 0` such that for every continuous driver `V`
with `|V t| < η` on `[0, T]`:

* the left hull `L^V_T` lies in the `δ`-neighbourhood of `slitI T = [-2 √T i, 2 √T i]` and has a
  point above `2 √T i - i δ` and a point below `-2 √T i + i δ`;
* the right hull `R^V_T` lies in the `δ`-neighbourhood of `slitR T = [-2 √T, 2 √T]` and has a
  point to the right of `2 √T - δ` and one to the left of `-(2 √T - δ)`;
* away from the slit, `f^V_T` is `δ`-close to `zeroMap T`.

The left-hull statements come from `exists_small_driver_approx` (the EXTERNAL E12) and the Koebe
bound (`LineApproxKoebe`). The right-hull statements follow by the duality
`leftHull (dualDriver V T) T = i R^V_T` (`leftHull_dualDriver`), since the dual driver is again
uniformly small on `[0, T]`.

The hypothesis `V 0 = 0` of the source is not needed, and the statements below omit it.
-/

public section

open scoped NNReal ENNReal
open Set Metric

namespace ComplexSLE.Internal

/-- Rotation by `i` maps the horizontal slit onto the vertical slit. -/
theorem mul_I_mem_slitI_iff {T : ℝ≥0} {w : ℂ} : Complex.I * w ∈ slitI T ↔ w ∈ slitR T := by
  rw [mem_slitI_iff, mem_slitR_iff]
  simp

theorem image_mul_I_slitR (T : ℝ≥0) : (fun z => Complex.I * z) '' slitR T = slitI T := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact mul_I_mem_slitI_iff.2 hw
  · intro hz
    refine ⟨-Complex.I * z, ?_, ?_⟩
    · rw [← mul_I_mem_slitI_iff]
      have : Complex.I * (-Complex.I * z) = z := by
        linear_combination (-z) * Complex.I_mul_I
      rwa [this]
    · simp only
      linear_combination (-z) * Complex.I_mul_I

theorem infDist_mul_I (T : ℝ≥0) (w : ℂ) :
    infDist (Complex.I * w) (slitI T) = infDist w (slitR T) := by
  have hiso : Isometry (fun z : ℂ => Complex.I * z) :=
    Isometry.of_dist_eq fun x y => by
      simp only [dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_I, one_mul]
  rw [← image_mul_I_slitR T]
  exact infDist_image hiso

/-- The dual driver is uniformly small on `[0, t]` when the driver is. -/
theorem norm_dualDriver_lt {u : ℝ≥0 → ℂ} {t : ℝ≥0} {ρ : ℝ} (h : ∀ s ≤ t, ‖u s‖ < ρ) :
    ∀ s ≤ t, ‖dualDriver u t s‖ < 2 * ρ := by
  intro s hs
  have e : dualDriver u t s = Complex.I * (u (t - s) - u t) := by
    simp [dualDriver, max_eq_right hs]
  rw [e, norm_mul, Complex.norm_I, one_mul]
  calc ‖u (t - s) - u t‖ ≤ ‖u (t - s)‖ + ‖u t‖ := norm_sub_le _ _
    _ < ρ + ρ := add_lt_add (h _ tsub_le_self) (h t le_rfl)
    _ = 2 * ρ := by ring

/-- The left-hull half of `lineApprox`: all clauses that concern `L^V_T` and `f^V_T`. -/
theorem leftApprox (T : ℝ≥0) (hT : 0 < T) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ > 0, ∀ (V : ℝ≥0 → ℂ) (hV : Continuous V), (∀ t ≤ T, ‖V t‖ < ρ) →
      (∀ z ∈ leftHull V T, infDist z (slitI T) < δ) ∧
      (∃ z ∈ leftHull V T, 2 * Real.sqrt T - δ < z.im) ∧
      (∃ z ∈ leftHull V T, z.im < -(2 * Real.sqrt T - δ)) ∧
      ∀ z (h : z ∈ (leftHull V T)ᶜ), δ ≤ infDist z (slitI T) →
        ‖centeredLoewnerMap V hV T ⟨z, h⟩ - zeroMap T z‖ < δ := by
  obtain ⟨ρ₁, hρ₁, h₁⟩ := exists_small_driver_approx T hδ hδ
  obtain ⟨ρ₂, hρ₂, h₂⟩ := exists_mem_leftHull_im_gt T hT hδ
  obtain ⟨ρ₃, hρ₃, h₃⟩ := exists_mem_leftHull_im_lt T hT hδ
  refine ⟨min ρ₁ (min ρ₂ ρ₃), lt_min hρ₁ (lt_min hρ₂ hρ₃), fun V hV hs => ?_⟩
  have hs₁ : ∀ t ≤ T, ‖V t‖ < ρ₁ := fun t ht => (hs t ht).trans_le (min_le_left _ _)
  have hs₂ : ∀ t ≤ T, ‖V t‖ < ρ₂ := fun t ht =>
    (hs t ht).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hs₃ : ∀ t ≤ T, ‖V t‖ < ρ₃ := fun t ht =>
    (hs t ht).trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨fun z hz => ?_, h₂ V hV hs₂, h₃ V hV hs₃, fun z h hfar => ?_⟩
  · by_contra hnot
    obtain ⟨h', -⟩ := h₁ V hV hs₁ z (not_lt.1 hnot)
    exact h' hz
  · obtain ⟨h', hlt⟩ := h₁ V hV hs₁ z hfar
    exact hlt

/-- **Lemmas 4.2 and 4.3 (deterministic form).** For `T > 0` and `δ > 0` there is `η > 0` such that
every continuous driver `V` with `|V t| < η` on `[0, T]` satisfies:

* `L^V_T` lies in the `δ`-neighbourhood of `slitI T`;
* `R^V_T` lies in the `δ`-neighbourhood of `slitR T`;
* `L^V_T` has points with `Im z > 2 √T - δ` and with `Im z < -(2 √T - δ)`;
* `R^V_T` has points with `Re w > 2 √T - δ` and with `Re w < -(2 √T - δ)`;
* for every `z ∉ L^V_T` at distance `≥ δ` from `slitI T`, `|f^V_T (z) - zeroMap T z| < δ`.

(`zeroMap T` is `f⁰_T`, `slitI T = L⁰_T`, `slitR T = R⁰_T`: `leftHull_zero`, `rightHull_zero`,
`centeredLoewnerMap_zero`.) Uses the EXTERNAL `loewnerMap_tendstoUniformly`. -/
theorem lineApprox (T : ℝ≥0) (hT : 0 < T) (δ : ℝ) (hδ : 0 < δ) :
    ∃ η > 0, ∀ (V : ℝ≥0 → ℂ) (hV : Continuous V), (∀ t ≤ T, ‖V t‖ < η) →
      (∀ z ∈ leftHull V T, infDist z (slitI T) < δ) ∧
      (∀ w ∈ rightHull V hV T, infDist w (slitR T) < δ) ∧
      (∃ z ∈ leftHull V T, 2 * Real.sqrt T - δ < z.im) ∧
      (∃ z ∈ leftHull V T, z.im < -(2 * Real.sqrt T - δ)) ∧
      (∃ w ∈ rightHull V hV T, 2 * Real.sqrt T - δ < w.re) ∧
      (∃ w ∈ rightHull V hV T, w.re < -(2 * Real.sqrt T - δ)) ∧
      ∀ z (h : z ∈ (leftHull V T)ᶜ), δ ≤ infDist z (slitI T) →
        ‖centeredLoewnerMap V hV T ⟨z, h⟩ - zeroMap T z‖ < δ := by
  obtain ⟨ρ, hρ, hL⟩ := leftApprox T hT hδ
  refine ⟨ρ / 2, half_pos hρ, fun V hV hs => ?_⟩
  have hs₁ : ∀ t ≤ T, ‖V t‖ < ρ := fun t ht => (hs t ht).trans (half_lt_self hρ)
  obtain ⟨h1, h3, h4, h7⟩ := hL V hV hs₁
  have hdual : ∀ t ≤ T, ‖dualDriver V T t‖ < ρ := fun t ht => by
    have := norm_dualDriver_lt hs t ht
    rwa [mul_div_cancel₀ _ two_ne_zero] at this
  obtain ⟨h1', h3', h4', -⟩ := hL (dualDriver V T) (continuous_dualDriver hV T) hdual
  have hdl := leftHull_dualDriver hV T
  refine ⟨h1, fun w hw => ?_, h3, h4, ?_, ?_, h7⟩
  · have hmem : Complex.I * w ∈ leftHull (dualDriver V T) T := by
      rw [hdl]; exact ⟨w, hw, rfl⟩
    have := h1' _ hmem
    rwa [infDist_mul_I] at this
  · obtain ⟨z, hz, hzim⟩ := h3'
    rw [hdl] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨w, hw, by simpa using hzim⟩
  · obtain ⟨z, hz, hzim⟩ := h4'
    rw [hdl] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨w, hw, by simpa using hzim⟩

end ComplexSLE.Internal

end
