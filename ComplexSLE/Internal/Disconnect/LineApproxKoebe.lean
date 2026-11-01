/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Disconnect.LineApproxSeq
public import ComplexSLE.Internal.Phases.KoebeHit
import ComplexSLE.Internal.Loewner.Transform
import Mathlib.Analysis.Complex.Liouville

/-!
# Lemma 4.3 (second bullet) via the Koebe distance bound

arXiv:2203.07313v4, Lemma 4.3 (`lem-haus`, paper.tex:L2008-2019). The paper proves that the hull
`L^V_T` of a small driver reaches the tips `±2 √T i` of the zero-driver slit by a Hurwitz argument.
Here lower semicontinuity of the hulls is obtained instead from the Koebe distance bound
`norm_deriv_fPath_mul_infDist_le` (`|f_T'(z)| · dist(z, L_T) ≤ koebeK |f_T(z)|`, `koebeK = 48`)
at `z = i (2 √T + δ')`, together with the Cauchy estimate for `f^V_T' - zeroMap'` coming from
`exists_small_driver_approx`.

This file consumes the EXTERNAL `loewnerMap_tendstoUniformly`.
-/

public section

open scoped NNReal ENNReal Topology
open Set Filter Metric

namespace ComplexSLE.Internal

open KoebeChain (koebeK koebeK_pos)

/-- **Koebe estimate for the top of the hull.** For `T > 0` and `δ' > 0` there is `ρ > 0` such that
every continuous driver `V` with `|V t| < ρ` on `[0, T]` has
`dist (i (2 √T + δ'), L^V_T) ≤ 8 koebeK δ'` (`= 384 δ'`; `32 δ'` for the sharp Koebe constant).

Proof (paper.tex:L2008-2019, with Koebe replacing the Hurwitz argument). Put `z₀ = i (2 √T + δ')`,
`w = zeroMap T z₀`. Then `|w|² = δ' (4 √T + δ')` and `w · w' = z₀` for `w' = (zeroMap T)'(z₀)`.
`exists_small_driver_approx` (with `ε = δ'/2`) gives `|f^V_T - zeroMap T| < η` on the closed disc
`B(z₀, δ'/2)`; the Cauchy estimate then bounds `|(f^V_T)'(z₀) - w'| ≤ 2η/δ'`. The Koebe
bound `|f_T'(z₀)| · dist(z₀, L_T) ≤ koebeK |f_T(z₀)|` (`norm_deriv_fPath_mul_infDist_le`)
finishes. -/
theorem infDist_leftHull_top_le (T : ℝ≥0) (hT : 0 < T) {δ' : ℝ} (hδ' : 0 < δ') :
    ∃ ρ > 0, ∀ (V : ℝ≥0 → ℂ) (_hV : Continuous V), (∀ t ≤ T, ‖V t‖ < ρ) →
      infDist (((2 * Real.sqrt T + δ' : ℝ) : ℂ) * Complex.I) (leftHull V T) ≤ 8 * koebeK * δ' := by
  set c : ℝ := 2 * Real.sqrt T with hc
  have hsq : 0 < Real.sqrt T := Real.sqrt_pos.2 (by exact_mod_cast hT)
  have hc0 : 0 < c := by positivity
  have hc2 : c ^ 2 = 4 * T := by
    rw [hc, mul_pow, Real.sq_sqrt T.coe_nonneg]; norm_num
  set z₀ : ℂ := ((c + δ' : ℝ) : ℂ) * Complex.I with hz₀
  have hz₀S : z₀ ∉ slitI T := by
    rw [mem_slitI_iff]
    rintro ⟨-, h⟩
    simp only [hz₀, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
      Complex.I_re, mul_zero, add_zero] at h
    nlinarith
  have hz₀n : ‖z₀‖ = c + δ' := by
    rw [hz₀, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_of_nonneg (by positivity)]
  have hz₀sq : z₀ ^ 2 = ((-(c + δ') ^ 2 : ℝ) : ℂ) := by
    rw [hz₀, mul_pow, Complex.I_sq]; push_cast; ring
  have hz0 : z₀ ≠ 0 := ne_zero_of_notMem_slitI hz₀S
  set w := zeroMap T z₀ with hw
  set w' := deriv (zeroMap T) z₀ with hw'
  have hww' : w * w' = z₀ := zeroMap_mul_deriv hz₀S
  have hwsq : w ^ 2 = z₀ ^ 2 + 4 * ((T : ℝ) : ℂ) := zeroMap_sq hz0
  have hm2 : ‖w‖ ^ 2 = δ' * (2 * c + δ') := by
    rw [← norm_pow, hwsq, hz₀sq]
    have : ((-(c + δ') ^ 2 : ℝ) : ℂ) + 4 * ((T : ℝ) : ℂ) = ((-(c + δ') ^ 2 + 4 * T : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonpos (by nlinarith)]
    nlinarith
  have hmpos : 0 < ‖w‖ := by
    have : 0 < ‖w‖ ^ 2 := by rw [hm2]; positivity
    exact lt_of_le_of_ne (norm_nonneg _) (fun h => by rw [← h] at this; simp at this)
  have hmm' : ‖w‖ * ‖w'‖ = c + δ' := by rw [← norm_mul, hww', hz₀n]
  have hm'pos : 0 < ‖w'‖ := by
    have : 0 < ‖w‖ * ‖w'‖ := by rw [hmm']; positivity
    exact (pos_iff_pos_of_mul_pos this).1 hmpos
  set η : ℝ := min ‖w‖ (δ' * ‖w'‖ / 4) with hη
  have hηpos : 0 < η := lt_min hmpos (by positivity)
  have hη1 : η ≤ ‖w‖ := min_le_left _ _
  have hη2 : η ≤ δ' * ‖w'‖ / 4 := min_le_right _ _
  obtain ⟨ρ, hρ, hA⟩ := exists_small_driver_approx T (ε := δ' / 2) (half_pos hδ') hηpos
  refine ⟨ρ, hρ, fun V hV hsmall => ?_⟩
  have hinf : δ' ≤ infDist z₀ (slitI T) := by
    refine (le_infDist ⟨0, zero_mem_slitI T⟩).2 fun p hp => ?_
    rw [mem_slitI_iff] at hp
    have h1 : |(z₀ - p).im| ≤ dist z₀ p := by
      rw [dist_eq_norm]; exact Complex.abs_im_le_norm _
    have h2 : p.im ≤ c := by nlinarith [hp.2]
    have h3 : (z₀ - p).im = c + δ' - p.im := by
      simp [hz₀]
    rw [h3] at h1
    have := le_abs_self (c + δ' - p.im)
    linarith
  have hfar : ∀ z ∈ closedBall z₀ (δ' / 2), δ' / 2 ≤ infDist z (slitI T) := by
    intro z hz
    have := infDist_le_infDist_add_dist (x := z₀) (y := z) (s := slitI T)
    rw [mem_closedBall, dist_comm] at hz
    linarith
  have hnotS : ∀ z ∈ closedBall z₀ (δ' / 2), z ∉ slitI T := fun z hz hzS => by
    have := hfar z hz
    rw [infDist_zero_of_mem hzS] at this; linarith
  have hAV := fun z (hz : z ∈ closedBall z₀ (δ' / 2)) => hA V hV hsmall z (hfar z hz)
  have hnotL : ∀ z ∈ closedBall z₀ (δ' / 2), z ∈ (leftHull V T)ᶜ := fun z hz => (hAV z hz).1
  set F : ℂ → ℂ := fun x => Polar.fPath V hV x T with hF
  have hFd : ∀ z ∈ closedBall z₀ (δ' / 2), DifferentiableAt ℂ F z := fun z hz =>
    (Polar.hasDerivAt_fPath_initial hV (Polar.coe_mem_lifeSet_iff.2 (hnotL z hz))).differentiableAt
  set D : ℂ → ℂ := fun x => F x - zeroMap T x with hD
  have hDd : DifferentiableOn ℂ D (closedBall z₀ (δ' / 2)) := fun z hz =>
    ((hFd z hz).sub (differentiableAt_zeroMap (hnotS z hz))).differentiableWithinAt
  have hDC : DiffContOnCl ℂ D (ball z₀ (δ' / 2)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ (half_pos hδ').ne']
    exact hDd
  have hDF : ∀ z (hz : z ∈ closedBall z₀ (δ' / 2)),
      ‖F z - zeroMap T z‖ < η := by
    intro z hz
    obtain ⟨h, hlt⟩ := hAV z hz
    rw [hF]
    simpa only [Polar.centeredLoewnerMap_eq_fPath hV T h] using hlt
  have hcauchy : ‖deriv D z₀‖ ≤ η / (δ' / 2) :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (half_pos hδ') hDC
      (fun z hz => (hDF z (sphere_subset_closedBall hz)).le)
  have hderivD : deriv D z₀ = deriv F z₀ - w' :=
    deriv_sub (hFd z₀ (mem_closedBall_self (half_pos hδ').le)) (differentiableAt_zeroMap hz₀S)
  have hFz₀ : ‖F z₀‖ ≤ 2 * ‖w‖ := by
    have h1 := hDF z₀ (mem_closedBall_self (half_pos hδ').le)
    have h2 := norm_sub_norm_le (F z₀) w
    linarith
  have hFd₀ : ‖w'‖ / 2 ≤ ‖deriv F z₀‖ := by
    have h1 : ‖w'‖ - ‖deriv F z₀‖ ≤ ‖deriv D z₀‖ := by
      rw [hderivD]
      have := norm_sub_norm_le w' (deriv F z₀)
      rwa [norm_sub_rev] at this
    have h2 : η / (δ' / 2) ≤ ‖w'‖ / 2 := by
      rw [div_le_iff₀ (half_pos hδ')]
      nlinarith
    linarith
  by_cases hd : 0 < infDist z₀ (leftHull V T)
  · have hk := Polar.norm_deriv_fPath_mul_infDist_le hV hd
    set d := infDist z₀ (leftHull V T) with hdd
    have h1 : ‖w'‖ / 2 * d ≤ koebeK * (2 * ‖w‖) := by
      calc ‖w'‖ / 2 * d ≤ ‖deriv F z₀‖ * d := by gcongr
        _ ≤ koebeK * ‖F z₀‖ := hk
        _ ≤ koebeK * (2 * ‖w‖) := mul_le_mul_of_nonneg_left hFz₀ koebeK_pos.le
    have h2 : (c + δ') * d ≤ 4 * koebeK * (δ' * (2 * c + δ')) := by
      rw [← hmm', ← hm2]
      nlinarith [mul_le_mul_of_nonneg_left h1 hmpos.le]
    have h3 : (c + δ') * d ≤ (c + δ') * (8 * koebeK * δ') := by
      nlinarith [mul_nonneg koebeK_pos.le (sq_nonneg δ')]
    exact le_of_mul_le_mul_left h3 (by positivity)
  · push Not at hd
    have := mul_pos koebeK_pos hδ'
    linarith


/-- **Lemma 4.3, second bullet, upper half** (paper.tex:L2008-2019, Koebe version). For `T > 0` and
`δ > 0` there is `ρ > 0` such that every continuous driver `V` with `|V t| < ρ` on `[0, T]` has a
point `z ∈ L^V_T` with `Im z > 2 √T - δ`. -/
theorem exists_mem_leftHull_im_gt (T : ℝ≥0) (hT : 0 < T) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ > 0, ∀ (V : ℝ≥0 → ℂ), Continuous V → (∀ t ≤ T, ‖V t‖ < ρ) →
      ∃ z ∈ leftHull V T, 2 * Real.sqrt T - δ < z.im := by
  have hK := koebeK_pos
  obtain ⟨ρ, hρ, h⟩ := infDist_leftHull_top_le T hT (δ' := δ / (16 * koebeK)) (by positivity)
  refine ⟨ρ, hρ, fun V hV hs => ?_⟩
  have hd := h V hV hs
  have e : 8 * koebeK * (δ / (16 * koebeK)) = δ / 2 := by field_simp; ring
  rw [e] at hd
  have hδ'pos : 0 < δ / (16 * koebeK) := by positivity
  generalize hr : 2 * Real.sqrt T + δ / (16 * koebeK) = r at hd
  have hclosed : IsClosed (leftHull V T) := isOpen_compl_iff.1 (Polar.isOpen_compl_leftHull V hV T)
  obtain ⟨z, hzL, hzd⟩ := hclosed.exists_infDist_eq_dist (leftHull_nonempty V T)
    (((r : ℝ) : ℂ) * Complex.I)
  refine ⟨z, hzL, ?_⟩
  have h1 : |((((r : ℝ) : ℂ) * Complex.I) - z).im| ≤
      dist (((r : ℝ) : ℂ) * Complex.I) z := by
    rw [dist_eq_norm]; exact Complex.abs_im_le_norm _
  have h2 : ((((r : ℝ) : ℂ) * Complex.I) - z).im =
      r - z.im := by simp
  rw [h2] at h1
  have h3 := le_abs_self (r - z.im)
  linarith

/-- **Lemma 4.3, second bullet, lower half**, by the symmetry `V ↦ -V`
(`leftHull_neg`): a point `z ∈ L^V_T` with `Im z < -(2 √T - δ)`. -/
theorem exists_mem_leftHull_im_lt (T : ℝ≥0) (hT : 0 < T) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ > 0, ∀ (V : ℝ≥0 → ℂ), Continuous V → (∀ t ≤ T, ‖V t‖ < ρ) →
      ∃ z ∈ leftHull V T, z.im < -(2 * Real.sqrt T - δ) := by
  obtain ⟨ρ, hρ, h⟩ := exists_mem_leftHull_im_gt T hT hδ
  refine ⟨ρ, hρ, fun V hV hs => ?_⟩
  obtain ⟨z, hz, hzim⟩ := h (fun s => -V s) hV.neg (fun t ht => by simpa using hs t ht)
  rw [leftHull_neg] at hz
  obtain ⟨z', hz', rfl⟩ := hz
  exact ⟨z', hz', by simp at hzim; linarith⟩

end ComplexSLE.Internal

end
