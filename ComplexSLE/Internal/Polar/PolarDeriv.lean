/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.PolarDerivShift
public import ComplexSLE.Internal.Polar.Argument
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The derivative `g_t'(z)` of the Loewner map (M7/D0, `step:polar-derivative-sde`, deterministic)

For a continuous driver `U`, a point `z` and `t ∈ [0, T_z)` we show that `w ↦ g_t(w)` is
complex-differentiable at `z` (paper.tex:L880-890, L928: the paper asserts the
`z`-differentiability of `f_t(z)` without proof) with derivative

  `g_t'(z) = derivPath U hU z t = exp(-2 ∫₀ᵗ f_s(z)⁻² ds) ≠ 0`,

the solution of the variational equation `∂_t g_t'(z) = -2 g_t'(z) / f_t(z)²`, `g_0'(z) = 1`
(`hasDerivWithinAt_derivPath`). Taking logarithms of the modulus,

  `log|g_t'(z)| = -2 ∫₀ᵗ Re(f_s(z)⁻²) ds = -2 ∫₀ᵗ cos(2θ_s) |f_s(z)|⁻² ds`

(`log_norm_derivPath_eq_cos`), the deterministic content of (2.27) before the time change.

The proof of differentiability does not use the conformality external: by
`exists_lipschitz_initial`, `‖f_s(w) - f_s(z)‖ ≤ C ‖w - z‖` on `[0, t]` for `w` near `z`, and the
remainder `r_s = g_s(w) - g_s(z) - (w - z) g_s'(z)` satisfies `r_0 = 0` and the linear differential
inequality `‖r'_s‖ ≤ K ‖r_s‖ + C₂ ‖w - z‖²`, so Grönwall gives `‖r_t‖ = O(‖w - z‖²)`.
-/

public section

open scoped NNReal ENNReal Real
open Set Complex

namespace ComplexSLE.Internal.Polar

variable {U : ℝ≥0 → ℂ}

/-! ### The integrand `f_s(z)⁻²` and the candidate derivative -/

/-- The integrand `f_s(z)⁻²` of the variational equation (junk off the life set). -/
@[expose] noncomputable def derivRate (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) (s : ℝ) : ℂ :=
  (fPath U hU z s)⁻¹ ^ 2

/-- `∫₀ᵗ f_s(z)⁻² ds` (meaningful for `t ∈ [0, T_z)`). -/
@[expose] noncomputable def derivIntegral (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) (t : ℝ) :
    ℂ :=
  ∫ s in (0 : ℝ)..t, derivRate U hU z s

/-- **The derivative `g_t'(z) = f_t'(z)`** of the Loewner map in the initial point:
`exp(-2 ∫₀ᵗ f_s(z)⁻² ds)` (meaningful for `t ∈ [0, T_z)`; `hasDerivAt_solPath_initial`). -/
@[expose] noncomputable def derivPath (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-2 * derivIntegral U hU z t)

theorem continuousOn_derivRate (hU : Continuous U) (z : ℂ) :
    ContinuousOn (derivRate U hU z) (lifeSet U z) :=
  ((continuousOn_fPath hU z).inv₀ fun _ hs => fPath_ne_zero hU hs).pow 2

theorem intervalIntegrable_derivRate (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    IntervalIntegrable (derivRate U hU z) MeasureTheory.volume 0 t := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le ht.1]
  exact (continuousOn_derivRate hU z).mono (Icc_subset_lifeSet ht)

theorem derivIntegral_zero (hU : Continuous U) (z : ℂ) : derivIntegral U hU z 0 = 0 := by
  simp [derivIntegral]

/-- `∫₀ᵗ f_s(z)⁻² ds` is differentiable within `[0, ∞)` on the life set, with derivative
`f_t(z)⁻²`. -/
theorem hasDerivWithinAt_derivIntegral (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    HasDerivWithinAt (derivIntegral U hU z) (derivRate U hU z t) (Ici 0) t := by
  have hint := intervalIntegrable_derivRate hU ht
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0
    have hcont : ContinuousWithinAt (derivRate U hU z) (Ioi 0) 0 :=
      ((continuousOn_derivRate hU z) 0 ht).mono_of_mem_nhdsWithin
        (nhdsWithin_mono (0 : ℝ) Ioi_subset_Ici_self (lifeSet_mem_nhdsWithin ht))
    have hmeas : StronglyMeasurableAtFilter (derivRate U hU z) (nhdsWithin 0 (Ioi 0))
        MeasureTheory.volume := by
      refine ⟨lifeSet U z, ?_, ?_⟩
      · exact nhdsWithin_mono (0 : ℝ) Ioi_subset_Ici_self (lifeSet_mem_nhdsWithin ht)
      · exact (continuousOn_derivRate hU z).aestronglyMeasurable (lifeSet_measurableSet U z)
    exact intervalIntegral.integral_hasDerivWithinAt_right hint hmeas hcont
  · have hnhds := lifeSet_mem_nhds ht h0
    have hcont : ContinuousAt (derivRate U hU z) t :=
      (continuousOn_derivRate hU z).continuousAt hnhds
    have hmeas : StronglyMeasurableAtFilter (derivRate U hU z) (nhds t) MeasureTheory.volume :=
      ⟨lifeSet U z, hnhds,
        (continuousOn_derivRate hU z).aestronglyMeasurable (lifeSet_measurableSet U z)⟩
    exact (intervalIntegral.integral_hasDerivAt_right hint hmeas hcont).hasDerivWithinAt

theorem derivPath_zero (hU : Continuous U) (z : ℂ) : derivPath U hU z 0 = 1 := by
  simp [derivPath, derivIntegral_zero]

/-- `g_t'(z) ≠ 0`. -/
theorem derivPath_ne_zero (hU : Continuous U) (z : ℂ) (t : ℝ) : derivPath U hU z t ≠ 0 :=
  Complex.exp_ne_zero _

/-- **The variational equation**: `∂_t g_t'(z) = -2 g_t'(z) f_t(z)⁻²` within `[0, ∞)` on the life
set. -/
theorem hasDerivWithinAt_derivPath (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    HasDerivWithinAt (derivPath U hU z) (-2 * derivPath U hU z t * derivRate U hU z t)
      (Ici 0) t := by
  have := ((hasDerivWithinAt_derivIntegral hU ht).const_mul (-2 : ℂ)).cexp
  refine this.congr_deriv ?_
  simp only [derivPath]
  ring

theorem continuousOn_derivPath (hU : Continuous U) (z : ℂ) :
    ContinuousOn (derivPath U hU z) (lifeSet U z) := fun _ ht =>
  ((hasDerivWithinAt_derivPath hU ht).continuousWithinAt).mono (lifeSet_subset_Ici z)

/-! ### `log|g_t'(z)|` -/

theorem norm_derivPath (hU : Continuous U) (z : ℂ) (t : ℝ) :
    ‖derivPath U hU z t‖ = Real.exp (-2 * (derivIntegral U hU z t).re) := by
  rw [derivPath, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

theorem re_derivIntegral (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    (derivIntegral U hU z t).re = ∫ s in (0 : ℝ)..t, (derivRate U hU z s).re := by
  have := Complex.reCLM.intervalIntegral_comp_comm (intervalIntegrable_derivRate hU ht)
  simpa [derivIntegral] using this.symm

/-- `log|g_t'(z)| = -2 ∫₀ᵗ Re(f_s(z)⁻²) ds`. -/
theorem log_norm_derivPath (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    Real.log ‖derivPath U hU z t‖ = -2 * ∫ s in (0 : ℝ)..t, (derivRate U hU z s).re := by
  rw [norm_derivPath, Real.log_exp, re_derivIntegral hU ht]

/-- `Re(f_s(z)⁻²) = cos(2θ_s) |f_s(z)|⁻²` on the life set. -/
theorem re_derivRate (hU : Continuous U) {z : ℂ} {s : ℝ} (hs : s ∈ lifeSet U z) :
    (derivRate U hU z s).re = Real.cos (2 * argPath U hU z s) * clockRate U hU z s := by
  have h1 : (fPath U hU z s)⁻¹ ^ 2 =
      (((‖fPath U hU z s‖ ^ 2)⁻¹ : ℝ) : ℂ) * exp (((-(2 * argPath U hU z s) : ℝ) : ℂ) * I) := by
    conv_lhs => rw [fPath_eq_norm_mul_exp hU hs]
    rw [mul_inv, ← Complex.exp_neg, mul_pow, sq (exp _), ← Complex.exp_add]
    push_cast
    rw [inv_pow]
    congr 2
    ring
  rw [derivRate, clockRate, h1, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  ring

/-- **(2.27) before the time change**: `log|g_t'(z)| = -2 ∫₀ᵗ cos(2θ_s(z)) |f_s(z)|⁻² ds` for
`t ∈ [0, T_z)`. -/
theorem log_norm_derivPath_eq_cos (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    Real.log ‖derivPath U hU z t‖ =
      -2 * ∫ s in (0 : ℝ)..t, Real.cos (2 * argPath U hU z s) * clockRate U hU z s := by
  rw [log_norm_derivPath hU ht]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht.1] at hs
  exact re_derivRate hU (Icc_subset_lifeSet ht hs)

/-! ### Differentiability of `g_t` in the initial point -/

/-- **Complex differentiability of `g_t` in the initial point** (`step:polar-derivative-sde`,
`SOURCE_GAP` closed): for `t ∈ [0, T_z)`, `w ↦ g_t(w)` is complex-differentiable at `z` with
derivative `g_t'(z) = exp(-2 ∫₀ᵗ f_s(z)⁻² ds)`. (The function `w ↦ solPath U hU w t` agrees with
`loewnerMap U hU t` on `ℂ ∖ L_t`, `loewnerMap_eq_solPath`, which is a neighbourhood of `z`.) -/
theorem hasDerivAt_solPath_initial (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    HasDerivAt (fun w => solPath U hU w t) (derivPath U hU z t) z := by
  obtain ⟨η, hη, hηle⟩ := exists_pos_le_norm_fPath hU ht
  obtain ⟨ρ, hρ, C, hC0, hC⟩ := exists_lipschitz_initial hU ht
  obtain ⟨M, hM⟩ : ∃ M, ∀ s ∈ Icc 0 t, ‖derivPath U hU z s‖ ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn
      ((continuousOn_derivPath hU z).norm.mono (Icc_subset_lifeSet ht))).isBounded.bddAbove
    exact ⟨M, fun s hs => hM ⟨s, hs, rfl⟩⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_rfl, ht.1⟩)
  set K : ℝ := 4 / η ^ 2 with hK
  have hKpos : 0 < K := by positivity
  set C₂ : ℝ := 4 * M * C / η ^ 3 with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  set ρ' : ℝ := min ρ (η / (2 * (C + 1))) with hρ'
  have hρ'pos : 0 < ρ' := lt_min hρ (by positivity)
  -- Step 1: the remainder bound by Grönwall
  have hrem : ∀ w : ℂ, ‖w - z‖ < ρ' →
      ‖solPath U hU w t - solPath U hU z t - (w - z) * derivPath U hU z t‖ ≤
        gronwallBound 0 K (C₂ * ‖w - z‖ ^ 2) t := by
    intro w hw
    have hwρ : ‖w - z‖ < ρ := lt_of_lt_of_le hw (min_le_left _ _)
    have hwC : C * ‖w - z‖ ≤ η / 2 := by
      have h1 : ‖w - z‖ ≤ η / (2 * (C + 1)) := (lt_of_lt_of_le hw (min_le_right _ _)).le
      have h2 : C * ‖w - z‖ ≤ C * (η / (2 * (C + 1))) := mul_le_mul_of_nonneg_left h1 hC0
      have h3 : C * (η / (2 * (C + 1))) ≤ η / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
    obtain ⟨hlife, hlip⟩ := hC w hwρ
    have hsub_w : Icc 0 t ⊆ lifeSet U w := Icc_subset_lifeSet hlife
    have hsub_z : Icc 0 t ⊆ lifeSet U z := Icc_subset_lifeSet ht
    set r : ℝ → ℂ := fun s =>
      solPath U hU w s - solPath U hU z s - (w - z) * derivPath U hU z s with hr
    set r' : ℝ → ℂ := fun s => 2 / fPath U hU w s - 2 / fPath U hU z s -
      (w - z) * (-2 * derivPath U hU z s * derivRate U hU z s) with hr'
    have hcont : ContinuousOn r (Icc 0 t) :=
      (((continuousOn_solPath hU w).mono hsub_w).sub ((continuousOn_solPath hU z).mono hsub_z)).sub
        (continuousOn_const.mul ((continuousOn_derivPath hU z).mono hsub_z))
    have hderiv : ∀ x ∈ Ico 0 t, HasDerivWithinAt r (r' x) (Ici x) x := by
      intro x hx
      have hxI : x ∈ Icc 0 t := Ico_subset_Icc_self hx
      have h1 := (hasDerivWithinAt_solPath hU (hsub_w hxI)).mono (Ici_subset_Ici.2 hx.1)
      have h2 := (hasDerivWithinAt_solPath hU (hsub_z hxI)).mono (Ici_subset_Ici.2 hx.1)
      have h3 := ((hasDerivWithinAt_derivPath hU (hsub_z hxI)).mono
        (Ici_subset_Ici.2 hx.1)).const_mul (w - z)
      exact (h1.sub h2).sub h3
    have h0 : ‖r 0‖ ≤ 0 := by
      simp [hr, solPath_zero, derivPath_zero]
    have hbound : ∀ x ∈ Ico 0 t, ‖r' x‖ ≤ K * ‖r x‖ + C₂ * ‖w - z‖ ^ 2 := by
      intro x hx
      have hxI : x ∈ Icc 0 t := Ico_subset_Icc_self hx
      have hb : η ≤ ‖fPath U hU z x‖ := hηle x hxI
      have hab : ‖fPath U hU w x - fPath U hU z x‖ ≤ C * ‖w - z‖ := hlip x hxI
      have ha : η / 2 ≤ ‖fPath U hU w x‖ := by
        have := norm_sub_norm_le (fPath U hU z x) (fPath U hU w x)
        rw [norm_sub_rev] at this
        linarith
      have ha0 : fPath U hU w x ≠ 0 := norm_pos_iff.1 (by linarith)
      have hb0 : fPath U hU z x ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hη hb)
      have hD : ‖derivPath U hU z x‖ ≤ M := hM x hxI
      have hrx : r x = fPath U hU w x - fPath U hU z x - (w - z) * derivPath U hU z x := by
        simp only [hr, fPath]; ring
      have hid : r' x = -2 * r x / (fPath U hU w x * fPath U hU z x) +
          2 * ((w - z) * derivPath U hU z x) * (fPath U hU w x - fPath U hU z x) /
            (fPath U hU w x * fPath U hU z x ^ 2) := by
        rw [hrx]
        simp only [hr', derivRate]
        field_simp
        ring
      rw [hid]
      have hnorm_ab : η / 2 * η ≤ ‖fPath U hU w x‖ * ‖fPath U hU z x‖ :=
        mul_le_mul ha hb hη.le (norm_nonneg _)
      have hpos_ab : 0 < ‖fPath U hU w x‖ * ‖fPath U hU z x‖ :=
        lt_of_lt_of_le (by positivity) hnorm_ab
      have ht1 : 2 * ‖r x‖ / (‖fPath U hU w x‖ * ‖fPath U hU z x‖) ≤ K * ‖r x‖ := by
        rw [div_le_iff₀ hpos_ab]
        have hKη : K * (η / 2 * η) = 2 := by rw [hK]; field_simp; ring
        calc 2 * ‖r x‖ = K * ‖r x‖ * (η / 2 * η) := by linear_combination -‖r x‖ * hKη
          _ ≤ K * ‖r x‖ * (‖fPath U hU w x‖ * ‖fPath U hU z x‖) :=
              mul_le_mul_of_nonneg_left hnorm_ab (by positivity)
      have ht2 : 2 * (‖w - z‖ * ‖derivPath U hU z x‖) * ‖fPath U hU w x - fPath U hU z x‖ /
          (‖fPath U hU w x‖ * ‖fPath U hU z x‖ ^ 2) ≤ C₂ * ‖w - z‖ ^ 2 := by
        have hden : η / 2 * η ^ 2 ≤ ‖fPath U hU w x‖ * ‖fPath U hU z x‖ ^ 2 :=
          mul_le_mul ha (pow_le_pow_left₀ hη.le hb 2) (by positivity) (norm_nonneg _)
        have hden_pos : 0 < ‖fPath U hU w x‖ * ‖fPath U hU z x‖ ^ 2 :=
          lt_of_lt_of_le (by positivity) hden
        rw [div_le_iff₀ hden_pos]
        have hnum : 2 * (‖w - z‖ * ‖derivPath U hU z x‖) * ‖fPath U hU w x - fPath U hU z x‖ ≤
            2 * M * C * ‖w - z‖ ^ 2 := by
          calc 2 * (‖w - z‖ * ‖derivPath U hU z x‖) * ‖fPath U hU w x - fPath U hU z x‖
              ≤ 2 * (‖w - z‖ * M) * (C * ‖w - z‖) := by gcongr
            _ = 2 * M * C * ‖w - z‖ ^ 2 := by ring
        have hC₂η : C₂ * (η / 2 * η ^ 2) = 2 * M * C := by rw [hC₂]; field_simp; ring
        calc 2 * (‖w - z‖ * ‖derivPath U hU z x‖) * ‖fPath U hU w x - fPath U hU z x‖
            ≤ 2 * M * C * ‖w - z‖ ^ 2 := hnum
          _ = C₂ * ‖w - z‖ ^ 2 * (η / 2 * η ^ 2) := by linear_combination -‖w - z‖ ^ 2 * hC₂η
          _ ≤ C₂ * ‖w - z‖ ^ 2 * (‖fPath U hU w x‖ * ‖fPath U hU z x‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hden (by positivity)
      calc ‖-2 * r x / (fPath U hU w x * fPath U hU z x) +
            2 * ((w - z) * derivPath U hU z x) * (fPath U hU w x - fPath U hU z x) /
              (fPath U hU w x * fPath U hU z x ^ 2)‖
          ≤ ‖-2 * r x / (fPath U hU w x * fPath U hU z x)‖ +
            ‖2 * ((w - z) * derivPath U hU z x) * (fPath U hU w x - fPath U hU z x) /
              (fPath U hU w x * fPath U hU z x ^ 2)‖ := norm_add_le _ _
        _ = 2 * ‖r x‖ / (‖fPath U hU w x‖ * ‖fPath U hU z x‖) +
            2 * (‖w - z‖ * ‖derivPath U hU z x‖) * ‖fPath U hU w x - fPath U hU z x‖ /
              (‖fPath U hU w x‖ * ‖fPath U hU z x‖ ^ 2) := by
            simp only [norm_div, norm_mul, norm_neg, norm_pow, Complex.norm_ofNat]
        _ ≤ K * ‖r x‖ + C₂ * ‖w - z‖ ^ 2 := add_le_add ht1 ht2
    have := norm_le_gronwallBound_of_norm_deriv_right_le hcont hderiv h0 hbound t ⟨ht.1, le_rfl⟩
    simpa only [hr, sub_zero] using this
  -- Step 2: the Grönwall bound is `O(‖w - z‖²)`, hence `o(‖w - z‖)`
  set C₁ : ℝ := (Real.exp (K * t) - 1) / K with hC₁
  have hgb : ∀ ε, gronwallBound 0 K ε t = ε * C₁ := by
    intro ε
    rw [gronwallBound_of_K_ne_0 hKpos.ne']
    simp only [hC₁]
    ring
  rw [hasDerivAt_iff_isLittleO]
  refine Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_pow_sub_sub z one_lt_two)
  refine Asymptotics.IsBigO.of_bound (C₂ * C₁) ?_
  filter_upwards [Metric.ball_mem_nhds z hρ'pos] with w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have h := hrem w hw
  rw [hgb] at h
  rw [smul_eq_mul, norm_pow, norm_norm]
  calc ‖solPath U hU w t - solPath U hU z t - (w - z) * derivPath U hU z t‖
      ≤ C₂ * ‖w - z‖ ^ 2 * C₁ := h
    _ = C₂ * C₁ * ‖w - z‖ ^ 2 := by ring

/-- `f_t = g_t - U_t` has the same derivative in the initial point: `f_t'(z) = g_t'(z)`. -/
theorem hasDerivAt_fPath_initial (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    HasDerivAt (fun w => fPath U hU w t) (derivPath U hU z t) z :=
  (hasDerivAt_solPath_initial hU ht).sub_const (U t.toNNReal)

theorem deriv_fPath_initial (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    deriv (fun w => fPath U hU w t) z = derivPath U hU z t :=
  (hasDerivAt_fPath_initial hU ht).deriv

/-- **Holomorphy of `g_t` on `ℂ ∖ L_t`** (the holomorphy conjunct of `loewnerMap_conformal`,
proved for the extension `w ↦ solPath U hU w t`, which agrees with `loewnerMap U hU t` on
`ℂ ∖ L_t` by `loewnerMap_eq_solPath`). -/
theorem differentiableOn_solPath_initial (hU : Continuous U) (t : ℝ≥0) :
    DifferentiableOn ℂ (fun w => solPath U hU w t) (leftHull U t)ᶜ := fun _ hz =>
  (hasDerivAt_solPath_initial hU (coe_mem_lifeSet_iff.2 hz)).differentiableAt.differentiableWithinAt

end ComplexSLE.Internal.Polar

end
