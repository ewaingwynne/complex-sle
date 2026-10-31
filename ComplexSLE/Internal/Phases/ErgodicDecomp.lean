/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.PolarThetaHat
public import ComplexSLE.Internal.Polar.PolarThetaBrIto
public import ComplexSLE.Internal.Phases.AllZFHat
public import ComplexSLE.Internal.Stationary.SLEStatKernel
public import ComplexSLE.Infrastructure.Stochastic.BoundedBracket

/-!
# `log |f̂_s(𝐳)|` along a fixed unit point: drift, `L²`-martingale part, sublinear growth (M7/A5a)

Fix an adapted SLE driver `hU : IsSLEDriverAdapted a b c U P ℱ` with `a > 0`, `c² ≤ ab`, and a point
`z = e^{iu}` on the unit circle. With `Y_s = log |f̂_s(z)|` (`fHat`), `D_s = ∫₀ˢ ν(θ̂_v) dv`
(`pathIntegral` of `ν ∘ θ̂`) and `M = sigmaLogMart` (the martingale part of Lemma 2.11):

* `ae_log_norm_fHat_eq`: almost surely, for all `s`, `Y_s = D_s + M_s` (`Y_0 = 0` since `|z| = 1`);
* `fiber_sigmaLogMart`: `M` is an `L²`-martingale with `E M_t = 0`, `E M_t² ≤ (a + b + |c|) t`
  and `M_s / s → 0` almost surely. This is `IsContLocalMartingale.bounded_bracket` for the pair
  `M`, `M² - ∫₀ˢ Γ̂` of `thetaHat_sigmaLogMart_decomposition`, with `Γ̂ = a cos² θ̂ + b sin² θ̂ +
  2c sin θ̂ cos θ̂` bounded by `a + b + |c|`;
* `abs_pathIntegral_nu_sub_le`: `|D_s - D_r| ≤ C_ν (s - r)`, `C_ν` a bound for `|ν|`.

No external input is used beyond those of `thetaHat_sigmaLogMart_decomposition`
(`ito_formula`, `timeChange_isContLocalMartingale`).
-/

@[expose] public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal

open Polar

/-! ### Elementary bounds -/

theorem abs_logBracketFn_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (θ : ℝ) :
    |logBracketFn a b c θ| ≤ a + b + |c| := by
  unfold logBracketFn
  have h1 : |a * Real.cos θ ^ 2| ≤ a := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [Real.cos_sq_le_one θ]
  have h2 : |b * Real.sin θ ^ 2| ≤ b := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [Real.sin_sq_le_one θ]
  have h3 : |2 * c * Real.sin θ * Real.cos θ| ≤ |c| := by
    have : 2 * c * Real.sin θ * Real.cos θ = c * Real.sin (2 * θ) := by
      rw [Real.sin_two_mul]; ring
    rw [this, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  calc |a * Real.cos θ ^ 2 + b * Real.sin θ ^ 2 + 2 * c * Real.sin θ * Real.cos θ|
      ≤ |a * Real.cos θ ^ 2 + b * Real.sin θ ^ 2| + |2 * c * Real.sin θ * Real.cos θ| :=
        abs_add_le _ _
    _ ≤ (|a * Real.cos θ ^ 2| + |b * Real.sin θ ^ 2|) + |c| :=
        add_le_add (abs_add_le _ _) h3
    _ ≤ a + b + |c| := by linarith

theorem abs_nu_le (a b c u : ℝ) : |nu a b c u| ≤ |2 - a / 2 + b / 2| + |c| := by
  unfold nu
  have h1 : |(2 - a / 2 + b / 2) * Real.cos (2 * u)| ≤ |2 - a / 2 + b / 2| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have h2 : |c * Real.sin (2 * u)| ≤ |c| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  calc |(2 - a / 2 + b / 2) * Real.cos (2 * u) - c * Real.sin (2 * u)|
      ≤ |(2 - a / 2 + b / 2) * Real.cos (2 * u)| + |c * Real.sin (2 * u)| := abs_sub _ _
    _ ≤ |2 - a / 2 + b / 2| + |c| := add_le_add h1 h2

section Fiber

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ} (hU : IsSLEDriverAdapted a b c U P ℱ) {z : ℂ}

/-- Every section `s ↦ θ̂_s(z)(ω)` is measurable (progressivity of `θ̂`). -/
theorem measurable_thetaHat_time (ω : Ω) : Measurable fun s : ℝ≥0 => thetaHat hU z s ω :=
  Infrastructure.measurable_time_of_isStronglyProgressive (isStronglyProgressive_thetaHat hU) ω

/-- A bounded measurable function of `θ̂` is interval integrable in time. -/
theorem intervalIntegrable_comp_thetaHat {φ : ℝ → ℝ} (hφ : Measurable φ) {C : ℝ}
    (hC : ∀ x, |φ x| ≤ C) (ω : Ω) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => φ (thetaHat hU z s.toNNReal ω)) volume 0 t := by
  have hm : Measurable fun s : ℝ => φ (thetaHat hU z s.toNNReal ω) :=
    hφ.comp ((measurable_thetaHat_time hU ω).comp measurable_real_toNNReal)
  exact (intervalIntegrable_const (c := C)).mono_fun' hm.aestronglyMeasurable
    (ae_of_all _ fun s => by simpa [Real.norm_eq_abs] using hC _)

/-- `|D_s - D_r| ≤ C (s - r)` for the drift integral `D = ∫₀ˢ φ(θ̂)` of a bounded measurable `φ`. -/
theorem abs_pathIntegral_comp_thetaHat_sub_le {φ : ℝ → ℝ} (hφ : Measurable φ) {C : ℝ}
    (hC : ∀ x, |φ x| ≤ C) (ω : Ω) {r s : ℝ≥0} (hrs : r ≤ s) :
    |pathIntegral (fun v ω => φ (thetaHat hU z v ω)) s ω -
        pathIntegral (fun v ω => φ (thetaHat hU z v ω)) r ω| ≤ C * ((s : ℝ) - r) := by
  have h1 := intervalIntegrable_comp_thetaHat hU (z := z) hφ hC ω
  have e : pathIntegral (fun v ω => φ (thetaHat hU z v ω)) s ω -
      pathIntegral (fun v ω => φ (thetaHat hU z v ω)) r ω =
      ∫ v in (r : ℝ)..(s : ℝ), φ (thetaHat hU z v.toNNReal ω) :=
    intervalIntegral.integral_interval_sub_left (h1 s) (h1 r)
  rw [e]
  have := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun v : ℝ => φ (thetaHat hU z v.toNNReal ω)) (a := (r : ℝ)) (b := (s : ℝ)) (C := C)
    fun v _ => by simpa [Real.norm_eq_abs] using hC _
  have hrs' : (r : ℝ) ≤ s := hrs
  simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hrs')] using this

theorem sigmaLogMart_zero (ω : Ω) : sigmaLogMart hU z 0 ω = 0 := by
  unfold sigmaLogMart
  split_ifs with h
  · have hz := zero_mem_lifeSet_iff.2 (pos_absorbingTime_of_mem_sigmaDom (hU.cont ω) h)
    simp only [NNReal.coe_zero]
    rw [sigmaTime_zero (hU.cont ω) hz]
    simp
  · rfl

/-- **The martingale part of `log |f̂|` is an `L²`-martingale with sublinear growth.** For
`0 < a`, `0 < b`, `c² ≤ ab`, `z ≠ 0`: `M = sigmaLogMart` satisfies `E M_t² ≤ (a + b + |c|) t`,
`E M_t = 0`, and `M_s / s → 0` almost surely. -/
theorem fiber_sigmaLogMart [IsProbabilityMeasure P] (ha : 0 < a) (hb : 0 < b)
    (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) :
    (∀ t : ℝ≥0, Integrable (fun ω => sigmaLogMart hU z t ω ^ 2) P) ∧
      (∀ t : ℝ≥0, ∫ ω, sigmaLogMart hU z t ω ^ 2 ∂P ≤ (a + b + |c|) * t) ∧
      (∀ t : ℝ≥0, ∫ ω, sigmaLogMart hU z t ω ∂P = 0) ∧
      ∀ᵐ ω ∂P, Tendsto (fun s : ℝ≥0 => sigmaLogMart hU z s ω / s) atTop (𝓝 0) := by
  have hprog := isStronglyProgressive_thetaHat hU (z := z)
  have hΓp : IsStronglyProgressive (sigmaFiltration hU z)
      fun s ω => logBracketFn a b c (thetaHat hU z s ω) :=
    fun i => (continuous_logBracketFn a b c).comp_stronglyMeasurable (hprog i)
  exact IsContLocalMartingale.bounded_bracket (ℱ := sigmaFiltration hU z)
    (Γ := fun s ω => logBracketFn a b c (thetaHat hU z s ω)) (K := a + b + |c|)
    (by positivity) (fun s ω => abs_logBracketFn_le ha.le hb.le _)
    (isStronglyProgressive_pathIntegral' hΓp)
    (fun ω => continuous_pathIntegral' fun t => intervalIntegrable_comp_thetaHat hU
      (continuous_logBracketFn a b c).measurable (fun x => abs_logBracketFn_le ha.le hb.le x) ω t)
    (isContLocalMartingale_sigmaLogMart hU ha hc hz) (ae_of_all _ fun ω => sigmaLogMart_zero hU ω)
    (thetaHat_sigmaLogMart_decomposition hU ha hc hz).2.2.2.1

/-- `M_t = sigmaLogMart` is measurable. -/
theorem measurable_sigmaLogMart (ha : 0 < a) (hc : c ^ 2 ≤ a * b) [IsProbabilityMeasure P]
    (hz : z ≠ 0) (t : ℝ≥0) : Measurable (sigmaLogMart hU z t) :=
  (((isContLocalMartingale_sigmaLogMart hU ha hc hz).1.stronglyAdapted t).mono
    ((sigmaFiltration hU z).le t)).measurable

theorem integrable_sigmaLogMart [IsProbabilityMeasure P] (ha : 0 < a) (hb : 0 < b)
    (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) (t : ℝ≥0) : Integrable (sigmaLogMart hU z t) P :=
  ((memLp_two_iff_integrable_sq
    (measurable_sigmaLogMart hU ha hc hz t).aestronglyMeasurable).2
      ((fiber_sigmaLogMart hU ha hb hc hz).1 t)).integrable one_le_two

/-- **`log |f̂_s(𝐳)| = ∫₀ˢ ν(θ̂_v) dv + M_s`** for `|z| = 1`, almost surely for all `s`
(`Y_0 = log |z - U 0| = 0` a.s.). -/
theorem ae_log_norm_fHat_eq [IsProbabilityMeasure P] (ha : 0 < a) (hc : c ^ 2 ≤ a * b)
    (hz : ‖z‖ = 1) :
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0, Real.log ‖fHat hU z s ω‖ =
      pathIntegral (fun v ω => nu a b c (thetaHat hU z v ω)) s ω + sigmaLogMart hU z s ω := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.1 (by rw [hz]; exact one_ne_zero)
  filter_upwards [ae_sigmaLogMart_eq hU ha hc hz0, hU.toIsSLEDriver.zero,
    ae_sigmaDom_eq_Ici hU z ha hc hz0] with ω h1 h0 hd s
  have hmem : (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z := by
    rw [hd]; exact s.coe_nonneg
  rw [fHat_of_mem hU hmem, h1 s, fPath_zero, h0, sub_zero, hz, Real.log_one]
  ring

end Fiber

end ComplexSLE.Internal

end
