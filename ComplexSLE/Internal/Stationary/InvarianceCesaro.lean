/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.InvariancePoisson
public import ComplexSLE.Internal.Stationary.InvarianceApprox
public import ComplexSLE.Internal.Stationary.ThetaSemigroupDynkin

/-!
# Cesàro convergence of the semigroup of `θ̂` from every start (M10-R4, steps 3–4)

Write `Q_t f(u) = thetaSemigroup hU t f u = E f(θ̂_t(e^{iu}))` and `ν = admissibleMeasure p`.

* `tendsto_cesaro_of_contDiff`: for `f ∈ C²` `π`-periodic and every `u`,
  `T⁻¹ ∫₀ᵀ Q_t f(u) dt → ∫ f dν`. With `g` the solution of `L g = f - C` of
  `exists_poisson_generator` and `C = ∫ f dν` (`poisson_const_eq`), Dynkin gives
  `∫₀ᵀ Q_t f(u) dt = C T + (Q_T g(u) - g(u))` and `|Q_T g(u) - g(u)| ≤ 2 sup |g|`.
* `tendsto_cesaro_of_continuous`: the same for continuous `π`-periodic `f`, by uniform
  approximation by `C²` periodic functions (`exists_contDiff_periodic_approx`), since
  `|Q_t f - Q_t f'| ≤ sup |f - f'|`.

No transition kernel, no Hörmander smoothing and no Markov external is used.
-/

public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter Function intervalIntegral

namespace ComplexSLE.Internal

open Polar

section Helpers

/-- A probability-measure estimate: if `|F - G| ≤ ε` pointwise then `|∫ F - ∫ G| ≤ ε`. -/
theorem abs_integral_sub_le_of_bound {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [IsProbabilityMeasure μ] {F G : α → ℝ} (hF : Integrable F μ) (hG : Integrable G μ) {ε : ℝ}
    (h : ∀ x, |F x - G x| ≤ ε) : |∫ x, F x ∂μ - ∫ x, G x ∂μ| ≤ ε := by
  rw [← integral_sub hF hG]
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => F x - G x) (C := ε)
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using h x)
  simpa using this

/-- A continuous bounded function is integrable for a finite measure on `ℝ`. -/
theorem integrable_of_continuous_of_bound {μ : Measure ℝ} [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : Continuous f) (hb : ∃ C, ∀ v, |f v| ≤ C) : Integrable f μ := by
  obtain ⟨C, hC⟩ := hb
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (Eventually.of_forall fun v => by simpa [Real.norm_eq_abs] using hC v)

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ} [IsProbabilityMeasure P]

/-- `f(θ̂_t(z))` is integrable for `f` measurable and bounded. -/
theorem integrable_comp_thetaHat (hU : IsSLEDriverAdapted a b c U P ℱ) {f : ℝ → ℝ}
    (hf : Measurable f) (hb : ∃ C, ∀ v, |f v| ≤ C) (z : ℂ) (t : ℝ≥0) :
    Integrable (fun ω => f (thetaHat hU z t ω)) P := by
  obtain ⟨C, hC⟩ := hb
  exact Integrable.of_bound (hf.comp (measurable_thetaHat hU z t)).aestronglyMeasurable C
    (Eventually.of_forall fun _ => by simpa [Real.norm_eq_abs] using hC _)

/-- `Q_t (f - C) = Q_t f - C`. -/
theorem thetaSemigroup_sub_const (hU : IsSLEDriverAdapted a b c U P ℱ) {f : ℝ → ℝ}
    (hf : Measurable f) (hb : ∃ C, ∀ v, |f v| ≤ C) (C : ℝ) (t : ℝ≥0) (u : ℝ) :
    thetaSemigroup hU t (fun v => f v - C) u = thetaSemigroup hU t f u - C := by
  unfold thetaSemigroup
  rw [integral_sub (integrable_comp_thetaHat hU hf hb _ t) (integrable_const C),
    MeasureTheory.integral_const]
  simp

/-- `|Q_t f - Q_t f'| ≤ ε` when `|f - f'| ≤ ε`. -/
theorem abs_thetaSemigroup_sub_le (hU : IsSLEDriverAdapted a b c U P ℱ) {f f' : ℝ → ℝ}
    (hf : Measurable f) (hfb : ∃ C, ∀ v, |f v| ≤ C) (hf' : Measurable f')
    (hfb' : ∃ C, ∀ v, |f' v| ≤ C) {ε : ℝ} (h : ∀ v, |f v - f' v| ≤ ε) (t : ℝ≥0) (u : ℝ) :
    |thetaSemigroup hU t f u - thetaSemigroup hU t f' u| ≤ ε :=
  abs_integral_sub_le_of_bound (integrable_comp_thetaHat hU hf hfb _ t)
    (integrable_comp_thetaHat hU hf' hfb' _ t) fun _ => h _

variable (ha : 0 < a) (hc : c ^ 2 ≤ a * b)
include ha hc

/-- `t ↦ Q_{t⁺} f(u)` is continuous on `ℝ`. -/
theorem continuous_thetaSemigroup_real_time (hU : IsSLEDriverAdapted a b c U P ℱ) {f : ℝ → ℝ}
    (hf : Continuous f) (hb : ∃ C, ∀ v, |f v| ≤ C) (u : ℝ) :
    Continuous fun t : ℝ => thetaSemigroup hU t.toNNReal f u :=
  (continuous_thetaSemigroup_time hU ha hc hf hb u).comp continuous_real_toNNReal

end Helpers

section Cesaro

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ} [IsProbabilityMeasure P]

/-- **Cesàro convergence for `C²` periodic test functions, from every start.** -/
theorem tendsto_cesaro_of_contDiff (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b)
    (hc : c ^ 2 ≤ a * b) {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfper : Function.Periodic f π) (u : ℝ) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0)..T, thetaSemigroup hU t.toNNReal f u) atTop
      (𝓝 (∫ v, f v ∂(admissibleMeasure p))) := by
  obtain ⟨β, hβc, hβ⟩ := exists_contDiff_beta_sq ha hb hc
  obtain ⟨C, g, hgc, hgper, hgen⟩ := exists_poisson_generator ha hb hc hβ hf hfper
  have hCeq := poisson_const_eq ha hb hc hβ hp hf hfper hgc hgper hgen
  obtain ⟨Cg, hCg⟩ := exists_abs_le_of_periodic hgc.continuous hgper
  have hfc : Continuous f := hf.continuous
  obtain ⟨Cf, hCf⟩ := exists_abs_le_of_periodic hfc hfper
  have hQc := continuous_thetaSemigroup_real_time ha hc hU hfc ⟨Cf, hCf⟩ u
  -- Dynkin: `∫₀ᵀ Q_t f(u) dt = C T + (Q_T g(u) - g(u))`
  have hD : ∀ T : ℝ, 0 ≤ T → (∫ t in (0)..T, thetaSemigroup hU t.toNNReal f u) =
      C * T + (thetaSemigroup hU T.toNNReal g u - g u) := by
    intro T hT
    have h := thetaSemigroup_sub_self hU ha hb hc hβc.continuous hβ hgc hgper T.toNNReal u
    rw [Real.coe_toNNReal T hT] at h
    have hgen' : generator (mu a b c) β g = fun v => f v - C := funext hgen
    rw [hgen'] at h
    simp only [thetaSemigroup_sub_const hU hfc.measurable ⟨Cf, hCf⟩] at h
    rw [intervalIntegral.integral_sub (hQc.intervalIntegrable _ _) intervalIntegrable_const] at h
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
    linarith
  have hbd : ∀ T : ℝ, |thetaSemigroup hU T.toNNReal g u - g u| ≤ 2 * Cg := fun T => by
    have h1 := abs_thetaSemigroup_le hU T.toNNReal hCg u
    have h2 := hCg u
    calc |thetaSemigroup hU T.toNNReal g u - g u|
        ≤ |thetaSemigroup hU T.toNNReal g u| + |g u| := abs_sub _ _
      _ ≤ 2 * Cg := by linarith
  have h0 : Tendsto (fun T : ℝ => T⁻¹ * (thetaSemigroup hU T.toNNReal g u - g u)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_
      (by simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (2 * Cg))
    filter_upwards [eventually_gt_atTop 0] with T hT
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hT), mul_comm]
    exact mul_le_mul_of_nonneg_right (hbd T) (inv_pos.2 hT).le
  have hlim : Tendsto (fun T : ℝ => C + T⁻¹ * (thetaSemigroup hU T.toNNReal g u - g u)) atTop
      (𝓝 C) := by
    simpa using h0.const_add C
  rw [← hCeq]
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  rw [hD T hT.le]
  field_simp

/-- **Cesàro convergence for continuous periodic test functions, from every start.** -/
theorem tendsto_cesaro_of_continuous (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a)
    (hb : 0 < b) (hc : c ^ 2 ≤ a * b) {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p)
    {f : ℝ → ℝ} (hf : Continuous f) (hfper : Function.Periodic f π) (u : ℝ) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0)..T, thetaSemigroup hU t.toNNReal f u) atTop
      (𝓝 (∫ v, f v ∂(admissibleMeasure p))) := by
  have := isProbabilityMeasure_admissibleMeasure hp
  obtain ⟨Cf, hCf⟩ := exists_abs_le_of_periodic hf hfper
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / 4 := by positivity
  obtain ⟨f', hf'c, hf'per, hff'⟩ := exists_contDiff_periodic_approx hf hfper hδ
  obtain ⟨Cf', hCf'⟩ := exists_abs_le_of_periodic hf'c.continuous hf'per
  have hQc := continuous_thetaSemigroup_real_time ha hc hU hf ⟨Cf, hCf⟩ u
  have hQc' := continuous_thetaSemigroup_real_time ha hc hU hf'c.continuous ⟨Cf', hCf'⟩ u
  have h' := tendsto_cesaro_of_contDiff hU ha hb hc hp hf'c hf'per u
  rw [Metric.tendsto_nhds] at h'
  filter_upwards [h' (ε / 4) hδ, eventually_gt_atTop 0] with T hT hT0
  -- the three pieces
  have hI : |∫ v, f' v ∂(admissibleMeasure p) - ∫ v, f v ∂(admissibleMeasure p)| ≤ ε / 4 :=
    abs_integral_sub_le_of_bound (integrable_of_continuous_of_bound hf'c.continuous ⟨Cf', hCf'⟩)
      (integrable_of_continuous_of_bound hf ⟨Cf, hCf⟩) fun v => by
        rw [abs_sub_comm]; exact hff' v
  have hint : ∀ t : ℝ, |thetaSemigroup hU t.toNNReal f u - thetaSemigroup hU t.toNNReal f' u| ≤
      ε / 4 := fun t =>
    abs_thetaSemigroup_sub_le hU hf.measurable ⟨Cf, hCf⟩ hf'c.continuous.measurable
      ⟨Cf', hCf'⟩ hff' _ u
  have hdiff : |T⁻¹ * (∫ t in (0)..T, thetaSemigroup hU t.toNNReal f u) -
      T⁻¹ * (∫ t in (0)..T, thetaSemigroup hU t.toNNReal f' u)| ≤ ε / 4 := by
    rw [← mul_sub, ← intervalIntegral.integral_sub (hQc.intervalIntegrable _ _)
      (hQc'.intervalIntegrable _ _), abs_mul, abs_of_pos (inv_pos.2 hT0)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T)
      (f := fun t => thetaSemigroup hU t.toNNReal f u - thetaSemigroup hU t.toNNReal f' u)
      (C := ε / 4) fun t _ => by simpa [Real.norm_eq_abs] using hint t
    rw [Real.norm_eq_abs, sub_zero, abs_of_pos hT0] at this
    calc T⁻¹ * |∫ t in (0)..T, (thetaSemigroup hU t.toNNReal f u -
          thetaSemigroup hU t.toNNReal f' u)| ≤ T⁻¹ * (ε / 4 * T) :=
          mul_le_mul_of_nonneg_left this (inv_pos.2 hT0).le
      _ = ε / 4 := by field_simp
  rw [Real.dist_eq] at hT ⊢
  have htri := abs_sub_le (T⁻¹ * (∫ t in (0)..T, thetaSemigroup hU t.toNNReal f u))
    (T⁻¹ * (∫ t in (0)..T, thetaSemigroup hU t.toNNReal f' u)) (∫ v, f v ∂(admissibleMeasure p))
  have htri2 := abs_sub_le (T⁻¹ * (∫ t in (0)..T, thetaSemigroup hU t.toNNReal f' u))
    (∫ v, f' v ∂(admissibleMeasure p)) (∫ v, f v ∂(admissibleMeasure p))
  linarith

end Cesaro

end ComplexSLE.Internal

end
