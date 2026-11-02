/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.InvarianceCesaro
public import ComplexSLE.Internal.Stationary.Law
public import ComplexSLE.Internal.Polar.PolarContMeas

/-!
# Invariance of `ν` and one-time stationarity of `θ̂` (M10-R4, steps 5–6)

For `a, b > 0`, `c² ≤ ab`, an adapted driver, an admissible density `p` and
`ν = admissibleMeasure p`:

* `integral_thetaSemigroup_admissible`: for every continuous `π`-periodic `f` and `s ≥ 0`,
  `∫ Q_s f dν = ∫ f dν`. `h = Q_s f` is continuous and `π`-periodic (Feller, periodicity), so the
  Cesàro limit `T⁻¹ ∫₀ᵀ Q_t h(0) dt` is `∫ h dν` (`tendsto_cesaro_of_continuous`).
  By Chapman–Kolmogorov `Q_t h = Q_{t+s} f`, hence `T⁻¹∫₀ᵀ Q_t h(0) dt` differs from
  `T⁻¹∫₀ᵀ Q_t f(0) dt` by at most `2 s sup|f| / T`, and the latter tends to `∫ f dν`.
  Uniqueness of limits.
* `integral_comp_thetaHat_prod_admissible`, `map_addCircle_thetaHat_prod_eq_admissible`,
  `map_exp_thetaHat_prod_eq_admissible`: one-time stationarity of `θ̂` on the product space
  `(Ω × ℝ, P ⊗ ν)` (integral form, law of `θ̂_s mod π`, law of `e^{2iθ̂_s}`), by Fubini and the
  trigonometric-polynomial density argument of `Law.lean`.

No transition kernel, no Hörmander smoothing and no Markov external is used.
-/

public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter Function intervalIntegral

namespace ComplexSLE.Internal

open Polar

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- **Invariance of `ν` under the semigroup of `θ̂`**: for continuous `π`-periodic `f` and every
`s ≥ 0`, `∫ Q_s f dν = ∫ f dν`. -/
theorem integral_thetaSemigroup_admissible [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (s : ℝ≥0) {f : ℝ → ℝ} (hf : Continuous f)
    (hfper : Function.Periodic f π) :
    ∫ u, thetaSemigroup hU s f u ∂(admissibleMeasure p) = ∫ u, f u ∂(admissibleMeasure p) := by
  obtain ⟨Cf, hCf⟩ := exists_abs_le_of_periodic hf hfper
  have hhc : Continuous (thetaSemigroup hU s f) := continuous_thetaSemigroup hU ha hc s hf hfper
  have hhper : Function.Periodic (thetaSemigroup hU s f) π :=
    thetaSemigroup_periodic hU ha hc s hf.measurable hfper ⟨Cf, hCf⟩
  have L1 := tendsto_cesaro_of_continuous hU ha hb hc hp hhc hhper 0
  have L2 := tendsto_cesaro_of_continuous hU ha hb hc hp hf hfper 0
  set φ : ℝ → ℝ := fun t => thetaSemigroup hU t.toNNReal f 0 with hφ
  have hφc : Continuous φ := continuous_thetaSemigroup_real_time ha hc hU hf ⟨Cf, hCf⟩ 0
  have hφb : ∀ t, |φ t| ≤ Cf := fun t => abs_thetaSemigroup_le hU _ hCf 0
  -- Chapman–Kolmogorov turns `Q_t (Q_s f)` into the shifted `φ (t + s)`
  have hshift : ∀ T : ℝ, 0 ≤ T → (∫ t in (0)..T, thetaSemigroup hU t.toNNReal
      (thetaSemigroup hU s f) 0) = ∫ t in (0)..T, φ (t + s) := by
    intro T hT
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hT] at ht
    have e : (t + (s : ℝ)).toNNReal = t.toNNReal + s := by
      rw [Real.toNNReal_add ht.1 (NNReal.coe_nonneg s), Real.toNNReal_coe]
    simp only [hφ, e]
    exact (thetaSemigroup_add hU ha hc t.toNNReal s hf.measurable hfper ⟨Cf, hCf⟩ 0).symm
  -- the shifted integral differs from the unshifted one by `O(s sup|f|)`
  have hdiffint : ∀ T : ℝ, 0 ≤ T →
      |(∫ t in (0)..T, φ (t + s)) - ∫ t in (0)..T, φ t| ≤ 2 * Cf * s := by
    intro T hT
    have hs0 : (0 : ℝ) ≤ s := NNReal.coe_nonneg s
    have hi : ∀ x y : ℝ, IntervalIntegrable φ volume x y := fun x y => hφc.intervalIntegrable _ _
    rw [intervalIntegral.integral_comp_add_right φ (s : ℝ), zero_add]
    have e1 := integral_add_adjacent_intervals (hi 0 (s : ℝ)) (hi (s : ℝ) (T + s))
    have e2 := integral_add_adjacent_intervals (hi 0 T) (hi T (T + s))
    have key : (∫ t in (s : ℝ)..(T + s), φ t) - ∫ t in (0)..T, φ t =
        (∫ t in T..(T + s), φ t) - ∫ t in (0)..(s : ℝ), φ t := by linarith
    rw [key]
    have b1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := T) (b := T + s) (f := φ)
      (C := Cf) fun t _ => by simpa [Real.norm_eq_abs] using hφb t
    have b2 := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (s : ℝ)) (f := φ)
      (C := Cf) fun t _ => by simpa [Real.norm_eq_abs] using hφb t
    rw [Real.norm_eq_abs, show T + (s : ℝ) - T = s by ring, abs_of_nonneg hs0] at b1
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hs0] at b2
    calc |(∫ t in T..(T + s), φ t) - ∫ t in (0)..(s : ℝ), φ t|
        ≤ |∫ t in T..(T + s), φ t| + |∫ t in (0)..(s : ℝ), φ t| := abs_sub _ _
      _ ≤ 2 * Cf * s := by linarith
  have hD : Tendsto (fun T : ℝ =>
      T⁻¹ * (∫ t in (0)..T, thetaSemigroup hU t.toNNReal (thetaSemigroup hU s f) 0) -
        T⁻¹ * (∫ t in (0)..T, φ t)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_
      (by simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (2 * Cf * s))
    filter_upwards [eventually_gt_atTop 0] with T hT
    rw [← mul_sub, hshift T hT.le, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hT), mul_comm]
    exact mul_le_mul_of_nonneg_right (hdiffint T hT.le) (inv_pos.2 hT).le
  have L1' : Tendsto (fun T : ℝ => T⁻¹ *
      (∫ t in (0)..T, thetaSemigroup hU t.toNNReal (thetaSemigroup hU s f) 0)) atTop
      (𝓝 (∫ u, f u ∂(admissibleMeasure p))) := by
    have := hD.add L2
    simpa using this
  exact tendsto_nhds_unique L1 L1'

section Prod

variable [IsProbabilityMeasure P]

/-- **One-time stationarity of `θ̂` on the product space, integral form.** -/
theorem integral_comp_thetaHat_prod_admissible
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (s : ℝ≥0) {f : ℝ → ℝ} (hf : Continuous f)
    (hfper : Function.Periodic f π) :
    ∫ q, f (thetaHat hU (unitPt q.2) s q.1) ∂(P.prod (admissibleMeasure p)) =
      ∫ u, f u ∂(admissibleMeasure p) := by
  have := isProbabilityMeasure_admissibleMeasure hp
  obtain ⟨C, hC⟩ := exists_abs_le_of_periodic hf hfper
  have hint : Integrable (fun q : Ω × ℝ => f (thetaHat hU (unitPt q.2) s q.1))
      (P.prod (admissibleMeasure p)) :=
    (integrable_const C).mono'
      (hf.measurable.comp (measurable_thetaHat_unit hU s)).aestronglyMeasurable
      (Eventually.of_forall fun q => by simpa [Real.norm_eq_abs] using hC _)
  rw [integral_prod_symm _ hint]
  exact integral_thetaSemigroup_admissible hU ha hb hc hp s hf hfper

/-- **One-time stationarity of `θ̂` on the product space, mod `π`.** -/
theorem map_addCircle_thetaHat_prod_eq_admissible
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b)
    (hc : c ^ 2 ≤ a * b) {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (s : ℝ≥0) :
    (P.prod (admissibleMeasure p)).map
        (fun q : Ω × ℝ => ((thetaHat hU (unitPt q.2) s q.1 : ℝ) : AddCircle π)) =
      (admissibleMeasure p).map ((↑) : ℝ → AddCircle π) := by
  have := isProbabilityMeasure_admissibleMeasure hp
  have h := map_addCircle_eq_of_forall_integral_eq (P := P.prod (admissibleMeasure p))
    (Y := fun q : Ω × ℝ => thetaHat hU (unitPt q.2) s q.1) (Z := Prod.snd)
    (measurable_thetaHat_unit hU s) measurable_snd fun f hf hfper => by
      rw [integral_comp_thetaHat_prod_admissible hU ha hb hc hp s hf.continuous hfper,
        ← integral_map measurable_snd.aemeasurable hf.continuous.aestronglyMeasurable,
        Measure.map_snd_prod]
      simp
  rw [h, show (fun q : Ω × ℝ => ((q.2 : ℝ) : AddCircle π)) =
      ((↑) : ℝ → AddCircle π) ∘ Prod.snd from rfl,
    ← Measure.map_map measurable_coe_addCircle measurable_snd, Measure.map_snd_prod]
  simp

/-- **One-time stationarity of `θ̂` on the product space, `e^{2iθ̂}`.** -/
theorem map_exp_thetaHat_prod_eq_admissible
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b)
    (hc : c ^ 2 ≤ a * b) {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (s : ℝ≥0) :
    (P.prod (admissibleMeasure p)).map
        (fun q : Ω × ℝ => Complex.exp (2 * Complex.I * (thetaHat hU (unitPt q.2) s q.1 : ℝ))) =
      (admissibleMeasure p).map (fun u : ℝ => Complex.exp (2 * Complex.I * u)) := by
  have := isProbabilityMeasure_admissibleMeasure hp
  have h := map_exp_eq_of_forall_integral_eq (P := P.prod (admissibleMeasure p))
    (Y := fun q : Ω × ℝ => thetaHat hU (unitPt q.2) s q.1) (Z := Prod.snd)
    (measurable_thetaHat_unit hU s) measurable_snd fun f hf hfper => by
      rw [integral_comp_thetaHat_prod_admissible hU ha hb hc hp s hf.continuous hfper,
        ← integral_map measurable_snd.aemeasurable hf.continuous.aestronglyMeasurable,
        Measure.map_snd_prod]
      simp
  have hm : Measurable fun u : ℝ => Complex.exp (2 * Complex.I * u) := by fun_prop
  rw [h, show (fun q : Ω × ℝ => Complex.exp (2 * Complex.I * (q.2 : ℝ))) =
      (fun u : ℝ => Complex.exp (2 * Complex.I * u)) ∘ Prod.snd from rfl,
    ← Measure.map_map hm measurable_snd, Measure.map_snd_prod]
  simp

end Prod

end ComplexSLE.Internal

end
