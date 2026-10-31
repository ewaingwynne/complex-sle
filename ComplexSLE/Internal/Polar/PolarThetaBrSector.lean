/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.PolarThetaBrIto

/-!
# The bracket of `θ` and the cross bracket with `log|f|` between two sector times (M6/S13;
`step:polar-real-imag`, brackets of `eqn-theta-t-op` and `eqn-abs-zt-op`)

For an adapted `SLE_Σ` driver (`0 < a`, `c² ≤ ab`), `z ≠ 0` and a sector index `k`, with
`ρ = S_k ≤ σ = S_{k+1} ≤ τ_n` the sector times, we apply the generic bracket lemmas of
`PolarThetaBrIto.lean` to the sector state `X_t = (f_{t ∧ σ}, f_{t ∧ ρ}) ∈ ℝ⁴` of
`PolarThetaIto.lean`, with the functions `argProd` (`Arg (w v̄)`) and

  `logRatio (w, v) = ½ log |w|² - ½ log |v|²`,

so that `argProd (X_t) = θ̃_{t ∧ σ} - θ̃_{t ∧ ρ}` and
`logRatio (X_t) = log|f_{t ∧ σ}| - log|f_{t ∧ ρ}|`.
With the bracket densities (paper.tex:L870-L885, the coefficients `(-√a sin θ, √b cos θ)` of
`dθ` and `(√a cos θ, √b sin θ)` of `d log|f|` with correlation `c/√(ab)`)

* `thetaBracketFn (x, y) = (a y² - 2cxy + b x²)/(x² + y²)²`
  `( = (a sin²θ + b cos²θ - 2c sin θ cos θ)/|f|² )`,
* `crossFn (x, y) = ((b - a) xy + c (x² - y²))/(x² + y²)²`
  `( = ((b - a) sin θ cos θ + c (cos²θ - sin²θ))/|f|² )`,

the results are: with `Δ_k = Θ^n_{· ∧ S_{k+1}} - Θ^n_{· ∧ S_k}`,
`Δ'_k = N^n_{· ∧ S_{k+1}} - N^n_{· ∧ S_k}`,
`B = ∫ 1_{s ≤ τ_n} thetaBracketFn (f_s)` and `C = ∫ 1_{s ≤ τ_n} crossFn (f_s)`,

* `Δ_k² - (B_{· ∧ S_{k+1}} - B_{· ∧ S_k})` is a continuous local martingale
  (`isContLocalMartingale_sectorIncrement_sq`);
* `Δ_k Δ'_k - (C_{· ∧ S_{k+1}} - C_{· ∧ S_k})` is a continuous local martingale
  (`isContLocalMartingale_sectorIncrement_mul`).
-/

public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal.Polar

/-! ### The bracket densities as functions of `f ∈ ℂ ≅ ℝ²` -/

/-- `(a y² - 2cxy + b x²)/(x² + y²)²`, the bracket density of `θ` per unit time. -/
@[expose] noncomputable def thetaBracketFn (a b c : ℝ) (v : Fin 2 → ℝ) : ℝ :=
  (a * v 1 ^ 2 - 2 * c * v 0 * v 1 + b * v 0 ^ 2) / (v 0 ^ 2 + v 1 ^ 2) ^ 2

/-- `((b - a) xy + c (x² - y²))/(x² + y²)²`, the cross bracket density of `θ` and `log|f|`. -/
@[expose] noncomputable def crossFn (a b c : ℝ) (v : Fin 2 → ℝ) : ℝ :=
  ((b - a) * v 0 * v 1 + c * (v 0 ^ 2 - v 1 ^ 2)) / (v 0 ^ 2 + v 1 ^ 2) ^ 2

theorem measurable_thetaBracketFn (a b c : ℝ) : Measurable (thetaBracketFn a b c) := by
  unfold thetaBracketFn; fun_prop

theorem measurable_crossFn (a b c : ℝ) : Measurable (crossFn a b c) := by
  unfold crossFn; fun_prop

theorem continuousOn_thetaBracketFn (a b c : ℝ) : ContinuousOn (thetaBracketFn a b c) posSet₂ := by
  unfold thetaBracketFn
  exact ContinuousOn.div (by fun_prop) (by fun_prop) fun v hv => by
    have : (0 : ℝ) < v 0 ^ 2 + v 1 ^ 2 := hv
    positivity

theorem continuousOn_crossFn (a b c : ℝ) : ContinuousOn (crossFn a b c) posSet₂ := by
  unfold crossFn
  exact ContinuousOn.div (by fun_prop) (by fun_prop) fun v hv => by
    have : (0 : ℝ) < v 0 ^ 2 + v 1 ^ 2 := hv
    positivity

/-- `a sin² θ + b cos² θ - 2c sin θ cos θ`, the bracket density of `θ̂` in σ-time; it equals
`2 D(θ)` (`thetaBracketPolar_eq_two_mul_diffusionD`). -/
@[expose] noncomputable def thetaBracketPolar (a b c : ℝ) (θ : ℝ) : ℝ :=
  a * Real.sin θ ^ 2 + b * Real.cos θ ^ 2 - 2 * c * Real.sin θ * Real.cos θ

/-- `(b - a) sin θ cos θ + c (cos² θ - sin² θ)`, the cross bracket density in σ-time. -/
@[expose] noncomputable def crossPolar (a b c : ℝ) (θ : ℝ) : ℝ :=
  (b - a) * Real.sin θ * Real.cos θ + c * (Real.cos θ ^ 2 - Real.sin θ ^ 2)

theorem thetaBracketPolar_eq_two_mul_diffusionD (a b c θ : ℝ) :
    thetaBracketPolar a b c θ = 2 * diffusionD a b c θ := by
  unfold thetaBracketPolar diffusionD; ring

theorem continuous_thetaBracketPolar (a b c : ℝ) : Continuous (thetaBracketPolar a b c) := by
  unfold thetaBracketPolar; fun_prop

theorem continuous_crossPolar (a b c : ℝ) : Continuous (crossPolar a b c) := by
  unfold crossPolar; fun_prop

theorem continuous_mu (a b c : ℝ) : Continuous (mu a b c) := by
  unfold mu; fun_prop

/-- In polar coordinates, `thetaBracketFn = thetaBracketPolar θ / r²`. -/
theorem thetaBracketFn_polar (a b c : ℝ) {r θ : ℝ} (hr : 0 < r) :
    thetaBracketFn a b c ![r * Real.cos θ, r * Real.sin θ] = thetaBracketPolar a b c θ / r ^ 2 := by
  simp only [thetaBracketFn, thetaBracketPolar, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  have h1 : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
  rw [h1]
  have hr2 : r ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- In polar coordinates, `crossFn = crossPolar θ / r²`. -/
theorem crossFn_polar (a b c : ℝ) {r θ : ℝ} (hr : 0 < r) :
    crossFn a b c ![r * Real.cos θ, r * Real.sin θ] = crossPolar a b c θ / r ^ 2 := by
  simp only [crossFn, crossPolar, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  have h1 : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
  rw [h1]
  have hr2 : r ^ 2 ≠ 0 := by positivity
  field_simp

/-! ### `logRatio (w, v) = ½ log |w|² - ½ log |v|²` on `ℝ⁴` -/

/-- `logRatio u = ½ log (u₀² + u₁²) - ½ log (u₂² + u₃²)`. -/
@[expose] noncomputable def logRatio (u : Fin 4 → ℝ) : ℝ :=
  (1 / 2) * Real.log (u 0 ^ 2 + u 1 ^ 2) - (1 / 2) * Real.log (u 2 ^ 2 + u 3 ^ 2)

theorem measurable_logRatio : Measurable logRatio := by
  unfold logRatio; fun_prop

theorem contDiff_sq_add_sq₄ (a b : Fin 4) :
    ContDiff ℝ 2 fun u : Fin 4 → ℝ => u a ^ 2 + u b ^ 2 := by fun_prop

theorem contDiffOn_logRatio : ContDiffOn ℝ 2 logRatio argDomain := by
  unfold logRatio
  refine ContDiffOn.sub (contDiffOn_const.mul ?_) (contDiffOn_const.mul ?_)
  · exact (contDiff_sq_add_sq₄ 0 1).contDiffOn.log fun u hu => sq_add_sq_left_ne_zero hu
  · exact (contDiff_sq_add_sq₄ 2 3).contDiffOn.log fun u hu => sq_add_sq_right_ne_zero hu

/-- The gradient of `logRatio`: `(u₀/|w|², u₁/|w|², -u₂/|v|², -u₃/|v|²)`. -/
@[expose] noncomputable def gradLR (u : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![u 0 * (u 0 ^ 2 + u 1 ^ 2)⁻¹, u 1 * (u 0 ^ 2 + u 1 ^ 2)⁻¹,
    -(u 2 * (u 2 ^ 2 + u 3 ^ 2)⁻¹), -(u 3 * (u 2 ^ 2 + u 3 ^ 2)⁻¹)]

theorem hasFDerivAt_logRatio {u : Fin 4 → ℝ} (hu : u ∈ argDomain) :
    ∃ L : (Fin 4 → ℝ) →L[ℝ] ℝ, HasFDerivAt logRatio L u ∧
      ∀ e, L e = (1 / 2) * ((u 0 ^ 2 + u 1 ^ 2)⁻¹ * (2 * u 0 * e 0 + 2 * u 1 * e 1)) -
        (1 / 2) * ((u 2 ^ 2 + u 3 ^ 2)⁻¹ * (2 * u 2 * e 2 + 2 * u 3 * e 3)) := by
  obtain ⟨L0, hL0, hL0'⟩ := hasFDerivAt_sq_add_sq 0 1 u
  obtain ⟨L1, hL1, hL1'⟩ := hasFDerivAt_sq_add_sq 2 3 u
  refine ⟨_, ((hL0.log (sq_add_sq_left_ne_zero hu)).const_mul (1 / 2)).sub
    ((hL1.log (sq_add_sq_right_ne_zero hu)).const_mul (1 / 2)), fun e => ?_⟩
  simp [hL0', hL1']

theorem fderiv_logRatio_single {u : Fin 4 → ℝ} (hu : u ∈ argDomain) (i : Fin 4) :
    fderiv ℝ logRatio u (Pi.single i 1) = gradLR u i := by
  obtain ⟨L, hL, hL'⟩ := hasFDerivAt_logRatio hu
  rw [hL.fderiv, hL']
  fin_cases i <;> simp [gradLR] <;> ring

/-- The Hessian of `logRatio` (block diagonal), written as the derivative of the `j`-th component
of the gradient in direction `eᵢ`. -/
@[expose] noncomputable def hessLR (u : Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
  ![(Pi.single i 1 : Fin 4 → ℝ) 0 * (u 0 ^ 2 + u 1 ^ 2)⁻¹ + u 0 * (-((u 0 ^ 2 + u 1 ^ 2) ^ 2)⁻¹ *
      (2 * u 0 * (Pi.single i 1 : Fin 4 → ℝ) 0 + 2 * u 1 * (Pi.single i 1 : Fin 4 → ℝ) 1)),
    (Pi.single i 1 : Fin 4 → ℝ) 1 * (u 0 ^ 2 + u 1 ^ 2)⁻¹ + u 1 * (-((u 0 ^ 2 + u 1 ^ 2) ^ 2)⁻¹ *
      (2 * u 0 * (Pi.single i 1 : Fin 4 → ℝ) 0 + 2 * u 1 * (Pi.single i 1 : Fin 4 → ℝ) 1)),
    -((Pi.single i 1 : Fin 4 → ℝ) 2 * (u 2 ^ 2 + u 3 ^ 2)⁻¹ + u 2 * (-((u 2 ^ 2 + u 3 ^ 2) ^ 2)⁻¹ *
      (2 * u 2 * (Pi.single i 1 : Fin 4 → ℝ) 2 + 2 * u 3 * (Pi.single i 1 : Fin 4 → ℝ) 3))),
    -((Pi.single i 1 : Fin 4 → ℝ) 3 * (u 2 ^ 2 + u 3 ^ 2)⁻¹ + u 3 * (-((u 2 ^ 2 + u 3 ^ 2) ^ 2)⁻¹ *
      (2 * u 2 * (Pi.single i 1 : Fin 4 → ℝ) 2 + 2 * u 3 * (Pi.single i 1 : Fin 4 → ℝ) 3)))] j

theorem hasFDerivAt_gradLR {u : Fin 4 → ℝ} (hu : u ∈ argDomain) (j : Fin 4) :
    ∃ L : (Fin 4 → ℝ) →L[ℝ] ℝ, HasFDerivAt (fun w => gradLR w j) L u ∧
      ∀ i : Fin 4, L (Pi.single i 1) = hessLR u i j := by
  have hq0 := sq_add_sq_left_ne_zero hu
  have hq1 := sq_add_sq_right_ne_zero hu
  obtain ⟨L0, hL0, hL0'⟩ := hasFDerivAt_inv_sq_add_sq 0 1 hq0
  obtain ⟨L1, hL1, hL1'⟩ := hasFDerivAt_inv_sq_add_sq 2 3 hq1
  fin_cases j
  · refine ⟨_, (hasFDerivAt_apply (𝕜 := ℝ) 0 u).mul hL0, fun i => ?_⟩
    simp [hL0', hessLR]; ring
  · refine ⟨_, (hasFDerivAt_apply (𝕜 := ℝ) 1 u).mul hL0, fun i => ?_⟩
    simp [hL0', hessLR]; ring
  · refine ⟨_, ((hasFDerivAt_apply (𝕜 := ℝ) 2 u).mul hL1).neg, fun i => ?_⟩
    simp [hL1', hessLR]; ring
  · refine ⟨_, ((hasFDerivAt_apply (𝕜 := ℝ) 3 u).mul hL1).neg, fun i => ?_⟩
    simp [hL1', hessLR]; ring

theorem iteratedFDeriv_logRatio {u : Fin 4 → ℝ} (hu : u ∈ argDomain) (i j : Fin 4) :
    iteratedFDeriv ℝ 2 logRatio u ![Pi.single i 1, Pi.single j 1] = hessLR u i j := by
  obtain ⟨L, hL, hL'⟩ := hasFDerivAt_gradLR hu j
  rw [iteratedFDeriv_two_single isOpen_argDomain contDiffOn_logRatio hu
    (fun w hw => fderiv_logRatio_single hw j) hL, hL']

/-! ### The processes -/

section Processes

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

variable (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) (n : ℕ)

/-- The bracket density of `θ` stopped at `τ_n`: `1_{t ≤ τ_n} thetaBracketFn (f_t)`. -/
@[expose] noncomputable def thetaBracket (t : ℝ≥0) (ω : Ω) : ℝ :=
  beforeExit hU z n t ω * thetaBracketFn a b c (itoState hU z n t ω)

/-- The cross bracket density of `θ` and `log|f|` stopped at `τ_n`: `1_{t ≤ τ_n} crossFn (f_t)`. -/
@[expose] noncomputable def thetaLogCross (t : ℝ≥0) (ω : Ω) : ℝ :=
  beforeExit hU z n t ω * crossFn a b c (itoState hU z n t ω)

theorem isStronglyProgressive_thetaBracket : IsStronglyProgressive ℱ (thetaBracket hU z n) :=
  fun i => (isStronglyProgressive_beforeExit hU z n i).mul
    (((measurable_thetaBracketFn a b c).comp (isStronglyProgressive_itoState hU z n i).measurable)
      |>.stronglyMeasurable)

theorem isStronglyProgressive_thetaLogCross : IsStronglyProgressive ℱ (thetaLogCross hU z n) :=
  fun i => (isStronglyProgressive_beforeExit hU z n i).mul
    (((measurable_crossFn a b c).comp (isStronglyProgressive_itoState hU z n i).measurable)
      |>.stronglyMeasurable)

theorem isStronglyProgressive_logBracket : IsStronglyProgressive ℱ (logBracket hU z n) :=
  fun i => (isStronglyProgressive_beforeExit hU z n i).mul
    (((measurable_gammaFn a b c).comp (isStronglyProgressive_itoState hU z n i).measurable)
      |>.stronglyMeasurable)

theorem intervalIntegrable_thetaBracket (ω : Ω) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => thetaBracket hU z n s.toNNReal ω) volume 0 t :=
  intervalIntegrable_beforeExit_mul hU z n (continuousOn_thetaBracketFn a b c) ω t

theorem intervalIntegrable_thetaLogCross (ω : Ω) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => thetaLogCross hU z n s.toNNReal ω) volume 0 t :=
  intervalIntegrable_beforeExit_mul hU z n (continuousOn_crossFn a b c) ω t

theorem intervalIntegrable_logBracket (ω : Ω) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => logBracket hU z n s.toNNReal ω) volume 0 t :=
  intervalIntegrable_beforeExit_mul hU z n (continuousOn_gammaFn a b c) ω t

theorem intervalIntegrable_logDrift (ω : Ω) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => logDrift hU z n s.toNNReal ω) volume 0 t :=
  intervalIntegrable_beforeExit_mul hU z n (continuousOn_betaFn a b c) ω t

/-- `∫₀ᵗ 1_{s ≤ τ_n} thetaBracketFn (f_s) ds = ∫₀^{t ∧ τ_n} thetaBracketFn (f_s) ds`. -/
theorem pathIntegral_thetaBracket (ω : Ω) (t : ℝ≥0) :
    pathIntegral (thetaBracket hU z n) t ω =
      pathIntegral (fun s ω => thetaBracketFn a b c (itoState hU z n s ω))
        (min t (exitNN hU z n ω)) ω :=
  pathIntegral_beforeExit_mul hU z n ω t

theorem pathIntegral_thetaLogCross (ω : Ω) (t : ℝ≥0) :
    pathIntegral (thetaLogCross hU z n) t ω =
      pathIntegral (fun s ω => crossFn a b c (itoState hU z n s ω)) (min t (exitNN hU z n ω)) ω :=
  pathIntegral_beforeExit_mul hU z n ω t

/-- The bracket density in polar form: on `{T_z > 0}` and for `t ≤ τ_n`,
`thetaBracket t = (a sin² θ_t + b cos² θ_t - 2c sin θ_t cos θ_t) / |f_t|²`. -/
theorem thetaBracket_eq_polar {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) {t : ℝ≥0}
    (ht : (t : ℝ) ≤ exitR hU z n ω) :
    thetaBracket hU z n t ω =
      thetaBracketPolar a b c (argPath (fun s => U s ω) (hU.cont ω) z t) /
        ‖fPath (fun s => U s ω) (hU.cont ω) z t‖ ^ 2 := by
  have h1 : beforeExit hU z n t ω = 1 := by
    simp [beforeExit, (le_exitNN_iff hU z n).2 ht]
  rw [thetaBracket, h1, one_mul, itoState_eq_polar hU z n hz, min_eq_left ht,
    thetaBracketFn_polar _ _ _ (norm_pos_iff.2 (stoppedF_ne_zero hU z n hz t)),
    stoppedF_eq_of_le hU z n hz ht]

/-- The cross bracket density in polar form: on `{T_z > 0}` and for `t ≤ τ_n`,
`thetaLogCross t = ((b - a) sin θ_t cos θ_t + c (cos² θ_t - sin² θ_t)) / |f_t|²`. -/
theorem thetaLogCross_eq_polar {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) {t : ℝ≥0}
    (ht : (t : ℝ) ≤ exitR hU z n ω) :
    thetaLogCross hU z n t ω =
      crossPolar a b c (argPath (fun s => U s ω) (hU.cont ω) z t) /
        ‖fPath (fun s => U s ω) (hU.cont ω) z t‖ ^ 2 := by
  have h1 : beforeExit hU z n t ω = 1 := by
    simp [beforeExit, (le_exitNN_iff hU z n).2 ht]
  rw [thetaLogCross, h1, one_mul, itoState_eq_polar hU z n hz, min_eq_left ht,
    crossFn_polar _ _ _ (norm_pos_iff.2 (stoppedF_ne_zero hU z n hz t)),
    stoppedF_eq_of_le hU z n hz ht]

/-! ### `logRatio` on the sector state -/

variable (k : ℕ)

theorem logNormF_eq_half_log (t : ℝ≥0) (ω : Ω) :
    logNormF hU z n t ω =
      (1 / 2) * Real.log ((stoppedF hU z n t ω).re ^ 2 + (stoppedF hU z n t ω).im ^ 2) := by
  have h : (stoppedF hU z n t ω).re ^ 2 + (stoppedF hU z n t ω).im ^ 2 =
      ‖stoppedF hU z n t ω‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [logNormF, h, Real.log_pow]
  push_cast
  ring

/-- **The pathwise identity** `logRatio (X_t) = log|f_{t ∧ S_{k+1}}| - log|f_{t ∧ S_k}|`. -/
theorem logRatio_secState (t : ℝ≥0) (ω : Ω) :
    logRatio (secState hU z n k t ω) =
      logNormF hU z n (min t (sectorTime hU z n (k + 1) ω)) ω -
        logNormF hU z n (min t (sectorTime hU z n k ω)) ω := by
  simp only [logRatio, secState, secStop, itoState, reIm, logNormF_eq_half_log]
  simp

theorem continuous_logRatio_secState (ω : Ω) :
    Continuous fun t => logRatio (secState hU z n k t ω) := by
  simp only [logRatio_secState]
  exact ((continuous_logNormF hU z n ω).comp (continuous_id.min continuous_const)).sub
    ((continuous_logNormF hU z n ω).comp (continuous_id.min continuous_const))

theorem continuous_argProd_secState (ω : Ω) :
    Continuous fun t => argProd (secState hU z n k t ω) := by
  simp only [argProd_secState]
  exact ((continuous_argStopped hU z n ω).comp (continuous_id.min continuous_const)).sub
    ((continuous_argStopped hU z n ω).comp (continuous_id.min continuous_const))

theorem secQ_symm (s : ℝ≥0) (ω : Ω) (i j : Fin 4) :
    secQ hU z n k s ω i j = secQ hU z n k s ω j i := by
  have e : (fun ω => min (secStop hU z n k i ω) (secStop hU z n k j ω)) =
      fun ω => min (secStop hU z n k j ω) (secStop hU z n k i ω) := funext fun ω => min_comm _ _
  simp only [secQ_apply, e, covMatrix_comm (toFin2 i)]

/-! ### The integrand identities -/

/-- `∇argProdᵀ Q ∇argProd` at the sector state is `(1_{s ≤ S_{k+1}} - 1_{s ≤ S_k}) thetaBracket`. -/
theorem bracket_integrand_argProd (ω : Ω) (s : ℝ≥0)
    (hs : 0 < absorbingTime (fun r => U r ω) z ∨ 0 < s) :
    ∑ i, ∑ j, fderiv ℝ argProd (secState hU z n k s ω) (Pi.single i 1) *
        fderiv ℝ argProd (secState hU z n k s ω) (Pi.single j 1) * secQ hU z n k s ω i j =
      beforeTime (sectorTime hU z n (k + 1)) s ω * thetaBracket hU z n s ω -
        beforeTime (sectorTime hU z n k) s ω * thetaBracket hU z n s ω := by
  by_cases hz : 0 < absorbingTime (fun r => U r ω) z
  · have hD := secState_mem_argDomain hU z n k hz s
    simp only [fderiv_argProd_single hD, Fin.sum_univ_four, secQ_apply]
    have hq : ∀ r : ℝ≥0, (stoppedF hU z n r ω).re ^ 2 + (stoppedF hU z n r ω).im ^ 2 ≠ 0 :=
      fun r => ne_of_gt (itoState_mem_posSet₂ hU z n hz r)
    by_cases hsσ : s ≤ sectorTime hU z n (k + 1) ω
    · have hsτ : s ≤ exitNN hU z n ω := le_trans hsσ (sectorTime_le_exitNN hU z n _ ω)
      have hγ : beforeExit hU z n s ω = 1 := by simp [beforeExit, hsτ]
      have e1 : min s (sectorTime hU z n (k + 1) ω) = s := min_eq_left hsσ
      by_cases hsρ : s ≤ sectorTime hU z n k ω
      · have e2 : min s (sectorTime hU z n k ω) = s := min_eq_left hsρ
        have hs2 := hq s
        simp [secState, secStop, beforeTime, hsσ, hsρ, gradArg, thetaBracket, hγ,
          thetaBracketFn, covMatrix, itoState, reIm]
      · have hρs : sectorTime hU z n k ω < s := lt_of_not_ge hsρ
        have e2 : min s (sectorTime hU z n k ω) = sectorTime hU z n k ω :=
          min_eq_right (le_of_lt hρs)
        have hs2 := hq s
        have hρ2 := hq (sectorTime hU z n k ω)
        simp [secState, secStop, beforeTime, hsσ, hsρ, e2, gradArg, thetaBracket, hγ,
          thetaBracketFn, covMatrix, itoState, reIm]
        field_simp
        ring
    · have hsρ : ¬ s ≤ sectorTime hU z n k ω := fun h =>
        hsσ (le_trans h (sectorTime_le_succ hU z n k ω))
      simp [beforeTime, hsσ, hsρ, secStop]
  · have hs' : 0 < s := hs.resolve_left hz
    have hτ0 : exitNN hU z n ω = 0 := by
      rw [exitNN, exitR_eq_zero hU z n hz, Real.toNNReal_zero]
    have hσ0 : sectorTime hU z n (k + 1) ω = 0 :=
      le_antisymm (hτ0 ▸ sectorTime_le_exitNN hU z n _ ω) zero_le
    have hρ0 : sectorTime hU z n k ω = 0 :=
      le_antisymm (hτ0 ▸ sectorTime_le_exitNN hU z n _ ω) zero_le
    have hns : ¬ s ≤ (0 : ℝ≥0) := not_le.2 hs'
    simp [Fin.sum_univ_four, secQ_apply, beforeTime, secStop, hσ0, hρ0, hns]

/-- **The Itô integrand of `logRatio`** at the sector state is `(1_{s ≤ S_{k+1}} - 1_{s ≤ S_k})`
times the drift density `logDrift` (`eqn-abs-zt-op`). -/
theorem ito_integrand_logRatio (ω : Ω) (s : ℝ≥0)
    (hs : 0 < absorbingTime (fun r => U r ω) z ∨ 0 < s) :
    ∑ i, fderiv ℝ logRatio (secState hU z n k s ω) (Pi.single i 1) * secDrift hU z n k s ω i +
      (1 / 2) * ∑ i, ∑ j, iteratedFDeriv ℝ 2 logRatio (secState hU z n k s ω)
        ![Pi.single i 1, Pi.single j 1] * secQ hU z n k s ω i j =
      beforeTime (sectorTime hU z n (k + 1)) s ω * logDrift hU z n s ω -
        beforeTime (sectorTime hU z n k) s ω * logDrift hU z n s ω := by
  by_cases hz : 0 < absorbingTime (fun r => U r ω) z
  · have hD := secState_mem_argDomain hU z n k hz s
    simp only [fderiv_logRatio_single hD, iteratedFDeriv_logRatio hD, Fin.sum_univ_four,
      secQ_apply]
    have hq : ∀ r : ℝ≥0, (stoppedF hU z n r ω).re ^ 2 + (stoppedF hU z n r ω).im ^ 2 ≠ 0 :=
      fun r => ne_of_gt (itoState_mem_posSet₂ hU z n hz r)
    have hq' : ∀ r : ℝ≥0, (stoppedF hU z n r ω).re * (stoppedF hU z n r ω).re +
        (stoppedF hU z n r ω).im * (stoppedF hU z n r ω).im ≠ 0 := fun r => by
      rw [← sq, ← sq]; exact hq r
    by_cases hsσ : s ≤ sectorTime hU z n (k + 1) ω
    · have hsτ : s ≤ exitNN hU z n ω := le_trans hsσ (sectorTime_le_exitNN hU z n _ ω)
      have hγ : beforeExit hU z n s ω = 1 := by simp [beforeExit, hsτ]
      have e1 : min s (sectorTime hU z n (k + 1) ω) = s := min_eq_left hsσ
      by_cases hsρ : s ≤ sectorTime hU z n k ω
      · have e2 : min s (sectorTime hU z n k ω) = s := min_eq_left hsρ
        have hs2 := hq s
        have hs2' := hq' s
        simp [secDrift, secState, secStop, beforeTime, hsσ, hsρ, gradLR, hessLR,
          itoDrift, logDrift, hγ, betaFn, covMatrix, itoState, reIm, Complex.div_re,
          Complex.div_im, Complex.normSq_apply]
        field_simp
        ring
      · have hρs : sectorTime hU z n k ω < s := lt_of_not_ge hsρ
        have e2 : min s (sectorTime hU z n k ω) = sectorTime hU z n k ω :=
          min_eq_right (le_of_lt hρs)
        have hs2 := hq s
        have hs2' := hq' s
        have hρ2 := hq (sectorTime hU z n k ω)
        have hρ2' := hq' (sectorTime hU z n k ω)
        simp [secDrift, secState, secStop, beforeTime, hsσ, hsρ, e2, gradLR, hessLR,
          itoDrift, logDrift, hγ, betaFn, covMatrix, itoState, reIm, Complex.div_re,
          Complex.div_im, Complex.normSq_apply]
        field_simp
        ring
    · have hsρ : ¬ s ≤ sectorTime hU z n k ω := fun h =>
        hsσ (le_trans h (sectorTime_le_succ hU z n k ω))
      simp [secDrift, beforeTime, hsσ, hsρ, secStop]
  · have hs' : 0 < s := hs.resolve_left hz
    have hτ0 : exitNN hU z n ω = 0 := by
      rw [exitNN, exitR_eq_zero hU z n hz, Real.toNNReal_zero]
    have hσ0 : sectorTime hU z n (k + 1) ω = 0 :=
      le_antisymm (hτ0 ▸ sectorTime_le_exitNN hU z n _ ω) zero_le
    have hρ0 : sectorTime hU z n k ω = 0 :=
      le_antisymm (hτ0 ▸ sectorTime_le_exitNN hU z n _ ω) zero_le
    have hns : ¬ s ≤ (0 : ℝ≥0) := not_le.2 hs'
    simp [Fin.sum_univ_four, secDrift, secQ_apply, beforeTime, secStop, hσ0, hρ0, hns]

/-- `∇argProdᵀ Q ∇logRatio` at the sector state is
`(1_{s ≤ S_{k+1}} - 1_{s ≤ S_k}) thetaLogCross`. -/
theorem cross_integrand_argProd_logRatio (ω : Ω) (s : ℝ≥0)
    (hs : 0 < absorbingTime (fun r => U r ω) z ∨ 0 < s) :
    ∑ i, ∑ j, fderiv ℝ argProd (secState hU z n k s ω) (Pi.single i 1) *
        fderiv ℝ logRatio (secState hU z n k s ω) (Pi.single j 1) * secQ hU z n k s ω i j =
      beforeTime (sectorTime hU z n (k + 1)) s ω * thetaLogCross hU z n s ω -
        beforeTime (sectorTime hU z n k) s ω * thetaLogCross hU z n s ω := by
  by_cases hz : 0 < absorbingTime (fun r => U r ω) z
  · have hD := secState_mem_argDomain hU z n k hz s
    simp only [fderiv_argProd_single hD, fderiv_logRatio_single hD, Fin.sum_univ_four, secQ_apply]
    have hq : ∀ r : ℝ≥0, (stoppedF hU z n r ω).re ^ 2 + (stoppedF hU z n r ω).im ^ 2 ≠ 0 :=
      fun r => ne_of_gt (itoState_mem_posSet₂ hU z n hz r)
    by_cases hsσ : s ≤ sectorTime hU z n (k + 1) ω
    · have hsτ : s ≤ exitNN hU z n ω := le_trans hsσ (sectorTime_le_exitNN hU z n _ ω)
      have hγ : beforeExit hU z n s ω = 1 := by simp [beforeExit, hsτ]
      have e1 : min s (sectorTime hU z n (k + 1) ω) = s := min_eq_left hsσ
      by_cases hsρ : s ≤ sectorTime hU z n k ω
      · have e2 : min s (sectorTime hU z n k ω) = s := min_eq_left hsρ
        have hs2 := hq s
        simp [secState, secStop, beforeTime, hsσ, hsρ, gradArg, gradLR, thetaLogCross,
          hγ, crossFn, covMatrix, itoState, reIm]
      · have hρs : sectorTime hU z n k ω < s := lt_of_not_ge hsρ
        have e2 : min s (sectorTime hU z n k ω) = sectorTime hU z n k ω :=
          min_eq_right (le_of_lt hρs)
        have hs2 := hq s
        have hρ2 := hq (sectorTime hU z n k ω)
        simp [secState, secStop, beforeTime, hsσ, hsρ, e2, gradArg, gradLR, thetaLogCross,
          hγ, crossFn, covMatrix, itoState, reIm]
        field_simp
        ring
    · have hsρ : ¬ s ≤ sectorTime hU z n k ω := fun h =>
        hsσ (le_trans h (sectorTime_le_succ hU z n k ω))
      simp [beforeTime, hsσ, hsρ, secStop]
  · have hs' : 0 < s := hs.resolve_left hz
    have hτ0 : exitNN hU z n ω = 0 := by
      rw [exitNN, exitR_eq_zero hU z n hz, Real.toNNReal_zero]
    have hσ0 : sectorTime hU z n (k + 1) ω = 0 :=
      le_antisymm (hτ0 ▸ sectorTime_le_exitNN hU z n _ ω) zero_le
    have hρ0 : sectorTime hU z n k ω = 0 :=
      le_antisymm (hτ0 ▸ sectorTime_le_exitNN hU z n _ ω) zero_le
    have hns : ¬ s ≤ (0 : ℝ≥0) := not_le.2 hs'
    simp [Fin.sum_univ_four, secQ_apply, beforeTime, secStop, hσ0, hρ0, hns]

/-- `∇logRatioᵀ Q ∇logRatio` at the sector state is `(1_{s ≤ S_{k+1}} - 1_{s ≤ S_k}) logBracket`. -/
theorem bracket_integrand_logRatio (ω : Ω) (s : ℝ≥0)
    (hs : 0 < absorbingTime (fun r => U r ω) z ∨ 0 < s) :
    ∑ i, ∑ j, fderiv ℝ logRatio (secState hU z n k s ω) (Pi.single i 1) *
        fderiv ℝ logRatio (secState hU z n k s ω) (Pi.single j 1) * secQ hU z n k s ω i j =
      beforeTime (sectorTime hU z n (k + 1)) s ω * logBracket hU z n s ω -
        beforeTime (sectorTime hU z n k) s ω * logBracket hU z n s ω := by
  by_cases hz : 0 < absorbingTime (fun r => U r ω) z
  · have hD := secState_mem_argDomain hU z n k hz s
    simp only [fderiv_logRatio_single hD, Fin.sum_univ_four, secQ_apply]
    have hq : ∀ r : ℝ≥0, (stoppedF hU z n r ω).re ^ 2 + (stoppedF hU z n r ω).im ^ 2 ≠ 0 :=
      fun r => ne_of_gt (itoState_mem_posSet₂ hU z n hz r)
    by_cases hsσ : s ≤ sectorTime hU z n (k + 1) ω
    · have hsτ : s ≤ exitNN hU z n ω := le_trans hsσ (sectorTime_le_exitNN hU z n _ ω)
      have hγ : beforeExit hU z n s ω = 1 := by simp [beforeExit, hsτ]
      have e1 : min s (sectorTime hU z n (k + 1) ω) = s := min_eq_left hsσ
      by_cases hsρ : s ≤ sectorTime hU z n k ω
      · have e2 : min s (sectorTime hU z n k ω) = s := min_eq_left hsρ
        have hs2 := hq s
        simp [secState, secStop, beforeTime, hsσ, hsρ, gradLR, logBracket, hγ,
          gammaFn, covMatrix, itoState, reIm]
      · have hρs : sectorTime hU z n k ω < s := lt_of_not_ge hsρ
        have e2 : min s (sectorTime hU z n k ω) = sectorTime hU z n k ω :=
          min_eq_right (le_of_lt hρs)
        have hs2 := hq s
        have hρ2 := hq (sectorTime hU z n k ω)
        simp [secState, secStop, beforeTime, hsσ, hsρ, e2, gradLR, logBracket, hγ,
          gammaFn, covMatrix, itoState, reIm]
        field_simp
        ring
    · have hsρ : ¬ s ≤ sectorTime hU z n k ω := fun h =>
        hsσ (le_trans h (sectorTime_le_succ hU z n k ω))
      simp [beforeTime, hsσ, hsρ, secStop]
  · have hs' : 0 < s := hs.resolve_left hz
    have hτ0 : exitNN hU z n ω = 0 := by
      rw [exitNN, exitR_eq_zero hU z n hz, Real.toNNReal_zero]
    have hσ0 : sectorTime hU z n (k + 1) ω = 0 :=
      le_antisymm (hτ0 ▸ sectorTime_le_exitNN hU z n _ ω) zero_le
    have hρ0 : sectorTime hU z n k ω = 0 :=
      le_antisymm (hτ0 ▸ sectorTime_le_exitNN hU z n _ ω) zero_le
    have hns : ¬ s ≤ (0 : ℝ≥0) := not_le.2 hs'
    simp [Fin.sum_univ_four, secQ_apply, beforeTime, secStop, hσ0, hρ0, hns]

/-! ### The sector increments of the integrated densities -/

/-- `(1_{s ≤ σ} - 1_{s ≤ ρ}) ξ_s` integrated: `∫₀^{t ∧ σ} ξ - ∫₀^{t ∧ ρ} ξ`. -/
theorem pathIntegral_sector_sub {ξ : ℝ≥0 → Ω → ℝ} (ω : Ω) (t : ℝ≥0)
    (hξ : IntervalIntegrable (fun s : ℝ => ξ s.toNNReal ω) volume 0 t) :
    pathIntegral (fun s ω => beforeTime (sectorTime hU z n (k + 1)) s ω * ξ s ω -
      beforeTime (sectorTime hU z n k) s ω * ξ s ω) t ω =
      pathIntegral ξ (min t (sectorTime hU z n (k + 1) ω)) ω -
        pathIntegral ξ (min t (sectorTime hU z n k ω)) ω := by
  rw [pathIntegral_sub (intervalIntegrable_beforeTime_mul _ ω hξ)
    (intervalIntegrable_beforeTime_mul _ ω hξ), pathIntegral_beforeTime_mul,
    pathIntegral_beforeTime_mul]

theorem isStronglyProgressive_sector_sub {ξ : ℝ≥0 → Ω → ℝ} (hξ : IsStronglyProgressive ℱ ξ) :
    IsStronglyProgressive ℱ fun s ω => beforeTime (sectorTime hU z n (k + 1)) s ω * ξ s ω -
      beforeTime (sectorTime hU z n k) s ω * ξ s ω := fun i =>
  ((isStronglyProgressive_beforeTime (isStoppingTime_sectorTime hU z n (k + 1)) i).mul (hξ i)).sub
    ((isStronglyProgressive_beforeTime (isStoppingTime_sectorTime hU z n k) i).mul (hξ i))

theorem intervalIntegrable_sector_sub {ξ : ℝ≥0 → Ω → ℝ} (ω : Ω) (t : ℝ≥0)
    (hξ : IntervalIntegrable (fun s : ℝ => ξ s.toNNReal ω) volume 0 t) :
    IntervalIntegrable (fun s : ℝ => beforeTime (sectorTime hU z n (k + 1)) s.toNNReal ω *
      ξ s.toNNReal ω - beforeTime (sectorTime hU z n k) s.toNNReal ω * ξ s.toNNReal ω)
      volume 0 t :=
  (intervalIntegrable_beforeTime_mul _ ω hξ).sub (intervalIntegrable_beforeTime_mul _ ω hξ)

/-- `argProd (X_t) - argProd (X_0) - ∫ (1_σ - 1_ρ) thetaDrift =
Θ^n_{t ∧ S_{k+1}} - Θ^n_{t ∧ S_k}`. -/
theorem argProd_secState_sub_eq (t : ℝ≥0) (ω : Ω) :
    argProd (secState hU z n k t ω) - argProd (secState hU z n k 0 ω) -
      pathIntegral (fun s ω => beforeTime (sectorTime hU z n (k + 1)) s ω * thetaDrift hU z n s ω -
        beforeTime (sectorTime hU z n k) s ω * thetaDrift hU z n s ω) t ω =
      thetaMart hU z n (min t (sectorTime hU z n (k + 1) ω)) ω -
        thetaMart hU z n (min t (sectorTime hU z n k ω)) ω := by
  rw [argProd_secState, argProd_secState, min_eq_left zero_le, min_eq_left zero_le, sub_self,
    sub_zero, pathIntegral_sector_sub hU z n k ω t (intervalIntegrable_thetaDrift hU z n ω t)]
  simp only [thetaMart]
  ring

/-- `logRatio (X_t) - logRatio (X_0) - ∫ (1_σ - 1_ρ) logDrift =
N^n_{t ∧ S_{k+1}} - N^n_{t ∧ S_k}`. -/
theorem logRatio_secState_sub_eq (t : ℝ≥0) (ω : Ω) :
    logRatio (secState hU z n k t ω) - logRatio (secState hU z n k 0 ω) -
      pathIntegral (fun s ω => beforeTime (sectorTime hU z n (k + 1)) s ω * logDrift hU z n s ω -
        beforeTime (sectorTime hU z n k) s ω * logDrift hU z n s ω) t ω =
      logMart hU z n (min t (sectorTime hU z n (k + 1) ω)) ω -
        logMart hU z n (min t (sectorTime hU z n k ω)) ω := by
  rw [logRatio_secState, logRatio_secState, min_eq_left zero_le, min_eq_left zero_le, sub_self,
    sub_zero, pathIntegral_sector_sub hU z n k ω t (intervalIntegrable_logDrift hU z n ω t)]
  simp only [logMart]
  ring

/-! ### Applying the generic bracket lemmas -/

variable [IsProbabilityMeasure P]

/-- **The bracket of the sector increment of `Θ^n`**: for `0 < a`, `c² ≤ ab`, `z ≠ 0`,
`(Θ^n_{t ∧ S_{k+1}} - Θ^n_{t ∧ S_k})² - (B_{t ∧ S_{k+1}} - B_{t ∧ S_k})` is a continuous local
martingale, where `B_t = ∫₀ᵗ 1_{s ≤ τ_n} thetaBracketFn (f_s) ds`. -/
theorem isContLocalMartingale_sectorIncrement_sq (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) :
    IsContLocalMartingale ℱ (fun t ω =>
      (thetaMart hU z n (min t (sectorTime hU z n (k + 1) ω)) ω -
        thetaMart hU z n (min t (sectorTime hU z n k ω)) ω) ^ 2 -
      (pathIntegral (thetaBracket hU z n) (min t (sectorTime hU z n (k + 1) ω)) ω -
        pathIntegral (thetaBracket hU z n) (min t (sectorTime hU z n k ω)) ω)) P := by
  have hAint : ∀ᵐ ω ∂P, ∀ (i : Fin 4) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => secDrift hU z n k (Real.toNNReal s) ω i) volume 0 t :=
    Eventually.of_forall fun ω i t => intervalIntegrable_secDrift hU z n k ω i t
  have hQint : ∀ᵐ ω ∂P, ∀ (i j : Fin 4) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => secQ hU z n k (Real.toNNReal s) ω i j) volume 0 t :=
    Eventually.of_forall fun ω i j t => intervalIntegrable_secQ hU z n k ω i j t
  have hXD : ∀ᵐ ω ∂P, ∀ t, secState hU z n k t ω ∈ argDomain := by
    filter_upwards [ae_pos_absorbingTime hU z hz] with ω hω
    exact fun t => secState_mem_argDomain hU z n k hω t
  have hLint := fun ω t => intervalIntegrable_sector_sub hU z n k ω t
    (intervalIntegrable_thetaDrift hU z n ω t)
  have h := isContLocalMartingale_sq_sub_of_ito (secState hU z n k) (secDrift hU z n k)
    (secQ hU z n k) (isStronglyProgressive_secState hU z n k) (continuous_secState hU z n k)
    (isStronglyProgressive_secDrift hU z n k) hAint (isStronglyProgressive_secQ hU z n k) hQint
    (ito_hM_sec hU z n k) (ito_hMM_sec hU z n k ha hc) argDomain isOpen_argDomain argProd
    measurable_argProd contDiffOn_argProd hXD
    (fun s ω => beforeTime (sectorTime hU z n (k + 1)) s ω * thetaDrift hU z n s ω -
      beforeTime (sectorTime hU z n k) s ω * thetaDrift hU z n s ω)
    (fun s ω => beforeTime (sectorTime hU z n (k + 1)) s ω * thetaBracket hU z n s ω -
      beforeTime (sectorTime hU z n k) s ω * thetaBracket hU z n s ω)
    (isStronglyProgressive_sector_sub hU z n k (isStronglyProgressive_thetaDrift hU z n))
    (isStronglyProgressive_sector_sub hU z n k (isStronglyProgressive_thetaBracket hU z n))
    hLint (fun ω => continuous_pathIntegral' (hLint ω))
    (fun ω _ s hs => (ito_integrand_argProd hU z n k ω s (Or.inr hs)).symm)
    (fun ω _ s hs => (bracket_integrand_argProd hU z n k ω s (Or.inr hs)).symm)
  refine h.congr_fun' fun t ω => ?_
  rw [argProd_secState_sub_eq,
    pathIntegral_sector_sub hU z n k ω t (intervalIntegrable_thetaBracket hU z n ω t)]

/-- **The cross bracket of the sector increments of `Θ^n` and `N^n`**: for `0 < a`, `c² ≤ ab`,
`z ≠ 0`, `(Θ^n_{t ∧ S_{k+1}} - Θ^n_{t ∧ S_k}) (N^n_{t ∧ S_{k+1}} - N^n_{t ∧ S_k}) -
(C_{t ∧ S_{k+1}} - C_{t ∧ S_k})` is a continuous local martingale, where
`C_t = ∫₀ᵗ 1_{s ≤ τ_n} crossFn (f_s) ds`. -/
theorem isContLocalMartingale_sectorIncrement_mul (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) :
    IsContLocalMartingale ℱ (fun t ω =>
      (thetaMart hU z n (min t (sectorTime hU z n (k + 1) ω)) ω -
        thetaMart hU z n (min t (sectorTime hU z n k ω)) ω) *
      (logMart hU z n (min t (sectorTime hU z n (k + 1) ω)) ω -
        logMart hU z n (min t (sectorTime hU z n k ω)) ω) -
      (pathIntegral (thetaLogCross hU z n) (min t (sectorTime hU z n (k + 1) ω)) ω -
        pathIntegral (thetaLogCross hU z n) (min t (sectorTime hU z n k ω)) ω)) P := by
  have hAint : ∀ᵐ ω ∂P, ∀ (i : Fin 4) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => secDrift hU z n k (Real.toNNReal s) ω i) volume 0 t :=
    Eventually.of_forall fun ω i t => intervalIntegrable_secDrift hU z n k ω i t
  have hQint : ∀ᵐ ω ∂P, ∀ (i j : Fin 4) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => secQ hU z n k (Real.toNNReal s) ω i j) volume 0 t :=
    Eventually.of_forall fun ω i j t => intervalIntegrable_secQ hU z n k ω i j t
  have hXD : ∀ᵐ ω ∂P, ∀ t, secState hU z n k t ω ∈ argDomain := by
    filter_upwards [ae_pos_absorbingTime hU z hz] with ω hω
    exact fun t => secState_mem_argDomain hU z n k hω t
  have hL₁int := fun ω t => intervalIntegrable_sector_sub hU z n k ω t
    (intervalIntegrable_thetaDrift hU z n ω t)
  have hL₂int := fun ω t => intervalIntegrable_sector_sub hU z n k ω t
    (intervalIntegrable_logDrift hU z n ω t)
  have h := isContLocalMartingale_mul_sub_of_ito (secState hU z n k) (secDrift hU z n k)
    (secQ hU z n k) (isStronglyProgressive_secState hU z n k) (continuous_secState hU z n k)
    (isStronglyProgressive_secDrift hU z n k) hAint (isStronglyProgressive_secQ hU z n k) hQint
    (secQ_symm hU z n k) (ito_hM_sec hU z n k) (ito_hMM_sec hU z n k ha hc) argDomain
    isOpen_argDomain argProd logRatio measurable_argProd measurable_logRatio contDiffOn_argProd
    contDiffOn_logRatio hXD (continuous_argProd_secState hU z n k)
    (continuous_logRatio_secState hU z n k)
    (fun s ω => beforeTime (sectorTime hU z n (k + 1)) s ω * thetaDrift hU z n s ω -
      beforeTime (sectorTime hU z n k) s ω * thetaDrift hU z n s ω)
    (fun s ω => beforeTime (sectorTime hU z n (k + 1)) s ω * logDrift hU z n s ω -
      beforeTime (sectorTime hU z n k) s ω * logDrift hU z n s ω)
    (fun s ω => beforeTime (sectorTime hU z n (k + 1)) s ω * thetaBracket hU z n s ω -
      beforeTime (sectorTime hU z n k) s ω * thetaBracket hU z n s ω)
    (fun s ω => beforeTime (sectorTime hU z n (k + 1)) s ω * thetaLogCross hU z n s ω -
      beforeTime (sectorTime hU z n k) s ω * thetaLogCross hU z n s ω)
    (fun s ω => beforeTime (sectorTime hU z n (k + 1)) s ω * logBracket hU z n s ω -
      beforeTime (sectorTime hU z n k) s ω * logBracket hU z n s ω)
    (isStronglyProgressive_sector_sub hU z n k (isStronglyProgressive_thetaDrift hU z n))
    (isStronglyProgressive_sector_sub hU z n k (isStronglyProgressive_logDrift hU z n))
    (isStronglyProgressive_sector_sub hU z n k (isStronglyProgressive_thetaBracket hU z n))
    (isStronglyProgressive_sector_sub hU z n k (isStronglyProgressive_thetaLogCross hU z n))
    (isStronglyProgressive_sector_sub hU z n k (isStronglyProgressive_logBracket hU z n))
    hL₁int hL₂int
    (fun ω t => intervalIntegrable_sector_sub hU z n k ω t
      (intervalIntegrable_thetaBracket hU z n ω t))
    (fun ω t => intervalIntegrable_sector_sub hU z n k ω t
      (intervalIntegrable_thetaLogCross hU z n ω t))
    (fun ω t => intervalIntegrable_sector_sub hU z n k ω t
      (intervalIntegrable_logBracket hU z n ω t))
    (fun ω => continuous_pathIntegral' (hL₁int ω)) (fun ω => continuous_pathIntegral' (hL₂int ω))
    (fun ω _ s hs => (ito_integrand_argProd hU z n k ω s (Or.inr hs)).symm)
    (fun ω _ s hs => (ito_integrand_logRatio hU z n k ω s (Or.inr hs)).symm)
    (fun ω _ s hs => (bracket_integrand_argProd hU z n k ω s (Or.inr hs)).symm)
    (fun ω _ s hs => (cross_integrand_argProd_logRatio hU z n k ω s (Or.inr hs)).symm)
    (fun ω _ s hs => (bracket_integrand_logRatio hU z n k ω s (Or.inr hs)).symm)
  refine h.congr_fun' fun t ω => ?_
  rw [argProd_secState_sub_eq, logRatio_secState_sub_eq,
    pathIntegral_sector_sub hU z n k ω t (intervalIntegrable_thetaLogCross hU z n ω t)]

end Processes

end ComplexSLE.Internal.Polar

end
