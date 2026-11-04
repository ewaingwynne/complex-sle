/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.PolarItoState
public import ComplexSLE.Internal.Polar.PolarItoCalculus
public import ComplexSLE.External.ItoFormula
public import ComplexSLE.Frozen.Defs.Nu

/-!
# Itô's formula for `log|f_t(z)|` stopped at `τ_n` (M6/S8; `step:polar-ito-log`,
`step:polar-real-imag`, real part)

For an adapted `SLE_Σ` driver (`0 < a`, `c² ≤ ab`) and `z ≠ 0`, with `τ_n` the annulus exit time,
we apply the external Itô formula E1 (`External.ito_formula`) to the `ℝ³`-valued state
`Y_t = (Re f_{t ∧ τ_n}, Im f_{t ∧ τ_n}, log|f_0| + ∫₀ᵗ 1_{s ≤ τ_n} β(f_s) ds)`, where

  `β(x + iy) = ((2 - a/2 + b/2)(x² - y²) - 2cxy) / (x² + y²)²  ( = ν(θ)/|f|² in polar form )`,

with the function `F₁(w) = ½ log (w₀² + w₁²)` and then with `F₂(w) = (F₁(w) - w₂)²`. The results
(`eqn-abs-zt-op`, paper.tex:L911-L915, in martingale form):

* `logMart`: `N^n_t = log|f_{t ∧ τ_n}| - log|f_0| - ∫₀^{t ∧ τ_n} ν(θ_s) |f_s|⁻² ds` is a continuous
  `ℱ`-local martingale with everywhere continuous paths
  (`isContLocalMartingale_logMart`);
* its bracket is `∫₀^{t ∧ τ_n} (a cos² θ_s + b sin² θ_s + 2c sin θ_s cos θ_s) |f_s|⁻² ds`:
  `(N^n)² - ∫₀ᵗ 1_{s ≤ τ_n} Γ(f_s) ds` is a continuous local martingale
  (`isContLocalMartingale_logMart_sq_sub`), `Γ(x + iy) = (a x² + 2cxy + b y²)/(x² + y²)²`.

Using the third coordinate `log|f_0| + ∫ drift` (an `ℱ_0`-measurable constant plus the drift
integral, with zero martingale part) makes `F₂(Y_t) = (N^n_t)²` *exactly*, so no a.s. modification
is needed. Everything is stated for every `ω`; the only a.s. input is `U_0 = 0`, which gives
`T_z > 0` a.s. for `z ≠ 0` (hypothesis `hXD` of E1).
-/

public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal.Polar

/-! ### The drift and bracket densities as functions of `f ∈ ℂ ≅ ℝ²` -/

/-- `β(v) = ((2 - a/2 + b/2)(x² - y²) - 2cxy) / (x² + y²)²`, the drift of `log|f|` per unit time. -/
@[expose] noncomputable def betaFn (a b c : ℝ) (v : Fin 2 → ℝ) : ℝ :=
  ((2 - a / 2 + b / 2) * (v 0 ^ 2 - v 1 ^ 2) - 2 * c * v 0 * v 1) / (v 0 ^ 2 + v 1 ^ 2) ^ 2

/-- `Γ(v) = (a x² + 2cxy + b y²) / (x² + y²)²`, the bracket density of `log|f|`. -/
@[expose] noncomputable def gammaFn (a b c : ℝ) (v : Fin 2 → ℝ) : ℝ :=
  (a * v 0 ^ 2 + 2 * c * v 0 * v 1 + b * v 1 ^ 2) / (v 0 ^ 2 + v 1 ^ 2) ^ 2

/-- `{v ∈ ℝ² | v ≠ 0}`. -/
@[expose] def posSet₂ : Set (Fin 2 → ℝ) := {v | 0 < v 0 ^ 2 + v 1 ^ 2}

theorem measurable_betaFn (a b c : ℝ) : Measurable (betaFn a b c) := by
  unfold betaFn; fun_prop

theorem measurable_gammaFn (a b c : ℝ) : Measurable (gammaFn a b c) := by
  unfold gammaFn; fun_prop

theorem continuousOn_betaFn (a b c : ℝ) : ContinuousOn (betaFn a b c) posSet₂ := by
  unfold betaFn
  exact ContinuousOn.div (by fun_prop) (by fun_prop) fun v hv => by
    have : (0 : ℝ) < v 0 ^ 2 + v 1 ^ 2 := hv
    positivity

theorem continuousOn_gammaFn (a b c : ℝ) : ContinuousOn (gammaFn a b c) posSet₂ := by
  unfold gammaFn
  exact ContinuousOn.div (by fun_prop) (by fun_prop) fun v hv => by
    have : (0 : ℝ) < v 0 ^ 2 + v 1 ^ 2 := hv
    positivity

/-- In polar coordinates `v = r (cos θ, sin θ)`, `β = ν(θ) / r²`. -/
theorem betaFn_polar (a b c : ℝ) {r θ : ℝ} (hr : 0 < r) :
    betaFn a b c ![r * Real.cos θ, r * Real.sin θ] = nu a b c θ / r ^ 2 := by
  simp only [betaFn, nu, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Real.cos_two_mul, Real.sin_two_mul, mul_pow, Real.sin_sq]
  have hr2 : r ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- In polar coordinates, `Γ = (a cos² θ + b sin² θ + 2c sin θ cos θ) / r²`. -/
theorem gammaFn_polar (a b c : ℝ) {r θ : ℝ} (hr : 0 < r) :
    gammaFn a b c ![r * Real.cos θ, r * Real.sin θ] =
      (a * Real.cos θ ^ 2 + b * Real.sin θ ^ 2 + 2 * c * Real.sin θ * Real.cos θ) / r ^ 2 := by
  simp only [gammaFn, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have h1 : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
  rw [h1]
  have hr2 : r ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-! ### The processes -/

section Processes

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

variable (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) (n : ℕ)

/-- `log|f_{t ∧ τ_n}(z)|`. -/
@[expose] noncomputable def logNormF (t : ℝ≥0) (ω : Ω) : ℝ := Real.log ‖stoppedF hU z n t ω‖

/-- The drift density `1_{t ≤ τ_n} β(f_t)` (`= 1_{t ≤ τ_n} ν(θ_t)/|f_t|²`). -/
@[expose] noncomputable def logDrift (t : ℝ≥0) (ω : Ω) : ℝ :=
  beforeExit hU z n t ω * betaFn a b c (itoState hU z n t ω)

/-- The bracket density `1_{t ≤ τ_n} Γ(f_t)`. -/
@[expose] noncomputable def logBracket (t : ℝ≥0) (ω : Ω) : ℝ :=
  beforeExit hU z n t ω * gammaFn a b c (itoState hU z n t ω)

/-- **The martingale part of `log|f|` stopped at `τ_n`:**
`N^n_t = log|f_{t ∧ τ_n}| - log|f_0| - ∫₀ᵗ 1_{s ≤ τ_n} ν(θ_s)|f_s|⁻² ds`. -/
@[expose] noncomputable def logMart (t : ℝ≥0) (ω : Ω) : ℝ :=
  logNormF hU z n t ω - logNormF hU z n 0 ω - pathIntegral (logDrift hU z n) t ω

/-- The third coordinate of the augmented state: `log|f_0| + ∫₀ᵗ drift`. -/
@[expose] noncomputable def augD (t : ℝ≥0) (ω : Ω) : ℝ :=
  logNormF hU z n 0 ω + pathIntegral (logDrift hU z n) t ω

/-- The augmented state `(Re f, Im f, log|f_0| + ∫ drift)` stopped at `τ_n`. -/
@[expose] noncomputable def augState (t : ℝ≥0) (ω : Ω) : Fin 3 → ℝ :=
  ![itoState hU z n t ω 0, itoState hU z n t ω 1, augD hU z n t ω]

/-- The drift of the augmented state. -/
@[expose] noncomputable def augDrift (t : ℝ≥0) (ω : Ω) : Fin 3 → ℝ :=
  ![itoDrift hU z n t ω 0, itoDrift hU z n t ω 1, logDrift hU z n t ω]

/-- The (padded) covariance matrix. -/
@[expose] def covMatrix₃ (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![a, c, 0; c, b, 0; 0, 0, 0]

/-- The diffusion matrix of the augmented state. -/
@[expose] noncomputable def augQ (t : ℝ≥0) (ω : Ω) : Matrix (Fin 3) (Fin 3) ℝ :=
  beforeExit hU z n t ω • covMatrix₃ a b c

/-! #### Basic identities -/

theorem itoState_eq_polar {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) (t : ℝ≥0) :
    itoState hU z n t ω = ![‖stoppedF hU z n t ω‖ * Real.cos
      (argPath (fun s => U s ω) (hU.cont ω) z (min (t : ℝ) (exitR hU z n ω))),
      ‖stoppedF hU z n t ω‖ * Real.sin
      (argPath (fun s => U s ω) (hU.cont ω) z (min (t : ℝ) (exitR hU z n ω)))] := by
  have hmem := min_exitTime_mem_lifeSet (hU.cont ω) hz n (t := t) t.coe_nonneg
  ext i
  fin_cases i
  · simp only [itoState, reIm, Matrix.cons_val_zero, Fin.zero_eta]
    rw [stoppedF_eq hU z n hz]
    exact re_fPath (hU.cont ω) hmem
  · simp only [itoState, reIm, Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.mk_one]
    rw [stoppedF_eq hU z n hz]
    exact im_fPath (hU.cont ω) hmem

/-- The drift density in the form of the source (`eqn-abs-zt-op`): on `{T_z > 0}` and for
`t ≤ τ_n`, `logDrift t = ν(θ_t) / |f_t|²`. -/
theorem logDrift_eq_nu {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) {t : ℝ≥0}
    (ht : (t : ℝ) ≤ exitR hU z n ω) :
    logDrift hU z n t ω = nu a b c (argPath (fun s => U s ω) (hU.cont ω) z t) /
      ‖fPath (fun s => U s ω) (hU.cont ω) z t‖ ^ 2 := by
  have h1 : beforeExit hU z n t ω = 1 := by
    simp [beforeExit, (le_exitNN_iff hU z n).2 ht]
  rw [logDrift, h1, one_mul, itoState_eq_polar hU z n hz, min_eq_left ht,
    betaFn_polar _ _ _ (norm_pos_iff.2 (stoppedF_ne_zero hU z n hz t)),
    stoppedF_eq_of_le hU z n hz ht]

/-- The bracket density in polar form: on `{T_z > 0}` and for `t ≤ τ_n`,
`logBracket t = (a cos² θ_t + b sin² θ_t + 2c sin θ_t cos θ_t) / |f_t|²`. -/
theorem logBracket_eq_polar {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) {t : ℝ≥0}
    (ht : (t : ℝ) ≤ exitR hU z n ω) :
    logBracket hU z n t ω =
      (a * Real.cos (argPath (fun s => U s ω) (hU.cont ω) z t) ^ 2 +
        b * Real.sin (argPath (fun s => U s ω) (hU.cont ω) z t) ^ 2 +
        2 * c * Real.sin (argPath (fun s => U s ω) (hU.cont ω) z t) *
          Real.cos (argPath (fun s => U s ω) (hU.cont ω) z t)) /
      ‖fPath (fun s => U s ω) (hU.cont ω) z t‖ ^ 2 := by
  have h1 : beforeExit hU z n t ω = 1 := by
    simp [beforeExit, (le_exitNN_iff hU z n).2 ht]
  rw [logBracket, h1, one_mul, itoState_eq_polar hU z n hz, min_eq_left ht,
    gammaFn_polar _ _ _ (norm_pos_iff.2 (stoppedF_ne_zero hU z n hz t)),
    stoppedF_eq_of_le hU z n hz ht]

theorem logNormF_eq_logNorm₃ (t : ℝ≥0) (ω : Ω) :
    logNorm₃ (augState hU z n t ω) = logNormF hU z n t ω := by
  have h : (stoppedF hU z n t ω).re ^ 2 + (stoppedF hU z n t ω).im ^ 2 =
      ‖stoppedF hU z n t ω‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  simp only [logNorm₃, sqNorm₃, augState, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, itoState, reIm, logNormF]
  rw [h, Real.log_pow]
  push_cast
  ring

theorem augState_two (t : ℝ≥0) (ω : Ω) : augState hU z n t ω 2 = augD hU z n t ω := rfl
theorem augDrift_two (t : ℝ≥0) (ω : Ω) : augDrift hU z n t ω 2 = logDrift hU z n t ω := rfl

include hU in
/-- `0 < T_z` a.s. for `z ≠ 0` (since `U_0 = 0` a.s.). -/
theorem ae_pos_absorbingTime (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, 0 < absorbingTime (fun s => U s ω) z := by
  filter_upwards [hU.toIsSLEDriver.zero] with ω hω
  exact absorbingTime_pos_of_ne (hU.cont ω) (by rw [hω]; exact hz)

theorem itoState_mem_posSet₂ {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) (t : ℝ≥0) :
    itoState hU z n t ω ∈ posSet₂ := by
  have h := Complex.normSq_pos.2 (stoppedF_ne_zero hU z n hz t)
  rw [Complex.normSq_apply] at h
  change 0 < (stoppedF hU z n t ω).re ^ 2 + (stoppedF hU z n t ω).im ^ 2
  nlinarith [h]

theorem augState_mem_posSet₃ {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) (t : ℝ≥0) :
    augState hU z n t ω ∈ posSet₃ :=
  itoState_mem_posSet₂ hU z n hz t

theorem itoState_eq_zero {ω : Ω} (hz : ¬ 0 < absorbingTime (fun s => U s ω) z) (t : ℝ≥0) :
    itoState hU z n t ω = 0 := by
  simp [itoState, stoppedF_eq_zero hU z n hz, reIm_zero]

/-! #### Path integrals of continuous adapted integrands are adapted -/

/-- For an adapted process with everywhere continuous paths, `t ↦ ∫₀ᵗ ξ_s ds` is adapted
(Riemann sums). -/
theorem stronglyAdapted_pathIntegral {ξ : ℝ≥0 → Ω → ℝ} (hξ : StronglyAdapted ℱ ξ)
    (hc : ∀ ω, Continuous fun t => ξ t ω) :
    StronglyAdapted ℱ fun t ω => pathIntegral ξ t ω := by
  intro t
  refine Measurable.stronglyMeasurable ?_
  let _ : MeasurableSpace Ω := ℱ t
  let G : ℕ → Ω → ℝ := fun N ω => ∑ k ∈ Finset.range N, ((t : ℝ) / N) * ξ (gridPt t N k) ω
  have hG : ∀ N, Measurable (G N) := fun N =>
    Finset.measurable_sum _ fun k hk => measurable_const.mul
      ((hξ _).measurable.mono (ℱ.mono (gridPt_le t (Finset.mem_range.1 hk).le)) le_rfl)
  refine measurable_of_tendsto_metrizable hG ?_
  rw [tendsto_pi_nhds]
  intro ω
  have h := tendsto_riemannSum (φ := fun s : ℝ => ξ s.toNNReal ω) t.coe_nonneg
    ((hc ω).comp continuous_real_toNNReal).continuousOn
  refine h.congr' (Eventually.of_forall fun N => Finset.sum_congr rfl fun k _ => ?_)
  rw [← coe_gridPt, Real.toNNReal_coe]

theorem continuous_pathIntegral {ξ : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous fun t => ξ t ω)
    (ω : Ω) : Continuous fun t : ℝ≥0 => pathIntegral ξ t ω := by
  have hφ : Continuous fun s : ℝ => ξ s.toNNReal ω := (hc ω).comp continuous_real_toNNReal
  exact (intervalIntegral.continuous_primitive (fun a b => hφ.intervalIntegrable a b) 0).comp
    NNReal.continuous_coe

theorem isStronglyProgressive_pathIntegral {ξ : ℝ≥0 → Ω → ℝ} (hξ : StronglyAdapted ℱ ξ)
    (hc : ∀ ω, Continuous fun t => ξ t ω) :
    IsStronglyProgressive ℱ fun t ω => pathIntegral ξ t ω :=
  (stronglyAdapted_pathIntegral hξ hc).isStronglyProgressive_of_continuous
    (continuous_pathIntegral hc)

/-! #### Integrands of the form `1_{s ≤ τ_n} φ(f_s)` -/

section Phi

variable {φ : (Fin 2 → ℝ) → ℝ}

theorem continuous_comp_itoState (hφ : ContinuousOn φ posSet₂) (ω : Ω) :
    Continuous fun t => φ (itoState hU z n t ω) := by
  by_cases hz : 0 < absorbingTime (fun s => U s ω) z
  · exact hφ.comp_continuous (continuous_itoState hU z n ω) (itoState_mem_posSet₂ hU z n hz)
  · simp only [itoState_eq_zero hU z n hz]
    exact continuous_const

theorem stronglyAdapted_comp_itoState (hφm : Measurable φ) :
    StronglyAdapted ℱ fun t ω => φ (itoState hU z n t ω) := fun t =>
  (hφm.comp
    ((isStronglyProgressive_itoState hU z n).stronglyAdapted t).measurable).stronglyMeasurable

/-- `∫₀ᵗ 1_{s ≤ τ_n} φ(f_s) ds = ∫₀^{t ∧ τ_n} φ(f_s) ds`. -/
theorem pathIntegral_beforeExit_mul (ω : Ω) (t : ℝ≥0) :
    pathIntegral (fun s ω => beforeExit hU z n s ω * φ (itoState hU z n s ω)) t ω =
      pathIntegral (fun s ω => φ (itoState hU z n s ω)) (min t (exitNN hU z n ω)) ω := by
  simp only [pathIntegral, beforeExit_toNNReal, NNReal.coe_min, coe_exitNN]
  rw [← integral_indicator_Iic_eq (exitR_nonneg hU z n ω) t.coe_nonneg]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [indicator]
  split_ifs <;> simp

theorem isStronglyProgressive_pathIntegral_beforeExit (hφm : Measurable φ)
    (hφ : ContinuousOn φ posSet₂) :
    IsStronglyProgressive ℱ fun t ω =>
      pathIntegral (fun s ω => beforeExit hU z n s ω * φ (itoState hU z n s ω)) t ω := by
  have h := (isStronglyProgressive_pathIntegral (stronglyAdapted_comp_itoState hU z n hφm)
    (continuous_comp_itoState hU z n hφ)).stoppedProcess (isStoppingTime_exitNN hU z n)
  have heq : (fun t ω => pathIntegral (fun s ω => beforeExit hU z n s ω *
      φ (itoState hU z n s ω)) t ω) =
      stoppedProcess (fun t ω => pathIntegral (fun s ω => φ (itoState hU z n s ω)) t ω)
        fun ω => (exitNN hU z n ω : WithTop ℝ≥0) := by
    funext t ω
    rw [pathIntegral_beforeExit_mul]
    simp only [stoppedProcess]
    rw [← WithTop.coe_min]
    rfl
  rw [heq]; exact h

theorem continuous_pathIntegral_beforeExit (hφ : ContinuousOn φ posSet₂) (ω : Ω) :
    Continuous fun t => pathIntegral
      (fun s ω => beforeExit hU z n s ω * φ (itoState hU z n s ω)) t ω := by
  simp only [pathIntegral_beforeExit_mul]
  exact (continuous_pathIntegral (continuous_comp_itoState hU z n hφ) ω).comp
    (continuous_id.min continuous_const)

theorem intervalIntegrable_beforeExit_mul (hφ : ContinuousOn φ posSet₂) (ω : Ω) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => beforeExit hU z n s.toNNReal ω *
      φ (itoState hU z n s.toNNReal ω)) volume 0 t := by
  simp only [beforeExit_toNNReal]
  refine IntervalIntegrable.mul_continuousOn ?_ ?_
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg]
    exact (integrableOn_const (C := (1 : ℝ)) measure_Ioc_lt_top.ne).indicator measurableSet_Iic
  · exact ((continuous_comp_itoState hU z n hφ ω).comp continuous_real_toNNReal).continuousOn

end Phi

/-- Two integrands agreeing at all positive times have the same path integrals. -/
theorem pathIntegral_congr_pos {ξ ξ' : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (h : ∀ s : ℝ≥0, 0 < s → ξ s ω = ξ' s ω) (t : ℝ≥0) :
    pathIntegral ξ t ω = pathIntegral ξ' t ω := by
  simp only [pathIntegral]
  apply intervalIntegral.integral_congr_ae'
  · exact ae_of_all _ fun s hs => h _ (Real.toNNReal_pos.2 hs.1)
  · exact ae_of_all _ fun s hs => absurd (hs.2.trans t.coe_nonneg) (not_le.2 hs.1)

/-! #### Measurability, continuity and integrability of the augmented state -/

theorem isStronglyProgressive_logDrift : IsStronglyProgressive ℱ (logDrift hU z n) := fun i =>
  (isStronglyProgressive_beforeExit hU z n i).mul
    (((measurable_betaFn a b c).comp (isStronglyProgressive_itoState hU z n i).measurable)
      |>.stronglyMeasurable)

theorem measurable_logNormF_zero : Measurable[ℱ 0] (logNormF hU z n 0) :=
  Real.measurable_log.comp (measurable_norm.comp
    ((isStronglyProgressive_stoppedF hU z n).stronglyAdapted 0).measurable)

theorem isStronglyProgressive_augD : IsStronglyProgressive ℱ (augD hU z n) := by
  have h1 : IsStronglyProgressive ℱ fun _ ω => logNormF hU z n 0 ω :=
    StronglyAdapted.isStronglyProgressive_of_continuous
      (fun t => ((measurable_logNormF_zero hU z n).mono (ℱ.mono bot_le) le_rfl).stronglyMeasurable)
      fun _ => continuous_const
  have h2 := isStronglyProgressive_pathIntegral_beforeExit hU z n (measurable_betaFn a b c)
    (continuousOn_betaFn a b c)
  exact fun i => (h1 i).add (h2 i)

theorem continuous_augD (ω : Ω) : Continuous fun t => augD hU z n t ω :=
  continuous_const.add (continuous_pathIntegral_beforeExit hU z n (continuousOn_betaFn a b c) ω)

/-- The map `(x, (y, w)) ↦ ![x, y, w]` is continuous. -/
theorem continuous_vec3 : Continuous fun q : ℝ × ℝ × ℝ => (![q.1, q.2.1, q.2.2] : Fin 3 → ℝ) := by
  refine continuous_pi fun j => ?_
  fin_cases j
  · exact continuous_fst
  · exact continuous_snd.fst
  · exact continuous_snd.snd

theorem isStronglyProgressive_augState : IsStronglyProgressive ℱ (augState hU z n) := by
  intro i
  have h0 := (continuous_apply (0 : Fin 2)).comp_stronglyMeasurable
    (isStronglyProgressive_itoState hU z n i)
  have h1 := (continuous_apply (1 : Fin 2)).comp_stronglyMeasurable
    (isStronglyProgressive_itoState hU z n i)
  have h2 := isStronglyProgressive_augD hU z n i
  exact continuous_vec3.comp_stronglyMeasurable (h0.prodMk (h1.prodMk h2))

theorem continuous_augState (ω : Ω) : Continuous fun t => augState hU z n t ω := by
  refine continuous_pi fun j => ?_
  fin_cases j
  · exact (continuous_apply (0 : Fin 2)).comp (continuous_itoState hU z n ω)
  · exact (continuous_apply (1 : Fin 2)).comp (continuous_itoState hU z n ω)
  · exact continuous_augD hU z n ω

theorem isStronglyProgressive_augDrift : IsStronglyProgressive ℱ (augDrift hU z n) := by
  intro i
  have h0 := (continuous_apply (0 : Fin 2)).comp_stronglyMeasurable
    (isStronglyProgressive_itoDrift hU z n i)
  have h1 := (continuous_apply (1 : Fin 2)).comp_stronglyMeasurable
    (isStronglyProgressive_itoDrift hU z n i)
  have h2 := isStronglyProgressive_logDrift hU z n i
  exact continuous_vec3.comp_stronglyMeasurable (h0.prodMk (h1.prodMk h2))

theorem intervalIntegrable_augDrift (ω : Ω) (i : Fin 3) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => augDrift hU z n s.toNNReal ω i) volume 0 t := by
  fin_cases i
  · exact intervalIntegrable_itoDrift hU z n ω 0 t
  · exact intervalIntegrable_itoDrift hU z n ω 1 t
  · exact intervalIntegrable_beforeExit_mul hU z n (continuousOn_betaFn a b c) ω t

theorem isStronglyProgressive_augQ :
    IsStronglyProgressive ℱ (augQ hU z n (a := a) (b := b) (c := c)) :=
  fun i => (isStronglyProgressive_beforeExit hU z n i).smul stronglyMeasurable_const

theorem intervalIntegrable_augQ (ω : Ω) (i j : Fin 3) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => augQ hU z n (a := a) (b := b) (c := c) s.toNNReal ω i j)
      volume 0 t := by
  have : (fun s : ℝ => augQ hU z n (a := a) (b := b) (c := c) s.toNNReal ω i j) =
      fun s => (Iic (exitR hU z n ω)).indicator (fun _ => (1 : ℝ)) s * covMatrix₃ a b c i j := by
    funext s
    simp only [augQ, Matrix.smul_apply, smul_eq_mul, beforeExit_toNNReal]
  rw [this, intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg]
  exact Integrable.mul_const
    ((integrableOn_const (C := (1 : ℝ)) measure_Ioc_lt_top.ne).indicator measurableSet_Iic) _

/-! #### The martingale hypotheses of Itô's formula for the augmented state -/

theorem pathIntegral_zero_time (ξ : ℝ≥0 → Ω → ℝ) (ω : Ω) : pathIntegral ξ 0 ω = 0 := by
  simp [pathIntegral]

theorem pathIntegral_zero_fun (t : ℝ≥0) (ω : Ω) :
    pathIntegral (fun (_ : ℝ≥0) (_ : Ω) => (0 : ℝ)) t ω = 0 := by
  simp [pathIntegral]

/-- The third coordinate has zero martingale part. -/
theorem augState_two_sub_eq (t : ℝ≥0) (ω : Ω) :
    augState hU z n t ω 2 - augState hU z n 0 ω 2 -
      pathIntegral (fun s ω => augDrift hU z n s ω 2) t ω = 0 := by
  simp only [augState_two, augDrift_two, augD, pathIntegral_zero_time]
  ring

theorem isContLocalMartingale_zero : IsContLocalMartingale ℱ (fun _ _ => (0 : ℝ)) P :=
  (martingale_zero ℝ ℱ P).isContLocalMartingale fun _ => continuous_const

section Martingales

variable [IsProbabilityMeasure P]

theorem ito_hM_aug (i : Fin 3) :
    IsContLocalMartingale ℱ (fun t ω => augState hU z n t ω i - augState hU z n 0 ω i -
      pathIntegral (fun s ω => augDrift hU z n s ω i) t ω) P := by
  match i with
  | 0 => exact isContLocalMartingale_itoState_sub hU z n 0
  | 1 => exact isContLocalMartingale_itoState_sub hU z n 1
  | 2 =>
    have : (fun t ω => augState hU z n t ω 2 - augState hU z n 0 ω 2 -
        pathIntegral (fun s ω => augDrift hU z n s ω 2) t ω) = fun _ _ => 0 := by
      funext t ω; exact augState_two_sub_eq hU z n t ω
    rw [this]; exact isContLocalMartingale_zero

theorem covMatrix₃_apply_two_left (j : Fin 3) : covMatrix₃ a b c 2 j = 0 := by
  fin_cases j <;> rfl

theorem covMatrix₃_apply_two_right (i : Fin 3) : covMatrix₃ a b c i 2 = 0 := by
  fin_cases i <;> rfl

theorem ito_hMM_aug (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (i j : Fin 3) :
    IsContLocalMartingale ℱ (fun t ω =>
      (augState hU z n t ω i - augState hU z n 0 ω i -
          pathIntegral (fun s ω => augDrift hU z n s ω i) t ω) *
        (augState hU z n t ω j - augState hU z n 0 ω j -
          pathIntegral (fun s ω => augDrift hU z n s ω j) t ω) -
        pathIntegral (fun s ω => augQ hU z n (a := a) (b := b) (c := c) s ω i j) t ω) P := by
  -- the cases with an index `2` are the zero process
  by_cases h2 : i = 2 ∨ j = 2
  · have hQ : ∀ s ω, augQ hU z n (a := a) (b := b) (c := c) s ω i j = 0 := by
      intro s ω
      simp only [augQ, Matrix.smul_apply, smul_eq_mul]
      rcases h2 with rfl | rfl
      · rw [covMatrix₃_apply_two_left, mul_zero]
      · rw [covMatrix₃_apply_two_right, mul_zero]
    have hfun : (fun t ω =>
        (augState hU z n t ω i - augState hU z n 0 ω i -
            pathIntegral (fun s ω => augDrift hU z n s ω i) t ω) *
          (augState hU z n t ω j - augState hU z n 0 ω j -
            pathIntegral (fun s ω => augDrift hU z n s ω j) t ω) -
          pathIntegral (fun s ω => augQ hU z n (a := a) (b := b) (c := c) s ω i j) t ω) =
        fun _ _ => 0 := by
      funext t ω
      simp only [hQ, pathIntegral_zero_fun, sub_zero]
      rcases h2 with rfl | rfl
      · rw [augState_two_sub_eq, zero_mul]
      · rw [augState_two_sub_eq, mul_zero]
    rw [hfun]; exact isContLocalMartingale_zero
  · push Not at h2
    have hQ : ∀ s ω, augQ hU z n (a := a) (b := b) (c := c) s ω i j =
        itoQ hU z n (a := a) (b := b) (c := c) s ω (Fin.castPred i h2.1) (Fin.castPred j h2.2) := by
      intro s ω
      simp only [augQ, itoQ, Matrix.smul_apply, smul_eq_mul]
      congr 1
      fin_cases i <;> fin_cases j <;> first | rfl | exact absurd rfl h2.1 | exact absurd rfl h2.2
    have hX : ∀ t ω (k : Fin 3) (hk : k ≠ 2), augState hU z n t ω k =
        itoState hU z n t ω (Fin.castPred k hk) := by
      intro t ω k hk
      fin_cases k
      · rfl
      · rfl
      · exact absurd rfl hk
    have hA : ∀ t ω (k : Fin 3) (hk : k ≠ 2), augDrift hU z n t ω k =
        itoDrift hU z n t ω (Fin.castPred k hk) := by
      intro t ω k hk
      fin_cases k
      · rfl
      · rfl
      · exact absurd rfl hk
    simp only [hQ, hX _ _ i h2.1, hX _ _ j h2.2, hA _ _ i h2.1, hA _ _ j h2.2]
    exact isContLocalMartingale_itoState_mul_sub hU z n ha hc _ _

end Martingales

/-! ### Applying Itô's formula -/

section Apply

/-- The indicator `1_{s ≤ τ_n}` vanishes at positive times on `{T_z = 0}`. -/
theorem beforeExit_eq_zero_of_not_pos {ω : Ω} (hz : ¬ 0 < absorbingTime (fun r => U r ω) z)
    {s : ℝ≥0} (hs : 0 < s) : beforeExit hU z n s ω = 0 := by
  have : exitNN hU z n ω = 0 := by rw [exitNN, exitR_eq_zero hU z n hz, Real.toNNReal_zero]
  simp [beforeExit, this, hs.ne']

/-- **The Itô integrand of `½ log q`** at the augmented state is the drift density `logDrift`
(`eqn-abs-zt-op`): `∑ᵢ ∂ᵢF Aⁱ + ½ ∑ᵢⱼ ∂ᵢⱼF Qⁱʲ = 1_{s ≤ τ_n} ν(θ_s)/|f_s|²`. -/
theorem ito_integrand_logNorm₃ (ω : Ω) (s : ℝ≥0)
    (hs : 0 < absorbingTime (fun r => U r ω) z ∨ 0 < s) :
    ∑ i, fderiv ℝ logNorm₃ (augState hU z n s ω) (Pi.single i 1) * augDrift hU z n s ω i +
      (1 / 2) * ∑ i, ∑ j, iteratedFDeriv ℝ 2 logNorm₃ (augState hU z n s ω)
        ![Pi.single i 1, Pi.single j 1] * augQ hU z n (a := a) (b := b) (c := c) s ω i j =
      logDrift hU z n s ω := by
  by_cases hz : 0 < absorbingTime (fun r => U r ω) z
  · have hv := augState_mem_posSet₃ hU z n hz s
    have hq : (0 : ℝ) < (stoppedF hU z n s ω).re ^ 2 + (stoppedF hU z n s ω).im ^ 2 :=
      itoState_mem_posSet₂ hU z n hz s
    have hne : (stoppedF hU z n s ω).re ^ 2 + (stoppedF hU z n s ω).im ^ 2 ≠ 0 := ne_of_gt hq
    have hne' : (stoppedF hU z n s ω).re * (stoppedF hU z n s ω).re +
        (stoppedF hU z n s ω).im * (stoppedF hU z n s ω).im ≠ 0 := by
      rw [← sq, ← sq]; exact hne
    simp only [fderiv_logNorm₃_single hv, iteratedFDeriv_logNorm₃ hv, Fin.sum_univ_three]
    simp [gradLog₃, hessLog₃, augDrift, augQ, covMatrix₃, logDrift, itoDrift, betaFn, augState,
      itoState, reIm, sqNorm₃, Complex.div_re, Complex.div_im, Complex.normSq_apply]
    field_simp
    ring
  · have hs' : 0 < s := hs.resolve_left hz
    have hbe := beforeExit_eq_zero_of_not_pos hU z n hz hs'
    simp [augDrift, augQ, itoDrift, logDrift, hbe, Fin.sum_univ_three]

/-- **The Itô integrand of `(½ log q - d)²`** at the augmented state is the bracket density
`logBracket`: the terms containing `½ log q - d` cancel. -/
theorem ito_integrand_sqDev (ω : Ω) (s : ℝ≥0)
    (hs : 0 < absorbingTime (fun r => U r ω) z ∨ 0 < s) :
    ∑ i, fderiv ℝ sqDev (augState hU z n s ω) (Pi.single i 1) * augDrift hU z n s ω i +
      (1 / 2) * ∑ i, ∑ j, iteratedFDeriv ℝ 2 sqDev (augState hU z n s ω)
        ![Pi.single i 1, Pi.single j 1] * augQ hU z n (a := a) (b := b) (c := c) s ω i j =
      logBracket hU z n s ω := by
  by_cases hz : 0 < absorbingTime (fun r => U r ω) z
  · have hv := augState_mem_posSet₃ hU z n hz s
    have hq : (0 : ℝ) < (stoppedF hU z n s ω).re ^ 2 + (stoppedF hU z n s ω).im ^ 2 :=
      itoState_mem_posSet₂ hU z n hz s
    have hne : (stoppedF hU z n s ω).re ^ 2 + (stoppedF hU z n s ω).im ^ 2 ≠ 0 := ne_of_gt hq
    have hne' : (stoppedF hU z n s ω).re * (stoppedF hU z n s ω).re +
        (stoppedF hU z n s ω).im * (stoppedF hU z n s ω).im ≠ 0 := by
      rw [← sq, ← sq]; exact hne
    simp only [fderiv_sqDev_single hv, iteratedFDeriv_sqDev hv, Fin.sum_univ_three]
    generalize logDev (augState hU z n s ω) = E
    simp [gradDev, gradLog₃, hessLog₃, augDrift, augQ, covMatrix₃, logBracket, logDrift, itoDrift,
      betaFn, gammaFn, augState, itoState, reIm, sqNorm₃, Complex.div_re, Complex.div_im,
      Complex.normSq_apply]
    field_simp
    ring
  · have hs' : 0 < s := hs.resolve_left hz
    have hbe := beforeExit_eq_zero_of_not_pos hU z n hz hs'
    simp [augDrift, augQ, itoDrift, logBracket, logDrift, hbe, Fin.sum_univ_three]

/-- Pointwise congruence for continuous local martingales (avoids unfolding the predicate). -/
theorem _root_.ComplexSLE.IsContLocalMartingale.congr_fun' {M N : ℝ≥0 → Ω → ℝ}
    (h : IsContLocalMartingale ℱ M P) (heq : ∀ t ω, M t ω = N t ω) :
    IsContLocalMartingale ℱ N P := by
  have : N = M := funext fun t => funext fun ω => (heq t ω).symm
  rw [this]; exact h

variable [IsProbabilityMeasure P]

/-- **`log|f|` stopped at `τ_n`, martingale part** (`step:polar-ito-log`, `step:polar-real-imag`,
real part; paper.tex:L911-L915 in martingale form). For `0 < a`, `c² ≤ ab`, `z ≠ 0`:
`N^n_t = log|f_{t ∧ τ_n}(z)| - log|f_0(z)| - ∫₀ᵗ 1_{s ≤ τ_n} ν(θ_s) |f_s(z)|⁻² ds`
is a continuous `ℱ`-local martingale. -/
theorem isContLocalMartingale_logMart (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) :
    IsContLocalMartingale ℱ (logMart hU z n) P := by
  have hAint : ∀ᵐ ω ∂P, ∀ (i : Fin 3) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => augDrift hU z n (Real.toNNReal s) ω i) volume 0 t :=
    Eventually.of_forall fun ω i t => intervalIntegrable_augDrift hU z n ω i t
  have hQint : ∀ᵐ ω ∂P, ∀ (i j : Fin 3) (t : ℝ≥0),
      IntervalIntegrable
        (fun s : ℝ => augQ hU z n (a := a) (b := b) (c := c) (Real.toNNReal s) ω i j) volume 0 t :=
    Eventually.of_forall fun ω i j t => intervalIntegrable_augQ hU z n ω i j t
  have hXD : ∀ᵐ ω ∂P, ∀ t, augState hU z n t ω ∈ posSet₃ := by
    filter_upwards [ae_pos_absorbingTime hU z hz] with ω hω
    exact fun t => augState_mem_posSet₃ hU z n hω t
  have h := External.ito_formula ℱ (augState hU z n) (augDrift hU z n)
    (augQ hU z n (a := a) (b := b) (c := c))
    (isStronglyProgressive_augState hU z n) (continuous_augState hU z n)
    (isStronglyProgressive_augDrift hU z n) hAint (isStronglyProgressive_augQ hU z n) hQint
    (ito_hM_aug hU z n) (ito_hMM_aug hU z n ha hc)
    posSet₃ isOpen_posSet₃ logNorm₃ measurable_logNorm₃ contDiffOn_logNorm₃ hXD
  refine h.congr_fun' fun t ω => ?_
  rw [logMart, ← logNormF_eq_logNorm₃, ← logNormF_eq_logNorm₃]
  congr 1
  exact pathIntegral_congr_pos (fun s hs => ito_integrand_logNorm₃ hU z n ω s (Or.inr hs)) t

/-- **The bracket of `N^n`**: `(N^n_t)² - ∫₀ᵗ 1_{s ≤ τ_n} (a cos² θ_s + b sin² θ_s +
2c sin θ_s cos θ_s) |f_s(z)|⁻² ds` is a continuous `ℱ`-local martingale. -/
theorem isContLocalMartingale_logMart_sq_sub (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) :
    IsContLocalMartingale ℱ
      (fun t ω => logMart hU z n t ω ^ 2 - pathIntegral (logBracket hU z n) t ω) P := by
  have hAint : ∀ᵐ ω ∂P, ∀ (i : Fin 3) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => augDrift hU z n (Real.toNNReal s) ω i) volume 0 t :=
    Eventually.of_forall fun ω i t => intervalIntegrable_augDrift hU z n ω i t
  have hQint : ∀ᵐ ω ∂P, ∀ (i j : Fin 3) (t : ℝ≥0),
      IntervalIntegrable
        (fun s : ℝ => augQ hU z n (a := a) (b := b) (c := c) (Real.toNNReal s) ω i j) volume 0 t :=
    Eventually.of_forall fun ω i j t => intervalIntegrable_augQ hU z n ω i j t
  have hXD : ∀ᵐ ω ∂P, ∀ t, augState hU z n t ω ∈ posSet₃ := by
    filter_upwards [ae_pos_absorbingTime hU z hz] with ω hω
    exact fun t => augState_mem_posSet₃ hU z n hω t
  have h := External.ito_formula ℱ (augState hU z n) (augDrift hU z n)
    (augQ hU z n (a := a) (b := b) (c := c))
    (isStronglyProgressive_augState hU z n) (continuous_augState hU z n)
    (isStronglyProgressive_augDrift hU z n) hAint (isStronglyProgressive_augQ hU z n) hQint
    (ito_hM_aug hU z n) (ito_hMM_aug hU z n ha hc)
    posSet₃ isOpen_posSet₃ sqDev measurable_sqDev contDiffOn_sqDev hXD
  refine h.congr_fun' fun t ω => ?_
  have e1 : sqDev (augState hU z n t ω) = logMart hU z n t ω ^ 2 := by
    rw [sqDev, logNormF_eq_logNorm₃, augState_two, augD, logMart]
    ring
  have e0 : sqDev (augState hU z n 0 ω) = 0 := by
    rw [sqDev, logNormF_eq_logNorm₃, augState_two, augD, pathIntegral_zero_time]
    ring
  rw [e1, e0, sub_zero]
  congr 1
  exact pathIntegral_congr_pos (fun s hs => ito_integrand_sqDev hU z n ω s (Or.inr hs)) t

end Apply

/-! ### Path regularity of `N^n` -/

theorem continuous_logNormF (ω : Ω) : Continuous fun t => logNormF hU z n t ω := by
  by_cases hz : 0 < absorbingTime (fun s => U s ω) z
  · exact Real.continuousOn_log.comp_continuous
      (continuous_norm.comp (continuous_stoppedF hU z n ω)) fun t =>
        mem_compl_singleton_iff.2 (norm_pos_iff.2 (stoppedF_ne_zero hU z n hz t)).ne'
  · simp only [logNormF, stoppedF_eq_zero hU z n hz]
    exact continuous_const

/-- Every path of `N^n` is continuous. -/
theorem continuous_logMart (ω : Ω) : Continuous fun t => logMart hU z n t ω :=
  ((continuous_logNormF hU z n ω).sub continuous_const).sub
    (continuous_pathIntegral_beforeExit hU z n (continuousOn_betaFn a b c) ω)

theorem logMart_zero (ω : Ω) : logMart hU z n 0 ω = 0 := by
  simp [logMart, pathIntegral_zero_time]

/-- `N^n` is constant after `τ_n`. -/
theorem logMart_eq_of_le {ω : Ω} {s t : ℝ≥0} (hst : s ≤ t) (hs : exitNN hU z n ω ≤ s) :
    logMart hU z n t ω = logMart hU z n s ω := by
  simp only [logMart, logNormF, stoppedF, min_eq_right hs, min_eq_right (hs.trans hst)]
  congr 1
  change pathIntegral (fun s ω => beforeExit hU z n s ω * betaFn a b c (itoState hU z n s ω)) t ω =
    pathIntegral (fun s ω => beforeExit hU z n s ω * betaFn a b c (itoState hU z n s ω)) s ω
  rw [pathIntegral_beforeExit_mul, pathIntegral_beforeExit_mul, min_eq_right hs,
    min_eq_right (hs.trans hst)]

end Processes

end ComplexSLE.Internal.Polar

end
