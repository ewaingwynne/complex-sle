/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.PolarDeriv
public import ComplexSLE.Internal.Polar.PolarTimeChange
public import ComplexSLE.Internal.Polar.PolarSigmaTop

/-!
# `log|f̂'_s(z)|` in σ-time and the SDE for `log(|f̂'|/|f̂|)` (M7/D0, `step:polar-derivative-sde`)

Deterministic layer: with the time change `σ_z` of Definition 2.9 and the deterministic formula
`log|g_t'(z)| = -2 ∫₀ᵗ cos(2θ_u) |f_u|⁻² du` (`log_norm_derivPath_eq_cos`), the change of
variables `integral_comp_sigmaTime` gives (2.27) in integrated form,

  `log|f̂'_s(z)| = log|g'_{σ_z(s)}(z)| = -2 ∫₀ˢ cos(2θ̂_v) dv`,  `s ∈ sigmaDom`

(`log_norm_derivPath_sigmaTime`).

Probabilistic layer, for an adapted `SLE_Σ` driver: combined with the martingale form of (2.26)
(`sigmaLogMart`, `isContLocalMartingale_sigmaLogMart`) this yields the decomposition
(`eqn-sde-ratio`, paper.tex:L1437-1440) that Lemma 3.3 (`lem-integral-ii`) and the `c = 0`
boundary lemma (`lem-c0-bdy`) consume:

  `log(|f̂'_s|/|f̂_s|) = -log|f̂_0| - ∫₀ˢ (ν(θ̂_v) + 2 cos 2θ̂_v) dv - sigmaLogMart_s`

on `sigmaDom` (`sigmaLogRatio_eq`; a.s. for all `s` by Remark 2.12, `ae_sigmaLogRatio_eq`). The
drift density `ν + 2 cos 2·` is the integrand of the integral (II) (`integralII`), and the
martingale part `sigmaLogRatioMart = -sigmaLogMart` is a continuous `𝒢`-local martingale
(`isContLocalMartingale_sigmaLogRatioMart`) with the same bracket
`∫₀ˢ (a cos² θ̂ + b sin² θ̂ + 2c sin θ̂ cos θ̂) dv` (`sigmaLogMartSq_eq_ratio`,
`isContLocalMartingale_sigmaLogMartSq`).
-/

public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal.Polar

/-! ### Deterministic facts -/

section Deterministic

variable {U : ℝ≥0 → ℂ}

/-- `v ↦ θ_{σ_z(v)}` is continuous on `sigmaDom`. -/
theorem continuousOn_argPath_sigmaTime (hU : Continuous U) (z : ℂ) :
    ContinuousOn (fun v => argPath U hU z (sigmaTime U hU z v)) (sigmaDom U hU z) :=
  (continuousOn_argPath hU z).comp (continuousOn_sigmaTime hU z) fun _ hv =>
    sigmaTime_mem_lifeSet hU hv

/-- For continuous `φ` and `s ∈ sigmaDom`, `v ↦ φ(θ_{σ_z(v)})` is integrable on `[0, s]`. -/
theorem intervalIntegrable_comp_argPath_sigmaTime (hU : Continuous U) {z : ℂ} {φ : ℝ → ℝ}
    (hφ : Continuous φ) {s : ℝ} (hs : s ∈ sigmaDom U hU z) :
    IntervalIntegrable (fun v => φ (argPath U hU z (sigmaTime U hU z v))) volume 0 s := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hs.1]
  exact (hφ.comp_continuousOn (continuousOn_argPath_sigmaTime hU z)).mono fun v hv =>
    mem_sigmaDom_of_le hs hv.1 hv.2

/-- **(2.27), integrated, deterministic**: `log|f̂'_s(z)| = -2 ∫₀ˢ cos(2θ̂_v) dv` for
`s ∈ sigmaDom`, where `f̂'_s(z) = g'_{σ_z(s)}(z)` and `θ̂_v = θ_{σ_z(v)}(z)`. -/
theorem log_norm_derivPath_sigmaTime (hU : Continuous U) {z : ℂ} {s : ℝ}
    (hs : s ∈ sigmaDom U hU z) :
    Real.log ‖derivPath U hU z (sigmaTime U hU z s)‖ =
      -2 * ∫ v in (0 : ℝ)..s, Real.cos (2 * argPath U hU z (sigmaTime U hU z v)) := by
  rw [log_norm_derivPath_eq_cos hU (sigmaTime_mem_lifeSet hU hs)]
  congr 1
  exact integral_comp_sigmaTime hU (φ := fun θ => Real.cos (2 * θ)) (by fun_prop) hs

end Deterministic

/-! ### The processes in σ-time -/

section Processes

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

variable (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ)

/-- `cos(2θ̂_v) = cos(2θ_{σ_z(v)}(z))`. -/
@[expose] noncomputable def cosTwoHat (ω : Ω) (v : ℝ) : ℝ :=
  Real.cos (2 * argPath (fun r => U r ω) (hU.cont ω) z (sigmaTime (fun r => U r ω) (hU.cont ω) z v))

/-- `ν(θ̂_v) + 2 cos(2θ̂_v)`: the drift density of `-log(|f̂'|/|f̂|)`, i.e. the integrand of the
integral (II) evaluated along `θ̂`. -/
@[expose] noncomputable def ratioDriftHat (ω : Ω) (v : ℝ) : ℝ :=
  nuHat hU z ω v + 2 * cosTwoHat hU z ω v

/-- `log|f̂'_s(z)| = log|g'_{σ_z(s)}(z)|` (junk off `sigmaDom`, a.s. never). -/
@[expose] noncomputable def sigmaLogDeriv (s : ℝ≥0) (ω : Ω) : ℝ :=
  Real.log ‖derivPath (fun r => U r ω) (hU.cont ω) z (sigmaTime (fun r => U r ω) (hU.cont ω) z s)‖

/-- `log|f̂_s(z)| = log|f_{σ_z(s)}(z)|` (junk off `sigmaDom`, a.s. never). -/
@[expose] noncomputable def sigmaLogNorm (s : ℝ≥0) (ω : Ω) : ℝ :=
  Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z (sigmaTime (fun r => U r ω) (hU.cont ω) z s)‖

/-- **`log(|f̂'_s(z)| / |f̂_s(z)|)`**, the process of Lemma 3.3 (junk off `sigmaDom`). -/
@[expose] noncomputable def sigmaLogRatio (s : ℝ≥0) (ω : Ω) : ℝ :=
  sigmaLogDeriv hU z s ω - sigmaLogNorm hU z s ω

open Classical in
/-- **The martingale part of `log(|f̂'|/|f̂|)`**:
`log(|f̂'_s|/|f̂_s|) + log|f̂_0| + ∫₀ˢ (ν(θ̂_v) + 2 cos 2θ̂_v) dv` on `sigmaDom` (and `0` off it,
a.s. never). It equals `-sigmaLogMart` (`sigmaLogRatioMart_eq_neg`). -/
@[expose] noncomputable def sigmaLogRatioMart (s : ℝ≥0) (ω : Ω) : ℝ :=
  if (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z then
    sigmaLogRatio hU z s ω + Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z 0‖ +
      ∫ v in (0 : ℝ)..(s : ℝ), ratioDriftHat hU z ω v
  else 0

variable {z}

theorem continuousOn_cosTwoHat (ω : Ω) :
    ContinuousOn (cosTwoHat hU z ω) (sigmaDom (fun r => U r ω) (hU.cont ω) z) :=
  (Real.continuous_cos.comp (continuous_const.mul continuous_id)).comp_continuousOn
    (continuousOn_argPath_sigmaTime (hU.cont ω) z)

theorem continuousOn_nuHat (ω : Ω) :
    ContinuousOn (nuHat hU z ω) (sigmaDom (fun r => U r ω) (hU.cont ω) z) :=
  (continuous_nu a b c).comp_continuousOn (continuousOn_argPath_sigmaTime (hU.cont ω) z)

theorem continuousOn_ratioDriftHat (ω : Ω) :
    ContinuousOn (ratioDriftHat hU z ω) (sigmaDom (fun r => U r ω) (hU.cont ω) z) :=
  (continuousOn_nuHat hU ω).add (continuousOn_const.mul (continuousOn_cosTwoHat hU ω))

/-- The drift density is bounded: `|ν(θ̂) + 2 cos 2θ̂| ≤ |2 - a/2 + b/2| + |c| + 2`. -/
theorem abs_ratioDriftHat_le (ω : Ω) (v : ℝ) :
    |ratioDriftHat hU z ω v| ≤ |2 - a / 2 + b / 2| + |c| + 2 := by
  simp only [ratioDriftHat, nuHat, cosTwoHat, nu]
  set θ := argPath (fun r => U r ω) (hU.cont ω) z (sigmaTime (fun r => U r ω) (hU.cont ω) z v)
  have h1 : |(2 - a / 2 + b / 2) * Real.cos (2 * θ)| ≤ |2 - a / 2 + b / 2| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have h2 : |c * Real.sin (2 * θ)| ≤ |c| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  have h3 : |2 * Real.cos (2 * θ)| ≤ 2 := by
    rw [abs_mul, abs_two]; exact mul_le_of_le_one_right (by norm_num) (Real.abs_cos_le_one _)
  have : (2 - a / 2 + b / 2) * Real.cos (2 * θ) - c * Real.sin (2 * θ) + 2 * Real.cos (2 * θ) =
      (2 - a / 2 + b / 2) * Real.cos (2 * θ) + -(c * Real.sin (2 * θ)) + 2 * Real.cos (2 * θ) := by
    ring
  rw [this]
  refine (abs_add_three _ _ _).trans ?_
  rw [abs_neg]
  linarith

theorem intervalIntegrable_nuHat {ω : Ω} {s : ℝ}
    (hs : s ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z) :
    IntervalIntegrable (nuHat hU z ω) volume 0 s :=
  intervalIntegrable_comp_argPath_sigmaTime (hU.cont ω) (continuous_nu a b c) hs

theorem intervalIntegrable_cosTwoHat {ω : Ω} {s : ℝ}
    (hs : s ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z) :
    IntervalIntegrable (cosTwoHat hU z ω) volume 0 s :=
  intervalIntegrable_comp_argPath_sigmaTime (hU.cont ω) (φ := fun θ => Real.cos (2 * θ))
    (by fun_prop) hs

theorem intervalIntegrable_ratioDriftHat {ω : Ω} {s : ℝ}
    (hs : s ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z) :
    IntervalIntegrable (ratioDriftHat hU z ω) volume 0 s :=
  (intervalIntegrable_nuHat hU hs).add ((intervalIntegrable_cosTwoHat hU hs).const_mul 2)

/-- `∫₀ˢ (ν(θ̂) + 2 cos 2θ̂) = ∫₀ˢ ν(θ̂) + 2 ∫₀ˢ cos 2θ̂` on `sigmaDom`. -/
theorem integral_ratioDriftHat {ω : Ω} {s : ℝ}
    (hs : s ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z) :
    ∫ v in (0 : ℝ)..s, ratioDriftHat hU z ω v =
      (∫ v in (0 : ℝ)..s, nuHat hU z ω v) + 2 * ∫ v in (0 : ℝ)..s, cosTwoHat hU z ω v := by
  simp only [ratioDriftHat]
  rw [intervalIntegral.integral_add (intervalIntegrable_nuHat hU hs)
    ((intervalIntegrable_cosTwoHat hU hs).const_mul 2), intervalIntegral.integral_const_mul]

/-- **(2.27) in σ-time** (`eqn-abs-zt'`, integrated): `log|f̂'_s| = -2 ∫₀ˢ cos(2θ̂_v) dv` on
`sigmaDom`. -/
theorem sigmaLogDeriv_eq {s : ℝ≥0} {ω : Ω}
    (hs : (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z) :
    sigmaLogDeriv hU z s ω = -2 * ∫ v in (0 : ℝ)..(s : ℝ), cosTwoHat hU z ω v :=
  log_norm_derivPath_sigmaTime (hU.cont ω) hs

/-- `log(|f̂'_0|/|f̂_0|) = -log|f_0(z)| = -log|z - U_0|` when `T_z > 0`. -/
theorem sigmaLogRatio_zero {ω : Ω} (hz : 0 < absorbingTime (fun r => U r ω) z) :
    sigmaLogRatio hU z 0 ω = -Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z 0‖ := by
  have h0 : (0 : ℝ) ∈ lifeSet (fun r => U r ω) z := zero_mem_lifeSet_iff.2 hz
  simp only [sigmaLogRatio, sigmaLogDeriv, sigmaLogNorm, NNReal.coe_zero,
    sigmaTime_zero (hU.cont ω) h0, derivPath_zero, norm_one, Real.log_one, zero_sub]

/-- **(eqn-sde-ratio) in integrated form** (paper.tex:L1437-1440), on `sigmaDom`:
`log(|f̂'_s|/|f̂_s|) = -log|f̂_0| - ∫₀ˢ (ν(θ̂_v) + 2 cos 2θ̂_v) dv - sigmaLogMart_s`, where
`sigmaLogMart` is the continuous `𝒢`-local martingale part of `log|f̂|` (2.26). -/
theorem sigmaLogRatio_eq {s : ℝ≥0} {ω : Ω}
    (hs : (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z) :
    sigmaLogRatio hU z s ω = -Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z 0‖ -
      (∫ v in (0 : ℝ)..(s : ℝ), ratioDriftHat hU z ω v) - sigmaLogMart hU z s ω := by
  rw [sigmaLogMart, ite_eq_left hs, sigmaLogRatio, sigmaLogDeriv_eq hU hs, sigmaLogNorm,
    integral_ratioDriftHat hU hs]
  ring

/-- The martingale part of `log(|f̂'|/|f̂|)` is `-sigmaLogMart` (everywhere). -/
theorem sigmaLogRatioMart_eq_neg : sigmaLogRatioMart hU z = -sigmaLogMart hU z := by
  funext s ω
  rw [Pi.neg_apply, Pi.neg_apply]
  by_cases hs : (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z
  · rw [sigmaLogRatioMart, ite_eq_left hs, sigmaLogRatio_eq hU hs]
    ring
  · rw [sigmaLogRatioMart, ite_eq_right hs, sigmaLogMart, ite_eq_right hs, neg_zero]

/-- The bracket of `sigmaLogRatioMart` is that of `sigmaLogMart`: on `sigmaDom`,
`sigmaLogMartSq_s = sigmaLogRatioMart_s² - ∫₀ˢ (a cos² θ̂ + b sin² θ̂ + 2c sin θ̂ cos θ̂) dv`. -/
theorem sigmaLogMartSq_eq_ratio {s : ℝ≥0} {ω : Ω}
    (hs : (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z) :
    sigmaLogMartSq hU z s ω =
      sigmaLogRatioMart hU z s ω ^ 2 - ∫ v in (0 : ℝ)..(s : ℝ), logBracketHat hU z ω v := by
  rw [sigmaLogMartSq_eq hU z hs, sigmaLogRatioMart_eq_neg, Pi.neg_apply, Pi.neg_apply, neg_sq]

section Martingales

variable [IsProbabilityMeasure P]

/-- **(eqn-sde-ratio), martingale form** (`step:polar-derivative-sde` + (2.26)): for `0 < a`,
`c² ≤ ab`, `z ≠ 0`, the process `log(|f̂'_s|/|f̂_s|) + log|f̂_0| + ∫₀ˢ (ν(θ̂_v) + 2 cos 2θ̂_v) dv`
is a continuous local martingale for the σ-time filtration `𝒢_s = ℱ_{σ_z(s)}`. -/
theorem isContLocalMartingale_sigmaLogRatioMart (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) :
    IsContLocalMartingale (sigmaFiltration hU z) (sigmaLogRatioMart hU z) P := by
  rw [sigmaLogRatioMart_eq_neg]
  exact (isContLocalMartingale_sigmaLogMart hU ha hc hz).neg

/-- **(2.27) in σ-time, a.s. for all `s`** (with Remark 2.12): a.s.
`log|f̂'_s| = -2 ∫₀ˢ cos(2θ̂_v) dv` for every `s ≥ 0`. -/
theorem ae_sigmaLogDeriv_eq (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0,
      sigmaLogDeriv hU z s ω = -2 * ∫ v in (0 : ℝ)..(s : ℝ), cosTwoHat hU z ω v := by
  filter_upwards [ae_sigmaDom_eq_Ici hU z ha hc hz] with ω hω s
  exact sigmaLogDeriv_eq hU (by rw [hω]; exact s.coe_nonneg)

/-- **(eqn-sde-ratio), a.s. for all `s`** (with Remark 2.12): a.s., for every `s ≥ 0`,
`log(|f̂'_s|/|f̂_s|) = -log|f̂_0| - ∫₀ˢ (ν(θ̂_v) + 2 cos 2θ̂_v) dv - sigmaLogMart_s`. -/
theorem ae_sigmaLogRatio_eq (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0,
      sigmaLogRatio hU z s ω = -Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z 0‖ -
        (∫ v in (0 : ℝ)..(s : ℝ), ratioDriftHat hU z ω v) - sigmaLogMart hU z s ω := by
  filter_upwards [ae_sigmaDom_eq_Ici hU z ha hc hz] with ω hω s
  exact sigmaLogRatio_eq hU (by rw [hω]; exact s.coe_nonneg)

end Martingales

end Processes

end ComplexSLE.Internal.Polar

end
