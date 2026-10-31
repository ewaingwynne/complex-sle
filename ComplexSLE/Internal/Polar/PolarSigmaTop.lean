/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.PolarItoLog
public import ComplexSLE.Internal.Polar.PolarTimeCapExit

/-!
# Remark 2.12: `σ_z` is defined on all of `[0, ∞)` a.s. (M6/S12, `remark-sigma`)

For an adapted `SLE_Σ` driver (`0 < a`, `c² ≤ ab`) and `z ≠ 0`, almost surely
`clockSup = sup_{t < T_z} ∫₀ᵗ |f_s(z)|⁻² ds = ∞` (paper.tex:L893-L896), so that `σ_z` maps
`[0, ∞)` onto `[0, T_z)` (`image_sigmaTime`, `sigmaDom_eq_Ici`).

The source argues through the SDE (2.26) with bounded coefficients; in martingale form the
argument is an `L²` estimate in original time. With `N^N = logMart` the martingale part of
`log|f|` stopped at the annulus exit time `τ_N` and `Γ^N = logBracket` its bracket density
(`PolarItoLog.lean`), both densities are bounded by multiples of the clock rate `|f_s|⁻²`:
`|β| ≤ C_ν |f|⁻²`, `0 ≤ Γ ≤ (a + b + |c|) |f|⁻²`. Stopping at the capped exit time
`ρ = capExitTime n m T ≤ τ_N` (`PolarTimeCapExit.lean`), whose clock is at most `T`, gives
`E[(N^N_ρ)²] = E[∫₀^ρ Γ^N] ≤ (a + b + |c|) T` (optional stopping along a localising sequence and
Fatou), hence `P(|N^N_ρ| ≥ L) ≤ (a + b + |c|) T / L²`. On the event `{A(t) < T for all t < T_z}`
the clock cap is inactive and the annulus `1/n < |f| < n` is left in the life set, so for `m`
large `|log|f_ρ|| ≥ log n` while the drift integral is at most `C_ν T`; thus
`|N^N_ρ| ≥ log n - |log|f_0|| - C_ν T → ∞`, and the event is null.
-/

public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal.Polar

/-! ### Pointwise bounds on the drift and bracket densities -/

theorem abs_two_mul_mul_le (c x y : ℝ) : |2 * c * x * y| ≤ |c| * (x ^ 2 + y ^ 2) := by
  rw [show 2 * c * x * y = c * (2 * x * y) by ring, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]

/-- `|β(v)| ≤ (|2 - a/2 + b/2| + |c|) / |v|²`. -/
theorem abs_betaFn_le (a b c : ℝ) {v : Fin 2 → ℝ} (hv : v ∈ posSet₂) :
    |betaFn a b c v| ≤ (|2 - a / 2 + b / 2| + |c|) / (v 0 ^ 2 + v 1 ^ 2) := by
  have hq : 0 < v 0 ^ 2 + v 1 ^ 2 := hv
  unfold betaFn
  rw [abs_div, abs_of_pos (pow_pos hq 2), div_le_div_iff₀ (pow_pos hq 2) hq]
  have h1 : |(2 - a / 2 + b / 2) * (v 0 ^ 2 - v 1 ^ 2)| ≤
      |2 - a / 2 + b / 2| * (v 0 ^ 2 + v 1 ^ 2) := by
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  have h2 := abs_two_mul_mul_le c (v 0) (v 1)
  calc |(2 - a / 2 + b / 2) * (v 0 ^ 2 - v 1 ^ 2) - 2 * c * v 0 * v 1| * (v 0 ^ 2 + v 1 ^ 2)
      ≤ (|(2 - a / 2 + b / 2) * (v 0 ^ 2 - v 1 ^ 2)| + |2 * c * v 0 * v 1|) *
          (v 0 ^ 2 + v 1 ^ 2) := mul_le_mul_of_nonneg_right (abs_sub _ _) hq.le
    _ ≤ ((|2 - a / 2 + b / 2| + |c|) * (v 0 ^ 2 + v 1 ^ 2)) * (v 0 ^ 2 + v 1 ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) hq.le
    _ = (|2 - a / 2 + b / 2| + |c|) * (v 0 ^ 2 + v 1 ^ 2) ^ 2 := by ring

/-- `Γ(v) ≤ (a + b + |c|) / |v|²` for `a, b ≥ 0`. -/
theorem gammaFn_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (c : ℝ) {v : Fin 2 → ℝ}
    (hv : v ∈ posSet₂) : gammaFn a b c v ≤ (a + b + |c|) / (v 0 ^ 2 + v 1 ^ 2) := by
  have hq : 0 < v 0 ^ 2 + v 1 ^ 2 := hv
  unfold gammaFn
  rw [div_le_div_iff₀ (pow_pos hq 2) hq]
  have h2 := (le_abs_self _).trans (abs_two_mul_mul_le c (v 0) (v 1))
  calc (a * v 0 ^ 2 + 2 * c * v 0 * v 1 + b * v 1 ^ 2) * (v 0 ^ 2 + v 1 ^ 2)
      ≤ ((a + b + |c|) * (v 0 ^ 2 + v 1 ^ 2)) * (v 0 ^ 2 + v 1 ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ hq.le
        nlinarith [mul_nonneg ha (sq_nonneg (v 1)), mul_nonneg hb (sq_nonneg (v 0))]
    _ = (a + b + |c|) * (v 0 ^ 2 + v 1 ^ 2) ^ 2 := by ring

/-- `Γ ≥ 0` when the covariance matrix is positive semidefinite. -/
theorem gammaFn_nonneg {a b c : ℝ} (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (v : Fin 2 → ℝ) :
    0 ≤ gammaFn a b c v := by
  unfold gammaFn
  refine div_nonneg ?_ (by positivity)
  have : 0 ≤ a * (a * v 0 ^ 2 + 2 * c * v 0 * v 1 + b * v 1 ^ 2) := by
    nlinarith [sq_nonneg (a * v 0 + c * v 1), mul_nonneg (sub_nonneg.2 hc) (sq_nonneg (v 1))]
  exact (mul_nonneg_iff_of_pos_left ha).1 this

theorem b_nonneg_of_sq_le {a b c : ℝ} (ha : 0 < a) (hc : c ^ 2 ≤ a * b) : 0 ≤ b :=
  (mul_nonneg_iff_of_pos_left ha).1 ((sq_nonneg c).trans hc)

/-! ### The capped exit times as random times -/

section Processes

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

variable (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ)

/-- The capped exit time `capExitTime n m T` as a real random time. -/
@[expose] noncomputable def capExitR (n : ℕ) (mT T : ℝ) (ω : Ω) : ℝ :=
  capExitTime (fun r => U r ω) (hU.cont ω) z n mT T

/-- The capped exit time as an `ℝ≥0`-valued random time. -/
@[expose] noncomputable def capExitNN (n : ℕ) (mT T : ℝ) (ω : Ω) : ℝ≥0 :=
  (capExitR hU z n mT T ω).toNNReal

theorem capExitR_nonneg (n : ℕ) (mT T : ℝ) (ω : Ω) : 0 ≤ capExitR hU z n mT T ω :=
  capExitTime_nonneg' _ _ _ _ _

theorem coe_capExitNN (n : ℕ) (mT T : ℝ) (ω : Ω) :
    ((capExitNN hU z n mT T ω : ℝ≥0) : ℝ) = capExitR hU z n mT T ω :=
  Real.coe_toNNReal _ (capExitR_nonneg hU z n mT T ω)

theorem isStoppingTime_capExitNN (n : ℕ) (mT T : ℝ) :
    IsStoppingTime ℱ fun ω => (capExitNN hU z n mT T ω : WithTop ℝ≥0) :=
  isStoppingTime_capExitTime hU.cont hU.adapted z n mT T

theorem capExitR_le_exitR {n N : ℕ} (hn : n ≤ N) {mT : ℝ} (hm : mT ≤ N) (T : ℝ) (ω : Ω) :
    capExitR hU z n mT T ω ≤ exitR hU z N ω := by
  by_cases hz : 0 < absorbingTime (fun s => U s ω) z
  · exact capExitTime_le_exitTime (hU.cont ω) hz hn hm T
  · rw [capExitR, capExitTime_eq_zero_of_not_pos (hU.cont ω) hz, exitR,
      exitTime_eq_zero_of_not_pos (hU.cont ω) hz]

theorem capExitNN_le_exitNN {n N : ℕ} (hn : n ≤ N) {mT : ℝ} (hm : mT ≤ N) (T : ℝ) (ω : Ω) :
    capExitNN hU z n mT T ω ≤ exitNN hU z N ω := by
  rw [← NNReal.coe_le_coe, coe_capExitNN, coe_exitNN]
  exact capExitR_le_exitR hU z hn hm T ω

theorem exitNN_le_nat (N : ℕ) (ω : Ω) : exitNN hU z N ω ≤ N := by
  rw [exitNN, Real.toNNReal_le_iff_le_coe, NNReal.coe_natCast]
  by_cases hz : 0 < absorbingTime (fun s => U s ω) z
  · exact exitTime_le_nat (hU.cont ω) hz N
  · rw [exitR, exitTime_eq_zero_of_not_pos (hU.cont ω) hz]; exact N.cast_nonneg

theorem capExitNN_le_nat {n N : ℕ} (hn : n ≤ N) {mT : ℝ} (hm : mT ≤ N) (T : ℝ) (ω : Ω) :
    capExitNN hU z n mT T ω ≤ N :=
  (capExitNN_le_exitNN hU z hn hm T ω).trans (exitNN_le_nat hU z N ω)

/-! ### Integral bounds up to the capped exit time -/

/-- `|v|² = ‖f‖²` for the Itô state before `τ_N`. -/
theorem itoState_sq_sum {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) {N : ℕ} {s : ℝ}
    (hs : 0 ≤ s) (hsτ : s ≤ exitR hU z N ω) :
    itoState hU z N s.toNNReal ω 0 ^ 2 + itoState hU z N s.toNNReal ω 1 ^ 2 =
      ‖fPath (fun r => U r ω) (hU.cont ω) z s‖ ^ 2 := by
  have hs' : (s.toNNReal : ℝ) ≤ exitR hU z N ω := by rwa [Real.coe_toNNReal _ hs]
  rw [itoState, stoppedF_eq_of_le hU z N hz hs', Real.coe_toNNReal _ hs, reIm_zero_apply,
    reIm_one_apply, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- **Bracket bound**: for `u ≤ capExitTime n m T` and `n, m ≤ N`,
`∫₀ᵘ Γ^N ≤ (a + b + |c|) T`. -/
theorem pathIntegral_logBracket_le (ha : 0 < a) (hc : c ^ 2 ≤ a * b) {n N : ℕ} (hn : n ≤ N)
    {mT : ℝ} (hm : mT ≤ N) {T : ℝ} (hT : 0 ≤ T) {ω : Ω} {u : ℝ≥0}
    (hu : u ≤ capExitNN hU z n mT T ω) :
    pathIntegral (logBracket hU z N) u ω ≤ (a + b + |c|) * T := by
  have hb : 0 ≤ b := b_nonneg_of_sq_le ha hc
  by_cases hz : 0 < absorbingTime (fun s => U s ω) z
  · have hρl : capExitR hU z n mT T ω ∈ lifeSet (fun s => U s ω) z :=
      capExitTime_mem_lifeSet (hU.cont ω) hz n mT T
    have hu' : (u : ℝ) ≤ capExitR hU z n mT T ω := by
      rwa [← coe_capExitNN, NNReal.coe_le_coe]
    have hul : (u : ℝ) ∈ lifeSet (fun s => U s ω) z := mem_lifeSet_of_le hρl u.coe_nonneg hu'
    have hρτ : capExitR hU z n mT T ω ≤ exitR hU z N ω :=
      capExitTime_le_exitTime (hU.cont ω) hz hn hm T
    have hpt : ∀ s ∈ Icc (0 : ℝ) u, logBracket hU z N s.toNNReal ω ≤
        (a + b + |c|) * clockRate (fun r => U r ω) (hU.cont ω) z s := by
      intro s hs
      have hsτ : s ≤ exitR hU z N ω := hs.2.trans (hu'.trans hρτ)
      have hs' : (s.toNNReal : ℝ) ≤ exitR hU z N ω := by rwa [Real.coe_toNNReal _ hs.1]
      have h1 : beforeExit hU z N s.toNNReal ω = 1 := by
        simp [beforeExit, (le_exitNN_iff hU z N).2 hs']
      rw [logBracket, h1, one_mul, clockRate, ← div_eq_mul_inv,
        ← itoState_sq_sum hU z hz hs.1 hsτ]
      exact gammaFn_le ha.le hb c (itoState_mem_posSet₂ hU z N hz _)
    calc pathIntegral (logBracket hU z N) u ω
        ≤ ∫ s in (0 : ℝ)..u, (a + b + |c|) * clockRate (fun r => U r ω) (hU.cont ω) z s := by
          unfold pathIntegral
          refine intervalIntegral.integral_mono_on u.coe_nonneg ?_ ?_ hpt
          · exact intervalIntegrable_beforeExit_mul hU z N (continuousOn_gammaFn a b c) ω u
          · exact (intervalIntegrable_clockRate (hU.cont ω) hul).const_mul _
      _ = (a + b + |c|) * clock (fun r => U r ω) (hU.cont ω) z u := by
          rw [intervalIntegral.integral_const_mul]; rfl
      _ ≤ (a + b + |c|) * T := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact (clock_monotoneOn (hU.cont ω) z hul hρl hu').trans
            (clock_capExitTime_le (hU.cont ω) hz n mT hT)
  · have hu0 : u = 0 := by
      refine le_antisymm ?_ bot_le
      have := hu
      rwa [capExitNN, capExitR, capExitTime_eq_zero_of_not_pos (hU.cont ω) hz,
        Real.toNNReal_zero] at this
    subst hu0
    rw [pathIntegral_zero_time]
    positivity

/-- The bracket integral is nonnegative. -/
theorem pathIntegral_logBracket_nonneg (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (N : ℕ) (u : ℝ≥0)
    (ω : Ω) : 0 ≤ pathIntegral (logBracket hU z N) u ω := by
  unfold pathIntegral
  refine intervalIntegral.integral_nonneg u.coe_nonneg fun s _ => ?_
  unfold logBracket beforeExit
  split_ifs <;> simp [gammaFn_nonneg ha hc]

/-- **Drift bound**: for `u ≤ capExitTime n m T` and `n, m ≤ N`,
`|∫₀ᵘ 1_{s ≤ τ_N} ν(θ_s)|f_s|⁻² ds| ≤ (|2 - a/2 + b/2| + |c|) T`. -/
theorem abs_pathIntegral_logDrift_le {n N : ℕ} (hn : n ≤ N) {mT : ℝ} (hm : mT ≤ N) {T : ℝ}
    (hT : 0 ≤ T) {ω : Ω} {u : ℝ≥0} (hu : u ≤ capExitNN hU z n mT T ω) :
    |pathIntegral (logDrift hU z N) u ω| ≤ (|2 - a / 2 + b / 2| + |c|) * T := by
  by_cases hz : 0 < absorbingTime (fun s => U s ω) z
  · have hρl : capExitR hU z n mT T ω ∈ lifeSet (fun s => U s ω) z :=
      capExitTime_mem_lifeSet (hU.cont ω) hz n mT T
    have hu' : (u : ℝ) ≤ capExitR hU z n mT T ω := by
      rwa [← coe_capExitNN, NNReal.coe_le_coe]
    have hul : (u : ℝ) ∈ lifeSet (fun s => U s ω) z := mem_lifeSet_of_le hρl u.coe_nonneg hu'
    have hρτ : capExitR hU z n mT T ω ≤ exitR hU z N ω :=
      capExitTime_le_exitTime (hU.cont ω) hz hn hm T
    have hpt : ∀ s ∈ Icc (0 : ℝ) u, |logDrift hU z N s.toNNReal ω| ≤
        (|2 - a / 2 + b / 2| + |c|) * clockRate (fun r => U r ω) (hU.cont ω) z s := by
      intro s hs
      have hsτ : s ≤ exitR hU z N ω := hs.2.trans (hu'.trans hρτ)
      have hs' : (s.toNNReal : ℝ) ≤ exitR hU z N ω := by rwa [Real.coe_toNNReal _ hs.1]
      have h1 : beforeExit hU z N s.toNNReal ω = 1 := by
        simp [beforeExit, (le_exitNN_iff hU z N).2 hs']
      rw [logDrift, h1, one_mul, clockRate, ← div_eq_mul_inv,
        ← itoState_sq_sum hU z hz hs.1 hsτ]
      exact abs_betaFn_le a b c (itoState_mem_posSet₂ hU z N hz _)
    calc |pathIntegral (logDrift hU z N) u ω|
        ≤ ∫ s in (0 : ℝ)..u, |logDrift hU z N s.toNNReal ω| :=
          intervalIntegral.abs_integral_le_integral_abs u.coe_nonneg
      _ ≤ ∫ s in (0 : ℝ)..u, (|2 - a / 2 + b / 2| + |c|) *
            clockRate (fun r => U r ω) (hU.cont ω) z s := by
          refine intervalIntegral.integral_mono_on u.coe_nonneg ?_ ?_ hpt
          · exact (intervalIntegrable_beforeExit_mul hU z N (continuousOn_betaFn a b c) ω u).abs
          · exact (intervalIntegrable_clockRate (hU.cont ω) hul).const_mul _
      _ = (|2 - a / 2 + b / 2| + |c|) * clock (fun r => U r ω) (hU.cont ω) z u := by
          rw [intervalIntegral.integral_const_mul]; rfl
      _ ≤ (|2 - a / 2 + b / 2| + |c|) * T := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact (clock_monotoneOn (hU.cont ω) z hul hρl hu').trans
            (clock_capExitTime_le (hU.cont ω) hz n mT hT)
  · have hu0 : u = 0 := by
      refine le_antisymm ?_ bot_le
      have := hu
      rwa [capExitNN, capExitR, capExitTime_eq_zero_of_not_pos (hU.cont ω) hz,
        Real.toNNReal_zero] at this
    subst hu0
    rw [pathIntegral_zero_time, abs_zero]
    positivity

/-! ### The value of `N^N` at the capped exit time -/

/-- On `{T_z > 0}`, the value of `N^N` at the capped exit time `ρ = capExitTime n N T`:
`N^N_ρ = log|f_ρ| - log|f_0| - ∫₀^ρ ν(θ)|f|⁻²`. -/
theorem logMart_capExitNN_eq {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) {n N : ℕ}
    (hn : n ≤ N) (T : ℝ) :
    logMart hU z N (capExitNN hU z n N T ω) ω =
      Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z (capExitR hU z n N T ω)‖ -
        Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z 0‖ -
        pathIntegral (logDrift hU z N) (capExitNN hU z n N T ω) ω := by
  have hρτ : ((capExitNN hU z n N T ω : ℝ≥0) : ℝ) ≤ exitR hU z N ω := by
    rw [coe_capExitNN]; exact capExitTime_le_exitTime (hU.cont ω) hz hn le_rfl T
  rw [logMart, logNormF, logNormF, stoppedF_eq_of_le hU z N hz hρτ, coe_capExitNN,
    stoppedF_eq_of_le hU z N hz (by rw [NNReal.coe_zero]; exact exitR_nonneg hU z N ω),
    NNReal.coe_zero]

/-! ### The `L²` bound at the capped exit time -/

section Martingale

variable [IsProbabilityMeasure P]

/-- The stopped value `N^N_ρ` is measurable. -/
theorem measurable_logMart_capExitNN (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) {n N : ℕ}
    (hn : n ≤ N) {mT : ℝ} (hm : mT ≤ N) (T : ℝ) :
    Measurable fun ω => logMart hU z N (capExitNN hU z n mT T ω) ω := by
  have h := stronglyMeasurable_stoppedValue_of_le (isContLocalMartingale_logMart hU z N ha hc hz).1
    (isStoppingTime_capExitNN hU z n mT T) (n := N)
    (fun ω => WithTop.coe_le_coe.2 (capExitNN_le_nat hU z hn hm T ω))
  exact (h.measurable.mono (ℱ.le N) le_rfl)

/-- **`L²` bound at the capped exit time**: `E[(N^N_ρ)²] ≤ (a + b + |c|) T` for
`ρ = capExitTime n m T`, `n, m ≤ N`. -/
theorem lintegral_sq_logMart_capExitNN_le (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0)
    {n N : ℕ} (hn : n ≤ N) {mT : ℝ} (hm : mT ≤ N) {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ ω, ENNReal.ofReal (logMart hU z N (capExitNN hU z n mT T ω) ω ^ 2) ∂P ≤
      ENNReal.ofReal ((a + b + |c|) * T) := by
  set ρ := capExitNN hU z n mT T with hρdef
  have hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0) := isStoppingTime_capExitNN hU z n mT T
  have hρN : ∀ ω, ρ ω ≤ N := capExitNN_le_nat hU z hn hm T
  -- the stopped processes
  set Mρ : ℝ≥0 → Ω → ℝ := fun t ω => logMart hU z N (min t (ρ ω)) ω with hMρ
  set Gρ : ℝ≥0 → Ω → ℝ := fun t ω => pathIntegral (logBracket hU z N) (min t (ρ ω)) ω with hGρ
  have hstop : ∀ (X : ℝ≥0 → Ω → ℝ), (fun t ω => X (min t (ρ ω)) ω) =
      stoppedProcess X fun ω => (ρ ω : WithTop ℝ≥0) := by
    intro X; funext t ω
    simp only [stoppedProcess]
    rw [← WithTop.coe_min]
    rfl
  have hMρprog : IsStronglyProgressive ℱ Mρ := by
    rw [hMρ, hstop]
    exact (isContLocalMartingale_logMart hU z N ha hc hz).1.stoppedProcess hρ
  have hGρprog : IsStronglyProgressive ℱ Gρ := by
    rw [hGρ, hstop]
    exact (isStronglyProgressive_pathIntegral_beforeExit hU z N (measurable_gammaFn a b c)
      (continuousOn_gammaFn a b c)).stoppedProcess hρ
  -- `Z_t = M(t ∧ ρ)² - ∫₀^{t ∧ ρ} Γ` is a continuous local martingale
  have hZ : IsContLocalMartingale ℱ (fun t ω => Mρ t ω ^ 2 - Gρ t ω) P :=
    (isContLocalMartingale_logMart_sq_sub hU z N ha hc hz).stopped_min_of_continuous ℱ
      (fun ω => ((continuous_logMart hU z N ω).pow 2).sub
        (continuous_pathIntegral_beforeExit hU z N (continuousOn_gammaFn a b c) ω)) hρ
  obtain ⟨-, -, σ, hσ, hσev, hmart⟩ := hZ
  -- the values at time `N` of the processes stopped at `σ k`
  have hbound : ∀ ω (t : ℝ≥0), Gρ t ω ≤ (a + b + |c|) * T := fun ω t =>
    pathIntegral_logBracket_le hU z ha hc hn hm hT (min_le_right _ _)
  have hGnn : ∀ ω (t : ℝ≥0), 0 ≤ Gρ t ω := fun ω t =>
    pathIntegral_logBracket_nonneg hU z ha hc N _ ω
  have hmeasM : ∀ k, Measurable (stoppedProcess Mρ (σ k) N) := fun k =>
    ((hMρprog.stoppedProcess (hσ k)).stronglyAdapted N).measurable.mono (ℱ.le N) le_rfl
  have hmeasG : ∀ k, Measurable (stoppedProcess Gρ (σ k) N) := fun k =>
    ((hGρprog.stoppedProcess (hσ k)).stronglyAdapted N).measurable.mono (ℱ.le N) le_rfl
  have hintG : ∀ k, Integrable (stoppedProcess Gρ (σ k) N) P := fun k => by
    refine Integrable.of_bound (hmeasG k).aestronglyMeasurable ((a + b + |c|) * T)
      (Eventually.of_forall fun ω => ?_)
    change ‖Gρ ((min (N : WithTop ℝ≥0) (σ k ω)).untopA) ω‖ ≤ (a + b + |c|) * T
    rw [Real.norm_eq_abs, abs_of_nonneg (hGnn ω _)]
    exact hbound ω _
  have hZeq : ∀ k, stoppedProcess (fun t ω => Mρ t ω ^ 2 - Gρ t ω) (σ k) N =
      fun ω => stoppedProcess Mρ (σ k) N ω ^ 2 - stoppedProcess Gρ (σ k) N ω := fun k => rfl
  have hintZ : ∀ k, Integrable (stoppedProcess (fun t ω => Mρ t ω ^ 2 - Gρ t ω) (σ k) N) P :=
    fun k => (hmart k).integrable N
  have hintM : ∀ k, Integrable (fun ω => stoppedProcess Mρ (σ k) N ω ^ 2) P := fun k => by
    have h := (hintZ k).add (hintG k)
    rw [hZeq] at h
    refine h.congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply]; ring
  -- optional stopping: `E[Z^{σ k}_N] = E[Z^{σ k}_0] = 0`
  have hEZ : ∀ k, ∫ ω, stoppedProcess (fun t ω => Mρ t ω ^ 2 - Gρ t ω) (σ k) N ω ∂P = 0 := by
    intro k
    have h := (hmart k).setIntegral_eq (by simp : (0 : ℝ≥0) ≤ N) MeasurableSet.univ
    rw [setIntegral_univ, setIntegral_univ] at h
    rw [← h]
    have h0 : ∀ ω, stoppedProcess (fun t ω => Mρ t ω ^ 2 - Gρ t ω) (σ k) 0 ω = 0 := by
      intro ω
      simp only [stoppedProcess, hMρ, hGρ]
      have : (min ((0 : ℝ≥0) : WithTop ℝ≥0) (σ k ω)).untopA = 0 := by
        rw [min_eq_left (by simp)]; rfl
      rw [this]
      simp [logMart_zero, pathIntegral_zero_time]
    simp [h0]
  -- hence `E[M(N ∧ σ k ∧ ρ)²] = E[Γ-integral] ≤ K T`
  have hEM : ∀ k, ∫⁻ ω, ENNReal.ofReal (stoppedProcess Mρ (σ k) N ω ^ 2) ∂P ≤
      ENNReal.ofReal ((a + b + |c|) * T) := by
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal (hintM k) (Eventually.of_forall fun ω => sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : ∫ ω, stoppedProcess Mρ (σ k) N ω ^ 2 ∂P =
        ∫ ω, stoppedProcess (fun t ω => Mρ t ω ^ 2 - Gρ t ω) (σ k) N ω ∂P +
          ∫ ω, stoppedProcess Gρ (σ k) N ω ∂P := by
      rw [← integral_add (hintZ k) (hintG k), hZeq]
      congr 1; funext ω; ring
    rw [h1, hEZ k, zero_add]
    calc ∫ ω, stoppedProcess Gρ (σ k) N ω ∂P ≤ ∫ _, (a + b + |c|) * T ∂P :=
          integral_mono (hintG k) (integrable_const _) fun ω => hbound ω _
      _ = (a + b + |c|) * T := by simp
  -- Fatou: `M(N ∧ σ k ∧ ρ) → M ρ` pointwise a.s. (eventually `σ k ≥ N ≥ ρ`)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun k => ENNReal.ofReal (stoppedProcess Mρ (σ k) N ω ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (logMart hU z N (ρ ω) ω ^ 2))) := by
    filter_upwards [hσev] with ω hω
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hω N] with k hk
    simp only [stoppedProcess, hMρ]
    rw [min_eq_left hk]
    have : ((N : ℝ≥0) : WithTop ℝ≥0).untopA = N := rfl
    rw [this, min_eq_right (hρN ω)]
  calc ∫⁻ ω, ENNReal.ofReal (logMart hU z N (ρ ω) ω ^ 2) ∂P
      = ∫⁻ ω, liminf (fun k => ENNReal.ofReal (stoppedProcess Mρ (σ k) N ω ^ 2)) atTop ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hlim] with ω hω
        exact hω.liminf_eq.symm
    _ ≤ liminf (fun k => ∫⁻ ω, ENNReal.ofReal (stoppedProcess Mρ (σ k) N ω ^ 2) ∂P) atTop :=
        lintegral_liminf_le' fun k => (ENNReal.measurable_ofReal.comp
          ((hmeasM k).pow_const 2)).aemeasurable
    _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal ((a + b + |c|) * T)) atTop :=
        liminf_le_liminf (Eventually.of_forall hEM)
    _ = ENNReal.ofReal ((a + b + |c|) * T) := liminf_const _

/-- **Chebyshev at the capped exit time**: `P(|N^N_ρ| ≥ L) ≤ (a + b + |c|) T / L²`. -/
theorem measure_le_abs_logMart_capExitNN_le (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0)
    {n N : ℕ} (hn : n ≤ N) {mT : ℝ} (hm : mT ≤ N) {T : ℝ} (hT : 0 ≤ T) {L : ℝ} (hL : 0 < L) :
    P {ω | L ≤ |logMart hU z N (capExitNN hU z n mT T ω) ω|} ≤
      ENNReal.ofReal ((a + b + |c|) * T / L ^ 2) := by
  have hmeas := measurable_logMart_capExitNN hU z ha hc hz hn hm T
  have h1 := mul_meas_ge_le_lintegral₀ (μ := P)
    (f := fun ω => ENNReal.ofReal (logMart hU z N (capExitNN hU z n mT T ω) ω ^ 2))
    (ENNReal.measurable_ofReal.comp (hmeas.pow_const 2)).aemeasurable (ENNReal.ofReal (L ^ 2))
  have h2 := lintegral_sq_logMart_capExitNN_le hU z ha hc hz hn hm hT
  have hsub : {ω | L ≤ |logMart hU z N (capExitNN hU z n mT T ω) ω|} ⊆
      {ω | ENNReal.ofReal (L ^ 2) ≤
        ENNReal.ofReal (logMart hU z N (capExitNN hU z n mT T ω) ω ^ 2)} := by
    intro ω hω
    refine ENNReal.ofReal_le_ofReal ?_
    calc L ^ 2 ≤ |logMart hU z N (capExitNN hU z n mT T ω) ω| ^ 2 := pow_le_pow_left₀ hL.le hω 2
      _ = logMart hU z N (capExitNN hU z n mT T ω) ω ^ 2 := sq_abs _
  have hL2 : (0 : ℝ) < L ^ 2 := by positivity
  calc P {ω | L ≤ |logMart hU z N (capExitNN hU z n mT T ω) ω|}
      ≤ P {ω | ENNReal.ofReal (L ^ 2) ≤
          ENNReal.ofReal (logMart hU z N (capExitNN hU z n mT T ω) ω ^ 2)} := measure_mono hsub
    _ ≤ ENNReal.ofReal ((a + b + |c|) * T) / ENNReal.ofReal (L ^ 2) := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hL2).ne')
          (Or.inl ENNReal.ofReal_ne_top), mul_comm]
        exact h1.trans h2
    _ = ENNReal.ofReal ((a + b + |c|) * T / L ^ 2) := (ENNReal.ofReal_div_of_pos hL2).symm

/-! ### Remark 2.12 -/

/-- **Remark 2.12** (`remark-sigma`, paper.tex:L893-L896): for an adapted `SLE_Σ` driver
(`0 < a`, `c² ≤ ab`) and `z ≠ 0`, almost surely `sup_{t < T_z} ∫₀ᵗ |f_s(z)|⁻² ds = ∞`, i.e.
`σ_z` is defined on all of `[0, ∞)` and maps it onto `[0, T_z)` (`image_sigmaTime`). -/
theorem ae_clockSup_eq_top (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, clockSup (fun s => U s ω) (hU.cont ω) z = ⊤ := by
  set K : ℝ := a + b + |c| with hK
  set Cν : ℝ := |2 - a / 2 + b / 2| + |c| with hCν
  have hCν0 : 0 ≤ Cν := by positivity
  -- Step A: the events `E T R` are null
  have hnull : ∀ T R : ℕ, P {ω | 0 < absorbingTime (fun s => U s ω) z ∧
      (∀ t ∈ lifeSet (fun s => U s ω) z, clock (fun s => U s ω) (hU.cont ω) z t < T) ∧
      |Real.log ‖fPath (fun s => U s ω) (hU.cont ω) z 0‖| ≤ R} = 0 := by
    intro T R
    set E := {ω | 0 < absorbingTime (fun s => U s ω) z ∧
      (∀ t ∈ lifeSet (fun s => U s ω) z, clock (fun s => U s ω) (hU.cont ω) z t < T) ∧
      |Real.log ‖fPath (fun s => U s ω) (hU.cont ω) z 0‖| ≤ R} with hE
    have hT0 : (0 : ℝ) ≤ T := T.cast_nonneg
    -- the bound for a fixed level `n`
    have hbound : ∀ n : ℕ, 0 < Real.log n - R - Cν * T →
        P E ≤ ENNReal.ofReal (K * T / (Real.log n - R - Cν * T) ^ 2) := by
      intro n hL
      have hn1 : 1 ≤ n := by
        rcases Nat.eq_zero_or_pos n with hn0 | hnpos
        · exfalso
          rw [hn0, Nat.cast_zero, Real.log_zero] at hL
          have : (0 : ℝ) ≤ R := R.cast_nonneg
          nlinarith
        · exact hnpos
      set L := Real.log n - R - Cν * T with hLdef
      have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
      let B : ℕ → Set Ω := fun k =>
        {ω | L ≤ |logMart hU z (n + k) (capExitNN hU z n ((n + k : ℕ) : ℝ) T ω) ω|}
      have hB : ∀ k, P (B k) ≤ ENNReal.ofReal (K * T / L ^ 2) := fun k =>
        measure_le_abs_logMart_capExitNN_le hU z ha hc hz (Nat.le_add_right n k) le_rfl hT0 hL
      have hsub : E ⊆ ⋃ j, ⋂ k, ⋂ (_ : j ≤ k), B k := by
        rintro ω ⟨hz', hEω, hR⟩
        obtain ⟨t, ht, hex⟩ := exists_annulus_exit (hU.cont ω) hz' hn1 hEω
        refine mem_iUnion.2 ⟨⌈t⌉₊ + 1, mem_iInter₂.2 fun k hk => ?_⟩
        have htm : t < ((n + k : ℕ) : ℝ) := by
          have h1 : t ≤ ⌈t⌉₊ := Nat.le_ceil t
          have h2 : ((⌈t⌉₊ + 1 : ℕ) : ℝ) ≤ ((n + k : ℕ) : ℝ) := by
            exact_mod_cast hk.trans (Nat.le_add_left k n)
          push_cast at h2 ⊢
          linarith
        have hann := norm_fPath_capExitTime_of_exit (hU.cont ω) hz' hEω ht htm hex
        set ρ := capExitR hU z n ((n + k : ℕ) : ℝ) T ω with hρ
        have hρl : ρ ∈ lifeSet (fun s => U s ω) z :=
          capExitTime_mem_lifeSet (hU.cont ω) hz' n _ T
        have hfpos : 0 < ‖fPath (fun r => U r ω) (hU.cont ω) z ρ‖ := norm_fPath_pos (hU.cont ω) hρl
        -- `|log|f_ρ|| ≥ log n`
        have hlog : Real.log n ≤ |Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z ρ‖| := by
          rcases hann with h | h
          · have := Real.log_le_log hfpos h
            rw [one_div, Real.log_inv] at this
            have := neg_le_abs (Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z ρ‖)
            linarith
          · exact (Real.log_le_log hnr h).trans (le_abs_self _)
        have hD := abs_pathIntegral_logDrift_le hU z (Nat.le_add_right n k) le_rfl hT0
          (le_refl (capExitNN hU z n ((n + k : ℕ) : ℝ) T ω))
        have hM := logMart_capExitNN_eq hU z hz' (Nat.le_add_right n k) (N := n + k) T
        change L ≤ |logMart hU z (n + k) (capExitNN hU z n ((n + k : ℕ) : ℝ) T ω) ω|
        rw [hM]
        set A := Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z ρ‖
        set B' := Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z 0‖
        set D := pathIntegral (logDrift hU z (n + k)) (capExitNN hU z n ((n + k : ℕ) : ℝ) T ω) ω
        have h3 : |A| ≤ |A - B' - D| + |B'| + |D| := by
          calc |A| = |(A - B' - D) + B' + D| := by congr 1; ring
            _ ≤ |A - B' - D| + |B'| + |D| := abs_add_three _ _ _
        rw [hLdef]
        linarith
      have hmono : Monotone fun j => ⋂ k, ⋂ (_ : j ≤ k), B k := by
        intro j j' hjj' ω hω
        simp only [mem_iInter] at hω ⊢
        exact fun k hk => hω k (hjj'.trans hk)
      calc P E ≤ P (⋃ j, ⋂ k, ⋂ (_ : j ≤ k), B k) := measure_mono hsub
        _ = ⨆ j, P (⋂ k, ⋂ (_ : j ≤ k), B k) := hmono.measure_iUnion
        _ ≤ ENNReal.ofReal (K * T / L ^ 2) :=
            iSup_le fun j => (measure_mono (iInter₂_subset j le_rfl)).trans (hB j)
    -- Step B: `n → ∞`
    have hLtend : Tendsto (fun n : ℕ => Real.log n - R - Cν * T) atTop atTop := by
      have h := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_add
        (tendsto_const_nhds (x := -(R : ℝ) - Cν * T))
      refine h.congr fun n => ?_
      simp only [Function.comp]; ring
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (K * T / (Real.log n - R - Cν * T) ^ 2))
        atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      refine ENNReal.tendsto_ofReal (tendsto_const_nhds.div_atTop ?_)
      exact (tendsto_pow_atTop two_ne_zero).comp hLtend
    refine le_antisymm (ge_of_tendsto hlim ?_) (by simp)
    filter_upwards [hLtend.eventually_gt_atTop 0] with n hn using hbound n hn
  -- Step C: assemble
  have hz0 : P {ω | ¬ 0 < absorbingTime (fun s => U s ω) z} = 0 :=
    ae_iff.1 (ae_pos_absorbingTime hU z hz)
  rw [ae_iff]
  refine measure_mono_null ?_ (measure_union_null hz0
    (measure_iUnion_null fun T => measure_iUnion_null fun R => hnull T R))
  intro ω hω
  by_cases hz' : 0 < absorbingTime (fun s => U s ω) z
  · right
    obtain ⟨T, hT⟩ := ENNReal.exists_nat_gt hω
    refine mem_iUnion.2 ⟨T, mem_iUnion.2
      ⟨⌈|Real.log ‖fPath (fun s => U s ω) (hU.cont ω) z 0‖|⌉₊, hz', fun t ht => ?_, Nat.le_ceil _⟩⟩
    have h1 := ofReal_clock_le_clockSup (hU.cont ω) ht
    have h2 : ENNReal.ofReal (clock (fun s => U s ω) (hU.cont ω) z t) < ENNReal.ofReal T :=
      lt_of_le_of_lt h1 (by rwa [ENNReal.ofReal_natCast])
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (clock_nonneg (hU.cont ω) ht)).1 h2
  · left; exact hz'

/-- Remark 2.12 in the form used downstream: a.s. the domain of `σ_z` is all of `[0, ∞)`. -/
theorem ae_sigmaDom_eq_Ici (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, sigmaDom (fun s => U s ω) (hU.cont ω) z = Ici 0 := by
  filter_upwards [ae_clockSup_eq_top hU z ha hc hz] with ω hω
  exact sigmaDom_eq_Ici hω

end Martingale

end Processes

end ComplexSLE.Internal.Polar

end
