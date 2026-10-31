/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.PolarTimeSigma
public import ComplexSLE.Internal.Polar.PolarSigmaTop
public import ComplexSLE.Infrastructure.Stochastic.TimeChangeTransfer
public import ComplexSLE.External.TimeChangeIsContLocalMartingale

/-!
# The time change by `σ_z` for `log|f|` (M6/S12, `step:polar-time-change`, real part of
Lemma 2.11 in martingale form)

Generic layer (shared with the θ-half, `PolarTheta*`): for an everywhere continuous `ℱ`-local
martingale `M`, the time change `s ↦ M_{σ^n_s}` by the stopped σ-time `σ^n_s = σ_z(s ∧ A(τ_n))`
is a continuous local martingale for the stopped σ-time filtration `𝒢^n_s = ℱ_{σ^n_s}` (external
E2c, `isContLocalMartingale_comp_sigmaStop`) and, since it is frozen after the `𝒢`-stopping time
`A(τ_n)`, for the σ-time filtration `𝒢_s = ℱ_{σ_z(s)}` itself
(`isContLocalMartingale_comp_sigmaStop'`, filtration transfer). Letting `n → ∞` along the
exit times, a process that agrees with these on `[0, A(τ_n)]` is a continuous `𝒢`-local
martingale (`isContLocalMartingale_sigma_of_stopped`; Remark 2.12 supplies `A(τ_n) → ∞` a.s.).

Applied to `N^n = logMart` and `(N^n)² - ∫ Γ^n` (`PolarItoLog.lean`) with the change of
variables `∫₀^{σ^n_s} ν(θ_u)|f_u|⁻² du = ∫₀^{s ∧ A(τ_n)} ν(θ̂_v) dv` this gives, in the notation
`ρ̂_s = log|f_{σ_z(s)}(z)|`, `θ̂_s = θ_{σ_z(s)}(z)` of Lemma 2.11 (paper.tex:L870-L885,
`eqn-abs-zt`), that

* `ρ̂_s - ρ̂_0 - ∫₀ˢ ν(θ̂_v) dv` (`sigmaLogMart`) and
* its square minus `∫₀ˢ (a cos² θ̂_v + b sin² θ̂_v + 2c sin θ̂_v cos θ̂_v) dv` (`sigmaLogMartSq`)

are continuous `𝒢`-local martingales (`isContLocalMartingale_sigmaLogMart`,
`isContLocalMartingale_sigmaLogMartSq`), i.e. the martingale-form content of (2.26) with the
bracket of its martingale part. Off the a.s. event `sigmaDom = [0, ∞)` the processes are set to
`0`.
-/

public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal.Polar

/-! ### The bracket density in polar form -/

/-- `a cos² θ + b sin² θ + 2c sin θ cos θ`, the bracket density of `log|f̂|` in σ-time. -/
@[expose] noncomputable def logBracketFn (a b c : ℝ) (θ : ℝ) : ℝ :=
  a * Real.cos θ ^ 2 + b * Real.sin θ ^ 2 + 2 * c * Real.sin θ * Real.cos θ

theorem continuous_logBracketFn (a b c : ℝ) : Continuous (logBracketFn a b c) := by
  unfold logBracketFn; fun_prop

theorem continuous_nu (a b c : ℝ) : Continuous (nu a b c) := by
  unfold nu; fun_prop

section Processes

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

variable (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ)

/-! ### Generic layer: time change of a local martingale by `σ^n`, and the limit `n → ∞` -/

section Generic

variable [IsProbabilityMeasure P]

/-- **Time change by the stopped σ-time** (external E2c): for an everywhere continuous
`ℱ`-local martingale `M`, `s ↦ M_{σ^n_s}` is a continuous `𝒢^n`-local martingale. -/
theorem isContLocalMartingale_comp_sigmaStop (n : ℕ) {M : ℝ≥0 → Ω → ℝ}
    (hM : IsContLocalMartingale ℱ M P) (hMc : ∀ ω, Continuous fun t => M t ω) :
    IsContLocalMartingale (sigmaStopFiltration hU z n)
      (fun s ω => M (sigmaStop hU z n s ω) ω) P :=
  External.timeChange_isContLocalMartingale ℱ M hM hMc (sigmaStop hU z n)
    (isStoppingTime_sigmaStop hU z n) (sigmaStop_zero hU n)
    (fun ω => ⟨continuous_sigmaStop hU n ω, sigmaStop_mono hU n ω⟩)
    (sigmaStopFiltration hU z n) (fun _ => rfl)

/-- **Time change by the stopped σ-time, σ-time filtration**: `s ↦ M_{σ^n_s}` is a continuous
`𝒢`-local martingale, `𝒢_s = ℱ_{σ_z(s)}` (it is frozen after the `𝒢`-stopping time `A(τ_n)`). -/
theorem isContLocalMartingale_comp_sigmaStop' (n : ℕ) {M : ℝ≥0 → Ω → ℝ}
    (hM : IsContLocalMartingale ℱ M P) (hMc : ∀ ω, Continuous fun t => M t ω) :
    IsContLocalMartingale (sigmaFiltration hU z) (fun s ω => M (sigmaStop hU z n s ω) ω) P :=
  isContLocalMartingale_of_le_of_inter_lt (sigmaStopFiltration hU z n) (sigmaFiltration hU z)
    (sigmaStopFiltration_le hU n) (isStoppingTime_clockExit hU n)
    (measurableSet_inter_lt_clockExit hU n)
    (isContLocalMartingale_comp_sigmaStop hU z n hM hMc) fun ω s t hst hρs => by
      rw [sigmaStop_eq_exitNN_of_le hU hρs, sigmaStop_eq_exitNN_of_le hU (hρs.trans hst)]

open Classical in
/-- **The limit `n → ∞` in σ-time.** Let `N k` be continuous `𝒢`-local martingales with
everywhere continuous paths of the form `N k s = Φ(s ∧ A(τ_k))` on `{T_z > 0}` (and `0` on
`{T_z = 0}`). Then `s ↦ Φ(s)` on `sigmaDom` (and `0` elsewhere) is a continuous `𝒢`-local
martingale. Remark 2.12 (`ae_clockSup_eq_top`) provides `A(τ_k) → ∞` a.s. -/
theorem isContLocalMartingale_sigma_of_stopped (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0)
    {Φ : Ω → ℝ → ℝ} {N : ℕ → ℝ≥0 → Ω → ℝ}
    (hN : ∀ k, IsContLocalMartingale (sigmaFiltration hU z) (N k) P)
    (hNc : ∀ k ω, Continuous fun s => N k s ω)
    (hNeq : ∀ k ω, 0 < absorbingTime (fun r => U r ω) z →
      ∀ s : ℝ≥0, N k s ω = Φ ω (min (s : ℝ) (clockExitR hU z k ω)))
    (hN0 : ∀ k ω, ¬ 0 < absorbingTime (fun r => U r ω) z → ∀ s : ℝ≥0, N k s ω = 0) :
    IsContLocalMartingale (sigmaFiltration hU z) (fun s ω =>
      if (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z then Φ ω s else 0) P := by
  refine IsContLocalMartingale.of_consistent_seq (ρ := clockExit hU z) (isStoppingTime_clockExit hU)
    (clockExit_mono hU) ?_ hN hNc ?_ ?_ ?_ ?_
  · -- `A(τ_k) → ∞` a.s. (Remark 2.12)
    filter_upwards [ae_clockSup_eq_top hU z ha hc hz] with ω hω t
    have hz' : 0 < absorbingTime (fun r => U r ω) z := by
      by_contra h
      rw [clockSup_eq_zero_of_not_pos (hU.cont ω) h] at hω
      exact ENNReal.zero_ne_top hω
    have hlt : ((t : ℝ≥0) : ℝ≥0∞) < clockSup (fun r => U r ω) (hU.cont ω) z := by
      rw [hω]; exact ENNReal.coe_lt_top
    change ((t : ℝ≥0) : ℝ≥0∞) < ⨆ t' ∈ lifeSet (fun r => U r ω) z,
      ENNReal.ofReal (clock (fun r => U r ω) (hU.cont ω) z t') at hlt
    obtain ⟨t', ht', hlt'⟩ := lt_biSup_iff.1 hlt
    obtain ⟨k₀, hk₀⟩ := exists_lt_exitTime (hU.cont ω) ht'
    filter_upwards [eventually_ge_atTop k₀] with k hk
    rw [← NNReal.coe_le_coe, coe_clockExit]
    have h1 : (t : ℝ) < clock (fun r => U r ω) (hU.cont ω) z t' := by
      rw [← ENNReal.ofReal_coe_nnreal] at hlt'
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg t.coe_nonneg).1 hlt'
    have h2 : clock (fun r => U r ω) (hU.cont ω) z t' ≤ clockExitR hU z k ω :=
      clock_monotoneOn (hU.cont ω) z ht' (exitR_mem_lifeSet hU z k hz')
        (hk₀.le.trans (exitTime_mono (hU.cont ω) hz' hk))
    exact (h1.trans_le h2).le
  · -- constancy after `A(τ_k)`
    intro k ω s t hst hρs
    by_cases hz' : 0 < absorbingTime (fun r => U r ω) z
    · rw [hNeq k ω hz', hNeq k ω hz']
      have hρs' : clockExitR hU z k ω ≤ s := by rwa [← coe_clockExit, NNReal.coe_le_coe]
      rw [min_eq_right hρs', min_eq_right (hρs'.trans (NNReal.coe_le_coe.2 hst))]
    · rw [hN0 k ω hz', hN0 k ω hz']
  · -- agreement on `[0, A(τ_k))`
    intro k ω s hs
    have hs' : (s : ℝ) < clockExitR hU z k ω := by rwa [← coe_clockExit, NNReal.coe_lt_coe]
    have hz' : 0 < absorbingTime (fun r => U r ω) z := by
      by_contra h
      rw [clockExitR_eq_zero_of_not_pos hU h] at hs'
      exact absurd hs' (not_lt.2 s.coe_nonneg)
    have hsd : (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z :=
      mem_sigmaDom_of_le (clockExitR_mem_sigmaDom hU hz' k) s.coe_nonneg hs'.le
    rw [ite_eq_left hsd, hNeq k ω hz', min_eq_left hs'.le]
  · -- agreement at `A(τ_k)`
    intro k ω
    by_cases hz' : 0 < absorbingTime (fun r => U r ω) z
    · have hd : ((clockExit hU z k ω : ℝ≥0) : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z := by
        rw [coe_clockExit]; exact clockExitR_mem_sigmaDom hU hz' k
      rw [ite_eq_left hd, hNeq k ω hz', coe_clockExit, min_self]
    · rw [hN0 k ω hz', clockExit_eq_zero_of_not_pos hU hz',
        ite_eq_right (notMem_sigmaDom_of_not_pos (hU.cont ω) hz' _)]
  · -- vanishing where no `A(τ_k)` is above `s`
    intro ω s hs
    refine ite_eq_right fun hsd => ?_
    have hz' := pos_absorbingTime_of_mem_sigmaDom (hU.cont ω) hsd
    have hσ := sigmaTime_mem_lifeSet (hU.cont ω) hsd
    obtain ⟨k, hk⟩ := exists_lt_exitTime (hU.cont ω) hσ
    have h1 : (s : ℝ) < clockExitR hU z k ω := by
      rw [← clock_sigmaTime (hU.cont ω) hsd]
      exact clock_lt_clock (hU.cont ω) hσ.1 hk (exitR_mem_lifeSet hU z k hz')
    have h2 := hs k
    rw [← NNReal.coe_le_coe, coe_clockExit] at h2
    exact absurd h1 (not_lt.2 h2)

end Generic

/-! ### The time-changed drift and bracket densities -/

/-- `ν(θ̂_v) = ν(θ_{σ_z(v)}(z))`. -/
@[expose] noncomputable def nuHat (ω : Ω) (v : ℝ) : ℝ :=
  nu a b c (argPath (fun r => U r ω) (hU.cont ω) z (sigmaTime (fun r => U r ω) (hU.cont ω) z v))

/-- `a cos² θ̂_v + b sin² θ̂_v + 2c sin θ̂_v cos θ̂_v`. -/
@[expose] noncomputable def logBracketHat (ω : Ω) (v : ℝ) : ℝ :=
  logBracketFn a b c
    (argPath (fun r => U r ω) (hU.cont ω) z (sigmaTime (fun r => U r ω) (hU.cont ω) z v))

variable {z}

/-- On `{T_z = 0}` the process `N^n` vanishes. -/
theorem logMart_eq_zero_of_not_pos {ω : Ω} (hz : ¬ 0 < absorbingTime (fun r => U r ω) z) (n : ℕ)
    (t : ℝ≥0) : logMart hU z n t ω = 0 := by
  have hD : ∀ s : ℝ≥0, logDrift hU z n s ω = 0 := fun s => by
    simp [logDrift, itoState_eq_zero hU z n hz, betaFn]
  simp [logMart, logNormF, stoppedF_eq_zero hU z n hz, pathIntegral, hD]

theorem pathIntegral_logBracket_eq_zero_of_not_pos {ω : Ω}
    (hz : ¬ 0 < absorbingTime (fun r => U r ω) z) (n : ℕ) (t : ℝ≥0) :
    pathIntegral (logBracket hU z n) t ω = 0 := by
  have hG : ∀ s : ℝ≥0, logBracket hU z n s ω = 0 := fun s => by
    simp [logBracket, itoState_eq_zero hU z n hz, gammaFn]
  simp [pathIntegral, hG]

/-- **`N^n` in σ-time** (`T_z > 0`): `N^n_{σ^n_s} = log|f_{σ^n_s}| - log|f_0| -
∫₀^{s ∧ A(τ_n)} ν(θ̂_v) dv`. -/
theorem logMart_sigmaStop_eq {ω : Ω} (hz : 0 < absorbingTime (fun r => U r ω) z) (n : ℕ)
    (s : ℝ≥0) :
    logMart hU z n (sigmaStop hU z n s ω) ω =
      Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z (sigmaStopR hU z n s ω)‖ -
        Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z 0‖ -
        ∫ v in (0 : ℝ)..min (s : ℝ) (clockExitR hU z n ω), nuHat hU z ω v := by
  rw [logMart, logNormF, logNormF,
    stoppedF_eq_of_le hU z n hz (by rw [coe_sigmaStop]; exact sigmaStopR_le_exitR hU n s ω),
    coe_sigmaStop,
    stoppedF_eq_of_le hU z n hz (by rw [NNReal.coe_zero]; exact exitR_nonneg hU z n ω),
    NNReal.coe_zero]
  congr 1
  exact pathIntegral_sigmaStop_eq hU hz (continuous_nu a b c)
    (fun t ht => by rw [logDrift_eq_nu hU z n hz ht, clockRate, div_eq_mul_inv]) s

/-- **The bracket integral in σ-time** (`T_z > 0`): `∫₀^{σ^n_s} Γ^n = ∫₀^{s ∧ A(τ_n)}
(a cos² θ̂_v + b sin² θ̂_v + 2c sin θ̂_v cos θ̂_v) dv`. -/
theorem pathIntegral_logBracket_sigmaStop_eq {ω : Ω}
    (hz : 0 < absorbingTime (fun r => U r ω) z) (n : ℕ) (s : ℝ≥0) :
    pathIntegral (logBracket hU z n) (sigmaStop hU z n s ω) ω =
      ∫ v in (0 : ℝ)..min (s : ℝ) (clockExitR hU z n ω), logBracketHat hU z ω v :=
  pathIntegral_sigmaStop_eq hU hz (continuous_logBracketFn a b c)
    (fun t ht => by rw [logBracket_eq_polar hU z n hz ht, clockRate, div_eq_mul_inv]; rfl) s

/-! ### The processes of Lemma 2.11 in σ-time -/

variable (z)

open Classical in
/-- **The martingale part of `log|f̂|` in σ-time**:
`ρ̂_s - ρ̂_0 - ∫₀ˢ ν(θ̂_v) dv` with `ρ̂_s = log|f_{σ_z(s)}(z)|` (and `0` off `sigmaDom`, a.s.
never). -/
@[expose] noncomputable def sigmaLogMart (s : ℝ≥0) (ω : Ω) : ℝ :=
  if (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z then
    Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z (sigmaTime (fun r => U r ω) (hU.cont ω) z s)‖ -
      Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z 0‖ - ∫ v in (0 : ℝ)..(s : ℝ), nuHat hU z ω v
  else 0

open Classical in
/-- **The bracket process of `sigmaLogMart`**: `(ρ̂_s - ρ̂_0 - ∫₀ˢ ν(θ̂))² -
∫₀ˢ (a cos² θ̂_v + b sin² θ̂_v + 2c sin θ̂_v cos θ̂_v) dv` (and `0` off `sigmaDom`). -/
@[expose] noncomputable def sigmaLogMartSq (s : ℝ≥0) (ω : Ω) : ℝ :=
  if (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z then
    (Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z
        (sigmaTime (fun r => U r ω) (hU.cont ω) z s)‖ -
      Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z 0‖ -
      ∫ v in (0 : ℝ)..(s : ℝ), nuHat hU z ω v) ^ 2 -
      ∫ v in (0 : ℝ)..(s : ℝ), logBracketHat hU z ω v
  else 0

theorem sigmaLogMartSq_eq {s : ℝ≥0} {ω : Ω}
    (hs : (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z) :
    sigmaLogMartSq hU z s ω =
      sigmaLogMart hU z s ω ^ 2 - ∫ v in (0 : ℝ)..(s : ℝ), logBracketHat hU z ω v := by
  rw [sigmaLogMartSq, sigmaLogMart, ite_eq_left hs, ite_eq_left hs]

variable {z}

/-! ### Lemma 2.11, real part, in martingale form -/

section Martingales

variable [IsProbabilityMeasure P]

/-- **`N^n_{σ^n_s}` is a continuous `𝒢`-local martingale** (`step:polar-time-change`, stopped
form). -/
theorem isContLocalMartingale_logMart_sigmaStop (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0)
    (n : ℕ) :
    IsContLocalMartingale (sigmaFiltration hU z)
      (fun s ω => logMart hU z n (sigmaStop hU z n s ω) ω) P :=
  isContLocalMartingale_comp_sigmaStop' hU z n (isContLocalMartingale_logMart hU z n ha hc hz)
    (continuous_logMart hU z n)

/-- **The bracket of `N^n_{σ^n_·}`**: `(N^n_{σ^n_s})² - ∫₀^{σ^n_s} Γ^n` is a continuous
`𝒢`-local martingale. -/
theorem isContLocalMartingale_logMart_sigmaStop_sq_sub (ha : 0 < a) (hc : c ^ 2 ≤ a * b)
    (hz : z ≠ 0) (n : ℕ) :
    IsContLocalMartingale (sigmaFiltration hU z) (fun s ω =>
      logMart hU z n (sigmaStop hU z n s ω) ω ^ 2 -
        pathIntegral (logBracket hU z n) (sigmaStop hU z n s ω) ω) P :=
  isContLocalMartingale_comp_sigmaStop' hU z n
    (isContLocalMartingale_logMart_sq_sub hU z n ha hc hz) fun ω =>
      ((continuous_logMart hU z n ω).pow 2).sub
        (continuous_pathIntegral_beforeExit hU z n (continuousOn_gammaFn a b c) ω)

/-- **Lemma 2.11, real part, martingale form** (`eqn-abs-zt`, drift): for `0 < a`, `c² ≤ ab`,
`z ≠ 0`, the process `ρ̂_s - ρ̂_0 - ∫₀ˢ ν(θ̂_v) dv` is a continuous local martingale for the
σ-time filtration `𝒢_s = ℱ_{σ_z(s)}`. -/
theorem isContLocalMartingale_sigmaLogMart (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) :
    IsContLocalMartingale (sigmaFiltration hU z) (sigmaLogMart hU z) P :=
  isContLocalMartingale_sigma_of_stopped hU z ha hc hz
    (Φ := fun ω v => Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z
        (sigmaTime (fun r => U r ω) (hU.cont ω) z v)‖ -
      Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z 0‖ - ∫ u in (0 : ℝ)..v, nuHat hU z ω u)
    (N := fun k s ω => logMart hU z k (sigmaStop hU z k s ω) ω)
    (fun k => isContLocalMartingale_logMart_sigmaStop hU ha hc hz k)
    (fun k ω => (continuous_logMart hU z k ω).comp (continuous_sigmaStop hU k ω))
    (fun k _ hz' s => logMart_sigmaStop_eq hU hz' k s)
    (fun k _ hz' _ => logMart_eq_zero_of_not_pos hU hz' k _)

/-- **Lemma 2.11, real part, martingale form** (`eqn-abs-zt`, bracket): the square of
`ρ̂_s - ρ̂_0 - ∫₀ˢ ν(θ̂_v) dv` minus `∫₀ˢ (a cos² θ̂_v + b sin² θ̂_v + 2c sin θ̂_v cos θ̂_v) dv` is
a continuous `𝒢`-local martingale. -/
theorem isContLocalMartingale_sigmaLogMartSq (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) :
    IsContLocalMartingale (sigmaFiltration hU z) (sigmaLogMartSq hU z) P :=
  isContLocalMartingale_sigma_of_stopped hU z ha hc hz
    (Φ := fun ω v => (Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z
        (sigmaTime (fun r => U r ω) (hU.cont ω) z v)‖ -
      Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z 0‖ - ∫ u in (0 : ℝ)..v, nuHat hU z ω u) ^ 2 -
      ∫ u in (0 : ℝ)..v, logBracketHat hU z ω u)
    (N := fun k s ω => logMart hU z k (sigmaStop hU z k s ω) ω ^ 2 -
      pathIntegral (logBracket hU z k) (sigmaStop hU z k s ω) ω)
    (fun k => isContLocalMartingale_logMart_sigmaStop_sq_sub hU ha hc hz k)
    (fun k ω => (((continuous_logMart hU z k ω).comp (continuous_sigmaStop hU k ω)).pow 2).sub
      ((continuous_pathIntegral_beforeExit hU z k (continuousOn_gammaFn a b c) ω).comp
        (continuous_sigmaStop hU k ω)))
    (fun k _ hz' s => by
      rw [logMart_sigmaStop_eq hU hz' k s, pathIntegral_logBracket_sigmaStop_eq hU hz' k s]
      rfl)
    (fun k _ hz' _ => by
      rw [logMart_eq_zero_of_not_pos hU hz' k, pathIntegral_logBracket_eq_zero_of_not_pos hU hz' k]
      ring)

end Martingales

end Processes

end ComplexSLE.Internal.Polar

end
