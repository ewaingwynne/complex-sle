/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.PolarThetaBrMart
public import ComplexSLE.Internal.Polar.PolarTimeChange

/-!
# The time change by `σ_z` for `θ`: `θ̂` is a diffusion (M6/S13, `step:polar-time-change`,
imaginary part of Lemma 2.11 in martingale form, `eqn-theta-t`, paper.tex:L870-L885)

With `θ̂_s = θ_{σ_z(s)}(z)` (`thetaHat`, set to `0` off the a.s. full domain `sigmaDom`), the
generic σ-time layer of `PolarTimeChange.lean` applied to `Θ^n`, `(Θ^n)² - B^n` and
`Θ^n N^n - C^n` (`PolarThetaMart.lean`, `PolarThetaBrMart.lean`) with the change of variables
`pathIntegral_sigmaStop_eq` gives, for the σ-time filtration `𝒢_s = ℱ_{σ_z(s)}`:

* `θ̂_s - θ̂_0 - ∫₀ˢ µ(θ̂_v) dv` is a continuous `𝒢`-local martingale (`sigmaThetaMart`,
  `isContLocalMartingale_sigmaThetaMart`);
* its square minus `∫₀ˢ (a sin² θ̂_v + b cos² θ̂_v - 2c sin θ̂_v cos θ̂_v) dv = ∫₀ˢ 2 D(θ̂_v) dv`
  is a continuous `𝒢`-local martingale (`sigmaThetaMartSq`,
  `isContLocalMartingale_sigmaThetaMartSq`);
* its product with `ρ̂_s - ρ̂_0 - ∫₀ˢ ν(θ̂_v) dv` minus
  `∫₀ˢ ((b - a) sin θ̂_v cos θ̂_v + c (cos² θ̂_v - sin² θ̂_v)) dv` is a continuous `𝒢`-local
  martingale (`sigmaThetaLogCross`, `isContLocalMartingale_sigmaThetaLogCross`).

The honest process `θ̂` is `𝒢`-progressive (`isStronglyProgressive_thetaHat`: it is the pointwise
limit of `1_{s < A(τ_k)} θ_{σ^k_s}`, where `θ_{σ^k_s}` is `ℱ_{σ^k_s}`-measurable and continuous
in `s`) and a.s. continuous, and the martingale-form SDE (2.25) in the vocabulary of the external
inputs is

  `IsDiffusionSolution (sigmaFiltration hU z) (mu a b c) (fun u => √(2 * diffusionD a b c u)) θ̂ P`

(`isDiffusionSolution_thetaHat`), with the bracket identity
`2 D(u) = a sin² u + b cos² u - 2c sin u cos u` (`thetaBracketPolar_eq_two_mul_diffusionD`).
The joint decomposition of `(θ̂, log|f̂|)` consumed by Lemma 3.3 (`lem-stationary-sde`) is
recorded in `thetaHat_sigmaLogMart_decomposition`.
-/

public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal.Polar

/-! ### `D ≥ 0` -/

theorem diffusionD_nonneg {a b c : ℝ} (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (u : ℝ) :
    0 ≤ diffusionD a b c u := by
  have h : 0 ≤ a * (a * Real.sin u ^ 2 + b * Real.cos u ^ 2 - 2 * c * Real.sin u * Real.cos u) := by
    nlinarith [sq_nonneg (a * Real.sin u - c * Real.cos u),
      mul_nonneg (sub_nonneg.2 hc) (sq_nonneg (Real.cos u))]
  have h' := (mul_nonneg_iff_of_pos_left ha).1 h
  unfold diffusionD; linarith

theorem sq_sqrt_two_mul_diffusionD {a b c : ℝ} (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (u : ℝ) :
    (√(2 * diffusionD a b c u)) ^ 2 = thetaBracketPolar a b c u := by
  rw [Real.sq_sqrt (by linarith [diffusionD_nonneg ha hc u]),
    thetaBracketPolar_eq_two_mul_diffusionD]

section Processes

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

variable (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ)

/-! ### The densities in σ-time -/

/-- `µ(θ̂_v) = µ(θ_{σ_z(v)}(z))`. -/
@[expose] noncomputable def muHat (ω : Ω) (v : ℝ) : ℝ :=
  mu a b c (argPath (fun r => U r ω) (hU.cont ω) z (sigmaTime (fun r => U r ω) (hU.cont ω) z v))

/-- `a sin² θ̂_v + b cos² θ̂_v - 2c sin θ̂_v cos θ̂_v = 2 D(θ̂_v)`. -/
@[expose] noncomputable def thetaBracketHat (ω : Ω) (v : ℝ) : ℝ :=
  thetaBracketPolar a b c
    (argPath (fun r => U r ω) (hU.cont ω) z (sigmaTime (fun r => U r ω) (hU.cont ω) z v))

/-- `(b - a) sin θ̂_v cos θ̂_v + c (cos² θ̂_v - sin² θ̂_v)`. -/
@[expose] noncomputable def crossHat (ω : Ω) (v : ℝ) : ℝ :=
  crossPolar a b c
    (argPath (fun r => U r ω) (hU.cont ω) z (sigmaTime (fun r => U r ω) (hU.cont ω) z v))

open Classical in
/-- **The time-changed argument** `θ̂_s = θ_{σ_z(s)}(z)` on `sigmaDom` (a.s. all of `[0, ∞)`,
Remark 2.12), and `0` elsewhere. -/
@[expose] noncomputable def thetaHat (s : ℝ≥0) (ω : Ω) : ℝ :=
  if (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z then
    argPath (fun r => U r ω) (hU.cont ω) z (sigmaTime (fun r => U r ω) (hU.cont ω) z s) else 0

variable {z}

theorem thetaHat_of_mem {s : ℝ≥0} {ω : Ω}
    (hs : (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z) :
    thetaHat hU z s ω =
      argPath (fun r => U r ω) (hU.cont ω) z (sigmaTime (fun r => U r ω) (hU.cont ω) z s) := by
  rw [thetaHat, ite_eq_left hs]

theorem thetaHat_of_notMem {s : ℝ≥0} {ω : Ω}
    (hs : (s : ℝ) ∉ sigmaDom (fun r => U r ω) (hU.cont ω) z) : thetaHat hU z s ω = 0 := by
  rw [thetaHat, ite_eq_right hs]

/-! ### On `{T_z = 0}` -/

theorem thetaMart_eq_zero_of_not_pos {ω : Ω} (hz : ¬ 0 < absorbingTime (fun r => U r ω) z)
    (n : ℕ) (t : ℝ≥0) : thetaMart hU z n t ω = 0 := by
  have hD : ∀ s : ℝ≥0, thetaDrift hU z n s ω = 0 := fun s => by
    simp [thetaDrift, itoState_eq_zero hU z n hz, muFn]
  simp [thetaMart, argStopped_eq_zero hU z n hz, pathIntegral, hD]

theorem pathIntegral_thetaBracket_eq_zero_of_not_pos {ω : Ω}
    (hz : ¬ 0 < absorbingTime (fun r => U r ω) z) (n : ℕ) (t : ℝ≥0) :
    pathIntegral (thetaBracket hU z n) t ω = 0 := by
  have hG : ∀ s : ℝ≥0, thetaBracket hU z n s ω = 0 := fun s => by
    simp [thetaBracket, itoState_eq_zero hU z n hz, thetaBracketFn]
  simp [pathIntegral, hG]

theorem pathIntegral_thetaLogCross_eq_zero_of_not_pos {ω : Ω}
    (hz : ¬ 0 < absorbingTime (fun r => U r ω) z) (n : ℕ) (t : ℝ≥0) :
    pathIntegral (thetaLogCross hU z n) t ω = 0 := by
  have hG : ∀ s : ℝ≥0, thetaLogCross hU z n s ω = 0 := fun s => by
    simp [thetaLogCross, itoState_eq_zero hU z n hz, crossFn]
  simp [pathIntegral, hG]

/-! ### The stopped processes in σ-time (`T_z > 0`) -/

/-- **`Θ^n` in σ-time**: `Θ^n_{σ^n_s} = θ_{σ^n_s} - θ_0 - ∫₀^{s ∧ A(τ_n)} µ(θ̂_v) dv`. -/
theorem thetaMart_sigmaStop_eq {ω : Ω} (hz : 0 < absorbingTime (fun r => U r ω) z) (n : ℕ)
    (s : ℝ≥0) :
    thetaMart hU z n (sigmaStop hU z n s ω) ω =
      argPath (fun r => U r ω) (hU.cont ω) z (sigmaStopR hU z n s ω) -
        argPath (fun r => U r ω) (hU.cont ω) z 0 -
        ∫ v in (0 : ℝ)..min (s : ℝ) (clockExitR hU z n ω), muHat hU z ω v := by
  rw [thetaMart, argStopped_eq hU z n hz, argStopped_eq hU z n hz, coe_sigmaStop,
    min_eq_left (sigmaStopR_le_exitR hU n s ω), NNReal.coe_zero,
    min_eq_left (exitR_nonneg hU z n ω)]
  congr 1
  exact pathIntegral_sigmaStop_eq hU hz (continuous_mu a b c)
    (fun t ht => by rw [thetaDrift_eq_mu hU z n hz ht, clockRate, div_eq_mul_inv]) s

/-- **The bracket integral of `Θ^n` in σ-time**: `∫₀^{σ^n_s} B^n = ∫₀^{s ∧ A(τ_n)} 2 D(θ̂_v) dv`. -/
theorem pathIntegral_thetaBracket_sigmaStop_eq {ω : Ω}
    (hz : 0 < absorbingTime (fun r => U r ω) z) (n : ℕ) (s : ℝ≥0) :
    pathIntegral (thetaBracket hU z n) (sigmaStop hU z n s ω) ω =
      ∫ v in (0 : ℝ)..min (s : ℝ) (clockExitR hU z n ω), thetaBracketHat hU z ω v :=
  pathIntegral_sigmaStop_eq hU hz (continuous_thetaBracketPolar a b c)
    (fun t ht => by rw [thetaBracket_eq_polar hU z n hz ht, clockRate, div_eq_mul_inv]) s

/-- **The cross bracket integral in σ-time**. -/
theorem pathIntegral_thetaLogCross_sigmaStop_eq {ω : Ω}
    (hz : 0 < absorbingTime (fun r => U r ω) z) (n : ℕ) (s : ℝ≥0) :
    pathIntegral (thetaLogCross hU z n) (sigmaStop hU z n s ω) ω =
      ∫ v in (0 : ℝ)..min (s : ℝ) (clockExitR hU z n ω), crossHat hU z ω v :=
  pathIntegral_sigmaStop_eq hU hz (continuous_crossPolar a b c)
    (fun t ht => by rw [thetaLogCross_eq_polar hU z n hz ht, clockRate, div_eq_mul_inv]) s

/-! ### The processes of Lemma 2.11, imaginary part, in σ-time -/

variable (z)

open Classical in
/-- **The martingale part of `θ̂`**: `θ̂_s - θ̂_0 - ∫₀ˢ µ(θ̂_v) dv` (and `0` off `sigmaDom`, a.s.
never). -/
@[expose] noncomputable def sigmaThetaMart (s : ℝ≥0) (ω : Ω) : ℝ :=
  if (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z then
    argPath (fun r => U r ω) (hU.cont ω) z (sigmaTime (fun r => U r ω) (hU.cont ω) z s) -
      argPath (fun r => U r ω) (hU.cont ω) z 0 - ∫ v in (0 : ℝ)..(s : ℝ), muHat hU z ω v
  else 0

open Classical in
/-- **The bracket process of `sigmaThetaMart`**: `(θ̂_s - θ̂_0 - ∫₀ˢ µ(θ̂))² - ∫₀ˢ 2 D(θ̂_v) dv`
(and `0` off `sigmaDom`). -/
@[expose] noncomputable def sigmaThetaMartSq (s : ℝ≥0) (ω : Ω) : ℝ :=
  if (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z then
    (argPath (fun r => U r ω) (hU.cont ω) z (sigmaTime (fun r => U r ω) (hU.cont ω) z s) -
      argPath (fun r => U r ω) (hU.cont ω) z 0 - ∫ v in (0 : ℝ)..(s : ℝ), muHat hU z ω v) ^ 2 -
      ∫ v in (0 : ℝ)..(s : ℝ), thetaBracketHat hU z ω v
  else 0

open Classical in
/-- **The cross bracket process of `sigmaThetaMart` and `sigmaLogMart`**:
`(θ̂_s - θ̂_0 - ∫₀ˢ µ(θ̂)) (ρ̂_s - ρ̂_0 - ∫₀ˢ ν(θ̂))`
`- ∫₀ˢ ((b - a) sin θ̂ cos θ̂ + c (cos² θ̂ - sin² θ̂))`
(and `0` off `sigmaDom`). -/
@[expose] noncomputable def sigmaThetaLogCross (s : ℝ≥0) (ω : Ω) : ℝ :=
  if (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z then
    (argPath (fun r => U r ω) (hU.cont ω) z (sigmaTime (fun r => U r ω) (hU.cont ω) z s) -
      argPath (fun r => U r ω) (hU.cont ω) z 0 - ∫ v in (0 : ℝ)..(s : ℝ), muHat hU z ω v) *
    (Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z
        (sigmaTime (fun r => U r ω) (hU.cont ω) z s)‖ -
      Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z 0‖ -
      ∫ v in (0 : ℝ)..(s : ℝ), nuHat hU z ω v) -
      ∫ v in (0 : ℝ)..(s : ℝ), crossHat hU z ω v
  else 0

variable {z}

theorem sigmaThetaMartSq_eq {s : ℝ≥0} {ω : Ω}
    (hs : (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z) :
    sigmaThetaMartSq hU z s ω =
      sigmaThetaMart hU z s ω ^ 2 - ∫ v in (0 : ℝ)..(s : ℝ), thetaBracketHat hU z ω v := by
  rw [sigmaThetaMartSq, sigmaThetaMart, ite_eq_left hs, ite_eq_left hs]

theorem sigmaThetaLogCross_eq {s : ℝ≥0} {ω : Ω}
    (hs : (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z) :
    sigmaThetaLogCross hU z s ω =
      sigmaThetaMart hU z s ω * sigmaLogMart hU z s ω -
        ∫ v in (0 : ℝ)..(s : ℝ), crossHat hU z ω v := by
  rw [sigmaThetaLogCross, sigmaThetaMart, sigmaLogMart, ite_eq_left hs, ite_eq_left hs,
    ite_eq_left hs]

section Martingales

variable [IsProbabilityMeasure P]

/-- **`Θ^n_{σ^n_s}` is a continuous `𝒢`-local martingale.** -/
theorem isContLocalMartingale_thetaMart_sigmaStop (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0)
    (n : ℕ) :
    IsContLocalMartingale (sigmaFiltration hU z)
      (fun s ω => thetaMart hU z n (sigmaStop hU z n s ω) ω) P :=
  isContLocalMartingale_comp_sigmaStop' hU z n (isContLocalMartingale_thetaMart hU z n ha hc hz)
    (continuous_thetaMart hU z n)

/-- **The bracket of `Θ^n_{σ^n_·}`.** -/
theorem isContLocalMartingale_thetaMart_sigmaStop_sq_sub (ha : 0 < a) (hc : c ^ 2 ≤ a * b)
    (hz : z ≠ 0) (n : ℕ) :
    IsContLocalMartingale (sigmaFiltration hU z) (fun s ω =>
      thetaMart hU z n (sigmaStop hU z n s ω) ω ^ 2 -
        pathIntegral (thetaBracket hU z n) (sigmaStop hU z n s ω) ω) P :=
  isContLocalMartingale_comp_sigmaStop' hU z n
    (isContLocalMartingale_thetaMart_sq_sub hU z n ha hc hz) fun ω =>
      ((continuous_thetaMart hU z n ω).pow 2).sub (continuous_pathIntegral_thetaBracket hU z n ω)

/-- **The cross bracket of `Θ^n_{σ^n_·}` and `N^n_{σ^n_·}`.** -/
theorem isContLocalMartingale_thetaMart_mul_logMart_sigmaStop_sub (ha : 0 < a) (hc : c ^ 2 ≤ a * b)
    (hz : z ≠ 0) (n : ℕ) :
    IsContLocalMartingale (sigmaFiltration hU z) (fun s ω =>
      thetaMart hU z n (sigmaStop hU z n s ω) ω * logMart hU z n (sigmaStop hU z n s ω) ω -
        pathIntegral (thetaLogCross hU z n) (sigmaStop hU z n s ω) ω) P :=
  isContLocalMartingale_comp_sigmaStop' hU z n
    (isContLocalMartingale_thetaMart_mul_logMart_sub hU z n ha hc hz) fun ω =>
      ((continuous_thetaMart hU z n ω).mul (continuous_logMart hU z n ω)).sub
        (continuous_pathIntegral_thetaLogCross hU z n ω)

/-- **Lemma 2.11, imaginary part, martingale form** (`eqn-theta-t`, drift): for `0 < a`,
`c² ≤ ab`, `z ≠ 0`, the process `θ̂_s - θ̂_0 - ∫₀ˢ µ(θ̂_v) dv` is a continuous local martingale for
the σ-time filtration `𝒢_s = ℱ_{σ_z(s)}`. -/
theorem isContLocalMartingale_sigmaThetaMart (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) :
    IsContLocalMartingale (sigmaFiltration hU z) (sigmaThetaMart hU z) P :=
  isContLocalMartingale_sigma_of_stopped hU z ha hc hz
    (Φ := fun ω v => argPath (fun r => U r ω) (hU.cont ω) z
        (sigmaTime (fun r => U r ω) (hU.cont ω) z v) -
      argPath (fun r => U r ω) (hU.cont ω) z 0 - ∫ u in (0 : ℝ)..v, muHat hU z ω u)
    (N := fun k s ω => thetaMart hU z k (sigmaStop hU z k s ω) ω)
    (fun k => isContLocalMartingale_thetaMart_sigmaStop hU ha hc hz k)
    (fun k ω => (continuous_thetaMart hU z k ω).comp (continuous_sigmaStop hU k ω))
    (fun k _ hz' s => thetaMart_sigmaStop_eq hU hz' k s)
    (fun k _ hz' _ => thetaMart_eq_zero_of_not_pos hU hz' k _)

/-- **Lemma 2.11, imaginary part, martingale form** (`eqn-theta-t`, bracket): the square of
`θ̂_s - θ̂_0 - ∫₀ˢ µ(θ̂_v) dv` minus `∫₀ˢ (a sin² θ̂_v + b cos² θ̂_v - 2c sin θ̂_v cos θ̂_v) dv`
is a continuous `𝒢`-local martingale. -/
theorem isContLocalMartingale_sigmaThetaMartSq (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) :
    IsContLocalMartingale (sigmaFiltration hU z) (sigmaThetaMartSq hU z) P :=
  isContLocalMartingale_sigma_of_stopped hU z ha hc hz
    (Φ := fun ω v => (argPath (fun r => U r ω) (hU.cont ω) z
        (sigmaTime (fun r => U r ω) (hU.cont ω) z v) -
      argPath (fun r => U r ω) (hU.cont ω) z 0 - ∫ u in (0 : ℝ)..v, muHat hU z ω u) ^ 2 -
      ∫ u in (0 : ℝ)..v, thetaBracketHat hU z ω u)
    (N := fun k s ω => thetaMart hU z k (sigmaStop hU z k s ω) ω ^ 2 -
      pathIntegral (thetaBracket hU z k) (sigmaStop hU z k s ω) ω)
    (fun k => isContLocalMartingale_thetaMart_sigmaStop_sq_sub hU ha hc hz k)
    (fun k ω => (((continuous_thetaMart hU z k ω).comp (continuous_sigmaStop hU k ω)).pow 2).sub
      ((continuous_pathIntegral_thetaBracket hU z k ω).comp (continuous_sigmaStop hU k ω)))
    (fun k _ hz' s => by
      rw [thetaMart_sigmaStop_eq hU hz' k s, pathIntegral_thetaBracket_sigmaStop_eq hU hz' k s]
      rfl)
    (fun k _ hz' _ => by
      rw [thetaMart_eq_zero_of_not_pos hU hz' k,
        pathIntegral_thetaBracket_eq_zero_of_not_pos hU hz' k]
      ring)

/-- **Lemma 2.11, cross bracket, martingale form**: the product of the martingale parts of `θ̂`
and `log|f̂|` minus `∫₀ˢ ((b - a) sin θ̂_v cos θ̂_v + c (cos² θ̂_v - sin² θ̂_v)) dv` is a continuous
`𝒢`-local martingale. -/
theorem isContLocalMartingale_sigmaThetaLogCross (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) :
    IsContLocalMartingale (sigmaFiltration hU z) (sigmaThetaLogCross hU z) P :=
  isContLocalMartingale_sigma_of_stopped hU z ha hc hz
    (Φ := fun ω v => (argPath (fun r => U r ω) (hU.cont ω) z
        (sigmaTime (fun r => U r ω) (hU.cont ω) z v) -
      argPath (fun r => U r ω) (hU.cont ω) z 0 - ∫ u in (0 : ℝ)..v, muHat hU z ω u) *
      (Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z
          (sigmaTime (fun r => U r ω) (hU.cont ω) z v)‖ -
        Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z 0‖ -
        ∫ u in (0 : ℝ)..v, nuHat hU z ω u) -
      ∫ u in (0 : ℝ)..v, crossHat hU z ω u)
    (N := fun k s ω => thetaMart hU z k (sigmaStop hU z k s ω) ω *
      logMart hU z k (sigmaStop hU z k s ω) ω -
      pathIntegral (thetaLogCross hU z k) (sigmaStop hU z k s ω) ω)
    (fun k => isContLocalMartingale_thetaMart_mul_logMart_sigmaStop_sub hU ha hc hz k)
    (fun k ω => (((continuous_thetaMart hU z k ω).comp (continuous_sigmaStop hU k ω)).mul
      ((continuous_logMart hU z k ω).comp (continuous_sigmaStop hU k ω))).sub
      ((continuous_pathIntegral_thetaLogCross hU z k ω).comp (continuous_sigmaStop hU k ω)))
    (fun k _ hz' s => by
      rw [thetaMart_sigmaStop_eq hU hz' k s, logMart_sigmaStop_eq hU hz' k s,
        pathIntegral_thetaLogCross_sigmaStop_eq hU hz' k s]
      rfl)
    (fun k _ hz' _ => by
      rw [thetaMart_eq_zero_of_not_pos hU hz' k, logMart_eq_zero_of_not_pos hU hz' k,
        pathIntegral_thetaLogCross_eq_zero_of_not_pos hU hz' k]
      ring)

end Martingales

/-! ### `θ̂` is progressive for `𝒢` and a.s. continuous -/

/-- On `{s < A(τ_k)}`, `θ̂_s = θ̃^k_{σ^k_s}` (the stopped argument at the stopped σ-time). -/
theorem thetaHat_eq_argStopped_sigmaStop {k : ℕ} {s : ℝ≥0} {ω : Ω} (h : s < clockExit hU z k ω) :
    thetaHat hU z s ω = argStopped hU z k (sigmaStop hU z k s ω) ω := by
  have hlt := (sigmaStop_lt_exitNN_iff hU).2 h
  obtain ⟨hs, heq⟩ := of_sigmaStop_lt_exitNN hU hlt
  have hz := pos_absorbingTime_of_mem_sigmaDom (hU.cont ω) hs
  rw [thetaHat_of_mem hU hs, argStopped_eq hU z k hz, coe_sigmaStop,
    min_eq_left (sigmaStopR_le_exitR hU k s ω), heq]

/-- Every `s ∈ sigmaDom` lies below some `A(τ_k)`. -/
theorem exists_lt_clockExit_of_mem_sigmaDom {s : ℝ≥0} {ω : Ω}
    (hs : (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z) : ∃ k, s < clockExit hU z k ω := by
  have hz := pos_absorbingTime_of_mem_sigmaDom (hU.cont ω) hs
  have hσ := sigmaTime_mem_lifeSet (hU.cont ω) hs
  obtain ⟨k, hk⟩ := exists_lt_exitTime (hU.cont ω) hσ
  refine ⟨k, ?_⟩
  rw [← NNReal.coe_lt_coe, coe_clockExit, ← clock_sigmaTime (hU.cont ω) hs]
  exact clock_lt_clock (hU.cont ω) hσ.1 hk (exitR_mem_lifeSet hU z k hz)

theorem thetaHat_eq_zero_of_forall_le {s : ℝ≥0} {ω : Ω} (h : ∀ k, clockExit hU z k ω ≤ s) :
    thetaHat hU z s ω = 0 := by
  refine thetaHat_of_notMem hU fun hs => ?_
  obtain ⟨k, hk⟩ := exists_lt_clockExit_of_mem_sigmaDom hU hs
  exact absurd hk (not_lt.2 (h k))

/-- `s ↦ θ̃^k_{σ^k_s}` is `𝒢`-progressive: it is `𝒢`-adapted (`θ̃^k` is progressive and `σ^k_s` a
bounded stopping time) with continuous paths. -/
theorem isStronglyProgressive_argStopped_sigmaStop (k : ℕ) :
    IsStronglyProgressive (sigmaFiltration hU z)
      fun s ω => argStopped hU z k (sigmaStop hU z k s ω) ω := by
  refine StronglyAdapted.isStronglyProgressive_of_continuous (fun s => ?_)
    fun ω => (continuous_argStopped hU z k ω).comp (continuous_sigmaStop hU k ω)
  have h := measurable_stoppedValue (isStronglyProgressive_argStopped hU z k)
    (isStoppingTime_sigmaStop hU z k s)
  rw [Infrastructure.stoppedValue_coe] at h
  exact (h.mono (sigmaStopFiltration_le hU k s) le_rfl).stronglyMeasurable

/-- **`θ̂` is progressively measurable for the σ-time filtration**: it is the pointwise limit of
the `𝒢`-progressive processes `1_{s < A(τ_k)} θ̃^k_{σ^k_s}`. -/
theorem isStronglyProgressive_thetaHat :
    IsStronglyProgressive (sigmaFiltration hU z) (thetaHat hU z) := by
  intro i
  let X : ℕ → Iic i × Ω → ℝ := fun K p =>
    (if ((p.1 : ℝ≥0) : WithTop ℝ≥0) < (clockExit hU z K p.2 : WithTop ℝ≥0) then (1 : ℝ) else 0) *
      argStopped hU z K (sigmaStop hU z K p.1 p.2) p.2
  have hX : ∀ K, StronglyMeasurable[Subtype.instMeasurableSpace.prod (sigmaFiltration hU z i)]
      (X K) := fun K =>
    ((Infrastructure.isStronglyProgressive_indicator_lt (isStoppingTime_clockExit hU K)) i).mul
      (isStronglyProgressive_argStopped_sigmaStop hU K i)
  refine stronglyMeasurable_of_tendsto atTop hX ?_
  rw [tendsto_pi_nhds]
  intro p
  by_cases h : ∃ k, (p.1 : ℝ≥0) < clockExit hU z k p.2
  · obtain ⟨k, hk⟩ := h
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop k] with K hK
    have hK' : (p.1 : ℝ≥0) < clockExit hU z K p.2 := lt_of_lt_of_le hk (clockExit_mono hU p.2 hK)
    simp only [X, WithTop.coe_lt_coe, hK', ite_true, one_mul]
    exact thetaHat_eq_argStopped_sigmaStop hU hK'
  · push Not at h
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun K => ?_)
    have : ¬ ((p.1 : ℝ≥0) : WithTop ℝ≥0) < clockExit hU z K p.2 := by
      rw [WithTop.coe_lt_coe]; exact not_lt.2 (h K)
    simp only [X, this, ite_false, zero_mul]
    exact thetaHat_eq_zero_of_forall_le hU h

/-- On the a.s. event `sigmaDom = [0, ∞)` (Remark 2.12), `θ̂_s = θ_{σ_z(s)}` for every `s` and the
path is continuous. -/
theorem ae_thetaHat_eq_and_continuous [IsProbabilityMeasure P] (ha : 0 < a) (hc : c ^ 2 ≤ a * b)
    (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, (∀ s : ℝ≥0, (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z) ∧
      Continuous fun s => thetaHat hU z s ω := by
  filter_upwards [ae_sigmaDom_eq_Ici hU z ha hc hz] with ω hω
  have hmem : ∀ s : ℝ≥0, (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z := fun s => by
    rw [hω]; exact s.coe_nonneg
  refine ⟨hmem, ?_⟩
  have e : (fun s => thetaHat hU z s ω) = fun s : ℝ≥0 => argPath (fun r => U r ω) (hU.cont ω) z
      (sigmaTime (fun r => U r ω) (hU.cont ω) z s) := funext fun s => thetaHat_of_mem hU (hmem s)
  rw [e]
  exact ((continuousOn_argPath (hU.cont ω) z).comp (continuousOn_sigmaTime (hU.cont ω) z)
    fun _ hv => sigmaTime_mem_lifeSet (hU.cont ω) hv).comp_continuous NNReal.continuous_coe hmem

/-! ### The martingale-form SDE for `θ̂` -/

section Diffusion

variable [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- Path integrals of continuous functions of `θ̂` in the form of the σ-time densities, on the
a.s. event `sigmaDom = [0, ∞)`. -/
theorem pathIntegral_comp_thetaHat_eq {ω : Ω}
    (hmem : ∀ s : ℝ≥0, (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z) (φ : ℝ → ℝ)
    (t : ℝ≥0) :
    pathIntegral (fun s ω => φ (thetaHat hU z s ω)) t ω =
      ∫ v in (0 : ℝ)..(t : ℝ), φ (argPath (fun r => U r ω) (hU.cont ω) z
        (sigmaTime (fun r => U r ω) (hU.cont ω) z v)) := by
  simp only [pathIntegral]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le t.coe_nonneg] at hs
  rw [thetaHat_of_mem hU (hmem _), Real.coe_toNNReal _ hs.1]

/-- The martingale part of `θ̂` in the vocabulary of `IsDiffusionSolution` agrees a.s. with
`sigmaThetaMart`. -/
theorem ae_thetaHat_mart_eq (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, thetaHat hU z t ω - thetaHat hU z 0 ω -
      pathIntegral (fun s ω => mu a b c (thetaHat hU z s ω)) t ω = sigmaThetaMart hU z t ω := by
  filter_upwards [ae_thetaHat_eq_and_continuous hU ha hc hz] with ω hω t
  have hmem := hω.1
  have hz' : 0 < absorbingTime (fun r => U r ω) z :=
    pos_absorbingTime_of_mem_sigmaDom (hU.cont ω) (hmem 0)
  rw [sigmaThetaMart, ite_eq_left (hmem t), thetaHat_of_mem hU (hmem t),
    thetaHat_of_mem hU (hmem 0),
    NNReal.coe_zero, sigmaTime_zero (hU.cont ω) (zero_mem_lifeSet_iff.2 hz'),
    pathIntegral_comp_thetaHat_eq hU hmem]
  rfl

/-- **`θ̂` solves the martingale problem of `(2.25)`** (`eqn-theta-t`, Lemma 2.11, imaginary
part): for `0 < a`, `c² ≤ ab`, `z ≠ 0`,
`IsDiffusionSolution (sigmaFiltration hU z) (mu a b c) (fun u => √(2 * diffusionD a b c u)) θ̂ P`,
i.e. `θ̂` is `𝒢`-progressive with a.s. continuous paths, `θ̂_s - θ̂_0 - ∫₀ˢ µ(θ̂_v) dv` is a
continuous `𝒢`-local martingale, and so is its square minus `∫₀ˢ 2 D(θ̂_v) dv`. -/
theorem isDiffusionSolution_thetaHat (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) :
    IsDiffusionSolution (sigmaFiltration hU z) (mu a b c) (fun u => √(2 * diffusionD a b c u))
      (thetaHat hU z) P := by
  have hprog := isStronglyProgressive_thetaHat hU (z := z)
  have hμp : IsStronglyProgressive (sigmaFiltration hU z) fun s ω => mu a b c (thetaHat hU z s ω) :=
    fun i => (continuous_mu a b c).comp_stronglyMeasurable (hprog i)
  have hβc : Continuous fun u : ℝ => (√(2 * diffusionD a b c u)) ^ 2 := by
    unfold diffusionD; fun_prop
  have hβp : IsStronglyProgressive (sigmaFiltration hU z)
      fun s ω => (√(2 * diffusionD a b c (thetaHat hU z s ω))) ^ 2 :=
    fun i => hβc.comp_stronglyMeasurable (hprog i)
  have h0p : IsStronglyProgressive (sigmaFiltration hU z) fun (_ : ℝ≥0) ω => thetaHat hU z 0 ω :=
    StronglyAdapted.isStronglyProgressive_of_continuous
      (fun t => (hprog.stronglyAdapted 0).mono ((sigmaFiltration hU z).mono bot_le))
      fun _ => continuous_const
  have hMp : IsStronglyProgressive (sigmaFiltration hU z) fun t ω => thetaHat hU z t ω -
      thetaHat hU z 0 ω - pathIntegral (fun s ω => mu a b c (thetaHat hU z s ω)) t ω :=
    fun i => ((hprog i).sub (h0p i)).sub (isStronglyProgressive_pathIntegral' hμp i)
  refine ⟨hprog, ?_, ?_, ?_⟩
  · filter_upwards [ae_thetaHat_eq_and_continuous hU ha hc hz] with ω hω using hω.2
  · exact (isContLocalMartingale_sigmaThetaMart hU ha hc hz).congr_ae hMp
      (ae_thetaHat_mart_eq hU ha hc hz)
  · refine (isContLocalMartingale_sigmaThetaMartSq hU ha hc hz).congr_ae
      (fun i => ((hMp i).pow 2).sub (isStronglyProgressive_pathIntegral' hβp i)) ?_
    filter_upwards [ae_thetaHat_mart_eq hU ha hc hz, ae_thetaHat_eq_and_continuous hU ha hc hz]
      with ω hω hω' t
    rw [hω t, sigmaThetaMartSq_eq hU (hω'.1 t),
      pathIntegral_comp_thetaHat_eq hU hω'.1 (fun u => (√(2 * diffusionD a b c u)) ^ 2) t]
    congr 1
    refine intervalIntegral.integral_congr fun v _ => ?_
    simp only [thetaBracketHat, sq_sqrt_two_mul_diffusionD ha hc]

/-! ### The joint decomposition of `(θ̂, log|f̂|)` for Lemma 3.3 -/

/-- `sigmaLogMart` in terms of `θ̂`, on the a.s. event `sigmaDom = [0, ∞)`:
`ρ̂_s - ρ̂_0 - ∫₀ˢ ν(θ̂_v) dv` with `ρ̂_s = log|f_{σ_z(s)}(z)|`. -/
theorem ae_sigmaLogMart_eq (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0, sigmaLogMart hU z s ω =
      Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z
          (sigmaTime (fun r => U r ω) (hU.cont ω) z s)‖ -
        Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z 0‖ -
        pathIntegral (fun v ω => nu a b c (thetaHat hU z v ω)) s ω := by
  filter_upwards [ae_thetaHat_eq_and_continuous hU ha hc hz] with ω hω s
  rw [sigmaLogMart, ite_eq_left (hω.1 s), pathIntegral_comp_thetaHat_eq hU hω.1]
  rfl

/-- **The joint decomposition of `(θ̂, log|f̂|)` in martingale form** (Lemma 2.11, the input to
Lemma 3.3): with `M^θ_s = θ̂_s - θ̂_0 - ∫₀ˢ µ(θ̂)` and `M^ρ = sigmaLogMart` (a.s. equal to
`ρ̂_s - ρ̂_0 - ∫₀ˢ ν(θ̂)`, `ae_sigmaLogMart_eq`), the processes `M^θ`, `M^ρ`,
`(M^θ)² - ∫₀ˢ 2 D(θ̂)`, `(M^ρ)² - ∫₀ˢ (a cos² θ̂ + b sin² θ̂ + 2c sin θ̂ cos θ̂)` and
`M^θ M^ρ - ∫₀ˢ ((b - a) sin θ̂ cos θ̂ + c (cos² θ̂ - sin² θ̂))` are continuous `𝒢`-local
martingales. -/
theorem thetaHat_sigmaLogMart_decomposition (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) :
    IsContLocalMartingale (sigmaFiltration hU z) (fun t ω => thetaHat hU z t ω -
      thetaHat hU z 0 ω - pathIntegral (fun s ω => mu a b c (thetaHat hU z s ω)) t ω) P ∧
    IsContLocalMartingale (sigmaFiltration hU z) (sigmaLogMart hU z) P ∧
    IsContLocalMartingale (sigmaFiltration hU z) (fun t ω => (thetaHat hU z t ω -
      thetaHat hU z 0 ω - pathIntegral (fun s ω => mu a b c (thetaHat hU z s ω)) t ω) ^ 2 -
      pathIntegral (fun s ω => 2 * diffusionD a b c (thetaHat hU z s ω)) t ω) P ∧
    IsContLocalMartingale (sigmaFiltration hU z) (fun t ω => sigmaLogMart hU z t ω ^ 2 -
      pathIntegral (fun s ω => logBracketFn a b c (thetaHat hU z s ω)) t ω) P ∧
    IsContLocalMartingale (sigmaFiltration hU z) (fun t ω => (thetaHat hU z t ω -
      thetaHat hU z 0 ω - pathIntegral (fun s ω => mu a b c (thetaHat hU z s ω)) t ω) *
      sigmaLogMart hU z t ω -
      pathIntegral (fun s ω => crossPolar a b c (thetaHat hU z s ω)) t ω) P := by
  have hprog := isStronglyProgressive_thetaHat hU (z := z)
  have hμp : IsStronglyProgressive (sigmaFiltration hU z) fun s ω => mu a b c (thetaHat hU z s ω) :=
    fun i => (continuous_mu a b c).comp_stronglyMeasurable (hprog i)
  have h0p : IsStronglyProgressive (sigmaFiltration hU z) fun (_ : ℝ≥0) ω => thetaHat hU z 0 ω :=
    StronglyAdapted.isStronglyProgressive_of_continuous
      (fun t => (hprog.stronglyAdapted 0).mono ((sigmaFiltration hU z).mono bot_le))
      fun _ => continuous_const
  have hMp : IsStronglyProgressive (sigmaFiltration hU z) fun t ω => thetaHat hU z t ω -
      thetaHat hU z 0 ω - pathIntegral (fun s ω => mu a b c (thetaHat hU z s ω)) t ω :=
    fun i => ((hprog i).sub (h0p i)).sub (isStronglyProgressive_pathIntegral' hμp i)
  have hL := isContLocalMartingale_sigmaLogMart hU ha hc hz
  have hDp : IsStronglyProgressive (sigmaFiltration hU z)
      fun s ω => 2 * diffusionD a b c (thetaHat hU z s ω) :=
    fun i => (by unfold diffusionD; fun_prop : Continuous fun u : ℝ => 2 * diffusionD a b c u)
      |>.comp_stronglyMeasurable (hprog i)
  have hΓp : IsStronglyProgressive (sigmaFiltration hU z)
      fun s ω => logBracketFn a b c (thetaHat hU z s ω) :=
    fun i => (continuous_logBracketFn a b c).comp_stronglyMeasurable (hprog i)
  have hCp : IsStronglyProgressive (sigmaFiltration hU z)
      fun s ω => crossPolar a b c (thetaHat hU z s ω) :=
    fun i => (continuous_crossPolar a b c).comp_stronglyMeasurable (hprog i)
  refine ⟨(isContLocalMartingale_sigmaThetaMart hU ha hc hz).congr_ae hMp
    (ae_thetaHat_mart_eq hU ha hc hz), hL, ?_, ?_, ?_⟩
  · refine (isContLocalMartingale_sigmaThetaMartSq hU ha hc hz).congr_ae
      (fun i => ((hMp i).pow 2).sub (isStronglyProgressive_pathIntegral' hDp i)) ?_
    filter_upwards [ae_thetaHat_mart_eq hU ha hc hz, ae_thetaHat_eq_and_continuous hU ha hc hz]
      with ω hω hω' t
    rw [hω t, sigmaThetaMartSq_eq hU (hω'.1 t),
      pathIntegral_comp_thetaHat_eq hU hω'.1 (fun u => 2 * diffusionD a b c u) t]
    congr 1
    refine intervalIntegral.integral_congr fun v _ => ?_
    simp only [thetaBracketHat, thetaBracketPolar_eq_two_mul_diffusionD]
  · refine (isContLocalMartingale_sigmaLogMartSq hU ha hc hz).congr_ae
      (fun i => ((hL.1 i).pow 2).sub (isStronglyProgressive_pathIntegral' hΓp i)) ?_
    filter_upwards [ae_thetaHat_eq_and_continuous hU ha hc hz] with ω hω t
    rw [sigmaLogMartSq_eq hU z (hω.1 t), pathIntegral_comp_thetaHat_eq hU hω.1]
    rfl
  · refine (isContLocalMartingale_sigmaThetaLogCross hU ha hc hz).congr_ae
      (fun i => ((hMp i).mul (hL.1 i)).sub (isStronglyProgressive_pathIntegral' hCp i)) ?_
    filter_upwards [ae_thetaHat_mart_eq hU ha hc hz, ae_thetaHat_eq_and_continuous hU ha hc hz]
      with ω hω hω' t
    rw [hω t, sigmaThetaLogCross_eq hU (hω'.1 t), pathIntegral_comp_thetaHat_eq hU hω'.1]
    rfl

end Diffusion

end Processes

end ComplexSLE.Internal.Polar

end
