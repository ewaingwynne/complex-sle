/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.DriverMeasurability
public import ComplexSLE.Internal.Polar.DriverBridge
public import ComplexSLE.Infrastructure.Stochastic.LocalMartingaleAlgebra
public import ComplexSLE.Infrastructure.Stochastic.ProgressiveTools
public import ComplexSLE.Frozen.Defs.PathIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The state of the Itô step: `f_t(z)` stopped at the annulus exit time `τ_n` (M6/S8)

For an adapted `SLE_Σ` driver `hU : IsSLEDriverAdapted a b c U P ℱ` and `z : ℂ`, the state fed to
Itô's formula (E1, `step:polar-ito-log`) is the `ℝ²`-valued process
`X_t = (Re f_{t ∧ τ_n}(z), Im f_{t ∧ τ_n}(z))`, where `τ_n = exitTime` is the first time
`|f| ≤ 1/n`,
`|f| ≥ n` or `t = n` (a finite `ℱ`-stopping time lying in `[0, T_z)`), with the conventions
`X ≡ 0` on the event `{T_z = 0}` (which is `P`-null for `z ≠ 0`). Its characteristics are

* drift `A_s = 1_{s ≤ τ_n} (Re (2 / f_s), Im (2 / f_s))` (from `ġ = 2 / f`, `f = g - U`),
* diffusion matrix `Q_s = 1_{s ≤ τ_n} Σ`, `Σ = covMatrix a b c`,

in the sense that `Xⁱ_t - Xⁱ_0 - ∫₀ᵗ Aⁱ = -(Uⁱ_{t ∧ τ_n} - Uⁱ_0)` and
`(Uⁱ_t - Uⁱ_0)(Uʲ_t - Uʲ_0) - Σⁱʲ t` are continuous (local) martingales (`DriverBridge.lean`,
`step:driver-representation`). This file proves the pathwise identities and all hypotheses of
`External.ito_formula` for this state (`itoState`, `itoDrift`, `itoQ`); the formula itself is
applied in `PolarItoLog.lean`.

Measurability: the path `t ↦ f_t(z)` set to `0` off `[0, T_z)` (`centeredOrZero`) is adapted and
right-continuous, hence progressive; stopping at `τ_n` gives the (everywhere continuous, adapted)
state.
-/

public section

open scoped NNReal ENNReal Topology
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal.Polar

/-! ### Deterministic facts: exit times and the fundamental theorem of calculus for `g` -/

section Deterministic

variable {V : ℝ≥0 → ℂ}

/-- The life set is empty when `T_z = 0`. -/
theorem lifeSet_eq_empty_of_not_pos {z : ℂ} (hz : ¬ 0 < absorbingTime V z) : lifeSet V z = ∅ := by
  ext t
  simp only [mem_lifeSet, mem_empty_iff_false, iff_false, not_and, not_lt]
  intro _
  exact le_trans (not_lt.1 hz) bot_le

/-- The exit time is nonnegative (also when `T_z = 0`, where it is `sInf ∅ = 0`). -/
theorem exitTime_nonneg' (hV : Continuous V) (z : ℂ) (n : ℕ) : 0 ≤ exitTime V hV z n := by
  by_cases h : (exitSet V hV z n).Nonempty
  · exact le_csInf h fun _ ht => ht.1.1
  · rw [not_nonempty_iff_eq_empty] at h
    simp [exitTime, h]

/-- When `T_z = 0` the exit time is `0`. -/
theorem exitTime_eq_zero_of_not_pos (hV : Continuous V) {z : ℂ} (hz : ¬ 0 < absorbingTime V z)
    (n : ℕ) : exitTime V hV z n = 0 := by
  have : exitSet V hV z n = ∅ := by
    ext t
    simp [exitSet, lifeSet_eq_empty_of_not_pos hz]
  simp [exitTime, this]

/-- `t ∧ τ_n ∈ [0, T_z)` when `T_z > 0`. -/
theorem min_exitTime_mem_lifeSet (hV : Continuous V) {z : ℂ} (hz : 0 < absorbingTime V z)
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : min t (exitTime V hV z n) ∈ lifeSet V z :=
  mem_lifeSet_of_le (exitTime_mem_lifeSet hV hz n) (le_min ht (exitTime_nonneg hV hz n))
    (min_le_right _ _)

/-- `2 / f` is interval integrable on `[0, r]` for `r ∈ [0, T_z)`. -/
theorem intervalIntegrable_two_div_fPath (hV : Continuous V) {z : ℂ} {r : ℝ}
    (hr : r ∈ lifeSet V z) :
    IntervalIntegrable (fun s => 2 / fPath V hV z s) volume 0 r := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hr.1]
  exact (continuousOn_const.div (continuousOn_fPath hV z) fun _ hs => fPath_ne_zero hV hs).mono
    (Icc_subset_lifeSet hr)

/-- **FTC for `g`**: `g_r(z) - g_0(z) = ∫₀ʳ 2 / f_s(z) ds` on the life set. -/
theorem integral_two_div_fPath (hV : Continuous V) {z : ℂ} {r : ℝ} (hr : r ∈ lifeSet V z) :
    ∫ s in (0 : ℝ)..r, 2 / fPath V hV z s = solPath V hV z r - solPath V hV z 0 :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.1
    ((continuousOn_solPath hV z).mono (Icc_subset_lifeSet hr))
    (fun _ hs => hasDerivAt_solPath hV (Icc_subset_lifeSet hr (Ioo_subset_Icc_self hs)) hs.1)
    (intervalIntegrable_two_div_fPath hV hr)

/-- `f_r(z) - f_0(z) = ∫₀ʳ 2 / f_s(z) ds - (U_r - U_0)` on the life set. -/
theorem fPath_sub_fPath_zero (hV : Continuous V) {z : ℂ} {r : ℝ} (hr : r ∈ lifeSet V z) :
    fPath V hV z r - fPath V hV z 0 =
      (∫ s in (0 : ℝ)..r, 2 / fPath V hV z s) - (V r.toNNReal - V 0) := by
  rw [integral_two_div_fPath hV hr]
  simp only [fPath, Real.toNNReal_zero]
  ring

end Deterministic

/-! ### Right-continuity and progressive measurability of the path set to `0` off `[0, T_z)` -/

section Progressive

variable {Ω : Type*} {m : MeasurableSpace Ω} {U : ℝ≥0 → Ω → ℂ} {ℱ : Filtration ℝ≥0 m}
  {V : ℝ≥0 → ℂ}

/-- `{t : ℝ≥0 | t ∈ [0, T_z)}` is a neighbourhood of each of its points. -/
theorem coe_mem_lifeSet_mem_nhds {z : ℂ} {r : ℝ≥0}
    (hr : (r : ℝ) ∈ lifeSet V z) : {t : ℝ≥0 | (t : ℝ) ∈ lifeSet V z} ∈ 𝓝 r := by
  obtain ⟨O, hO, hrO, hsub⟩ := mem_nhdsWithin.1 (lifeSet_mem_nhdsWithin hr)
  refine Filter.mem_of_superset ((hO.preimage NNReal.continuous_coe).mem_nhds hrO) ?_
  intro t ht
  exact hsub ⟨ht, NNReal.coe_nonneg t⟩

/-- The path `t ↦ f_t(z)` set to `0` off the life set is right-continuous at every `r : ℝ≥0`. -/
theorem continuousWithinAt_centeredOrZero (hc : ∀ ω, Continuous fun t => U t ω) (z : ℂ) (ω : Ω)
    (r : ℝ≥0) :
    ContinuousWithinAt (fun t => centeredOrZero U hc z t ω) (Ici r) r := by
  by_cases hr : (r : ℝ) ∈ lifeSet (fun s => U s ω) z
  · -- near `r` the process is `f ∘ coe`, which is continuous at `r`
    have hcont : ContinuousAt (fun t : ℝ≥0 => fPath (fun s => U s ω) (hc ω) z t) r := by
      have h1 : ContinuousWithinAt (fPath (fun s => U s ω) (hc ω) z) (Ici 0) (r : ℝ) :=
        continuousWithinAt_fPath_Ici (hc ω) hr
      have h2 : ContinuousWithinAt (fun t : ℝ≥0 => (t : ℝ)) univ r :=
        NNReal.continuous_coe.continuousWithinAt
      have := h1.comp h2 (fun t _ => NNReal.coe_nonneg t)
      rwa [continuousWithinAt_univ] at this
    refine (hcont.congr_of_eventuallyEq ?_).continuousWithinAt
    filter_upwards [coe_mem_lifeSet_mem_nhds hr] with t ht
    exact centeredOrZero_eq hc z ht
  · -- to the right of `r` the process vanishes
    refine (continuousWithinAt_const (b := (0 : ℂ))).congr (fun t ht => ?_) ?_
    · have : (t : ℝ) ∉ lifeSet (fun s => U s ω) z := fun h =>
        hr (mem_lifeSet_of_le h (NNReal.coe_nonneg r) (NNReal.coe_le_coe.2 ht))
      simp [centeredOrZero, this]
    · simp [centeredOrZero, hr]

/-- The path set to `0` off the life set is adapted. -/
theorem stronglyAdapted_centeredOrZero (hc : ∀ ω, Continuous fun t => U t ω) (had : Adapted ℱ U)
    (z : ℂ) : StronglyAdapted ℱ (centeredOrZero U hc z) := fun r =>
  (measurable_centeredOrZero hc had z r).stronglyMeasurable

/-- **The path set to `0` off the life set is progressively measurable.** -/
theorem isStronglyProgressive_centeredOrZero (hc : ∀ ω, Continuous fun t => U t ω)
    (had : Adapted ℱ U) (z : ℂ) : IsStronglyProgressive ℱ (centeredOrZero U hc z) :=
  (stronglyAdapted_centeredOrZero hc had z).isStronglyProgressive_of_rightContinuous
    fun ω r => continuousWithinAt_centeredOrZero hc z ω r

end Progressive

/-! ### The stopped path and the Itô state -/

section State

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

variable (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) (n : ℕ)

/-- `τ_n(ω)` as a real number. -/
@[expose] noncomputable def exitR (ω : Ω) : ℝ := exitTime (fun r => U r ω) (hU.cont ω) z n

/-- `τ_n(ω)` as an `ℝ≥0`-valued random time. -/
@[expose] noncomputable def exitNN (ω : Ω) : ℝ≥0 := (exitR hU z n ω).toNNReal

theorem exitR_nonneg (ω : Ω) : 0 ≤ exitR hU z n ω := exitTime_nonneg' _ _ _

theorem coe_exitNN (ω : Ω) : ((exitNN hU z n ω : ℝ≥0) : ℝ) = exitR hU z n ω :=
  Real.coe_toNNReal _ (exitR_nonneg hU z n ω)

theorem le_exitNN_iff {t : ℝ≥0} {ω : Ω} : t ≤ exitNN hU z n ω ↔ (t : ℝ) ≤ exitR hU z n ω := by
  rw [← NNReal.coe_le_coe, coe_exitNN]

/-- `τ_n` is an `ℱ`-stopping time. -/
theorem isStoppingTime_exitNN : IsStoppingTime ℱ fun ω => (exitNN hU z n ω : WithTop ℝ≥0) :=
  isStoppingTime_exitTime_of_isSLEDriverAdapted hU z n

theorem exitR_mem_lifeSet {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) :
    exitR hU z n ω ∈ lifeSet (fun s => U s ω) z :=
  exitTime_mem_lifeSet (hU.cont ω) hz n

theorem exitR_eq_zero {ω : Ω} (hz : ¬ 0 < absorbingTime (fun s => U s ω) z) :
    exitR hU z n ω = 0 :=
  exitTime_eq_zero_of_not_pos (hU.cont ω) hz n

/-- **The stopped path** `f_{t ∧ τ_n}(z)` (and `0` on `{T_z = 0}`). -/
@[expose] noncomputable def stoppedF (t : ℝ≥0) (ω : Ω) : ℂ :=
  centeredOrZero U hU.cont z (min t (exitNN hU z n ω)) ω

theorem stoppedF_eq_stoppedProcess :
    stoppedF hU z n = stoppedProcess (centeredOrZero U hU.cont z)
      fun ω => (exitNN hU z n ω : WithTop ℝ≥0) := by
  funext t ω
  simp only [stoppedF, stoppedProcess]
  rw [← WithTop.coe_min]
  rfl

/-- On `{T_z > 0}` the stopped path is `f_{t ∧ τ_n}(z)`. -/
theorem stoppedF_eq {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) (t : ℝ≥0) :
    stoppedF hU z n t ω =
      fPath (fun s => U s ω) (hU.cont ω) z (min (t : ℝ) (exitR hU z n ω)) := by
  have hmem : ((min t (exitNN hU z n ω) : ℝ≥0) : ℝ) ∈ lifeSet (fun s => U s ω) z := by
    rw [NNReal.coe_min, coe_exitNN]
    exact min_exitTime_mem_lifeSet (hU.cont ω) hz n t.coe_nonneg
  rw [stoppedF, centeredOrZero_eq hU.cont z hmem, NNReal.coe_min, coe_exitNN]

theorem stoppedF_eq_of_le {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) {t : ℝ≥0}
    (ht : (t : ℝ) ≤ exitR hU z n ω) :
    stoppedF hU z n t ω = fPath (fun s => U s ω) (hU.cont ω) z t := by
  rw [stoppedF_eq hU z n hz, min_eq_left ht]

theorem stoppedF_zero {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) :
    stoppedF hU z n 0 ω = z - U 0 ω := by
  rw [stoppedF_eq_of_le hU z n hz (by rw [NNReal.coe_zero]; exact exitR_nonneg hU z n ω),
    NNReal.coe_zero, fPath_zero]

/-- On `{T_z = 0}` the stopped path vanishes identically. -/
theorem stoppedF_eq_zero {ω : Ω} (hz : ¬ 0 < absorbingTime (fun s => U s ω) z) (t : ℝ≥0) :
    stoppedF hU z n t ω = 0 := by
  simp [stoppedF, centeredOrZero, lifeSet_eq_empty_of_not_pos hz]

theorem stoppedF_ne_zero {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) (t : ℝ≥0) :
    stoppedF hU z n t ω ≠ 0 := by
  rw [stoppedF_eq hU z n hz]
  exact fPath_ne_zero (hU.cont ω) (min_exitTime_mem_lifeSet (hU.cont ω) hz n t.coe_nonneg)

/-- Every path of the stopped process is continuous. -/
theorem continuous_stoppedF (ω : Ω) : Continuous fun t => stoppedF hU z n t ω := by
  by_cases hz : 0 < absorbingTime (fun s => U s ω) z
  · simp only [stoppedF_eq hU z n hz]
    refine (continuousOn_fPath (hU.cont ω) z).comp_continuous
      (NNReal.continuous_coe.min continuous_const) fun t => ?_
    exact min_exitTime_mem_lifeSet (hU.cont ω) hz n t.coe_nonneg
  · simp only [stoppedF_eq_zero hU z n hz]
    exact continuous_const

/-- The stopped path is progressively measurable. -/
theorem isStronglyProgressive_stoppedF : IsStronglyProgressive ℱ (stoppedF hU z n) := by
  rw [stoppedF_eq_stoppedProcess]
  exact (isStronglyProgressive_centeredOrZero hU.cont hU.adapted z).stoppedProcess
    (isStoppingTime_exitNN hU z n)

/-- The real components of a complex number, as a vector in `ℝ²`. -/
@[expose] def reIm (w : ℂ) : Fin 2 → ℝ := ![w.re, w.im]

theorem reIm_zero_apply (w : ℂ) : reIm w 0 = w.re := rfl

theorem reIm_one_apply (w : ℂ) : reIm w 1 = w.im := rfl

theorem continuous_reIm : Continuous reIm := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact Complex.continuous_re
  · exact Complex.continuous_im

/-- **The Itô state** `X_t = (Re f_{t ∧ τ_n}(z), Im f_{t ∧ τ_n}(z))`. -/
@[expose] noncomputable def itoState (t : ℝ≥0) (ω : Ω) : Fin 2 → ℝ := reIm (stoppedF hU z n t ω)

/-- The indicator `1_{t ≤ τ_n}`. -/
@[expose] noncomputable def beforeExit (t : ℝ≥0) (ω : Ω) : ℝ := if t ≤ exitNN hU z n ω then 1 else 0

/-- **The drift** `A_t = 1_{t ≤ τ_n} (Re (2 / f_t), Im (2 / f_t))`. -/
@[expose] noncomputable def itoDrift (t : ℝ≥0) (ω : Ω) : Fin 2 → ℝ :=
  beforeExit hU z n t ω • reIm (2 / stoppedF hU z n t ω)

/-- **The diffusion matrix** `Q_t = 1_{t ≤ τ_n} Σ`. -/
@[expose] noncomputable def itoQ (t : ℝ≥0) (ω : Ω) : Matrix (Fin 2) (Fin 2) ℝ :=
  beforeExit hU z n t ω • covMatrix a b c

theorem isStronglyProgressive_itoState : IsStronglyProgressive ℱ (itoState hU z n) := fun i =>
  continuous_reIm.comp_stronglyMeasurable (isStronglyProgressive_stoppedF hU z n i)

theorem continuous_itoState (ω : Ω) : Continuous fun t => itoState hU z n t ω :=
  continuous_reIm.comp (continuous_stoppedF hU z n ω)

theorem isStronglyProgressive_beforeExit : IsStronglyProgressive ℱ (beforeExit hU z n) :=
  Infrastructure.isStronglyProgressive_indicator_le_nnreal (isStoppingTime_exitNN hU z n)

theorem isStronglyProgressive_itoDrift : IsStronglyProgressive ℱ (itoDrift hU z n) := by
  intro i
  have h1 : StronglyMeasurable[Subtype.instMeasurableSpace.prod (ℱ i)]
      fun p : Iic i × Ω => (2 : ℂ) / stoppedF hU z n p.1 p.2 :=
    ((measurable_const.div measurable_id).comp
      (isStronglyProgressive_stoppedF hU z n i).measurable).stronglyMeasurable
  exact (isStronglyProgressive_beforeExit hU z n i).smul
    (continuous_reIm.comp_stronglyMeasurable h1)

theorem isStronglyProgressive_itoQ :
    IsStronglyProgressive ℱ (itoQ hU z n (a := a) (b := b) (c := c)) :=
  fun i => (isStronglyProgressive_beforeExit hU z n i).smul stronglyMeasurable_const

theorem reIm_zero : reIm 0 = 0 := by
  ext i; fin_cases i <;> simp [reIm]

theorem reIm_sub (x y : ℂ) : reIm (x - y) = reIm x - reIm y := by
  ext i; fin_cases i <;> simp [reIm]

theorem reIm_neg (x : ℂ) : reIm (-x) = -reIm x := by
  ext i; fin_cases i <;> simp [reIm]

/-- `reIm` as a continuous linear map (for commuting it with integrals). -/
@[expose] noncomputable def reImL : ℂ →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi ![Complex.reCLM, Complex.imCLM]

theorem reImL_apply (w : ℂ) : reImL w = reIm w := by
  ext i; fin_cases i <;> simp [reImL, reIm]

/-! ### The drift integral -/

/-- `∫₀ᵗ 1_{s ≤ τ} φ(s) ds = ∫₀^{t ∧ τ} φ(s) ds` for `τ, t ≥ 0`. -/
theorem integral_indicator_Iic_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : ℝ → E} {τ t : ℝ} (hτ : 0 ≤ τ) (ht : 0 ≤ t) :
    ∫ s in (0 : ℝ)..t, (Iic τ).indicator φ s = ∫ s in (0 : ℝ)..(min t τ), φ s := by
  rcases le_total τ t with h | h
  · rw [min_eq_right h]
    exact intervalIntegral.integral_indicator ⟨hτ, h⟩
  · rw [min_eq_left h]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht] at hs
    exact indicator_of_mem (mem_Iic.2 (hs.2.trans h)) φ

theorem beforeExit_toNNReal (ω : Ω) (s : ℝ) :
    beforeExit hU z n s.toNNReal ω = (Iic (exitR hU z n ω)).indicator (fun _ => (1 : ℝ)) s := by
  have key : s.toNNReal ≤ exitNN hU z n ω ↔ s ≤ exitR hU z n ω := by
    rw [exitNN, Real.toNNReal_le_toNNReal_iff (exitR_nonneg hU z n ω)]
  simp only [beforeExit, key, indicator, mem_Iic]

/-- On `{T_z = 0}` the drift vanishes. -/
theorem itoDrift_eq_zero {ω : Ω} (hz : ¬ 0 < absorbingTime (fun s => U s ω) z) (t : ℝ≥0) :
    itoDrift hU z n t ω = 0 := by
  simp [itoDrift, stoppedF_eq_zero hU z n hz, reIm_zero]

/-- On `{T_z > 0}` the drift at real time `s` is `1_{s ≤ τ_n} (Re, Im)(2 / f_s)`. -/
theorem itoDrift_toNNReal_eq {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) {s : ℝ}
    (hs : 0 ≤ s) :
    itoDrift hU z n s.toNNReal ω =
      (Iic (exitR hU z n ω)).indicator
        (fun s => reIm (2 / fPath (fun r => U r ω) (hU.cont ω) z s)) s := by
  rw [itoDrift, beforeExit_toNNReal]
  by_cases h : s ≤ exitR hU z n ω
  · rw [indicator_of_mem (mem_Iic.2 h), indicator_of_mem (mem_Iic.2 h), one_smul,
      stoppedF_eq_of_le hU z n hz (by rwa [Real.coe_toNNReal _ hs]), Real.coe_toNNReal _ hs]
  · rw [indicator_of_notMem (notMem_Iic.2 (not_le.1 h)), indicator_of_notMem
      (notMem_Iic.2 (not_le.1 h)), zero_smul]

/-- The drift is interval integrable (for every `ω`). -/
theorem intervalIntegrable_itoDrift (ω : Ω) (i : Fin 2) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => itoDrift hU z n s.toNNReal ω i) volume 0 t := by
  by_cases hz : 0 < absorbingTime (fun s => U s ω) z
  · have hφ : ContinuousOn (fun s => reIm (2 / fPath (fun r => U r ω) (hU.cont ω) z s) i)
        (Icc 0 (exitR hU z n ω)) := by
      refine ((continuous_apply i).comp continuous_reIm).comp_continuousOn ?_
      exact (continuousOn_const.div (continuousOn_fPath (hU.cont ω) z)
        fun _ hs => fPath_ne_zero (hU.cont ω) hs).mono
          (Icc_subset_lifeSet (exitR_mem_lifeSet hU z n hz))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg]
    have h1 : IntegrableOn (fun s : ℝ => (Iic (exitR hU z n ω)).indicator
        (fun s => reIm (2 / fPath (fun r => U r ω) (hU.cont ω) z s) i) s) (Ioc 0 t) := by
      rw [integrableOn_indicator_iff measurableSet_Iic.nullMeasurableSet]
      refine (hφ.integrableOn_compact isCompact_Icc).mono_set fun s hs => ?_
      simp only [mem_inter_iff, mem_Ioc, mem_Iic, mem_Icc] at hs ⊢
      exact ⟨hs.2.1.le, hs.1⟩
    refine h1.congr_fun (fun s hs => ?_) measurableSet_Ioc
    rw [itoDrift_toNNReal_eq hU z n hz hs.1.le]
    by_cases h : s ≤ exitR hU z n ω
    · simp only [indicator_of_mem (mem_Iic.2 h)]
    · simp only [indicator_of_notMem (notMem_Iic.2 (not_le.1 h)), Pi.zero_apply]
  · simp only [itoDrift_eq_zero hU z n hz, Pi.zero_apply]
    exact intervalIntegrable_const

/-- The diffusion matrix is interval integrable (for every `ω`). -/
theorem intervalIntegrable_itoQ (ω : Ω) (i j : Fin 2) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => itoQ hU z n (a := a) (b := b) (c := c) s.toNNReal ω i j)
      volume 0 t := by
  have : (fun s : ℝ => itoQ hU z n (a := a) (b := b) (c := c) s.toNNReal ω i j) =
      fun s => (Iic (exitR hU z n ω)).indicator (fun _ => (1 : ℝ)) s * covMatrix a b c i j := by
    funext s
    simp only [itoQ, Matrix.smul_apply, smul_eq_mul, beforeExit_toNNReal]
  rw [this, intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg]
  refine Integrable.mul_const ?_ _
  exact (integrableOn_const (C := (1 : ℝ)) measure_Ioc_lt_top.ne).indicator measurableSet_Iic

/-- `∫₀ᵗ Qⁱʲ = Σⁱʲ (t ∧ τ_n)`. -/
theorem pathIntegral_itoQ (ω : Ω) (i j : Fin 2) (t : ℝ≥0) :
    pathIntegral (fun s ω => itoQ hU z n (a := a) (b := b) (c := c) s ω i j) t ω =
      covMatrix a b c i j * min (t : ℝ) (exitR hU z n ω) := by
  simp only [pathIntegral, itoQ, Matrix.smul_apply, smul_eq_mul, beforeExit_toNNReal]
  rw [intervalIntegral.integral_mul_const,
    integral_indicator_Iic_eq (exitR_nonneg hU z n ω) t.coe_nonneg]
  simp [mul_comm]

/-- On `{T_z > 0}`: `∫₀ᵗ Aⁱ = (Re, Im)ⁱ ∫₀^{t ∧ τ_n} 2 / f_s ds`. -/
theorem pathIntegral_itoDrift {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) (i : Fin 2)
    (t : ℝ≥0) :
    pathIntegral (fun s ω => itoDrift hU z n s ω i) t ω =
      reIm (∫ s in (0 : ℝ)..(min (t : ℝ) (exitR hU z n ω)),
        2 / fPath (fun r => U r ω) (hU.cont ω) z s) i := by
  simp only [pathIntegral]
  have h1 : ∫ s in (0 : ℝ)..(t : ℝ), itoDrift hU z n s.toNNReal ω i =
      ∫ s in (0 : ℝ)..(t : ℝ), (Iic (exitR hU z n ω)).indicator
        (fun s => reIm (2 / fPath (fun r => U r ω) (hU.cont ω) z s) i) s := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le t.coe_nonneg] at hs
    rw [itoDrift_toNNReal_eq hU z n hz hs.1]
    by_cases h : s ≤ exitR hU z n ω
    · simp only [indicator_of_mem (mem_Iic.2 h)]
    · simp only [indicator_of_notMem (notMem_Iic.2 (not_le.1 h)), Pi.zero_apply]
  rw [h1, integral_indicator_Iic_eq (exitR_nonneg hU z n ω) t.coe_nonneg]
  have hint := intervalIntegrable_two_div_fPath (hU.cont ω)
    (min_exitTime_mem_lifeSet (hU.cont ω) hz n t.coe_nonneg)
  have h2 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).comp reImL
    |>.intervalIntegral_comp_comm hint
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, reImL_apply] at h2
  exact h2

/-- **The pathwise identity** `Xⁱ_t - Xⁱ_0 - ∫₀ᵗ Aⁱ = -(Uⁱ_{t ∧ τ_n} - Uⁱ_0)`. -/
theorem itoState_sub_eq (t : ℝ≥0) (ω : Ω) (i : Fin 2) :
    itoState hU z n t ω i - itoState hU z n 0 ω i -
        pathIntegral (fun s ω => itoDrift hU z n s ω i) t ω =
      -(reIm (U (min t (exitNN hU z n ω)) ω) i - reIm (U 0 ω) i) := by
  by_cases hz : 0 < absorbingTime (fun s => U s ω) z
  · have hr : (min (t : ℝ) (exitR hU z n ω)).toNNReal = min t (exitNN hU z n ω) := by
      refine NNReal.coe_injective ?_
      rw [Real.coe_toNNReal _ (le_min t.coe_nonneg (exitR_nonneg hU z n ω)), NNReal.coe_min,
        coe_exitNN]
    have hkey := fPath_sub_fPath_zero (hU.cont ω)
      (min_exitTime_mem_lifeSet (hU.cont ω) hz n t.coe_nonneg) (z := z)
    rw [show exitTime (fun r => U r ω) (hU.cont ω) z n = exitR hU z n ω from rfl, hr] at hkey
    rw [pathIntegral_itoDrift hU z n hz, itoState, itoState, stoppedF_eq hU z n hz,
      stoppedF_eq hU z n hz, NNReal.coe_zero, min_eq_left (exitR_nonneg hU z n ω)]
    have := congrArg (fun w => reIm w i) hkey
    simp only [reIm_sub, Pi.sub_apply] at this
    linarith
  · rw [pathIntegral, itoState, itoState, stoppedF_eq_zero hU z n hz, stoppedF_eq_zero hU z n hz]
    simp only [itoDrift_eq_zero hU z n hz, Pi.zero_apply, intervalIntegral.integral_zero,
      sub_self, reIm_zero]
    have : exitNN hU z n ω = 0 := by
      rw [exitNN, exitR_eq_zero hU z n hz, Real.toNNReal_zero]
    rw [this]
    simp

/-! ### The martingale hypotheses of Itô's formula -/

section Martingales

include hU

theorem stronglyMeasurable_reIm_U (t : ℝ≥0) (i : Fin 2) :
    StronglyMeasurable[ℱ t] fun ω => reIm (U t ω) i := by
  fin_cases i
  · exact hU.stronglyMeasurable_re t
  · exact hU.stronglyMeasurable_im t

theorem memLp_reIm_U (t : ℝ≥0) (i : Fin 2) : MemLp (fun ω => reIm (U t ω) i) 2 P := by
  fin_cases i
  · exact hU.memLp_re t
  · exact hU.memLp_im t

theorem continuous_centeredU (i : Fin 2) (ω : Ω) :
    Continuous fun t => reIm (U t ω) i - reIm (U 0 ω) i :=
  ((continuous_apply i).comp (continuous_reIm.comp (hU.cont ω))).sub continuous_const

theorem continuous_bracket_centeredU (i j : Fin 2) (ω : Ω) :
    Continuous fun t : ℝ≥0 =>
      (reIm (U t ω) i - reIm (U 0 ω) i) * (reIm (U t ω) j - reIm (U 0 ω) j) -
      covMatrix a b c i j * (t : ℝ) :=
  ((continuous_centeredU hU i ω).mul (continuous_centeredU hU j ω)).sub
    (continuous_const.mul NNReal.continuous_coe)

variable [IsProbabilityMeasure P]


/-- The centered component `Uⁱ_t - Uⁱ_0` is an `ℱ`-martingale. -/
theorem martingale_centeredU (i : Fin 2) :
    Martingale (fun t ω => reIm (U t ω) i - reIm (U 0 ω) i) ℱ P := by
  have h1 : Martingale (fun t ω => reIm (U t ω) i) ℱ P := by
    fin_cases i
    · exact hU.martingale_re
    · exact hU.martingale_im
  have h2 := Infrastructure.martingale_const_of_stronglyMeasurable
    (stronglyMeasurable_reIm_U hU 0 i) ((memLp_reIm_U hU 0 i).integrable one_le_two)
  exact h1.sub h2

theorem isContLocalMartingale_centeredU (i : Fin 2) :
    IsContLocalMartingale ℱ (fun t ω => reIm (U t ω) i - reIm (U 0 ω) i) P :=
  (martingale_centeredU hU i).isContLocalMartingale (continuous_centeredU hU i)

/-- The bracket martingales of `DriverBridge.lean` in `reIm` form:
`Uⁱ_t Uʲ_t - Σⁱʲ t` is an `ℱ`-martingale. -/
theorem martingale_reIm_mul (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (i j : Fin 2) :
    Martingale (fun t ω => reIm (U t ω) i * reIm (U t ω) j - covMatrix a b c i j * (t : ℝ))
      ℱ P := by
  fin_cases i <;> fin_cases j
  · have h := hU.martingale_re_sq ha hc
    simp only [sq] at h
    simpa [reIm, covMatrix] using h
  · simpa [reIm, covMatrix] using hU.martingale_re_mul_im ha hc
  · have h := hU.martingale_re_mul_im ha hc
    simp only [mul_comm ((U _ _).re)] at h
    simpa [reIm, covMatrix] using h
  · have h := hU.martingale_im_sq ha hc
    simp only [sq] at h
    simpa [reIm, covMatrix] using h

/-- `(Uⁱ_t - Uⁱ_0)(Uʲ_t - Uʲ_0) - Σⁱʲ t` is an `ℱ`-martingale (a.e. equal to the previous one
since `U_0 = 0` a.s.). -/
theorem martingale_bracket_centeredU (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (i j : Fin 2) :
    Martingale (fun t ω => (reIm (U t ω) i - reIm (U 0 ω) i) * (reIm (U t ω) j - reIm (U 0 ω) j) -
      covMatrix a b c i j * (t : ℝ)) ℱ P := by
  refine Infrastructure.martingale_of_ae_eq_of_le_sup_null (fun t => le_sup_left)
    (martingale_reIm_mul hU ha hc i j) (fun t => ?_) fun t => ?_
  · exact (((stronglyMeasurable_reIm_U hU t i).sub
      ((stronglyMeasurable_reIm_U hU 0 i).mono (ℱ.mono bot_le))).mul
      ((stronglyMeasurable_reIm_U hU t j).sub
        ((stronglyMeasurable_reIm_U hU 0 j).mono (ℱ.mono bot_le)))).sub stronglyMeasurable_const
  · filter_upwards [hU.toIsSLEDriver.zero] with ω hω
    simp [hω, reIm_zero]

/-- **Hypothesis `hM` of Itô's formula** for the state `(Re f, Im f)` stopped at `τ_n`. -/
theorem isContLocalMartingale_itoState_sub (i : Fin 2) :
    IsContLocalMartingale ℱ (fun t ω => itoState hU z n t ω i - itoState hU z n 0 ω i -
      pathIntegral (fun s ω => itoDrift hU z n s ω i) t ω) P := by
  have h := ((isContLocalMartingale_centeredU hU i).stopped_min_of_continuous ℱ
    (continuous_centeredU hU i) (isStoppingTime_exitNN hU z n)).neg
  have heq : (fun t ω => itoState hU z n t ω i - itoState hU z n 0 ω i -
      pathIntegral (fun s ω => itoDrift hU z n s ω i) t ω) =
      -(fun t ω => reIm (U (min t (exitNN hU z n ω)) ω) i - reIm (U 0 ω) i) := by
    funext t ω
    exact itoState_sub_eq hU z n t ω i
  rw [heq]; exact h

/-- **Hypothesis `hMM` of Itô's formula** for the state `(Re f, Im f)` stopped at `τ_n`. -/
theorem isContLocalMartingale_itoState_mul_sub (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (i j : Fin 2) :
    IsContLocalMartingale ℱ (fun t ω =>
      (itoState hU z n t ω i - itoState hU z n 0 ω i -
          pathIntegral (fun s ω => itoDrift hU z n s ω i) t ω) *
        (itoState hU z n t ω j - itoState hU z n 0 ω j -
          pathIntegral (fun s ω => itoDrift hU z n s ω j) t ω) -
        pathIntegral (fun s ω => itoQ hU z n (a := a) (b := b) (c := c) s ω i j) t ω) P := by
  have h := ((martingale_bracket_centeredU hU ha hc i j).isContLocalMartingale
    (continuous_bracket_centeredU hU i j)).stopped_min_of_continuous ℱ
    (continuous_bracket_centeredU hU i j) (isStoppingTime_exitNN hU z n)
  have heq : (fun t ω =>
      (itoState hU z n t ω i - itoState hU z n 0 ω i -
          pathIntegral (fun s ω => itoDrift hU z n s ω i) t ω) *
        (itoState hU z n t ω j - itoState hU z n 0 ω j -
          pathIntegral (fun s ω => itoDrift hU z n s ω j) t ω) -
        pathIntegral (fun s ω => itoQ hU z n (a := a) (b := b) (c := c) s ω i j) t ω) =
      fun t ω => (reIm (U (min t (exitNN hU z n ω)) ω) i - reIm (U 0 ω) i) *
        (reIm (U (min t (exitNN hU z n ω)) ω) j - reIm (U 0 ω) j) -
        covMatrix a b c i j * ((min t (exitNN hU z n ω) : ℝ≥0) : ℝ) := by
    funext t ω
    rw [itoState_sub_eq, itoState_sub_eq, pathIntegral_itoQ, NNReal.coe_min, coe_exitNN]
    ring
  rw [heq]; exact h

end Martingales


end State

end ComplexSLE.Internal.Polar

end
