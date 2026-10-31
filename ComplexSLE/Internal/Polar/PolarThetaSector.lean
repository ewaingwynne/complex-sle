/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.PolarItoLog
public import ComplexSLE.Internal.Polar.PolarThetaMultiplier
public import ComplexSLE.Frozen.Defs.Mu

/-!
# The stopped argument `θ_{t ∧ τ_n}`, its drift, and the sector times (M6/S11)

For an adapted `SLE_Σ` driver and `z : ℂ` we set up the processes of the θ-half of
`step:polar-real-imag` (paper.tex:L904-922; `eqn-theta-t-op`, L916-L920):

* `argStopped`: `θ̃_t = θ_{t ∧ τ_n}(z)` (and `0` on `{T_z = 0}`), an everywhere continuous,
  progressively measurable process (the unstopped `1_{t < T_z} θ_t` is adapted by
  `measurable_argPath` and right-continuous);
* `thetaDrift`: the drift density `1_{t ≤ τ_n} µ̂(f_t)` with
  `µ̂(x + iy) = ((a - b - 4) x y + c (y² - x²)) / (x² + y²)²  ( = µ(θ)/|f|² in polar form )`;
* `thetaMart`: `Θ^n_t = θ_{t ∧ τ_n} - θ_0 - ∫₀ᵗ 1_{s ≤ τ_n} µ(θ_s) |f_s|⁻² ds`, the process shown to
  be a continuous local martingale in `PolarThetaMart.lean`;
* `sectorTime`: `S_0 = 0`, `S_{k+1} = inf {t ≥ S_k | |θ̃_t - θ̃_{S_k}| ≥ π/2 or t ≥ τ_n}`, the
  sector times. They are `ℱ`-stopping times (`isStoppingTime_sectorTime`; the hitting condition
  is tested on a countable dense set of times by continuity), `S_k ≤ S_{k+1} ≤ τ_n`,
  `|θ̃_t - θ̃_{S_k}| ≤ π/2` on `[S_k, S_{k+1}]`, and `S_k = τ_n` for all large `k`
  (uniform continuity of `θ̃` on `[0, τ_n]`).
-/

public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal.Polar

/-! ### The drift density of `θ` as a function of `f ∈ ℂ ≅ ℝ²` -/

/-- `µ̂(v) = ((a - b - 4) x y + c (y² - x²)) / (x² + y²)²`, the drift of `θ` per unit time. -/
@[expose] noncomputable def muFn (a b c : ℝ) (v : Fin 2 → ℝ) : ℝ :=
  ((a - b - 4) * v 0 * v 1 + c * (v 1 ^ 2 - v 0 ^ 2)) / (v 0 ^ 2 + v 1 ^ 2) ^ 2

theorem measurable_muFn (a b c : ℝ) : Measurable (muFn a b c) := by
  unfold muFn; fun_prop

theorem continuousOn_muFn (a b c : ℝ) : ContinuousOn (muFn a b c) posSet₂ := by
  unfold muFn
  exact ContinuousOn.div (by fun_prop) (by fun_prop) fun v hv => by
    have : (0 : ℝ) < v 0 ^ 2 + v 1 ^ 2 := hv
    positivity

/-- In polar coordinates `v = r (cos θ, sin θ)`, `µ̂ = µ(θ) / r²`. -/
theorem muFn_polar (a b c : ℝ) {r θ : ℝ} (hr : 0 < r) :
    muFn a b c ![r * Real.cos θ, r * Real.sin θ] = mu a b c θ / r ^ 2 := by
  simp only [muFn, mu, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Real.cos_two_mul, Real.sin_two_mul, mul_pow, Real.sin_sq]
  have hr2 : r ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-! ### The processes -/

section Processes

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

variable (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) (n : ℕ)

open Classical in
/-- `θ_t(z)` on `{t < T_z}`, and `0` elsewhere. -/
@[expose] noncomputable def argOrZero (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : ℝ) ∈ lifeSet (fun s => U s ω) z then argPath (fun s => U s ω) (hU.cont ω) z t else 0

theorem argOrZero_eq {t : ℝ≥0} {ω : Ω} (h : (t : ℝ) ∈ lifeSet (fun s => U s ω) z) :
    argOrZero hU z t ω = argPath (fun s => U s ω) (hU.cont ω) z t := by
  simp [argOrZero, h]

theorem measurable_argOrZero (t : ℝ≥0) : Measurable[ℱ t] (argOrZero hU z t) :=
  measurable_argPath_of_isSLEDriverAdapted hU t z

/-- `1_{t < T_z} θ_t` is right-continuous at every `r : ℝ≥0`. -/
theorem continuousWithinAt_argOrZero (ω : Ω) (r : ℝ≥0) :
    ContinuousWithinAt (fun t => argOrZero hU z t ω) (Ici r) r := by
  by_cases hr : (r : ℝ) ∈ lifeSet (fun s => U s ω) z
  · have hcont : ContinuousAt (fun t : ℝ≥0 => argPath (fun s => U s ω) (hU.cont ω) z t) r := by
      have h1 : ContinuousWithinAt (argPath (fun s => U s ω) (hU.cont ω) z) (Ici 0) (r : ℝ) :=
        ((continuousOn_argPath (hU.cont ω) z) r hr).mono_of_mem_nhdsWithin
          (lifeSet_mem_nhdsWithin hr)
      have h2 : ContinuousWithinAt (fun t : ℝ≥0 => (t : ℝ)) univ r :=
        NNReal.continuous_coe.continuousWithinAt
      have := h1.comp h2 (fun t _ => NNReal.coe_nonneg t)
      rwa [continuousWithinAt_univ] at this
    refine (hcont.congr_of_eventuallyEq ?_).continuousWithinAt
    filter_upwards [coe_mem_lifeSet_mem_nhds hr] with t ht
    exact argOrZero_eq hU z ht
  · refine (continuousWithinAt_const (b := (0 : ℝ))).congr (fun t ht => ?_) ?_
    · have : (t : ℝ) ∉ lifeSet (fun s => U s ω) z := fun h =>
        hr (mem_lifeSet_of_le h (NNReal.coe_nonneg r) (NNReal.coe_le_coe.2 ht))
      simp [argOrZero, this]
    · simp [argOrZero, hr]

theorem isStronglyProgressive_argOrZero : IsStronglyProgressive ℱ (argOrZero hU z) :=
  StronglyAdapted.isStronglyProgressive_of_rightContinuous
    (fun t => (measurable_argOrZero hU z t).stronglyMeasurable)
    fun ω r => continuousWithinAt_argOrZero hU z ω r

/-- **The stopped argument** `θ̃_t = θ_{t ∧ τ_n}(z)` (and `0` on `{T_z = 0}`). -/
@[expose] noncomputable def argStopped (t : ℝ≥0) (ω : Ω) : ℝ :=
  argOrZero hU z (min t (exitNN hU z n ω)) ω

theorem argStopped_eq_stoppedProcess :
    argStopped hU z n =
      stoppedProcess (argOrZero hU z) fun ω => (exitNN hU z n ω : WithTop ℝ≥0) := by
  funext t ω
  rw [argStopped, stoppedProcess_coe_min]

/-- On `{T_z > 0}` the stopped argument is `θ_{t ∧ τ_n}`. -/
theorem argStopped_eq {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) (t : ℝ≥0) :
    argStopped hU z n t ω =
      argPath (fun s => U s ω) (hU.cont ω) z (min (t : ℝ) (exitR hU z n ω)) := by
  have hmem : ((min t (exitNN hU z n ω) : ℝ≥0) : ℝ) ∈ lifeSet (fun s => U s ω) z := by
    rw [NNReal.coe_min, coe_exitNN]
    exact min_exitTime_mem_lifeSet (hU.cont ω) hz n t.coe_nonneg
  rw [argStopped, argOrZero_eq hU z hmem, NNReal.coe_min, coe_exitNN]

theorem argStopped_eq_zero {ω : Ω} (hz : ¬ 0 < absorbingTime (fun s => U s ω) z) (t : ℝ≥0) :
    argStopped hU z n t ω = 0 := by
  simp [argStopped, argOrZero, lifeSet_eq_empty_of_not_pos hz]

theorem isStronglyProgressive_argStopped : IsStronglyProgressive ℱ (argStopped hU z n) := by
  rw [argStopped_eq_stoppedProcess]
  exact (isStronglyProgressive_argOrZero hU z).stoppedProcess (isStoppingTime_exitNN hU z n)

/-- Every path of the stopped argument is continuous. -/
theorem continuous_argStopped (ω : Ω) : Continuous fun t => argStopped hU z n t ω := by
  by_cases hz : 0 < absorbingTime (fun s => U s ω) z
  · simp only [argStopped_eq hU z n hz]
    refine (continuousOn_argPath (hU.cont ω) z).comp_continuous
      (NNReal.continuous_coe.min continuous_const) fun t => ?_
    exact min_exitTime_mem_lifeSet (hU.cont ω) hz n t.coe_nonneg
  · simp only [argStopped_eq_zero hU z n hz]
    exact continuous_const

theorem argStopped_eq_of_le {ω : Ω} {s t : ℝ≥0} (hst : s ≤ t) (hs : exitNN hU z n ω ≤ s) :
    argStopped hU z n t ω = argStopped hU z n s ω := by
  simp only [argStopped, min_eq_right hs, min_eq_right (le_trans hs hst)]

/-- The stopped argument is `ℱ_{S}`-measurable at a bounded stopping time `S ≤ u`
(as a function of `ω`, viewed in `ℱ u`). -/
theorem measurable_argStopped_min {S : Ω → ℝ≥0}
    (hS : IsStoppingTime ℱ fun ω => (S ω : WithTop ℝ≥0)) (u : ℝ≥0) :
    Measurable[ℱ u] fun ω => argStopped hU z n (min (S ω) u) ω := by
  have hst : IsStoppingTime ℱ fun ω => ((min (S ω) u : ℝ≥0) : WithTop ℝ≥0) := by
    have := hS.min_const u
    simpa only [WithTop.coe_min] using this
  have := stronglyMeasurable_stoppedValue_of_le (isStronglyProgressive_argStopped hU z n) hst
    (fun ω => WithTop.coe_le_coe.2 (min_le_right _ _))
  rw [Infrastructure.stoppedValue_coe] at this
  exact this.measurable

/-! ### The drift and the martingale part of `θ` -/

/-- The drift density `1_{t ≤ τ_n} µ̂(f_t)` (`= 1_{t ≤ τ_n} µ(θ_t)/|f_t|²`). -/
@[expose] noncomputable def thetaDrift (t : ℝ≥0) (ω : Ω) : ℝ :=
  beforeExit hU z n t ω * muFn a b c (itoState hU z n t ω)

/-- **The martingale part of `θ` stopped at `τ_n`:**
`Θ^n_t = θ_{t ∧ τ_n} - θ_0 - ∫₀ᵗ 1_{s ≤ τ_n} µ(θ_s)|f_s|⁻² ds`. -/
@[expose] noncomputable def thetaMart (t : ℝ≥0) (ω : Ω) : ℝ :=
  argStopped hU z n t ω - argStopped hU z n 0 ω - pathIntegral (thetaDrift hU z n) t ω

/-- The drift density in the form of the source (`eqn-theta-t-op`): on `{T_z > 0}` and for
`t ≤ τ_n`, `thetaDrift t = µ(θ_t) / |f_t|²`. -/
theorem thetaDrift_eq_mu {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) {t : ℝ≥0}
    (ht : (t : ℝ) ≤ exitR hU z n ω) :
    thetaDrift hU z n t ω = mu a b c (argPath (fun s => U s ω) (hU.cont ω) z t) /
      ‖fPath (fun s => U s ω) (hU.cont ω) z t‖ ^ 2 := by
  have h1 : beforeExit hU z n t ω = 1 := by
    simp [beforeExit, (le_exitNN_iff hU z n).2 ht]
  rw [thetaDrift, h1, one_mul, itoState_eq_polar hU z n hz, min_eq_left ht,
    muFn_polar _ _ _ (norm_pos_iff.2 (stoppedF_ne_zero hU z n hz t)),
    stoppedF_eq_of_le hU z n hz ht]

theorem thetaDrift_eq_zero_of_lt {ω : Ω} {t : ℝ≥0} (ht : exitR hU z n ω < t) :
    thetaDrift hU z n t ω = 0 := by
  have : beforeExit hU z n t ω = 0 := by
    simp [beforeExit, (le_exitNN_iff hU z n).not.2 (not_le.2 ht)]
  simp [thetaDrift, this]

theorem isStronglyProgressive_thetaDrift : IsStronglyProgressive ℱ (thetaDrift hU z n) :=
  fun i => (isStronglyProgressive_beforeExit hU z n i).mul
    (((measurable_muFn a b c).comp (isStronglyProgressive_itoState hU z n i).measurable)
      |>.stronglyMeasurable)

theorem intervalIntegrable_thetaDrift (ω : Ω) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => thetaDrift hU z n s.toNNReal ω) volume 0 t :=
  intervalIntegrable_beforeExit_mul hU z n (continuousOn_muFn a b c) ω t

/-- `∫₀ᵗ 1_{s ≤ τ_n} µ̂(f_s) ds = ∫₀^{t ∧ τ_n} µ̂(f_s) ds`. -/
theorem pathIntegral_thetaDrift (ω : Ω) (t : ℝ≥0) :
    pathIntegral (thetaDrift hU z n) t ω =
      pathIntegral (fun s ω => muFn a b c (itoState hU z n s ω)) (min t (exitNN hU z n ω)) ω :=
  pathIntegral_beforeExit_mul hU z n ω t

/-- Every path of `Θ^n` is continuous. -/
theorem continuous_thetaMart (ω : Ω) : Continuous fun t => thetaMart hU z n t ω :=
  ((continuous_argStopped hU z n ω).sub continuous_const).sub
    (continuous_pathIntegral_beforeExit hU z n (continuousOn_muFn a b c) ω)

theorem isStronglyProgressive_thetaMart : IsStronglyProgressive ℱ (thetaMart hU z n) := by
  intro i
  have h0 : IsStronglyProgressive ℱ fun _ ω => argStopped hU z n 0 ω :=
    StronglyAdapted.isStronglyProgressive_of_continuous
      (fun t => ((isStronglyProgressive_argStopped hU z n).stronglyAdapted 0).mono
        (ℱ.mono bot_le)) fun _ => continuous_const
  have h2 := isStronglyProgressive_pathIntegral_beforeExit hU z n (measurable_muFn a b c)
    (continuousOn_muFn a b c)
  exact ((isStronglyProgressive_argStopped hU z n i).sub (h0 i)).sub (h2 i)

theorem thetaMart_zero (ω : Ω) : thetaMart hU z n 0 ω = 0 := by
  simp [thetaMart, pathIntegral_zero_time]

/-- `Θ^n` is constant after `τ_n`. -/
theorem thetaMart_eq_of_le {ω : Ω} {s t : ℝ≥0} (hst : s ≤ t) (hs : exitNN hU z n ω ≤ s) :
    thetaMart hU z n t ω = thetaMart hU z n s ω := by
  simp only [thetaMart, argStopped_eq_of_le hU z n hst hs]
  congr 1
  rw [pathIntegral_thetaDrift, pathIntegral_thetaDrift, min_eq_right hs,
    min_eq_right (le_trans hs hst)]

/-! ### Sector times -/

/-- The sector set from `S`: the times `t ≥ S` at which `|θ̃_t - θ̃_S| ≥ π/2` or `t ≥ τ_n`. -/
@[expose] def sectorSet (S : ℝ≥0) (ω : Ω) : Set ℝ≥0 :=
  {t | S ≤ t ∧ (π / 2 ≤ |argStopped hU z n t ω - argStopped hU z n S ω| ∨ exitNN hU z n ω ≤ t)}

/-- **The sector times** `S_0 = 0`, `S_{k+1} = inf (sectorSet S_k)`: the first time after `S_k` at
which the argument has moved by `π/2`, capped at `τ_n`. -/
@[expose] noncomputable def sectorTime : ℕ → Ω → ℝ≥0
  | 0 => fun _ => 0
  | k + 1 => fun ω => sInf (sectorSet hU z n (sectorTime k ω) ω)

theorem isClosed_sectorSet (S : ℝ≥0) (ω : Ω) : IsClosed (sectorSet hU z n S ω) := by
  have hc : Continuous fun t => |argStopped hU z n t ω - argStopped hU z n S ω| :=
    continuous_abs.comp ((continuous_argStopped hU z n ω).sub continuous_const)
  have : sectorSet hU z n S ω = Ici S ∩
      ({t | π / 2 ≤ |argStopped hU z n t ω - argStopped hU z n S ω|} ∪ Ici (exitNN hU z n ω)) := by
    ext t; simp [sectorSet]
  rw [this]
  exact isClosed_Ici.inter ((isClosed_le continuous_const hc).union isClosed_Ici)

theorem exitNN_mem_sectorSet {S : ℝ≥0} {ω : Ω} (hS : S ≤ exitNN hU z n ω) :
    exitNN hU z n ω ∈ sectorSet hU z n S ω :=
  ⟨hS, Or.inr le_rfl⟩

theorem sInf_sectorSet_mem {S : ℝ≥0} {ω : Ω} (hS : S ≤ exitNN hU z n ω) :
    sInf (sectorSet hU z n S ω) ∈ sectorSet hU z n S ω :=
  (isClosed_sectorSet hU z n S ω).csInf_mem ⟨_, exitNN_mem_sectorSet hU z n hS⟩
    (OrderBot.bddBelow _)

theorem le_sInf_sectorSet {S : ℝ≥0} {ω : Ω} (hS : S ≤ exitNN hU z n ω) :
    S ≤ sInf (sectorSet hU z n S ω) :=
  (sInf_sectorSet_mem hU z n hS).1

theorem sInf_sectorSet_le_exitNN {S : ℝ≥0} {ω : Ω} (hS : S ≤ exitNN hU z n ω) :
    sInf (sectorSet hU z n S ω) ≤ exitNN hU z n ω :=
  csInf_le (OrderBot.bddBelow _) (exitNN_mem_sectorSet hU z n hS)

/-- Strictly before the next sector time the argument has moved by less than `π/2`, and we are
before `τ_n`. -/
theorem lt_of_lt_sInf_sectorSet {S t : ℝ≥0} {ω : Ω} (hSt : S ≤ t)
    (ht : t < sInf (sectorSet hU z n S ω)) :
    |argStopped hU z n t ω - argStopped hU z n S ω| < π / 2 ∧ t < exitNN hU z n ω := by
  by_contra h
  simp only [not_and_or, not_lt] at h
  have hmem : t ∈ sectorSet hU z n S ω := ⟨hSt, h⟩
  exact absurd (csInf_le (OrderBot.bddBelow _) hmem) (not_le.2 ht)

/-- Up to and including the next sector time, the argument has moved by at most `π/2`. -/
theorem abs_sub_le_of_le_sInf_sectorSet {S t : ℝ≥0} {ω : Ω} (hSt : S ≤ t)
    (ht : t ≤ sInf (sectorSet hU z n S ω)) :
    |argStopped hU z n t ω - argStopped hU z n S ω| ≤ π / 2 := by
  rcases lt_or_eq_of_le ht with hlt | heq
  · exact (lt_of_lt_sInf_sectorSet hU z n hSt hlt).1.le
  · subst heq
    rcases lt_or_eq_of_le hSt with hSlt | hSeq
    · by_contra hgt
      rw [not_le] at hgt
      have hcont : ContinuousAt (fun t => |argStopped hU z n t ω - argStopped hU z n S ω|)
          (sInf (sectorSet hU z n S ω)) :=
        (continuous_abs.comp ((continuous_argStopped hU z n ω).sub continuous_const)).continuousAt
      have hev : ∀ᶠ s in 𝓝 (sInf (sectorSet hU z n S ω)),
          π / 2 < |argStopped hU z n s ω - argStopped hU z n S ω| :=
        hcont.eventually (lt_mem_nhds hgt)
      obtain ⟨l, hl, hsub⟩ := exists_Ioc_subset_of_mem_nhds' hev hSlt
      obtain ⟨s, hls, hsN⟩ := exists_between hl.2
      have hs : π / 2 < |argStopped hU z n s ω - argStopped hU z n S ω| :=
        hsub ⟨hls, le_of_lt hsN⟩
      have := (lt_of_lt_sInf_sectorSet hU z n (le_trans hl.1 (le_of_lt hls)) hsN).1
      exact absurd hs (not_lt.2 this.le)
    · rw [← hSeq, sub_self, abs_zero]; positivity

theorem sectorTime_zero (ω : Ω) : sectorTime hU z n 0 ω = 0 := rfl

theorem sectorTime_succ (k : ℕ) (ω : Ω) :
    sectorTime hU z n (k + 1) ω = sInf (sectorSet hU z n (sectorTime hU z n k ω) ω) := rfl

theorem sectorTime_le_exitNN (k : ℕ) (ω : Ω) : sectorTime hU z n k ω ≤ exitNN hU z n ω := by
  induction k with
  | zero => exact zero_le
  | succ k ih => exact sInf_sectorSet_le_exitNN hU z n ih

theorem sectorTime_le_succ (k : ℕ) (ω : Ω) : sectorTime hU z n k ω ≤ sectorTime hU z n (k + 1) ω :=
  le_sInf_sectorSet hU z n (sectorTime_le_exitNN hU z n k ω)

theorem sectorTime_mono (ω : Ω) : Monotone fun k => sectorTime hU z n k ω :=
  monotone_nat_of_le_succ fun k => sectorTime_le_succ hU z n k ω

/-- On `[S_k, S_{k+1}]` the argument stays within `π/2` of `θ̃_{S_k}`. -/
theorem abs_argStopped_sub_le {k : ℕ} {ω : Ω} {t : ℝ≥0} (h1 : sectorTime hU z n k ω ≤ t)
    (h2 : t ≤ sectorTime hU z n (k + 1) ω) :
    |argStopped hU z n t ω - argStopped hU z n (sectorTime hU z n k ω) ω| ≤ π / 2 :=
  abs_sub_le_of_le_sInf_sectorSet hU z n h1 h2

/-- If `S_{k+1} < τ_n`, the argument has moved by exactly (at least) `π/2`. -/
theorem pi_div_two_le_of_sectorTime_lt {k : ℕ} {ω : Ω}
    (h : sectorTime hU z n (k + 1) ω < exitNN hU z n ω) :
    π / 2 ≤ |argStopped hU z n (sectorTime hU z n (k + 1) ω) ω -
      argStopped hU z n (sectorTime hU z n k ω) ω| := by
  have hmem := sInf_sectorSet_mem hU z n (sectorTime_le_exitNN hU z n k ω)
  rcases hmem.2 with h' | h'
  · exact h'
  · exact absurd h (not_lt.2 h')

/-- **The next sector time is a stopping time** when the current one is. -/
theorem isStoppingTime_sInf_sectorSet {S : Ω → ℝ≥0}
    (hS : IsStoppingTime ℱ fun ω => (S ω : WithTop ℝ≥0)) (hSle : ∀ ω, S ω ≤ exitNN hU z n ω) :
    IsStoppingTime ℱ fun ω => ((sInf (sectorSet hU z n (S ω) ω) : ℝ≥0) : WithTop ℝ≥0) := by
  refine Infrastructure.isStoppingTime_of_nnreal_le fun u => ?_
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  -- the measurable building blocks: `θ̃` at the bounded stopping times `(q ∨ S) ∧ u` and `S ∧ u`
  have hG : ∀ q : ℝ≥0, Measurable[ℱ u] fun ω => argStopped hU z n (min (max q (S ω)) u) ω := by
    intro q
    have hst : IsStoppingTime ℱ fun ω => (max q (S ω) : WithTop ℝ≥0) := by
      have := hS.max_const q
      simpa only [WithTop.coe_max, max_comm] using this
    exact measurable_argStopped_min hU z n hst u
  have hGS := measurable_argStopped_min hU z n hS u
  have key : {ω | sInf (sectorSet hU z n (S ω) ω) ≤ u} = {ω | S ω ≤ u} ∩
      ({ω | exitNN hU z n ω ≤ u} ∪ ⋂ m : ℕ, ⋃ q ∈ D, ({ω | q ≤ u} ∩
        {ω | π / 2 - 1 / ((m : ℝ) + 1) < |argStopped hU z n (min (max q (S ω)) u) ω -
          argStopped hU z n (min (S ω) u) ω|})) := by
    ext ω
    simp only [mem_inter_iff, mem_union, mem_iInter, mem_iUnion, mem_ofPred_eq, exists_prop]
    constructor
    · intro hle
      have hSu : S ω ≤ u := le_trans (le_sInf_sectorSet hU z n (hSle ω)) hle
      refine ⟨hSu, ?_⟩
      by_cases hτ : exitNN hU z n ω ≤ u
      · exact Or.inl hτ
      · right
        intro m
        have hτ' : u < exitNN hU z n ω := lt_of_not_ge hτ
        have hNτ : sInf (sectorSet hU z n (S ω) ω) < exitNN hU z n ω := lt_of_le_of_lt hle hτ'
        have hmem := sInf_sectorSet_mem hU z n (hSle ω)
        have hπ : π / 2 ≤ |argStopped hU z n (sInf (sectorSet hU z n (S ω) ω)) ω -
            argStopped hU z n (S ω) ω| := by
          rcases hmem.2 with h | h
          · exact h
          · exact absurd hNτ (not_lt.2 h)
        have hSN : S ω < sInf (sectorSet hU z n (S ω) ω) := by
          rcases lt_or_eq_of_le (le_sInf_sectorSet hU z n (hSle ω)) with h | h
          · exact h
          · exfalso
            rw [← h, sub_self, abs_zero] at hπ
            linarith [Real.pi_pos]
        have hcont : ContinuousAt (fun t => |argStopped hU z n t ω - argStopped hU z n (S ω) ω|)
            (sInf (sectorSet hU z n (S ω) ω)) :=
          (continuous_abs.comp
            ((continuous_argStopped hU z n ω).sub continuous_const)).continuousAt
        have hε : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
        have hev : ∀ᶠ s in 𝓝 (sInf (sectorSet hU z n (S ω) ω)), π / 2 - 1 / ((m : ℝ) + 1) <
            |argStopped hU z n s ω - argStopped hU z n (S ω) ω| :=
          hcont.eventually (lt_mem_nhds (by linarith))
        obtain ⟨l, hl, hsub⟩ := exists_Ioc_subset_of_mem_nhds' hev hSN
        obtain ⟨q, hqD, hlq, hqN⟩ := hDd.exists_between hl.2
        have hSq : S ω ≤ q := le_trans hl.1 (le_of_lt hlq)
        have hqu : q ≤ u := le_trans (le_of_lt hqN) hle
        refine ⟨q, hqD, hqu, ?_⟩
        rw [max_eq_left hSq, min_eq_left hqu, min_eq_left hSu]
        exact hsub ⟨hlq, le_of_lt hqN⟩
    · rintro ⟨hSu, h⟩
      rcases h with hτ | h
      · exact le_trans (sInf_sectorSet_le_exitNN hU z n (hSle ω)) hτ
      · have hφc : Continuous fun t => |argStopped hU z n t ω - argStopped hU z n (S ω) ω| :=
          continuous_abs.comp ((continuous_argStopped hU z n ω).sub continuous_const)
        obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hSu)
          hφc.continuousOn
        have hge : π / 2 ≤ |argStopped hU z n t₀ ω - argStopped hU z n (S ω) ω| := by
          by_contra hlt
          rw [not_le] at hlt
          obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
          obtain ⟨q, -, hqu, hq⟩ := h m
          rw [min_eq_left hSu, min_eq_left (max_le hqu hSu)] at hq
          have h' : |argStopped hU z n (max q (S ω)) ω - argStopped hU z n (S ω) ω| ≤
              |argStopped hU z n t₀ ω - argStopped hU z n (S ω) ω| :=
            hmax (⟨le_max_right _ _, max_le hqu hSu⟩ : max q (S ω) ∈ Icc (S ω) u)
          linarith
        have ht₀mem : t₀ ∈ sectorSet hU z n (S ω) ω := ⟨ht₀.1, Or.inl hge⟩
        exact le_trans (csInf_le (OrderBot.bddBelow _) ht₀mem) ht₀.2
  rw [key]
  refine (Infrastructure.measurableSet_nnreal_le hS u).inter
    ((Infrastructure.measurableSet_nnreal_le (isStoppingTime_exitNN hU z n) u).union ?_)
  refine MeasurableSet.iInter fun m => MeasurableSet.biUnion hDc fun q _ => ?_
  refine (MeasurableSet.const _).inter ?_
  exact measurableSet_lt measurable_const (continuous_abs.measurable.comp ((hG q).sub hGS))

/-- **The sector times are `ℱ`-stopping times.** -/
theorem isStoppingTime_sectorTime (k : ℕ) :
    IsStoppingTime ℱ fun ω => (sectorTime hU z n k ω : WithTop ℝ≥0) := by
  induction k with
  | zero => exact isStoppingTime_const ℱ 0
  | succ k ih => exact isStoppingTime_sInf_sectorSet hU z n ih (sectorTime_le_exitNN hU z n k)

/-- **The sector times exhaust `[0, τ_n]`**: `S_k = τ_n` for all large `k` (uniform continuity of
the stopped argument on `[0, τ_n]`). -/
theorem exists_sectorTime_eq_exitNN (ω : Ω) :
    ∃ K : ℕ, ∀ k, K ≤ k → sectorTime hU z n k ω = exitNN hU z n ω := by
  have hUC := isCompact_Icc.uniformContinuousOn_of_continuous
    (s := Icc (0 : ℝ≥0) (exitNN hU z n ω)) (continuous_argStopped hU z n ω).continuousOn
  obtain ⟨δ, hδ, hδθ⟩ := Metric.uniformContinuousOn_iff.1 hUC (π / 2) (by positivity)
  have claim : ∀ k, sectorTime hU z n k ω = exitNN hU z n ω ∨
      (k : ℝ) * δ ≤ (sectorTime hU z n k ω : ℝ) := by
    intro k
    induction k with
    | zero => right; simp [sectorTime_zero]
    | succ k ih =>
      by_cases hk : sectorTime hU z n (k + 1) ω = exitNN hU z n ω
      · exact Or.inl hk
      · right
        have hlt : sectorTime hU z n (k + 1) ω < exitNN hU z n ω :=
          lt_of_le_of_ne (sectorTime_le_exitNN hU z n _ ω) hk
        have hπ := pi_div_two_le_of_sectorTime_lt hU z n hlt
        have hkτ : sectorTime hU z n k ω ≠ exitNN hU z n ω := fun h =>
          hk (le_antisymm (sectorTime_le_exitNN hU z n _ ω) (h ▸ sectorTime_le_succ hU z n k ω))
        rcases ih with h | h
        · exact absurd h hkτ
        · have hdist : δ ≤ dist (sectorTime hU z n (k + 1) ω) (sectorTime hU z n k ω) := by
            by_contra hcon
            rw [not_le] at hcon
            have := hδθ _ ⟨zero_le, sectorTime_le_exitNN hU z n _ ω⟩ _
              ⟨zero_le, sectorTime_le_exitNN hU z n k ω⟩ hcon
            rw [Real.dist_eq] at this
            linarith
          rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2
            (NNReal.coe_le_coe.2 (sectorTime_le_succ hU z n k ω)))] at hdist
          push_cast
          linarith
  obtain ⟨K, hK⟩ := exists_nat_gt ((exitNN hU z n ω : ℝ) / δ)
  refine ⟨K, fun k hk => ?_⟩
  rcases claim k with h | h
  · exact h
  · exfalso
    have h1 : (K : ℝ) ≤ k := by exact_mod_cast hk
    have h2 : (sectorTime hU z n k ω : ℝ) ≤ exitNN hU z n ω :=
      NNReal.coe_le_coe.2 (sectorTime_le_exitNN hU z n k ω)
    have h3 : (exitNN hU z n ω : ℝ) < K * δ := by rwa [div_lt_iff₀ hδ] at hK
    have h4 : (K : ℝ) * δ ≤ k * δ := mul_le_mul_of_nonneg_right h1 hδ.le
    linarith

end Processes

end ComplexSLE.Internal.Polar

end
