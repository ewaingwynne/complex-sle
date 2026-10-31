/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.PolarItoLog
public import ComplexSLE.Internal.Polar.Sigma
public import ComplexSLE.Infrastructure.Stochastic.StoppedLocalMartingale

/-!
# The σ-time parametrisation as a family of stopping times (M6/S12, `step:polar-time-change`)

For an adapted `SLE_Σ` driver `hU` and `z`, with `τ_n = exitTime` the annulus exit times and
`A(t) = clock` the clock of Definition 2.9, we build the stopping-time families of the time change
by `σ_z = sigmaTime`:

* `sigmaStop hU z n s = σ_z (s ∧ A(τ_n))` (`= σ_z(s) ∧ τ_n`), an `ℝ≥0`-valued `ℱ`-stopping time,
  continuous and nondecreasing in `s` with value `0` at `s = 0`, with no junk: the argument
  `s ∧ A(τ_n)` always lies in the honest domain `sigmaDom` of `σ_z`
  (`{σ^n_s ≤ u} = {τ_n ≤ u} ∪ ({u < T_z} ∩ {s ≤ A(u)})`, `isStoppingTime_sigmaStop`);
* `sigmaStopFiltration hU z n`: `𝒢^n_s = ℱ_{σ^n_s}`;
* `sigmaTop hU z s`: the honest `σ_z(s)` as a `WithTop ℝ≥0`-valued stopping time (value `⊤` off
  `sigmaDom`; a.s. never, by Remark 2.12), and the **σ-time filtration**
  `sigmaFiltration hU z`: `𝒢_s = ℱ_{σ_z(s)}`;
* `clockExit hU z n = A(τ_n)`, the time in the σ-parametrisation at which the stopped family is
  frozen: a `𝒢`-stopping time, with `A ∩ {s < A(τ_n)} ∈ 𝒢^n_s` for `A ∈ 𝒢_s`
  (`measurableSet_inter_lt_clockExit`), the input to the filtration transfer
  `isContLocalMartingale_of_le_of_inter_lt`;
* the change of variables `∫₀^{σ_z(r)} φ(θ_u) |f_u|⁻² du = ∫₀ʳ φ(θ_{σ_z(v)}) dv`
  (`integral_comp_sigmaTime`, `pathIntegral_sigmaStop_eq`).
-/

public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal.Polar

/-! ### Deterministic facts -/

section Deterministic

variable {U : ℝ≥0 → ℂ}

/-- When `T_z = 0`, `σ_z` is identically `0` (as `sInf ∅`). -/
theorem sigmaTime_eq_zero_of_not_pos (hU : Continuous U) {z : ℂ} (hz : ¬ 0 < absorbingTime U z)
    (s : ℝ) : sigmaTime U hU z s = 0 := by
  have : {t | t ∈ lifeSet U z ∧ s ≤ clock U hU z t} = ∅ := by
    ext t; simp [lifeSet_eq_empty_of_not_pos hz]
  rw [sigmaTime, this, Real.sInf_empty]

/-- When `T_z = 0`, `clockSup = 0`. -/
theorem clockSup_eq_zero_of_not_pos (hU : Continuous U) {z : ℂ}
    (hz : ¬ 0 < absorbingTime U z) : clockSup U hU z = 0 := by
  simp [clockSup, lifeSet_eq_empty_of_not_pos hz]

theorem notMem_sigmaDom_of_not_pos (hU : Continuous U) {z : ℂ} (hz : ¬ 0 < absorbingTime U z)
    (s : ℝ) : s ∉ sigmaDom U hU z := by
  rintro ⟨-, h⟩
  rw [clockSup_eq_zero_of_not_pos hU hz] at h
  exact absurd h (not_lt.2 bot_le)

/-- Membership in `sigmaDom` forces `T_z > 0`. -/
theorem pos_absorbingTime_of_mem_sigmaDom (hU : Continuous U) {z : ℂ} {s : ℝ}
    (hs : s ∈ sigmaDom U hU z) : 0 < absorbingTime U z := by
  by_contra h
  exact notMem_sigmaDom_of_not_pos hU h s hs

/-- **Change of variables for the σ-time** (`eqn-defn-sigma`): for `r ∈ sigmaDom` and continuous
`φ`, `∫₀^{σ_z(r)} φ(θ_u) |f_u|⁻² du = ∫₀ʳ φ(θ_{σ_z(v)}) dv`. -/
theorem integral_comp_sigmaTime (hU : Continuous U) {z : ℂ} {φ : ℝ → ℝ} (hφ : Continuous φ)
    {r : ℝ} (hr : r ∈ sigmaDom U hU z) :
    ∫ u in (0 : ℝ)..sigmaTime U hU z r, φ (argPath U hU z u) * clockRate U hU z u =
      ∫ v in (0 : ℝ)..r, φ (argPath U hU z (sigmaTime U hU z v)) := by
  set σr := sigmaTime U hU z r with hσr
  have hσ : σr ∈ lifeSet U z := sigmaTime_mem_lifeSet hU hr
  have hσ0 : 0 ≤ σr := hσ.1
  have hsub : uIcc 0 σr ⊆ lifeSet U z := by
    rw [uIcc_of_le hσ0]; exact Icc_subset_lifeSet hσ
  set g : ℝ → ℝ := fun v => φ (argPath U hU z (sigmaTime U hU z v)) with hg
  have hgc : ContinuousOn g (sigmaDom U hU z) := by
    refine hφ.comp_continuousOn ((continuousOn_argPath hU z).comp (continuousOn_sigmaTime hU z)
      fun v hv => sigmaTime_mem_lifeSet hU hv)
  have key := intervalIntegral.integral_comp_mul_deriv'' (f := clock U hU z)
    (f' := clockRate U hU z) (g := g) (a := 0) (b := σr) ((continuousOn_clock hU z).mono hsub)
    (fun x hx => by
      rw [min_eq_left hσ0, max_eq_right hσ0] at hx
      have hxl : x ∈ lifeSet U z := hsub (by rw [uIcc_of_le hσ0]; exact Ioo_subset_Icc_self hx)
      exact (hasDerivWithinAt_clock hU hxl).mono fun y hy => hx.1.le.trans (le_of_lt hy))
    ((continuousOn_clockRate hU z).mono hsub)
    (hgc.mono (by
      rintro _ ⟨u, hu, rfl⟩
      exact clock_mem_sigmaDom hU (hsub hu)))
  rw [clock_zero, clock_sigmaTime hU hr] at key
  rw [← key]
  refine intervalIntegral.integral_congr fun u hu => ?_
  simp only [Function.comp, hg]
  rw [sigmaTime_clock hU (hsub hu)]

end Deterministic

/-! ### The stopped σ-time `σ_z(s ∧ A(τ_n))` -/

section Processes

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

variable (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ)

/-- `A(τ_n)`, as a real number. -/
@[expose] noncomputable def clockExitR (n : ℕ) (ω : Ω) : ℝ :=
  clock (fun r => U r ω) (hU.cont ω) z (exitR hU z n ω)

/-- `A(τ_n)`, as an `ℝ≥0`-valued random time (in the σ-parametrisation). -/
@[expose] noncomputable def clockExit (n : ℕ) (ω : Ω) : ℝ≥0 := (clockExitR hU z n ω).toNNReal

/-- `σ^n_s = σ_z(s ∧ A(τ_n))`, as a real number. -/
@[expose] noncomputable def sigmaStopR (n : ℕ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  sigmaTime (fun r => U r ω) (hU.cont ω) z (min (s : ℝ) (clockExitR hU z n ω))

/-- **The stopped σ-time** `σ^n_s = σ_z(s ∧ A(τ_n)) = σ_z(s) ∧ τ_n`. -/
@[expose] noncomputable def sigmaStop (n : ℕ) (s : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (sigmaStopR hU z n s ω).toNNReal

variable {z}

theorem clockExitR_nonneg (n : ℕ) (ω : Ω) : 0 ≤ clockExitR hU z n ω := by
  by_cases hz : 0 < absorbingTime (fun s => U s ω) z
  · exact clock_nonneg (hU.cont ω) (exitR_mem_lifeSet hU z n hz)
  · rw [clockExitR, exitR_eq_zero hU z n hz, clock_zero]

theorem coe_clockExit (n : ℕ) (ω : Ω) : ((clockExit hU z n ω : ℝ≥0) : ℝ) = clockExitR hU z n ω :=
  Real.coe_toNNReal _ (clockExitR_nonneg hU n ω)

theorem clockExitR_eq_zero_of_not_pos {ω : Ω} (hz : ¬ 0 < absorbingTime (fun s => U s ω) z)
    (n : ℕ) : clockExitR hU z n ω = 0 := by
  rw [clockExitR, exitR_eq_zero hU z n hz, clock_zero]

theorem clockExit_eq_zero_of_not_pos {ω : Ω} (hz : ¬ 0 < absorbingTime (fun s => U s ω) z)
    (n : ℕ) : clockExit hU z n ω = 0 := by
  rw [clockExit, clockExitR_eq_zero_of_not_pos hU hz, Real.toNNReal_zero]

theorem clockExitR_mem_sigmaDom {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) (n : ℕ) :
    clockExitR hU z n ω ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z :=
  clock_mem_sigmaDom (hU.cont ω) (exitR_mem_lifeSet hU z n hz)

theorem min_clockExitR_mem_sigmaDom {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) (n : ℕ)
    (s : ℝ≥0) : min (s : ℝ) (clockExitR hU z n ω) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z :=
  mem_sigmaDom_of_le (clockExitR_mem_sigmaDom hU hz n)
    (le_min s.coe_nonneg (clockExitR_nonneg hU n ω)) (min_le_right _ _)

theorem clockExitR_mono {ω : Ω} {n k : ℕ} (hnk : n ≤ k) :
    clockExitR hU z n ω ≤ clockExitR hU z k ω := by
  by_cases hz : 0 < absorbingTime (fun s => U s ω) z
  · exact clock_monotoneOn (hU.cont ω) z (exitR_mem_lifeSet hU z n hz)
      (exitR_mem_lifeSet hU z k hz) (exitTime_mono (hU.cont ω) hz hnk)
  · rw [clockExitR_eq_zero_of_not_pos hU hz, clockExitR_eq_zero_of_not_pos hU hz]

theorem clockExit_mono (ω : Ω) : Monotone fun n => clockExit hU z n ω := fun n k hnk => by
  rw [← NNReal.coe_le_coe, coe_clockExit, coe_clockExit]
  exact clockExitR_mono hU hnk

theorem sigmaStopR_eq_zero_of_not_pos {ω : Ω} (hz : ¬ 0 < absorbingTime (fun s => U s ω) z)
    (n : ℕ) (s : ℝ≥0) : sigmaStopR hU z n s ω = 0 :=
  sigmaTime_eq_zero_of_not_pos (hU.cont ω) hz _

theorem sigmaStop_eq_zero_of_not_pos {ω : Ω} (hz : ¬ 0 < absorbingTime (fun s => U s ω) z)
    (n : ℕ) (s : ℝ≥0) : sigmaStop hU z n s ω = 0 := by
  rw [sigmaStop, sigmaStopR_eq_zero_of_not_pos hU hz, Real.toNNReal_zero]

theorem sigmaStopR_mem_lifeSet {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) (n : ℕ)
    (s : ℝ≥0) : sigmaStopR hU z n s ω ∈ lifeSet (fun r => U r ω) z :=
  sigmaTime_mem_lifeSet (hU.cont ω) (min_clockExitR_mem_sigmaDom hU hz n s)

theorem sigmaStopR_nonneg (n : ℕ) (s : ℝ≥0) (ω : Ω) : 0 ≤ sigmaStopR hU z n s ω := by
  by_cases hz : 0 < absorbingTime (fun s => U s ω) z
  · exact (sigmaStopR_mem_lifeSet hU hz n s).1
  · rw [sigmaStopR_eq_zero_of_not_pos hU hz]

theorem coe_sigmaStop (n : ℕ) (s : ℝ≥0) (ω : Ω) :
    ((sigmaStop hU z n s ω : ℝ≥0) : ℝ) = sigmaStopR hU z n s ω :=
  Real.coe_toNNReal _ (sigmaStopR_nonneg hU n s ω)

/-- `A(σ^n_s) = s ∧ A(τ_n)`. -/
theorem clock_sigmaStopR {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) (n : ℕ) (s : ℝ≥0) :
    clock (fun r => U r ω) (hU.cont ω) z (sigmaStopR hU z n s ω) =
      min (s : ℝ) (clockExitR hU z n ω) :=
  clock_sigmaTime (hU.cont ω) (min_clockExitR_mem_sigmaDom hU hz n s)

theorem sigmaTime_clockExitR {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) (n : ℕ) :
    sigmaTime (fun r => U r ω) (hU.cont ω) z (clockExitR hU z n ω) = exitR hU z n ω :=
  sigmaTime_clock (hU.cont ω) (exitR_mem_lifeSet hU z n hz)

/-- `σ^n_s ≤ τ_n`. -/
theorem sigmaStopR_le_exitR (n : ℕ) (s : ℝ≥0) (ω : Ω) :
    sigmaStopR hU z n s ω ≤ exitR hU z n ω := by
  by_cases hz : 0 < absorbingTime (fun s => U s ω) z
  · have := (sigmaTime_monotoneOn (hU.cont ω) z) (min_clockExitR_mem_sigmaDom hU hz n s)
      (clockExitR_mem_sigmaDom hU hz n) (min_le_right _ _)
    rwa [sigmaTime_clockExitR hU hz] at this
  · rw [sigmaStopR_eq_zero_of_not_pos hU hz, exitR_eq_zero hU z n hz]

theorem sigmaStop_le_exitNN (n : ℕ) (s : ℝ≥0) (ω : Ω) :
    sigmaStop hU z n s ω ≤ exitNN hU z n ω := by
  rw [← NNReal.coe_le_coe, coe_sigmaStop, coe_exitNN]
  exact sigmaStopR_le_exitR hU n s ω

/-- For `s ≥ A(τ_n)`, `σ^n_s = τ_n`. -/
theorem sigmaStopR_eq_exitR_of_le {ω : Ω} {n : ℕ} {s : ℝ≥0} (h : clockExitR hU z n ω ≤ s) :
    sigmaStopR hU z n s ω = exitR hU z n ω := by
  by_cases hz : 0 < absorbingTime (fun s => U s ω) z
  · rw [sigmaStopR, min_eq_right h, sigmaTime_clockExitR hU hz]
  · rw [sigmaStopR_eq_zero_of_not_pos hU hz, exitR_eq_zero hU z n hz]

theorem sigmaStop_eq_exitNN_of_le {ω : Ω} {n : ℕ} {s : ℝ≥0} (h : clockExit hU z n ω ≤ s) :
    sigmaStop hU z n s ω = exitNN hU z n ω := by
  rw [sigmaStop, sigmaStopR_eq_exitR_of_le hU (by rwa [← coe_clockExit, NNReal.coe_le_coe])]
  rfl

/-- For `s ≤ A(τ_n)`, `σ^n_s = σ_z(s)`. -/
theorem sigmaStopR_eq_sigmaTime_of_le {ω : Ω} {n : ℕ} {s : ℝ≥0}
    (h : (s : ℝ) ≤ clockExitR hU z n ω) :
    sigmaStopR hU z n s ω = sigmaTime (fun r => U r ω) (hU.cont ω) z s := by
  rw [sigmaStopR, min_eq_left h]

theorem sigmaStop_zero (n : ℕ) (ω : Ω) : sigmaStop hU z n 0 ω = 0 := by
  by_cases hz : 0 < absorbingTime (fun s => U s ω) z
  · rw [sigmaStop, sigmaStopR, NNReal.coe_zero, min_eq_left (clockExitR_nonneg hU n ω),
      sigmaTime_zero (hU.cont ω) (zero_mem_lifeSet_iff.2 hz), Real.toNNReal_zero]
  · exact sigmaStop_eq_zero_of_not_pos hU hz n 0

theorem sigmaStop_mono (n : ℕ) (ω : Ω) : Monotone fun s => sigmaStop hU z n s ω := by
  intro s t hst
  by_cases hz : 0 < absorbingTime (fun s => U s ω) z
  · rw [← NNReal.coe_le_coe, coe_sigmaStop, coe_sigmaStop]
    exact (sigmaTime_monotoneOn (hU.cont ω) z) (min_clockExitR_mem_sigmaDom hU hz n s)
      (min_clockExitR_mem_sigmaDom hU hz n t) (min_le_min_right _ (NNReal.coe_le_coe.2 hst))
  · change sigmaStop hU z n s ω ≤ sigmaStop hU z n t ω
    rw [sigmaStop_eq_zero_of_not_pos hU hz, sigmaStop_eq_zero_of_not_pos hU hz]

theorem continuous_sigmaStop (n : ℕ) (ω : Ω) : Continuous fun s => sigmaStop hU z n s ω := by
  by_cases hz : 0 < absorbingTime (fun s => U s ω) z
  · refine continuous_real_toNNReal.comp ?_
    exact (continuousOn_sigmaTime (hU.cont ω) z).comp_continuous
      (NNReal.continuous_coe.min continuous_const) (min_clockExitR_mem_sigmaDom hU hz n)
  · simp only [sigmaStop_eq_zero_of_not_pos hU hz]
    exact continuous_const

/-- `{σ^n_s ≤ u} = {τ_n ≤ u} ∪ ({u < T_z} ∩ {s ≤ A(u)})`. -/
theorem sigmaStop_le_iff (n : ℕ) (s u : ℝ≥0) (ω : Ω) :
    sigmaStop hU z n s ω ≤ u ↔ exitNN hU z n ω ≤ u ∨
      ((u : ℝ) ∈ lifeSet (fun r => U r ω) z ∧
        (s : ℝ) ≤ clock (fun r => U r ω) (hU.cont ω) z u) := by
  by_cases hz : 0 < absorbingTime (fun s => U s ω) z
  · constructor
    · intro h
      by_cases hτ : exitNN hU z n ω ≤ u
      · exact Or.inl hτ
      · push Not at hτ
        have hu' : (u : ℝ) < exitR hU z n ω := by rwa [← coe_exitNN, NNReal.coe_lt_coe]
        have hul : (u : ℝ) ∈ lifeSet (fun r => U r ω) z :=
          mem_lifeSet_of_le (exitR_mem_lifeSet hU z n hz) u.coe_nonneg hu'.le
        refine Or.inr ⟨hul, ?_⟩
        have h1 : sigmaStopR hU z n s ω ≤ u := by rwa [← coe_sigmaStop, NNReal.coe_le_coe]
        have h2 := clock_monotoneOn (hU.cont ω) z (sigmaStopR_mem_lifeSet hU hz n s) hul h1
        rw [clock_sigmaStopR hU hz] at h2
        rcases le_total (s : ℝ) (clockExitR hU z n ω) with hs | hs
        · rwa [min_eq_left hs] at h2
        · exfalso
          rw [sigmaStopR_eq_exitR_of_le hU hs] at h1
          exact absurd h1 (not_le.2 hu')
    · rintro (h | ⟨hul, hsu⟩)
      · exact (sigmaStop_le_exitNN hU n s ω).trans h
      · rw [← NNReal.coe_le_coe, coe_sigmaStop]
        have h1 := (sigmaTime_monotoneOn (hU.cont ω) z) (min_clockExitR_mem_sigmaDom hU hz n s)
          (clock_mem_sigmaDom (hU.cont ω) hul) ((min_le_left _ _).trans hsu)
        rwa [sigmaTime_clock (hU.cont ω) hul] at h1
  · have h1 : exitNN hU z n ω = 0 := by
      rw [exitNN, exitR_eq_zero hU z n hz, Real.toNNReal_zero]
    simp [sigmaStop_eq_zero_of_not_pos hU hz, h1]

variable (z) in
open Classical in
/-- **`σ^n_s` is an `ℱ`-stopping time.** -/
theorem isStoppingTime_sigmaStop (n : ℕ) (s : ℝ≥0) :
    IsStoppingTime ℱ fun ω => (sigmaStop hU z n s ω : WithTop ℝ≥0) := by
  refine Infrastructure.isStoppingTime_of_nnreal_le fun u => ?_
  have key : {ω | sigmaStop hU z n s ω ≤ u} = {ω | exitNN hU z n ω ≤ u} ∪
      ({ω | (u : ℝ) ∈ lifeSet (fun r => U r ω) z} ∩
        {ω | (s : ℝ) ≤ if (u : ℝ) ∈ lifeSet (fun r => U r ω) z then
          clock (fun r => U r ω) (hU.cont ω) z u else 0}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_inter_iff]
    rw [sigmaStop_le_iff]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h1, by simpa [h1] using h2⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h1, by simpa [h1] using h2⟩
  rw [key]
  refine (Infrastructure.measurableSet_nnreal_le (isStoppingTime_exitNN hU z n) u).union
    ((measurableSet_mem_lifeSet hU.cont hU.adapted u z).inter ?_)
  exact (measurable_clock hU.cont hU.adapted u z) measurableSet_Ici

variable (z)

/-- **The stopped σ-time filtration** `𝒢^n_s = ℱ_{σ^n_s}`. -/
@[expose] noncomputable def sigmaStopFiltration (n : ℕ) : Filtration ℝ≥0 m where
  seq s := (isStoppingTime_sigmaStop hU z n s).measurableSpace
  mono' _ _ hst := IsStoppingTime.measurableSpace_mono _ _ fun ω =>
    WithTop.coe_le_coe.2 (sigmaStop_mono hU n ω hst)
  le' s := (isStoppingTime_sigmaStop hU z n s).measurableSpace_le

theorem sigmaStopFiltration_apply (n : ℕ) (s : ℝ≥0) :
    sigmaStopFiltration hU z n s = (isStoppingTime_sigmaStop hU z n s).measurableSpace := rfl

/-! ### The honest σ-time as a `WithTop`-valued stopping time -/

open Classical in
/-- **The σ-time `σ_z(s)`** as a `WithTop ℝ≥0`-valued random time: `σ_z(s)` on
`{s ∈ sigmaDom}` and `⊤` elsewhere (a.s. never, Remark 2.12). -/
@[expose] noncomputable def sigmaTop (s : ℝ≥0) (ω : Ω) : WithTop ℝ≥0 :=
  if (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z then
    (((sigmaTime (fun r => U r ω) (hU.cont ω) z s).toNNReal : ℝ≥0) : WithTop ℝ≥0) else ⊤

variable {z}

theorem sigmaTop_of_mem {s : ℝ≥0} {ω : Ω}
    (hs : (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z) :
    sigmaTop hU z s ω = (((sigmaTime (fun r => U r ω) (hU.cont ω) z s).toNNReal : ℝ≥0) :
      WithTop ℝ≥0) := by
  rw [sigmaTop, ite_eq_left hs]

theorem sigmaTop_of_notMem {s : ℝ≥0} {ω : Ω}
    (hs : (s : ℝ) ∉ sigmaDom (fun r => U r ω) (hU.cont ω) z) : sigmaTop hU z s ω = ⊤ := by
  rw [sigmaTop, ite_eq_right hs]

/-- On `{σ^n_s < τ_n}`: `s ∈ sigmaDom` and `σ^n_s = σ_z(s)`. -/
theorem of_sigmaStop_lt_exitNN {n : ℕ} {s : ℝ≥0} {ω : Ω}
    (h : sigmaStop hU z n s ω < exitNN hU z n ω) :
    (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z ∧
      sigmaStopR hU z n s ω = sigmaTime (fun r => U r ω) (hU.cont ω) z s := by
  have hz : 0 < absorbingTime (fun s => U s ω) z := by
    by_contra hz
    rw [sigmaStop_eq_zero_of_not_pos hU hz, exitNN, exitR_eq_zero hU z n hz,
      Real.toNNReal_zero] at h
    exact lt_irrefl _ h
  have hs : (s : ℝ) ≤ clockExitR hU z n ω := by
    by_contra hs
    push Not at hs
    rw [← NNReal.coe_lt_coe, coe_sigmaStop, coe_exitNN, sigmaStopR_eq_exitR_of_le hU hs.le] at h
    exact lt_irrefl _ h
  exact ⟨mem_sigmaDom_of_le (clockExitR_mem_sigmaDom hU hz n) s.coe_nonneg hs,
    sigmaStopR_eq_sigmaTime_of_le hU hs⟩

/-- `σ^n_s < τ_n ↔ s < A(τ_n)`. -/
theorem sigmaStop_lt_exitNN_iff {n : ℕ} {s : ℝ≥0} {ω : Ω} :
    sigmaStop hU z n s ω < exitNN hU z n ω ↔ s < clockExit hU z n ω := by
  constructor
  · intro h
    have hz : 0 < absorbingTime (fun s => U s ω) z := by
      by_contra hz
      rw [sigmaStop_eq_zero_of_not_pos hU hz, exitNN, exitR_eq_zero hU z n hz,
        Real.toNNReal_zero] at h
      exact lt_irrefl _ h
    by_contra hs
    push Not at hs
    rw [sigmaStop_eq_exitNN_of_le hU hs] at h
    exact lt_irrefl _ h
  · intro hs
    have hs' : (s : ℝ) < clockExitR hU z n ω := by rwa [← coe_clockExit, NNReal.coe_lt_coe]
    have hz : 0 < absorbingTime (fun s => U s ω) z := by
      by_contra hz
      rw [clockExitR_eq_zero_of_not_pos hU hz] at hs'
      exact absurd hs' (not_lt.2 s.coe_nonneg)
    rw [← NNReal.coe_lt_coe, coe_sigmaStop, coe_exitNN, sigmaStopR_eq_sigmaTime_of_le hU hs'.le,
      ← sigmaTime_clockExitR hU hz]
    exact (sigmaTime_strictMonoOn (hU.cont ω) z)
      (mem_sigmaDom_of_le (clockExitR_mem_sigmaDom hU hz n) s.coe_nonneg hs'.le)
      (clockExitR_mem_sigmaDom hU hz n) hs'

/-- `{σ_z(s) ≤ u} = ⋃ n, {σ^n_s < τ_n} ∩ {σ^n_s ≤ u}`. -/
theorem sigmaTop_le_iff (s u : ℝ≥0) (ω : Ω) :
    sigmaTop hU z s ω ≤ u ↔ ∃ n, sigmaStop hU z n s ω < exitNN hU z n ω ∧
      sigmaStop hU z n s ω ≤ u := by
  constructor
  · intro h
    by_cases hs : (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z
    · rw [sigmaTop_of_mem hU hs, WithTop.coe_le_coe] at h
      have hz := pos_absorbingTime_of_mem_sigmaDom (hU.cont ω) hs
      have hσ := sigmaTime_mem_lifeSet (hU.cont ω) hs
      obtain ⟨n, hn⟩ := exists_lt_exitTime (hU.cont ω) hσ
      have hlt : (s : ℝ) < clockExitR hU z n ω := by
        rw [← clock_sigmaTime (hU.cont ω) hs]
        exact clock_lt_clock (hU.cont ω) hσ.1 hn (exitR_mem_lifeSet hU z n hz)
      have heq : sigmaStop hU z n s ω = (sigmaTime (fun r => U r ω) (hU.cont ω) z s).toNNReal := by
        rw [sigmaStop, sigmaStopR_eq_sigmaTime_of_le hU hlt.le]
      refine ⟨n, ?_, by rw [heq]; exact h⟩
      rw [sigmaStop_lt_exitNN_iff, ← NNReal.coe_lt_coe, coe_clockExit]
      exact hlt
    · rw [sigmaTop_of_notMem hU hs] at h
      exact absurd h (WithTop.not_top_le_coe u)
  · rintro ⟨n, hlt, hle⟩
    obtain ⟨hs, heq⟩ := of_sigmaStop_lt_exitNN hU hlt
    rw [sigmaTop_of_mem hU hs, WithTop.coe_le_coe, ← heq]
    exact hle

variable (z) in
/-- **`σ_z(s)` is an `ℱ`-stopping time.** -/
theorem isStoppingTime_sigmaTop (s : ℝ≥0) : IsStoppingTime ℱ (sigmaTop hU z s) := by
  intro u
  have key : {ω | sigmaTop hU z s ω ≤ u} = ⋃ n, ({ω | (sigmaStop hU z n s ω : WithTop ℝ≥0) <
      (exitNN hU z n ω : WithTop ℝ≥0)} ∩ {ω | (sigmaStop hU z n s ω : WithTop ℝ≥0) ≤ u}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, WithTop.coe_lt_coe, WithTop.coe_le_coe]
    exact sigmaTop_le_iff hU s u ω
  rw [key]
  refine MeasurableSet.iUnion fun n => ?_
  have hσ := isStoppingTime_sigmaStop hU z n s
  have hτ := isStoppingTime_exitNN hU z n
  have h1 : MeasurableSet[hσ.measurableSpace] {ω | (sigmaStop hU z n s ω : WithTop ℝ≥0) <
      (exitNN hU z n ω : WithTop ℝ≥0)} := by
    have : {ω | (sigmaStop hU z n s ω : WithTop ℝ≥0) < (exitNN hU z n ω : WithTop ℝ≥0)} =
        {ω | (exitNN hU z n ω : WithTop ℝ≥0) ≤ (sigmaStop hU z n s ω : WithTop ℝ≥0)}ᶜ := by
      ext ω; simp only [mem_ofPred_eq, mem_compl_iff, not_le]
    rw [this]
    exact (IsStoppingTime.measurableSet_stopping_time_le hτ hσ).compl
  exact ((hσ.measurableSet _).1 h1).2 u

variable (z)

/-- **The σ-time filtration** `𝒢_s = ℱ_{σ_z(s)}`. -/
@[expose] noncomputable def sigmaFiltration : Filtration ℝ≥0 m where
  seq s := (isStoppingTime_sigmaTop hU z s).measurableSpace
  mono' s t hst := IsStoppingTime.measurableSpace_mono _ _ fun ω => by
    by_cases ht : (t : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z
    · have hs : (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z :=
        mem_sigmaDom_of_le ht s.coe_nonneg (NNReal.coe_le_coe.2 hst)
      rw [sigmaTop_of_mem hU hs, sigmaTop_of_mem hU ht, WithTop.coe_le_coe,
        Real.toNNReal_le_toNNReal_iff (sigmaTime_nonneg (hU.cont ω) ht)]
      exact (sigmaTime_monotoneOn (hU.cont ω) z) hs ht (NNReal.coe_le_coe.2 hst)
    · rw [sigmaTop_of_notMem hU ht]; exact le_top
  le' s := (isStoppingTime_sigmaTop hU z s).measurableSpace_le

theorem sigmaFiltration_apply (s : ℝ≥0) :
    sigmaFiltration hU z s = (isStoppingTime_sigmaTop hU z s).measurableSpace := rfl

variable {z}

/-- `σ^n_s ≤ σ_z(s)`. -/
theorem sigmaStop_le_sigmaTop (n : ℕ) (s : ℝ≥0) (ω : Ω) :
    (sigmaStop hU z n s ω : WithTop ℝ≥0) ≤ sigmaTop hU z s ω := by
  by_cases hs : (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z
  · rw [sigmaTop_of_mem hU hs, WithTop.coe_le_coe, sigmaStop,
      Real.toNNReal_le_toNNReal_iff (sigmaTime_nonneg (hU.cont ω) hs)]
    have hz := pos_absorbingTime_of_mem_sigmaDom (hU.cont ω) hs
    exact (sigmaTime_monotoneOn (hU.cont ω) z) (min_clockExitR_mem_sigmaDom hU hz n s) hs
      (min_le_left _ _)
  · rw [sigmaTop_of_notMem hU hs]; exact le_top

theorem sigmaStopFiltration_le (n : ℕ) (s : ℝ≥0) :
    sigmaStopFiltration hU z n s ≤ sigmaFiltration hU z s :=
  IsStoppingTime.measurableSpace_mono (isStoppingTime_sigmaStop hU z n s)
    (isStoppingTime_sigmaTop hU z s) (sigmaStop_le_sigmaTop hU n s)

/-! ### `A(τ_n)` as a stopping time in the σ-parametrisation -/

/-- `A(τ_n) ≤ s ↔ τ_n ≤ σ^n_s`. -/
theorem clockExit_le_iff {n : ℕ} {s : ℝ≥0} {ω : Ω} :
    clockExit hU z n ω ≤ s ↔ exitNN hU z n ω ≤ sigmaStop hU z n s ω := by
  rw [← not_iff_not, not_le, not_le, sigmaStop_lt_exitNN_iff]

/-- **`A(τ_n)` is a `𝒢`-stopping time.** -/
theorem isStoppingTime_clockExit (n : ℕ) :
    IsStoppingTime (sigmaFiltration hU z) fun ω => (clockExit hU z n ω : WithTop ℝ≥0) := by
  refine Infrastructure.isStoppingTime_of_nnreal_le fun s => ?_
  have key : {ω | clockExit hU z n ω ≤ s} =
      {ω | (exitNN hU z n ω : WithTop ℝ≥0) ≤ (sigmaStop hU z n s ω : WithTop ℝ≥0)} := by
    ext ω
    simp only [mem_ofPred_eq, WithTop.coe_le_coe]
    exact clockExit_le_iff hU
  rw [key]
  exact sigmaStopFiltration_le hU n s _
    (IsStoppingTime.measurableSet_stopping_time_le (isStoppingTime_exitNN hU z n)
      (isStoppingTime_sigmaStop hU z n s))

/-- **The transfer condition**: for `A ∈ 𝒢_s`, `A ∩ {s < A(τ_n)} ∈ 𝒢^n_s`. -/
theorem measurableSet_inter_lt_clockExit (n : ℕ) (s : ℝ≥0) (A : Set Ω)
    (hA : MeasurableSet[sigmaFiltration hU z s] A) :
    MeasurableSet[sigmaStopFiltration hU z n s] (A ∩ {ω | s < clockExit hU z n ω}) := by
  have hσ := isStoppingTime_sigmaStop hU z n s
  have hτ := isStoppingTime_exitNN hU z n
  have hσtop := isStoppingTime_sigmaTop hU z s
  have hmin : (fun ω => min (sigmaTop hU z s ω) (sigmaStop hU z n s ω : WithTop ℝ≥0)) =
      fun ω => (sigmaStop hU z n s ω : WithTop ℝ≥0) := by
    funext ω; exact min_eq_right (sigmaStop_le_sigmaTop hU n s ω)
  have h1 : MeasurableSet[hσ.measurableSpace] (A ∩ {ω | sigmaTop hU z s ω ≤
      (sigmaStop hU z n s ω : WithTop ℝ≥0)}) := by
    have := IsStoppingTime.measurableSet_inter_le hσtop hσ A hA
    rwa [IsStoppingTime.measurableSpace_congr ℱ (hσtop.min hσ) hσ hmin] at this
  have h2 : MeasurableSet[hσ.measurableSpace] {ω | (sigmaStop hU z n s ω : WithTop ℝ≥0) <
      (exitNN hU z n ω : WithTop ℝ≥0)} := by
    have : {ω | (sigmaStop hU z n s ω : WithTop ℝ≥0) < (exitNN hU z n ω : WithTop ℝ≥0)} =
        {ω | (exitNN hU z n ω : WithTop ℝ≥0) ≤ (sigmaStop hU z n s ω : WithTop ℝ≥0)}ᶜ := by
      ext ω; simp only [mem_ofPred_eq, mem_compl_iff, not_le]
    rw [this]
    exact (IsStoppingTime.measurableSet_stopping_time_le hτ hσ).compl
  have key : A ∩ {ω | s < clockExit hU z n ω} =
      (A ∩ {ω | sigmaTop hU z s ω ≤ (sigmaStop hU z n s ω : WithTop ℝ≥0)}) ∩
        {ω | (sigmaStop hU z n s ω : WithTop ℝ≥0) < (exitNN hU z n ω : WithTop ℝ≥0)} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, WithTop.coe_lt_coe]
    rw [← sigmaStop_lt_exitNN_iff hU]
    constructor
    · rintro ⟨hAω, hlt⟩
      obtain ⟨hs, heq⟩ := of_sigmaStop_lt_exitNN hU hlt
      refine ⟨⟨hAω, ?_⟩, hlt⟩
      rw [sigmaTop_of_mem hU hs, WithTop.coe_le_coe, sigmaStop, heq]
    · rintro ⟨⟨hAω, -⟩, hlt⟩
      exact ⟨hAω, hlt⟩
  rw [key]
  exact h1.inter h2

/-! ### Change of variables along `σ^n` -/

/-- **Change of variables along the stopped σ-time**: if an integrand `ξ` equals
`φ(θ_t) |f_t|⁻²` before `τ_n`, then `∫₀^{σ^n_s} ξ = ∫₀^{s ∧ A(τ_n)} φ(θ_{σ_z(v)}) dv`. -/
theorem pathIntegral_sigmaStop_eq {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) {n : ℕ}
    {ξ : ℝ≥0 → Ω → ℝ} {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hξ : ∀ t : ℝ≥0, (t : ℝ) ≤ exitR hU z n ω → ξ t ω =
      φ (argPath (fun r => U r ω) (hU.cont ω) z t) * clockRate (fun r => U r ω) (hU.cont ω) z t)
    (s : ℝ≥0) :
    pathIntegral ξ (sigmaStop hU z n s ω) ω =
      ∫ v in (0 : ℝ)..min (s : ℝ) (clockExitR hU z n ω),
        φ (argPath (fun r => U r ω) (hU.cont ω) z
          (sigmaTime (fun r => U r ω) (hU.cont ω) z v)) := by
  rw [← integral_comp_sigmaTime (hU.cont ω) hφ (min_clockExitR_mem_sigmaDom hU hz n s)]
  unfold pathIntegral
  rw [coe_sigmaStop]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le (sigmaStopR_nonneg hU n s ω)] at hu
  have hu' : (u.toNNReal : ℝ) ≤ exitR hU z n ω := by
    rw [Real.coe_toNNReal _ hu.1]; exact hu.2.trans (sigmaStopR_le_exitR hU n s ω)
  rw [hξ u.toNNReal hu', Real.coe_toNNReal _ hu.1]

end Processes

end ComplexSLE.Internal.Polar

end
