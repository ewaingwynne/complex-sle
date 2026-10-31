/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.PolarRestartPolar

/-!
# Deterministic restart identity (M7/A4b): the restart at `σ_z(t̃)`

The "future dependence" and "scale invariance" identities behind Lemma 3.2 and the regeneration step
of Lemma 3.3 (`paper.tex:L1804`, `L2207-2212`), deterministic and unconditional.

Fix a continuous driver `U`, a point `z` and `t̃ ∈ sigmaDom U hU z` (so `T_z > 0`). Put

* `T = σ_z(t̃) < T_z` (`sigmaTime U hU z t̃`), `w = f_T(z) ≠ 0`, `r = |w|` (`restartScale`);
* `V_s = r⁻¹ (U_{T + r² s} - U_T)` (`sigmaRestartDriver`), a continuous driver, and
  `z' = w / r` (`restartPoint`), `|z'| = 1`.

Then, for all `s ≥ 0`:

* **(i)** `T_{z'}(V) = (T_z(U) - T) / r²` (`restart_absorbingTime`), `s` is in the life set of `(V, z')`
  iff `T + r² s` is in that of `(U, z)` (`mem_lifeSet_restart_sigma`), and `f^V_s(z') =
  r⁻¹ f^U_{T + r² s}(z)` there (`restart_fPath`);
* **(ii)** `A^V_{z'}(s) = A^U_z(T + r² s) - t̃` (`restart_clock`; the clock is scale invariant), hence
  `sigmaDom V z' = {s ≥ 0 | t̃ + s ∈ sigmaDom U z}` (`mem_sigmaDom_restart_sigma`) and
  `σ^V_{z'}(s) = (σ^U_z(t̃ + s) - T) / r²` (`restart_sigmaTime`);
* **(iii)** `θ^V_{σ^V(s)}(z') - θ^V_0(z') = θ^U_{σ^U(t̃ + s)}(z) - θ^U_T(z)` (`restart_argPath`),
  `log |f^V_{σ^V(s)}(z')| = log |f^U_{σ^U(t̃ + s)}(z)| - log |f^U_T(z)|` (`restart_log_norm`), and
  `e^{iθ^V_0(z')} = z' = e^{iθ^U_T(z)} = e^{iθ̂_{t̃}(z)}` (`restart_exp_argPath_zero`, `restartPoint_eq_exp`).

Here `θ̂_{t̃}(z) = θ^U_{σ_z(t̃)}(z)` (`PolarThetaHat.lean`). The general-scale versions (any `r > 0`,
any `T ∈ [0, T_z)`) are in `PolarRestart.lean`, `PolarRestartClock.lean`, `PolarRestartPolar.lean`.
No external input is used.
-/

public section

open scoped NNReal ENNReal Real
open Set Complex

namespace ComplexSLE.Internal.Polar

variable {U : ℝ≥0 → ℂ}

/-! ### The restart data at `σ_z(t̃)` -/

/-- The restart time `T = σ_z(t̃)` as an element of `ℝ≥0`. -/
@[expose] noncomputable def restartTime (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) (tt : ℝ) : ℝ≥0 :=
  (sigmaTime U hU z tt).toNNReal

/-- The restart scale `r = |f_T(z)|` with `T = σ_z(t̃)`. -/
@[expose] noncomputable def restartScale (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) (tt : ℝ) : ℝ≥0 :=
  ‖fPath U hU z (sigmaTime U hU z tt)‖₊

/-- The restart point `z' = f_T(z) / |f_T(z)|` on the unit circle, `T = σ_z(t̃)`. -/
@[expose] noncomputable def restartPoint (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) (tt : ℝ) : ℂ :=
  fPath U hU z (sigmaTime U hU z tt) / (‖fPath U hU z (sigmaTime U hU z tt)‖ : ℂ)

/-- The restarted and rescaled driver `V_s = r⁻¹ (U_{T + r² s} - U_T)` with `T = σ_z(t̃)`,
`r = |f_T(z)|`. -/
@[expose] noncomputable def sigmaRestartDriver (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) (tt : ℝ) :
    ℝ≥0 → ℂ :=
  restartDriver U (restartTime U hU z tt) (restartScale U hU z tt)

theorem sigmaRestartDriver_continuous (hU : Continuous U) (z : ℂ) (tt : ℝ) :
    Continuous (sigmaRestartDriver U hU z tt) :=
  restartDriver_continuous hU _ _

theorem sigmaRestartDriver_apply (hU : Continuous U) (z : ℂ) (tt : ℝ) (s : ℝ≥0) :
    sigmaRestartDriver U hU z tt s =
      ((restartScale U hU z tt : ℝ≥0) : ℂ)⁻¹ *
        (U (restartTime U hU z tt + restartScale U hU z tt ^ 2 * s) - U (restartTime U hU z tt)) :=
  rfl

variable {hU : Continuous U} {z : ℂ} {tt : ℝ}

theorem coe_restartTime (ht : tt ∈ sigmaDom U hU z) :
    (restartTime U hU z tt : ℝ) = sigmaTime U hU z tt :=
  Real.coe_toNNReal _ (sigmaTime_nonneg hU ht)

theorem restartTime_mem_lifeSet (ht : tt ∈ sigmaDom U hU z) :
    (restartTime U hU z tt : ℝ) ∈ lifeSet U z := by
  rw [coe_restartTime ht]
  exact sigmaTime_mem_lifeSet hU ht

theorem coe_restartScale (hU : Continuous U) (z : ℂ) (tt : ℝ) :
    (restartScale U hU z tt : ℝ) = ‖fPath U hU z (sigmaTime U hU z tt)‖ :=
  coe_nnnorm _

theorem restartScale_pos (ht : tt ∈ sigmaDom U hU z) : 0 < restartScale U hU z tt :=
  nnnorm_pos.2 (fPath_ne_zero hU (sigmaTime_mem_lifeSet hU ht))

theorem clock_restartTime (ht : tt ∈ sigmaDom U hU z) : clock U hU z (restartTime U hU z tt) = tt := by
  rw [coe_restartTime ht]
  exact clock_sigmaTime hU ht

theorem restartPoint_eq (ht : tt ∈ sigmaDom U hU z) :
    restartPoint U hU z tt =
      restartPt U hU z (restartTime U hU z tt) (restartScale U hU z tt) := by
  unfold restartPoint restartPt
  rw [coe_restartTime ht, coe_restartScale, div_eq_inv_mul]

theorem norm_restartPoint (ht : tt ∈ sigmaDom U hU z) : ‖restartPoint U hU z tt‖ = 1 := by
  have hpos := norm_fPath_pos hU (sigmaTime_mem_lifeSet hU ht)
  unfold restartPoint
  rw [norm_div, Complex.norm_real, norm_norm, div_self hpos.ne']

/-- `z' = e^{iθ^U_T(z)} = e^{iθ̂_{t̃}(z)}`, `T = σ_z(t̃)`. -/
theorem restartPoint_eq_exp (ht : tt ∈ sigmaDom U hU z) :
    restartPoint U hU z tt = exp (argPath U hU z (sigmaTime U hU z tt) * I) :=
  (exp_argPath_mul_I hU (sigmaTime_mem_lifeSet hU ht)).symm

/-! ### (i) Life set, absorbing time and the path `f` -/

/-- **(i)** `T_{z'}(V) = (T_z(U) - T) / r²`. -/
theorem restart_absorbingTime (ht : tt ∈ sigmaDom U hU z) :
    absorbingTime (sigmaRestartDriver U hU z tt) (restartPoint U hU z tt) =
      (absorbingTime U z - ENNReal.ofReal (sigmaTime U hU z tt)) /
        ((restartScale U hU z tt ^ 2 : ℝ≥0) : ℝ≥0∞) := by
  rw [restartPoint_eq ht, sigmaRestartDriver,
    absorbingTime_restart hU (restartTime_mem_lifeSet ht) (restartScale_pos ht),
    ← coe_restartTime ht, ENNReal.ofReal_coe_nnreal]

/-- **(i)** `s` is in the life set of `(V, z')` iff `s ≥ 0` and `T + r² s` is in that of `(U, z)`. -/
theorem mem_lifeSet_restart_sigma (ht : tt ∈ sigmaDom U hU z) {s : ℝ} :
    s ∈ lifeSet (sigmaRestartDriver U hU z tt) (restartPoint U hU z tt) ↔
      0 ≤ s ∧ sigmaTime U hU z tt + (restartScale U hU z tt : ℝ) ^ 2 * s ∈ lifeSet U z := by
  rw [restartPoint_eq ht, sigmaRestartDriver,
    mem_lifeSet_restart hU (restartTime_mem_lifeSet ht) (restartScale_pos ht), coe_restartTime ht]

/-- **(i)** `f^V_s(z') = r⁻¹ f^U_{T + r² s}(z)` on the life set of `(V, z')`. -/
theorem restart_fPath (ht : tt ∈ sigmaDom U hU z) {s : ℝ}
    (hs : s ∈ lifeSet (sigmaRestartDriver U hU z tt) (restartPoint U hU z tt)) :
    fPath (sigmaRestartDriver U hU z tt) (sigmaRestartDriver_continuous hU z tt)
        (restartPoint U hU z tt) s =
      ((restartScale U hU z tt : ℝ≥0) : ℂ)⁻¹ *
        fPath U hU z (sigmaTime U hU z tt + (restartScale U hU z tt : ℝ) ^ 2 * s) := by
  rw [restartPoint_eq ht] at hs ⊢
  have := fPath_restart hU (restartTime_mem_lifeSet ht) (restartScale_pos ht) hs
  rw [coe_restartTime ht] at this
  exact this

theorem restart_fPath_zero (ht : tt ∈ sigmaDom U hU z) :
    fPath (sigmaRestartDriver U hU z tt) (sigmaRestartDriver_continuous hU z tt)
        (restartPoint U hU z tt) 0 = restartPoint U hU z tt := by
  rw [restartPoint_eq ht]
  exact fPath_restart_zero hU z _ _

/-! ### (ii) Clock and σ-time -/

/-- **(ii)** The clock is scale invariant: `A^V_{z'}(s) = A^U_z(T + r² s) - t̃`. -/
theorem restart_clock (ht : tt ∈ sigmaDom U hU z) {s : ℝ}
    (hs : s ∈ lifeSet (sigmaRestartDriver U hU z tt) (restartPoint U hU z tt)) :
    clock (sigmaRestartDriver U hU z tt) (sigmaRestartDriver_continuous hU z tt)
        (restartPoint U hU z tt) s =
      clock U hU z (sigmaTime U hU z tt + (restartScale U hU z tt : ℝ) ^ 2 * s) - tt := by
  rw [restartPoint_eq ht] at hs ⊢
  have := clock_restart hU (restartTime_mem_lifeSet ht) (restartScale_pos ht) hs
  rw [coe_restartTime ht, clock_sigmaTime hU ht] at this
  exact this

/-- **(ii)** `s ∈ sigmaDom V z'` iff `s ≥ 0` and `t̃ + s ∈ sigmaDom U z`. -/
theorem mem_sigmaDom_restart_sigma (ht : tt ∈ sigmaDom U hU z) {s : ℝ} :
    s ∈ sigmaDom (sigmaRestartDriver U hU z tt) (sigmaRestartDriver_continuous hU z tt)
        (restartPoint U hU z tt) ↔
      0 ≤ s ∧ tt + s ∈ sigmaDom U hU z := by
  rw [restartPoint_eq ht]
  have := mem_sigmaDom_restart hU (restartTime_mem_lifeSet ht) (restartScale_pos ht) (s := s)
  rw [clock_restartTime ht] at this
  exact this

/-- **(ii)** `sigmaDom V z' = [0, ∞) ∩ (t̃ + ·)⁻¹ (sigmaDom U z)`. -/
theorem sigmaDom_restart_sigma_eq (ht : tt ∈ sigmaDom U hU z) :
    sigmaDom (sigmaRestartDriver U hU z tt) (sigmaRestartDriver_continuous hU z tt)
        (restartPoint U hU z tt) =
      Ici 0 ∩ (fun s => tt + s) ⁻¹' sigmaDom U hU z := by
  ext s
  rw [mem_sigmaDom_restart_sigma ht]
  rfl

theorem zero_mem_sigmaDom_restart_sigma (ht : tt ∈ sigmaDom U hU z) :
    (0 : ℝ) ∈ sigmaDom (sigmaRestartDriver U hU z tt) (sigmaRestartDriver_continuous hU z tt)
      (restartPoint U hU z tt) :=
  (mem_sigmaDom_restart_sigma ht).2 ⟨le_rfl, by simpa using ht⟩

/-- **(ii)** If `σ_z` is defined on all of `[0, ∞)` (Remark 2.12), so is `σ` of the restarted chain. -/
theorem sigmaDom_restart_sigma_eq_Ici (ht : tt ∈ sigmaDom U hU z) (h : clockSup U hU z = ⊤) :
    sigmaDom (sigmaRestartDriver U hU z tt) (sigmaRestartDriver_continuous hU z tt)
      (restartPoint U hU z tt) = Ici 0 := by
  rw [restartPoint_eq ht]
  exact sigmaDom_restart_eq_Ici hU (restartTime_mem_lifeSet ht) (restartScale_pos ht) h

/-- **(ii)** `σ^V_{z'}(s) = (σ^U_z(t̃ + s) - σ^U_z(t̃)) / r²` on the domain of `σ^V_{z'}`. -/
theorem restart_sigmaTime (ht : tt ∈ sigmaDom U hU z) {s : ℝ}
    (hs : s ∈ sigmaDom (sigmaRestartDriver U hU z tt) (sigmaRestartDriver_continuous hU z tt)
      (restartPoint U hU z tt)) :
    sigmaTime (sigmaRestartDriver U hU z tt) (sigmaRestartDriver_continuous hU z tt)
        (restartPoint U hU z tt) s =
      (sigmaTime U hU z (tt + s) - sigmaTime U hU z tt) / (restartScale U hU z tt : ℝ) ^ 2 := by
  rw [restartPoint_eq ht] at hs ⊢
  have := sigmaTime_restart hU (restartTime_mem_lifeSet ht) (restartScale_pos ht) hs
  rw [coe_restartTime ht, clock_sigmaTime hU ht] at this
  exact this

/-- **(ii)**, additive form: `T + r² σ^V_{z'}(s) = σ^U_z(t̃ + s)`, and `σ^V_{z'}(s)` lies in the life
set of `(V, z')`. -/
theorem restart_sigmaTime_aux (ht : tt ∈ sigmaDom U hU z) {s : ℝ}
    (hs : s ∈ sigmaDom (sigmaRestartDriver U hU z tt) (sigmaRestartDriver_continuous hU z tt)
      (restartPoint U hU z tt)) :
    sigmaTime (sigmaRestartDriver U hU z tt) (sigmaRestartDriver_continuous hU z tt)
        (restartPoint U hU z tt) s ∈
        lifeSet (sigmaRestartDriver U hU z tt) (restartPoint U hU z tt) ∧
      sigmaTime U hU z tt + (restartScale U hU z tt : ℝ) ^ 2 *
        sigmaTime (sigmaRestartDriver U hU z tt) (sigmaRestartDriver_continuous hU z tt)
          (restartPoint U hU z tt) s = sigmaTime U hU z (tt + s) := by
  rw [restartPoint_eq ht] at hs ⊢
  have := sigmaTime_restart_aux hU (restartTime_mem_lifeSet ht) (restartScale_pos ht) hs
  rw [coe_restartTime ht, clock_sigmaTime hU ht] at this
  exact this

/-! ### (iii) Polar data -/

/-- **(iii)** The initial direction: `e^{iθ^V_0(z')} = z'`. -/
theorem restart_exp_argPath_zero (ht : tt ∈ sigmaDom U hU z) :
    exp (argPath (sigmaRestartDriver U hU z tt) (sigmaRestartDriver_continuous hU z tt)
      (restartPoint U hU z tt) 0 * I) = restartPoint U hU z tt := by
  have h1 := exp_argPath_restart_zero hU (restartTime_mem_lifeSet ht) (restartScale_pos ht)
  rw [coe_restartTime ht] at h1
  have e := restartPoint_eq ht
  conv_lhs => rw [e]
  exact h1.trans (restartPoint_eq_exp ht).symm

/-- **(iii)** `θ^V_0(z') ∈ [0, 2π)`. -/
theorem restart_argPath_zero_mem_Ico :
    argPath (sigmaRestartDriver U hU z tt) (sigmaRestartDriver_continuous hU z tt)
      (restartPoint U hU z tt) 0 ∈ Ico 0 (2 * π) :=
  argPath_zero_mem_Ico _ _

/-- **(iii)** The argument increments agree:
`θ^V_{σ^V(s)}(z') - θ^V_0(z') = θ^U_{σ^U(t̃ + s)}(z) - θ^U_T(z)`, `T = σ_z(t̃)`. -/
theorem restart_argPath (ht : tt ∈ sigmaDom U hU z) {s : ℝ}
    (hs : s ∈ sigmaDom (sigmaRestartDriver U hU z tt) (sigmaRestartDriver_continuous hU z tt)
      (restartPoint U hU z tt)) :
    argPath (sigmaRestartDriver U hU z tt) (sigmaRestartDriver_continuous hU z tt)
        (restartPoint U hU z tt)
        (sigmaTime (sigmaRestartDriver U hU z tt) (sigmaRestartDriver_continuous hU z tt)
          (restartPoint U hU z tt) s) -
      argPath (sigmaRestartDriver U hU z tt) (sigmaRestartDriver_continuous hU z tt)
        (restartPoint U hU z tt) 0 =
    argPath U hU z (sigmaTime U hU z (tt + s)) - argPath U hU z (sigmaTime U hU z tt) := by
  rw [restartPoint_eq ht] at hs ⊢
  have := argPath_restart_sigma hU (restartTime_mem_lifeSet ht) (restartScale_pos ht) hs
  rw [coe_restartTime ht, clock_sigmaTime hU ht] at this
  exact this

/-- **(iii)** The log-modulus increments agree:
`log |f^V_{σ^V(s)}(z')| = log |f^U_{σ^U(t̃ + s)}(z)| - log |f^U_T(z)|`, `T = σ_z(t̃)`. -/
theorem restart_log_norm (ht : tt ∈ sigmaDom U hU z) {s : ℝ}
    (hs : s ∈ sigmaDom (sigmaRestartDriver U hU z tt) (sigmaRestartDriver_continuous hU z tt)
      (restartPoint U hU z tt)) :
    Real.log ‖fPath (sigmaRestartDriver U hU z tt) (sigmaRestartDriver_continuous hU z tt)
        (restartPoint U hU z tt)
        (sigmaTime (sigmaRestartDriver U hU z tt) (sigmaRestartDriver_continuous hU z tt)
          (restartPoint U hU z tt) s)‖ =
      Real.log ‖fPath U hU z (sigmaTime U hU z (tt + s))‖ -
        Real.log ‖fPath U hU z (sigmaTime U hU z tt)‖ := by
  rw [restartPoint_eq ht] at hs ⊢
  have := log_norm_fPath_restart_sigma hU (restartTime_mem_lifeSet ht) (restartScale_pos ht) hs
  rw [coe_restartTime ht, clock_sigmaTime hU ht] at this
  rw [coe_restartScale] at this
  exact this

end ComplexSLE.Internal.Polar

end
