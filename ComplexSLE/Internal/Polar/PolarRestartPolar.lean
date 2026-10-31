/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.PolarRestartClock
public import ComplexSLE.Internal.Polar.Argument

/-!
# Deterministic restart identity (M7/A4b): the polar data of the restarted chain

Continuation of `PolarRestartClock.lean`. With `V = restartDriver U T r`, `z' = restartPt U hU z T r`
and `T ∈ [0, T_z)`, the continuous argument and the log-modulus of the restarted chain are
increments of those of the original chain, for every scale `r > 0`:

* `argPath_restart`: `θ^V_s(z') = θ^U_{T + r² s}(z) - θ^U_T(z) + θ^V_0(z')`, because the right side is
  continuous on the life set, a lift of `f^V_s(z')/|f^V_s(z')|`, and has initial value in `[0, 2π)`
  (uniqueness, `argPath_unique`); and `e^{iθ^V_0(z')} = e^{iθ^U_T(z)}`;
* `log_norm_fPath_restart`: `log |f^V_s(z')| = log |f^U_{T + r² s}(z)| - log r`;

and their σ-time versions on the domain of `σ^V_{z'}` (`argPath_restart_sigma`,
`log_norm_fPath_restart_sigma`), where `σ^V_{z'}(s)` corresponds to `σ^U_z(A^U_z(T) + s)`.
-/

public section

open scoped NNReal ENNReal Real
open Set Complex

namespace ComplexSLE.Internal.Polar

variable {U : ℝ≥0 → ℂ}

/-! ### The initial direction -/

/-- The initial direction of the restarted chain is the direction of `f_T(z)`:
`e^{iθ^V_0(z')} = e^{iθ^U_T(z)}`. -/
theorem exp_argPath_restart_zero (hU : Continuous U) {z : ℂ} {T : ℝ≥0}
    (hT : (T : ℝ) ∈ lifeSet U z) {r : ℝ≥0} (hr : 0 < r) :
    exp (argPath (restartDriver U T r) (restartDriver_continuous hU T r) (restartPt U hU z T r)
        0 * I) = exp (argPath U hU z (T : ℝ) * I) := by
  have h0 := zero_mem_lifeSet_restart hU hT hr
  rw [exp_argPath_mul_I (restartDriver_continuous hU T r) h0, exp_argPath_mul_I hU hT]
  have e1 := fPath_restart hU hT hr h0
  have e2 := norm_fPath_restart hU hT hr h0
  simp only [mul_zero, add_zero] at e1 e2
  rw [e2, e1]
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hn : (‖fPath U hU z (T : ℝ)‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_fPath_pos hU hT).ne'
  push_cast
  field_simp

/-! ### The argument -/

/-- **Polar data, argument** (`(iii)`): on the life set of the restarted chain,
`θ^V_s(z') = θ^U_{T + r² s}(z) - θ^U_T(z) + θ^V_0(z')`. -/
theorem argPath_restart (hU : Continuous U) {z : ℂ} {T : ℝ≥0} (hT : (T : ℝ) ∈ lifeSet U z)
    {r : ℝ≥0} (hr : 0 < r) {s : ℝ}
    (hs : s ∈ lifeSet (restartDriver U T r) (restartPt U hU z T r)) :
    argPath (restartDriver U T r) (restartDriver_continuous hU T r) (restartPt U hU z T r) s =
      argPath U hU z ((T : ℝ) + (r : ℝ) ^ 2 * s) - argPath U hU z (T : ℝ) +
        argPath (restartDriver U T r) (restartDriver_continuous hU T r)
          (restartPt U hU z T r) 0 := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  set hV := restartDriver_continuous hU T r with hVdef
  set θ : ℝ → ℝ := fun u => argPath U hU z ((T : ℝ) + (r : ℝ) ^ 2 * u) - argPath U hU z (T : ℝ) +
    argPath (restartDriver U T r) hV (restartPt U hU z T r) 0 with hθ
  have hmaps : MapsTo (fun u : ℝ => (T : ℝ) + (r : ℝ) ^ 2 * u)
      (lifeSet (restartDriver U T r) (restartPt U hU z T r)) (lifeSet U z) := fun u hu =>
    ((mem_lifeSet_restart hU hT hr).1 hu).2
  have hc : ContinuousOn θ (lifeSet (restartDriver U T r) (restartPt U hU z T r)) := by
    refine ContinuousOn.add (ContinuousOn.sub ?_ continuousOn_const) continuousOn_const
    exact (continuousOn_argPath hU z).comp (by fun_prop) hmaps
  have he : ∀ u ∈ lifeSet (restartDriver U T r) (restartPt U hU z T r),
      fPath (restartDriver U T r) hV (restartPt U hU z T r) u =
        ‖fPath (restartDriver U T r) hV (restartPt U hU z T r) u‖ * exp (θ u * I) := by
    intro u hu
    have hv : (T : ℝ) + (r : ℝ) ^ 2 * u ∈ lifeSet U z := hmaps hu
    rw [norm_fPath_restart hU hT hr hu, fPath_restart hU hT hr hu]
    have hexp : exp (θ u * I) = exp (argPath U hU z ((T : ℝ) + (r : ℝ) ^ 2 * u) * I) := by
      have h1 : θ u * I = argPath U hU z ((T : ℝ) + (r : ℝ) ^ 2 * u) * I +
          (argPath (restartDriver U T r) hV (restartPt U hU z T r) 0 * I -
            argPath U hU z (T : ℝ) * I) := by
        simp only [hθ]
        push_cast
        ring
      rw [h1, exp_add, exp_sub, exp_argPath_restart_zero hU hT hr]
      have : exp (argPath U hU z (T : ℝ) * I) ≠ 0 := exp_ne_zero _
      field_simp
    rw [hexp]
    conv_lhs => rw [fPath_eq_norm_mul_exp hU hv]
    push_cast
    ring
  have h0 : θ 0 ∈ Ico 0 (2 * π) := by
    have : θ 0 = argPath (restartDriver U T r) hV (restartPt U hU z T r) 0 := by
      simp [hθ]
    rw [this]
    exact argPath_zero_mem_Ico hV _
  exact (argPath_unique hV hc he h0 hs).symm

/-- **Polar data, log-modulus** (`(iii)`): on the life set of the restarted chain,
`log |f^V_s(z')| = log |f^U_{T + r² s}(z)| - log r`. -/
theorem log_norm_fPath_restart (hU : Continuous U) {z : ℂ} {T : ℝ≥0}
    (hT : (T : ℝ) ∈ lifeSet U z) {r : ℝ≥0} (hr : 0 < r) {s : ℝ}
    (hs : s ∈ lifeSet (restartDriver U T r) (restartPt U hU z T r)) :
    Real.log ‖fPath (restartDriver U T r) (restartDriver_continuous hU T r)
        (restartPt U hU z T r) s‖ =
      Real.log ‖fPath U hU z ((T : ℝ) + (r : ℝ) ^ 2 * s)‖ - Real.log (r : ℝ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hv := ((mem_lifeSet_restart hU hT hr).1 hs).2
  rw [norm_fPath_restart hU hT hr hs, Real.log_mul (inv_pos.2 hr').ne'
    (norm_fPath_pos hU hv).ne', Real.log_inv]
  ring

/-! ### σ-time versions -/

/-- **Polar data, argument, in σ-time** (`(iii)`): for `s` in the domain of `σ^V_{z'}`, with
`t̃ = A^U_z(T)`,
`θ^V_{σ^V(s)}(z') - θ^V_0(z') = θ^U_{σ^U(t̃ + s)}(z) - θ^U_T(z)`. -/
theorem argPath_restart_sigma (hU : Continuous U) {z : ℂ} {T : ℝ≥0}
    (hT : (T : ℝ) ∈ lifeSet U z) {r : ℝ≥0} (hr : 0 < r) {s : ℝ}
    (hs : s ∈ sigmaDom (restartDriver U T r) (restartDriver_continuous hU T r)
      (restartPt U hU z T r)) :
    argPath (restartDriver U T r) (restartDriver_continuous hU T r) (restartPt U hU z T r)
        (sigmaTime (restartDriver U T r) (restartDriver_continuous hU T r)
          (restartPt U hU z T r) s) -
      argPath (restartDriver U T r) (restartDriver_continuous hU T r) (restartPt U hU z T r) 0 =
    argPath U hU z (sigmaTime U hU z (clock U hU z T + s)) - argPath U hU z (T : ℝ) := by
  obtain ⟨hu, hσ⟩ := sigmaTime_restart_aux hU hT hr hs
  rw [argPath_restart hU hT hr hu, hσ]
  ring

/-- **Polar data, log-modulus, in σ-time** (`(iii)`): for `s` in the domain of `σ^V_{z'}`, with
`t̃ = A^U_z(T)`, `log |f^V_{σ^V(s)}(z')| = log |f^U_{σ^U(t̃ + s)}(z)| - log r`. -/
theorem log_norm_fPath_restart_sigma (hU : Continuous U) {z : ℂ} {T : ℝ≥0}
    (hT : (T : ℝ) ∈ lifeSet U z) {r : ℝ≥0} (hr : 0 < r) {s : ℝ}
    (hs : s ∈ sigmaDom (restartDriver U T r) (restartDriver_continuous hU T r)
      (restartPt U hU z T r)) :
    Real.log ‖fPath (restartDriver U T r) (restartDriver_continuous hU T r)
        (restartPt U hU z T r)
        (sigmaTime (restartDriver U T r) (restartDriver_continuous hU T r)
          (restartPt U hU z T r) s)‖ =
      Real.log ‖fPath U hU z (sigmaTime U hU z (clock U hU z T + s))‖ - Real.log (r : ℝ) := by
  obtain ⟨hu, hσ⟩ := sigmaTime_restart_aux hU hT hr hs
  rw [log_norm_fPath_restart hU hT hr hu, hσ]

end ComplexSLE.Internal.Polar

end
