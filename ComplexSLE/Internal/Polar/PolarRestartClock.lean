/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.PolarRestart
public import ComplexSLE.Internal.Polar.Sigma

/-!
# Deterministic restart identity (M7/A4b): the clock and the σ-time of the restarted chain

Continuation of `PolarRestart.lean`. With `V = restartDriver U T r`, `z' = restartPt U hU z T r`
and `T ∈ [0, T_z)` (as an element of `ℝ≥0`), the clock `A(t) = ∫₀ᵗ |f_u|⁻² du` of the restarted
chain is the increment of the clock of the original chain, *independent of the scale `r`*
(`clock_restart`; the clock is scale invariant):

  `A^V_{z'}(s) = A^U_z(T + r² s) - A^U_z(T)`.

Consequently, writing `t̃ = A^U_z(T)` (so `T = σ_z(t̃)` when `t̃ ∈ sigmaDom`), the domain of `σ` of
the restarted chain is the translate `{s ≥ 0 | t̃ + s ∈ sigmaDom U z}` (`mem_sigmaDom_restart`) and
`σ^V_{z'}(s) = (σ^U_z(t̃ + s) - T) / r²` (`sigmaTime_restart`).
-/

public section

open scoped NNReal ENNReal
open Set

namespace ComplexSLE.Internal.Polar

variable {U : ℝ≥0 → ℂ}

/-! ### The clock -/

theorem clockRate_restart (hU : Continuous U) {z : ℂ} {T : ℝ≥0} (hT : (T : ℝ) ∈ lifeSet U z)
    {r : ℝ≥0} (hr : 0 < r) {s : ℝ}
    (hs : s ∈ lifeSet (restartDriver U T r) (restartPt U hU z T r)) :
    clockRate (restartDriver U T r) (restartDriver_continuous hU T r) (restartPt U hU z T r) s =
      (r : ℝ) ^ 2 * clockRate U hU z ((T : ℝ) + (r : ℝ) ^ 2 * s) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  unfold clockRate
  rw [norm_fPath_restart hU hT hr hs, mul_pow, mul_inv, inv_pow, inv_inv]

/-- **The clock is scale invariant** (`(ii)`): `A^V_{z'}(s) = A^U_z(T + r² s) - A^U_z(T)`. -/
theorem clock_restart (hU : Continuous U) {z : ℂ} {T : ℝ≥0} (hT : (T : ℝ) ∈ lifeSet U z)
    {r : ℝ≥0} (hr : 0 < r) {s : ℝ}
    (hs : s ∈ lifeSet (restartDriver U T r) (restartPt U hU z T r)) :
    clock (restartDriver U T r) (restartDriver_continuous hU T r) (restartPt U hU z T r) s =
      clock U hU z ((T : ℝ) + (r : ℝ) ^ 2 * s) - clock U hU z T := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hs0 : 0 ≤ s := hs.1
  have hu := ((mem_lifeSet_restart hU hT hr).1 hs).2
  have hint1 := intervalIntegrable_clockRate hU hu
  have hint2 := intervalIntegrable_clockRate hU hT
  have h1 : ∫ u in (0 : ℝ)..s,
      clockRate (restartDriver U T r) (restartDriver_continuous hU T r) (restartPt U hU z T r) u =
      ∫ u in (0 : ℝ)..s, (r : ℝ) ^ 2 * clockRate U hU z ((r : ℝ) ^ 2 * u + T) := by
    refine intervalIntegral.integral_congr fun u hu' => ?_
    rw [uIcc_of_le hs0] at hu'
    have hmem := mem_lifeSet_of_le hs hu'.1 hu'.2
    rw [clockRate_restart hU hT hr hmem, add_comm (T : ℝ)]
  unfold clock
  rw [h1, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_add (clockRate U hU z) (by positivity) (T : ℝ),
    intervalIntegral.integral_interval_sub_left hint1 hint2]
  simp only [mul_zero, zero_add, smul_eq_mul]
  rw [add_comm ((r : ℝ) ^ 2 * s) (T : ℝ)]
  field_simp

/-! ### Intermediate values of the clock; the domain of `σ` -/

/-- `sigmaDom` is the image of the life set under the clock. -/
theorem mem_sigmaDom_iff_exists_clock (hU : Continuous U) {z : ℂ} {s : ℝ} :
    s ∈ sigmaDom U hU z ↔ ∃ t ∈ lifeSet U z, clock U hU z t = s :=
  ⟨exists_clock_eq hU, fun ⟨_, ht, h⟩ => h ▸ clock_mem_sigmaDom hU ht⟩

theorem le_of_clock_le_clock (hU : Continuous U) {z : ℂ} {T v : ℝ} (hT : T ∈ lifeSet U z)
    (hv : v ∈ lifeSet U z) (h : clock U hU z T ≤ clock U hU z v) : T ≤ v := by
  by_contra hlt
  push Not at hlt
  exact absurd (clock_lt_clock hU hv.1 hlt hT) (not_lt.2 h)

/-- **The domain of `σ` of the restarted chain** (`(ii)`): with `t̃ = A^U_z(T)`,
`sigmaDom V z' = {s ≥ 0 | t̃ + s ∈ sigmaDom U z}`, i.e. the translate of
`sigmaDom U z ∩ [t̃, ∞)` by `-t̃`. -/
theorem mem_sigmaDom_restart (hU : Continuous U) {z : ℂ} {T : ℝ≥0} (hT : (T : ℝ) ∈ lifeSet U z)
    {r : ℝ≥0} (hr : 0 < r) {s : ℝ} :
    s ∈ sigmaDom (restartDriver U T r) (restartDriver_continuous hU T r)
        (restartPt U hU z T r) ↔
      0 ≤ s ∧ clock U hU z T + s ∈ sigmaDom U hU z := by
  rw [mem_sigmaDom_iff_exists_clock, mem_sigmaDom_iff_exists_clock]
  constructor
  · rintro ⟨u, hu, hus⟩
    obtain ⟨hu0, hu'⟩ := (mem_lifeSet_restart hU hT hr).1 hu
    have hs0 : 0 ≤ s := hus ▸ clock_nonneg (restartDriver_continuous hU T r) hu
    rw [clock_restart hU hT hr hu] at hus
    exact ⟨hs0, _, hu', by rw [← hus]; ring⟩
  · rintro ⟨hs0, v, hv, hvs⟩
    have hTv : (T : ℝ) ≤ v := le_of_clock_le_clock hU hT hv (by rw [hvs]; linarith)
    obtain ⟨u, hu, huv, -⟩ := exists_mem_lifeSet_restart hU hT hr hv hTv
    refine ⟨u, hu, ?_⟩
    rw [clock_restart hU hT hr hu, huv, hvs]
    ring

/-! ### The σ-time -/

/-- **σ-time of the restarted chain** (`(ii)`), additive form: for `s` in the domain of `σ^V_{z'}`,
`T + r² σ^V_{z'}(s) = σ^U_z(A^U_z(T) + s)`. -/
theorem sigmaTime_restart_aux (hU : Continuous U) {z : ℂ} {T : ℝ≥0} (hT : (T : ℝ) ∈ lifeSet U z)
    {r : ℝ≥0} (hr : 0 < r) {s : ℝ}
    (hs : s ∈ sigmaDom (restartDriver U T r) (restartDriver_continuous hU T r)
      (restartPt U hU z T r)) :
    sigmaTime (restartDriver U T r) (restartDriver_continuous hU T r) (restartPt U hU z T r) s ∈
        lifeSet (restartDriver U T r) (restartPt U hU z T r) ∧
      (T : ℝ) + (r : ℝ) ^ 2 *
        sigmaTime (restartDriver U T r) (restartDriver_continuous hU T r)
          (restartPt U hU z T r) s = sigmaTime U hU z (clock U hU z T + s) := by
  obtain ⟨hs0, hsU⟩ := (mem_sigmaDom_restart hU hT hr).1 hs
  set v := sigmaTime U hU z (clock U hU z T + s) with hv
  have hvmem : v ∈ lifeSet U z := sigmaTime_mem_lifeSet hU hsU
  have hvc : clock U hU z v = clock U hU z T + s := clock_sigmaTime hU hsU
  have hTv : (T : ℝ) ≤ v := le_of_clock_le_clock hU hT hvmem (by rw [hvc]; linarith)
  obtain ⟨u, hu, huv, -⟩ := exists_mem_lifeSet_restart hU hT hr hvmem hTv
  have hcu : clock (restartDriver U T r) (restartDriver_continuous hU T r)
      (restartPt U hU z T r) u = s := by
    rw [clock_restart hU hT hr hu, huv, hvc]
    ring
  have hσ := sigmaTime_eq_of_clock_eq (restartDriver_continuous hU T r) hu hcu
  rw [hσ]
  exact ⟨hu, huv⟩

/-- **σ-time of the restarted chain** (`(ii)`): for `s` in the domain of `σ^V_{z'}`,
`σ^V_{z'}(s) = (σ^U_z(A^U_z(T) + s) - T) / r²`. -/
theorem sigmaTime_restart (hU : Continuous U) {z : ℂ} {T : ℝ≥0} (hT : (T : ℝ) ∈ lifeSet U z)
    {r : ℝ≥0} (hr : 0 < r) {s : ℝ}
    (hs : s ∈ sigmaDom (restartDriver U T r) (restartDriver_continuous hU T r)
      (restartPt U hU z T r)) :
    sigmaTime (restartDriver U T r) (restartDriver_continuous hU T r) (restartPt U hU z T r) s =
      (sigmaTime U hU z (clock U hU z T + s) - T) / (r : ℝ) ^ 2 := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  rw [eq_div_iff (by positivity), ← (sigmaTime_restart_aux hU hT hr hs).2]
  ring

end ComplexSLE.Internal.Polar

end
