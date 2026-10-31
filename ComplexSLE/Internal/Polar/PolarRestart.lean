/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Loewner.Concatenation
public import ComplexSLE.Internal.Loewner.Transform
public import ComplexSLE.Internal.Polar.Path

/-!
# Deterministic restart identity (M7/A4b): the restarted and rescaled chain

For a continuous driver `U`, a point `z` and a time `T ∈ [0, T_z)` (as an element of `ℝ≥0`), put
`w = f_T(z) = g_T(z) - U_T ≠ 0` and, for a scale `r > 0`,

* the restarted and rescaled driver `V_s = r⁻¹ (U_{T + r² s} - U_T)` (`restartDriver`), which is
  continuous, `V_0 = 0`;
* the restarted starting point `z' = r⁻¹ w` (`restartPt`); for `r = |w|` this is `w / |w|`
  (`restartPoint`), a point of the unit circle.

This file proves, for every `r > 0`, the *future dependence* and *scale invariance* of the Loewner
solution (concatenation (2.3) and scaling, `paper.tex:L559-565`):

* `absorbingTime_restart`: `T_{z'}(V) = (T_z(U) - T) / r²` in `ℝ≥0∞`;
* `mem_lifeSet_restart`: `s ∈ [0, T_{z'}(V))` iff `s ≥ 0` and `T + r² s ∈ [0, T_z(U))`;
* `fPath_restart`: `f^V_s(z') = r⁻¹ f^U_{T + r² s}(z)` on the life set of `(V, z')`.

The clock and σ-time identities are in `PolarRestartClock.lean`, the polar data (argument and
log-modulus) in `PolarRestartPolar.lean`. Everything is deterministic and uses no external input.
-/

public section

open scoped NNReal ENNReal
open Set

namespace ComplexSLE.Internal.Polar

variable {U : ℝ≥0 → ℂ}

/-! ### The restarted driver and starting point -/

/-- The restarted and rescaled driver `V_s = r⁻¹ (U_{T + r² s} - U_T)`. -/
@[expose] noncomputable def restartDriver (U : ℝ≥0 → ℂ) (T r : ℝ≥0) : ℝ≥0 → ℂ :=
  fun s => (r : ℂ)⁻¹ * (U (T + r ^ 2 * s) - U T)

theorem restartDriver_apply (U : ℝ≥0 → ℂ) (T r s : ℝ≥0) :
    restartDriver U T r s = (r : ℂ)⁻¹ * (U (T + r ^ 2 * s) - U T) := rfl

theorem restartDriver_zero (U : ℝ≥0 → ℂ) (T r : ℝ≥0) : restartDriver U T r 0 = 0 := by
  simp [restartDriver]

theorem restartDriver_continuous (hU : Continuous U) (T r : ℝ≥0) :
    Continuous (restartDriver U T r) := by
  unfold restartDriver
  fun_prop

/-- The restarted starting point `z' = r⁻¹ f_T(z)`. -/
@[expose] noncomputable def restartPt (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) (T r : ℝ≥0) : ℂ :=
  (r : ℂ)⁻¹ * fPath U hU z T

/-- The restarted driver is the composite of the shift `U ↦ U (· + T) - U T` and the scaling
`W ↦ r⁻¹ W(·/r⁻²)` of `Loewner/Transform.lean`. -/
theorem restartDriver_eq_scale_shift (U : ℝ≥0 → ℂ) (T : ℝ≥0) {r : ℝ≥0} (hr : 0 < r) :
    restartDriver U T r = fun s =>
      ((r⁻¹ : ℝ≥0) : ℂ) * ((fun x => U (x + T) - U T) (s / (r⁻¹) ^ 2)) := by
  funext s
  have hr0 : r ≠ 0 := hr.ne'
  have h : s / (r⁻¹) ^ 2 + T = T + r ^ 2 * s := by
    rw [inv_pow, div_inv_eq_mul, add_comm, mul_comm]
  simp only [restartDriver]
  rw [h]
  simp

theorem toNNReal_restart {T r : ℝ≥0} {s : ℝ} (hs : 0 ≤ s) :
    ((T : ℝ) + (r : ℝ) ^ 2 * s).toNNReal = T + r ^ 2 * s.toNNReal := by
  apply NNReal.coe_injective
  rw [Real.coe_toNNReal _ (by positivity)]
  push_cast
  rw [Real.coe_toNNReal _ hs]

theorem ofReal_restart {T r : ℝ≥0} {s : ℝ} (hs : 0 ≤ s) :
    ENNReal.ofReal ((T : ℝ) + (r : ℝ) ^ 2 * s) =
      (T : ℝ≥0∞) + ((r ^ 2 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal s := by
  rw [ENNReal.ofReal_add (NNReal.coe_nonneg T) (by positivity), ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_mul (sq_nonneg _)]
  congr 2
  rw [← NNReal.coe_pow, ENNReal.ofReal_coe_nnreal]

/-! ### The absorbing time and the life set of the restarted chain -/

/-- **Absorbing time of the restarted chain** (`(i)`): `T_{z'}(V) = (T_z(U) - T) / r²`. -/
theorem absorbingTime_restart (hU : Continuous U) {z : ℂ} {T : ℝ≥0} (hT : (T : ℝ) ∈ lifeSet U z)
    {r : ℝ≥0} (hr : 0 < r) :
    absorbingTime (restartDriver U T r) (restartPt U hU z T r) =
      (absorbingTime U z - (T : ℝ≥0∞)) / ((r ^ 2 : ℝ≥0) : ℝ≥0∞) := by
  have hz : z ∈ (leftHull U T)ᶜ := coe_mem_lifeSet_iff.1 hT
  have h1 := absorbingTime_eq_add_shift hU T z hz
  rw [centeredLoewnerMap_eq_fPath hU T hz] at h1
  have hrinv : 0 < r⁻¹ := inv_pos.2 hr
  have h2 := absorbingTime_scale (fun x => U (x + T) - U T) (fPath U hU z T) r⁻¹ hrinv
  have hpt : restartPt U hU z T r = ((r⁻¹ : ℝ≥0) : ℂ) * fPath U hU z T := by
    simp [restartPt]
  rw [restartDriver_eq_scale_shift U T hr, hpt, h2,
    ← ENNReal.sub_eq_of_eq_add_rev ENNReal.coe_ne_top h1, ENNReal.div_eq_inv_mul]
  have hr2 : (r ^ 2 : ℝ≥0) ≠ 0 := pow_ne_zero 2 hr.ne'
  rw [inv_pow, ENNReal.coe_inv hr2]

/-- The multiplicative form of `absorbingTime_restart`: `r² T_{z'}(V) = T_z(U) - T`. -/
theorem sq_mul_absorbingTime_restart (hU : Continuous U) {z : ℂ} {T : ℝ≥0}
    (hT : (T : ℝ) ∈ lifeSet U z) {r : ℝ≥0} (hr : 0 < r) :
    ((r ^ 2 : ℝ≥0) : ℝ≥0∞) * absorbingTime (restartDriver U T r) (restartPt U hU z T r) =
      absorbingTime U z - (T : ℝ≥0∞) := by
  rw [absorbingTime_restart hU hT hr, ENNReal.mul_div_cancel]
  · simpa using hr.ne'
  · exact ENNReal.coe_ne_top

/-- **Life set of the restarted chain** (`(i)`): `s ∈ [0, T_{z'}(V))` iff `s ≥ 0` and
`T + r² s ∈ [0, T_z(U))`. -/
theorem mem_lifeSet_restart (hU : Continuous U) {z : ℂ} {T : ℝ≥0} (hT : (T : ℝ) ∈ lifeSet U z)
    {r : ℝ≥0} (hr : 0 < r) {s : ℝ} :
    s ∈ lifeSet (restartDriver U T r) (restartPt U hU z T r) ↔
      0 ≤ s ∧ (T : ℝ) + (r : ℝ) ^ 2 * s ∈ lifeSet U z := by
  have hr2 : ((r ^ 2 : ℝ≥0) : ℝ≥0∞) ≠ 0 := by simpa using hr.ne'
  rw [mem_lifeSet, absorbingTime_restart hU hT hr]
  constructor
  · rintro ⟨hs, hlt⟩
    refine ⟨hs, by positivity, ?_⟩
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl hr2) (Or.inl ENNReal.coe_ne_top), lt_tsub_iff_left,
      mul_comm] at hlt
    rw [ofReal_restart hs]
    exact hlt
  · rintro ⟨hs, -, hlt⟩
    refine ⟨hs, ?_⟩
    rw [ofReal_restart hs] at hlt
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl hr2) (Or.inl ENNReal.coe_ne_top), lt_tsub_iff_left,
      mul_comm]
    exact hlt

theorem zero_mem_lifeSet_restart (hU : Continuous U) {z : ℂ} {T : ℝ≥0}
    (hT : (T : ℝ) ∈ lifeSet U z) {r : ℝ≥0} (hr : 0 < r) :
    (0 : ℝ) ∈ lifeSet (restartDriver U T r) (restartPt U hU z T r) :=
  (mem_lifeSet_restart hU hT hr).2 ⟨le_rfl, by simpa using hT⟩

/-- Every `v ∈ [T, T_z)` is `T + r² s` for a unique `s` in the life set of the restarted chain. -/
theorem exists_mem_lifeSet_restart (hU : Continuous U) {z : ℂ} {T : ℝ≥0}
    (hT : (T : ℝ) ∈ lifeSet U z) {r : ℝ≥0} (hr : 0 < r) {v : ℝ} (hv : v ∈ lifeSet U z)
    (hTv : (T : ℝ) ≤ v) :
    ∃ s ∈ lifeSet (restartDriver U T r) (restartPt U hU z T r), (T : ℝ) + (r : ℝ) ^ 2 * s = v ∧
      s = (v - T) / (r : ℝ) ^ 2 := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hs0 : 0 ≤ (v - T) / (r : ℝ) ^ 2 := div_nonneg (sub_nonneg.2 hTv) (by positivity)
  have hv' : (T : ℝ) + (r : ℝ) ^ 2 * ((v - T) / (r : ℝ) ^ 2) = v := by
    field_simp
    ring
  refine ⟨(v - T) / (r : ℝ) ^ 2, (mem_lifeSet_restart hU hT hr).2 ⟨hs0, by rwa [hv']⟩, hv', rfl⟩

/-! ### The restarted solution and the path `f` of the restarted chain -/

/-- The candidate solution `s ↦ r⁻¹ (g_{T + r² s}(z) - U_T)` of the restarted problem. -/
@[expose] noncomputable def restartSol (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) (T r : ℝ≥0)
    (s : ℝ) : ℂ :=
  (r : ℂ)⁻¹ * (solPath U hU z ((T : ℝ) + (r : ℝ) ^ 2 * s) - U T)

/-- `restartSol` solves the Loewner problem for `(V, z')` up to the absorbing time of `(V, z')`. -/
theorem isLoewnerSolution_restart (hU : Continuous U) {z : ℂ} {T : ℝ≥0}
    (hT : (T : ℝ) ∈ lifeSet U z) {r : ℝ≥0} (hr : 0 < r) :
    IsLoewnerSolution (restartDriver U T r) (restartPt U hU z T r)
      (absorbingTime (restartDriver U T r) (restartPt U hU z T r)) (restartSol U hU z T r) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  refine ⟨?_, fun s hs hsτ => ?_⟩
  · simp [restartSol, restartPt, fPath]
  · obtain ⟨-, hu⟩ := (mem_lifeSet_restart hU hT hr).1 (show s ∈ lifeSet _ _ from ⟨hs, hsτ⟩)
    obtain ⟨hne, hd⟩ := (solPath_isLoewnerSolution hU z).2 _ hu.1 hu.2
    rw [toNNReal_restart hs] at hne hd
    have hdiff : restartSol U hU z T r s - restartDriver U T r s.toNNReal =
        (r : ℂ)⁻¹ * (solPath U hU z ((T : ℝ) + (r : ℝ) ^ 2 * s) -
          U (T + r ^ 2 * s.toNNReal)) := by
      simp only [restartSol, restartDriver]
      ring
    have hne' : solPath U hU z ((T : ℝ) + (r : ℝ) ^ 2 * s) - U (T + r ^ 2 * s.toNNReal) ≠ 0 :=
      sub_ne_zero.2 hne
    refine ⟨?_, ?_⟩
    · intro h
      rw [← sub_eq_zero, hdiff] at h
      exact hne' ((mul_eq_zero.1 h).resolve_left (inv_ne_zero hrc))
    · have hh : HasDerivWithinAt (fun x : ℝ => (T : ℝ) + (r : ℝ) ^ 2 * x) ((r : ℝ) ^ 2)
          (Ici 0) s := by
        simpa using ((hasDerivWithinAt_id s (Ici 0)).const_mul ((r : ℝ) ^ 2)).const_add (T : ℝ)
      have hmaps : MapsTo (fun x : ℝ => (T : ℝ) + (r : ℝ) ^ 2 * x) (Ici 0) (Ici 0) := fun x hx =>
        add_nonneg (NNReal.coe_nonneg T) (mul_nonneg (sq_nonneg _) hx)
      have h2 := ((hd.scomp s hh hmaps).sub_const (U T)).const_mul (r : ℂ)⁻¹
      refine h2.congr_deriv ?_
      rw [hdiff]
      simp only [Complex.real_smul]
      push_cast
      field_simp

/-- On the life set of `(V, z')`, the solution path of `(V, z')` is `restartSol`. -/
theorem solPath_restart (hU : Continuous U) {z : ℂ} {T : ℝ≥0} (hT : (T : ℝ) ∈ lifeSet U z)
    {r : ℝ≥0} (hr : 0 < r) {s : ℝ}
    (hs : s ∈ lifeSet (restartDriver U T r) (restartPt U hU z T r)) :
    solPath (restartDriver U T r) (restartDriver_continuous hU T r) (restartPt U hU z T r) s =
      restartSol U hU z T r s :=
  (loewner_wellDefined (restartDriver U T r) (restartDriver_continuous hU T r)
    (restartPt U hU z T r)).2 _ _ _
    (solPath_isLoewnerSolution (restartDriver_continuous hU T r) (restartPt U hU z T r))
    (isLoewnerSolution_restart hU hT hr) hs

/-- **Future dependence and scale invariance** (`(i)`): on the life set of the restarted chain,
`f^V_s(z') = r⁻¹ f^U_{T + r² s}(z)`. -/
theorem fPath_restart (hU : Continuous U) {z : ℂ} {T : ℝ≥0} (hT : (T : ℝ) ∈ lifeSet U z)
    {r : ℝ≥0} (hr : 0 < r) {s : ℝ}
    (hs : s ∈ lifeSet (restartDriver U T r) (restartPt U hU z T r)) :
    fPath (restartDriver U T r) (restartDriver_continuous hU T r) (restartPt U hU z T r) s =
      (r : ℂ)⁻¹ * fPath U hU z ((T : ℝ) + (r : ℝ) ^ 2 * s) := by
  have hs0 : 0 ≤ s := hs.1
  unfold fPath
  rw [solPath_restart hU hT hr hs, toNNReal_restart hs0]
  simp only [restartSol, restartDriver]
  ring

theorem fPath_restart_zero (hU : Continuous U) (z : ℂ) (T r : ℝ≥0) :
    fPath (restartDriver U T r) (restartDriver_continuous hU T r) (restartPt U hU z T r) 0 =
      restartPt U hU z T r := by
  rw [fPath_zero]
  simp [restartDriver_zero]

theorem norm_fPath_restart (hU : Continuous U) {z : ℂ} {T : ℝ≥0} (hT : (T : ℝ) ∈ lifeSet U z)
    {r : ℝ≥0} (hr : 0 < r) {s : ℝ}
    (hs : s ∈ lifeSet (restartDriver U T r) (restartPt U hU z T r)) :
    ‖fPath (restartDriver U T r) (restartDriver_continuous hU T r) (restartPt U hU z T r) s‖ =
      (r : ℝ)⁻¹ * ‖fPath U hU z ((T : ℝ) + (r : ℝ) ^ 2 * s)‖ := by
  rw [fPath_restart hU hT hr hs, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg
    (NNReal.coe_nonneg r)]

end ComplexSLE.Internal.Polar

end
