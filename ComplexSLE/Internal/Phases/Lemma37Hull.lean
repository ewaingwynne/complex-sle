/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.LeftHull
public import ComplexSLE.Internal.Polar.PolarRestartSigma
public import ComplexSLE.Internal.Stationary.PathStatNeg
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Lemma 3.9 (`lem-computation`), deterministic half: the future hull after the restart (M7/E1)

For a continuous driver `U`, a point `z`, and times `t̃, s̃ ≥ 0` put (`paper.tex:L1506-1548`)

* `t = σ_z(t̃)` and `t + s = σ_z(s̃ + t̃)`, so `s = σ_z(s̃ + t̃) - σ_z(t̃)`;
* the *future hull* `L_{t,s+t} = leftHull (r ↦ U(r + t) - U t) s` (the hull of the concatenation
  property (2.3), `ComplexSLE.concatenation_leftHull`).

The two quantities compared in Lemma 3.9 are

* `futureDistRatio U hU z t̃ s̃ = dist(f_t(z), L_{t,s+t}) / |f_t(z)|` (with
  `f_t(z) = fPath U hU z t`, which equals `centeredLoewnerMap U hU t ⟨z, _⟩`,
  `centeredLoewnerMap_eq_fPath`), and
* `hullDist U hU z s̃ = dist(z, L_{σ_z(s̃)})`.

Both use the project's junk convention off the domain of `σ_z` (an almost sure event, Remark 2.12).

* `futureDistRatio_eq_hullDist_restart` (the pathwise identity behind Lemma 3.9): if `t̃` and
  `t̃ + s̃` lie in the domain of `σ_z`, then `futureDistRatio U hU z t̃ s̃` equals
  `hullDist V hV z' s̃` for the rescaled shifted driver `V = sigmaRestartDriver U hU z t̃`
  (`V_s = |f_t(z)|⁻¹ (U_{t + |f_t(z)|² s} - U_t)`) and the direction `z' = f_t(z)/|f_t(z)|`
  (`restartPoint`). The proof is the scaling relation of left hulls (`leftHull_scale`) together
  with the clock identity `σ^V_{z'}(s̃) = (σ_z(s̃ + t̃) - σ_z(t̃)) / |f_t(z)|²`
  (`restart_sigmaTime`).

No external input is used.
-/

@[expose] public section

open scoped NNReal ENNReal Real
open Set Metric
open scoped Pointwise

namespace ComplexSLE.Internal

open Polar

variable {U : ℝ≥0 → ℂ}

/-- **The left side of Lemma 3.9.** With `t = σ_z(t̃)` and `t + s = σ_z(s̃ + t̃)`, the quantity
`dist(f_t(z), L_{t,s+t}) / |f_t(z)|`, where `L_{t,s+t}` is the left hull of the future driver
`r ↦ U(r + t) - U t` at time `s`. -/
noncomputable def futureDistRatio (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ)
    (tt ss : ℝ≥0) : ℝ :=
  infDist (fPath U hU z (sigmaTime U hU z tt))
      (leftHull (fun r => U (r + (sigmaTime U hU z tt).toNNReal) -
          U (sigmaTime U hU z tt).toNNReal)
        (sigmaTime U hU z ((ss : ℝ) + tt) - sigmaTime U hU z tt).toNNReal) /
    ‖fPath U hU z (sigmaTime U hU z tt)‖

/-- **The right side of Lemma 3.9.** `dist(z, L_{σ_z(s̃)})`. -/
noncomputable def hullDist (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ)
    (ss : ℝ≥0) : ℝ :=
  infDist z (leftHull U (sigmaTime U hU z ss).toNNReal)

/-! ### The restart identity -/

theorem leftHull_restart_sigma {tt : ℝ≥0} {z : ℂ} (hU : Continuous U)
    (ht : (tt : ℝ) ∈ sigmaDom U hU z) (s : ℝ≥0)
    (hts : (s : ℝ) + tt ∈ sigmaDom U hU z) :
    leftHull (sigmaRestartDriver U hU z tt)
        (sigmaTime (sigmaRestartDriver U hU z tt) (sigmaRestartDriver_continuous hU z tt)
          (restartPoint U hU z tt) s).toNNReal =
      ((restartScale U hU z tt : ℝ≥0) : ℂ)⁻¹ •
        leftHull (fun r => U (r + (sigmaTime U hU z tt).toNNReal) -
            U (sigmaTime U hU z tt).toNNReal)
          (sigmaTime U hU z ((s : ℝ) + tt) - sigmaTime U hU z tt).toNNReal := by
  set T := restartTime U hU z tt with hTdef
  set r := restartScale U hU z tt with hrdef
  have hr : 0 < r := restartScale_pos ht
  have hrne : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hss : (s : ℝ) ∈ sigmaDom (sigmaRestartDriver U hU z tt)
      (sigmaRestartDriver_continuous hU z tt) (restartPoint U hU z tt) :=
    (mem_sigmaDom_restart_sigma ht).2 ⟨s.coe_nonneg, by rwa [add_comm] at hts⟩
  have hσ := restart_sigmaTime ht hss
  rw [add_comm (tt : ℝ) (s : ℝ), ← hrdef] at hσ
  have hσ0 := sigmaTime_nonneg (sigmaRestartDriver_continuous hU z tt) hss
  have hnn : 0 ≤ sigmaTime U hU z ((s : ℝ) + tt) - sigmaTime U hU z tt := by
    have h := mul_nonneg hσ0 (sq_nonneg (r : ℝ))
    rwa [hσ, div_mul_cancel₀ _ (pow_ne_zero 2 hrne)] at h
  have hscale : (sigmaTime (sigmaRestartDriver U hU z tt) (sigmaRestartDriver_continuous hU z tt)
      (restartPoint U hU z tt) s).toNNReal / (r⁻¹) ^ 2 =
      (sigmaTime U hU z ((s : ℝ) + tt) - sigmaTime U hU z tt).toNNReal := by
    apply NNReal.coe_injective
    rw [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_inv, Real.coe_toNNReal _ hσ0, hσ,
      Real.coe_toNNReal _ hnn]
    field_simp
  have hT : (T : ℝ) = sigmaTime U hU z tt := coe_restartTime ht
  have key : ∀ x : ℝ≥0, leftHull (sigmaRestartDriver U hU z tt) x =
      ((r⁻¹ : ℝ≥0) : ℂ) • leftHull (fun x => U (x + T) - U T) (x / (r⁻¹) ^ 2) := by
    intro x
    rw [show sigmaRestartDriver U hU z tt = _ from restartDriver_eq_scale_shift U T hr,
      leftHull_scale (fun x => U (x + T) - U T) r⁻¹ (inv_pos.2 hr) x, ← Set.image_smul]
    rfl
  rw [key, hscale]
  have hTn : (sigmaTime U hU z tt).toNNReal = T := by rw [← hT, Real.toNNReal_coe]
  rw [hTn]
  congr 1
  push_cast
  rfl

/-- **The pathwise identity behind Lemma 3.9.** If `t̃` and `s̃ + t̃` lie in the domain of `σ_z`,
the left side `dist(f_t(z), L_{t,s+t}) / |f_t(z)|` equals `dist(z', L^V_{σ^V_{z'}(s̃)})` for the
rescaled shifted driver `V = sigmaRestartDriver U hU z t̃` and `z' = f_t(z)/|f_t(z)|`. -/
theorem futureDistRatio_eq_hullDist_restart (hU : Continuous U) {z : ℂ} {tt ss : ℝ≥0}
    (ht : (tt : ℝ) ∈ sigmaDom U hU z) (hts : (ss : ℝ) + tt ∈ sigmaDom U hU z) :
    futureDistRatio U hU z tt ss =
      hullDist (sigmaRestartDriver U hU z tt) (sigmaRestartDriver_continuous hU z tt)
        (restartPoint U hU z tt) ss := by
  unfold futureDistRatio hullDist
  rw [leftHull_restart_sigma hU ht ss hts]
  have hpos : 0 < ‖fPath U hU z (sigmaTime U hU z tt)‖ :=
    norm_fPath_pos hU (sigmaTime_mem_lifeSet hU ht)
  have hc : ((restartScale U hU z tt : ℝ≥0) : ℂ) =
      ((‖fPath U hU z (sigmaTime U hU z tt)‖ : ℝ) : ℂ) := by
    rw [← coe_restartScale]
  have hpt : restartPoint U hU z tt = (((restartScale U hU z tt : ℝ≥0) : ℂ))⁻¹ •
      fPath U hU z (sigmaTime U hU z tt) := by
    unfold restartPoint
    rw [hc, smul_eq_mul, div_eq_inv_mul]
  have hne : (((restartScale U hU z tt : ℝ≥0) : ℂ))⁻¹ ≠ 0 := by
    rw [hc]; exact inv_ne_zero (by exact_mod_cast hpos.ne')
  rw [hpt, infDist_smul₀ hne, hc, norm_inv, Complex.norm_real, norm_norm, div_eq_inv_mul]

end ComplexSLE.Internal

end
