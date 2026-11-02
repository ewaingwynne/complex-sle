/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.ItoReal
public import ComplexSLE.Internal.Stationary.Coefficients
public import ComplexSLE.Internal.Polar.PolarThetaHat
public import ComplexSLE.Internal.Polar.PolarContMeas

/-!
# `θ̂(e^{iu})` as a solution of the one-noise martingale problem

For `a, b > 0`, `c² ≤ ab` and an adapted SLE_Σ driver `U`, the time-changed argument
`θ̂ = θ̂(e^{iu})` (`Polar.thetaHat`) solves the martingale problem `(2.25)` for the periodic
coefficients `α = µ`, `β² = 2D` (`Polar.isDiffusionSolution_thetaHat`).

* `IsDiffusionSolution` only depends on `β` through `β²` (`isDiffusionSolution_congr_sq`), so
  `θ̂(e^{iu})` solves the problem for every `β` with `β² = 2D`
  (`isDiffusionSolution_thetaHat_of_sq`);
* `ae_thetaHat_zero`, `thetaHat_zero_ae`: the start of `θ̂(e^{iu})` is a.s. the representative of
  `u` in `[0, 2π)` (resp. `argInit` of the zero driver).

Uses no external input beyond those of the polar layer.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set Function Real

namespace ComplexSLE.Internal

/-! ### `IsDiffusionSolution`: dependence on `β²` -/

section Solution

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m} {P : Measure Ω}
  {α β β' : ℝ → ℝ} {X : ℝ≥0 → Ω → ℝ}

/-- `IsDiffusionSolution` depends on `β` only through `β²`. -/
theorem isDiffusionSolution_congr_sq (h : ∀ u, β' u ^ 2 = β u ^ 2) :
    IsDiffusionSolution ℱ α β' X P ↔ IsDiffusionSolution ℱ α β X P := by
  unfold IsDiffusionSolution
  simp only [h]

end Solution

/-! ### The start of `θ̂` -/

open Polar

section Start

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

theorem unitPt_ne_zero (u : ℝ) : unitPt u ≠ 0 := by
  unfold unitPt
  exact Complex.exp_ne_zero _

theorem norm_unitPt (u : ℝ) : ‖unitPt u‖ = 1 := by
  unfold unitPt
  exact Complex.norm_exp_ofReal_mul_I u

/-- The start of `θ̂(e^{iu})` is a.s. the representative of `u` in `[0, 2π)`. -/
theorem ae_thetaHat_zero [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ)
    (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (u : ℝ) :
    ∀ᵐ ω ∂P, thetaHat hU (unitPt u) 0 ω = toIcoMod Real.two_pi_pos 0 u := by
  filter_upwards [hU.toIsSLEDriver.zero,
    ae_thetaHat_eq_and_continuous hU ha hc (unitPt_ne_zero u)] with ω h0 hω
  have hmem := hω.1 0
  have hz : (0 : ℝ) ∈ lifeSet (fun r => U r ω) (unitPt u) :=
    ne_driver_zero_of_mem_sigmaDomSet hmem
  rw [thetaHat_of_mem hU hmem, NNReal.coe_zero, sigmaTime_zero (hU.cont ω) hz]
  have hIco := argPath_zero_mem_Ico (hU.cont ω) (unitPt u)
  have hexp := exp_argPath_mul_I (hU.cont ω) hz
  rw [fPath_zero, h0, sub_zero, norm_unitPt, Complex.ofReal_one, div_one] at hexp
  have hexp' : Complex.exp ((argPath (fun r => U r ω) (hU.cont ω) (unitPt u) 0 : ℂ) * Complex.I) =
      Complex.exp ((u : ℂ) * Complex.I) := hexp
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 hexp'
  symm
  rw [toIcoMod_eq_iff]
  refine ⟨by simpa using hIco, -n, ?_⟩
  have hπ : (2 * (π : ℂ) * Complex.I) = ((2 * π : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hπ] at hn
  have hn'' : argPath (fun r => U r ω) (hU.cont ω) (unitPt u) 0 = u + n * (2 * π) := by
    have := congrArg Complex.im hn
    simpa using this
  rw [hn'']
  simp [zsmul_eq_mul]

/-- `θ̂_0(z)` is almost surely the deterministic representative of `arg z` in `[0, 2π)`
(`argInit` of the zero driver). -/
theorem thetaHat_zero_ae [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ)
    (ha : 0 < a) (hc : c ^ 2 ≤ a * b) {z : ℂ} (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, thetaHat hU z 0 ω = argInit (fun _ => (0 : ℂ)) continuous_const z := by
  filter_upwards [hU.toIsSLEDriver.zero, ae_thetaHat_eq_and_continuous hU ha hc hz] with ω h0 hω
  have hmem := hω.1 0
  have hz' : (0 : ℝ) ∈ lifeSet (fun r => U r ω) z :=
    zero_mem_lifeSet_iff.2 (pos_absorbingTime_of_mem_sigmaDom (hU.cont ω) hmem)
  rw [thetaHat_of_mem hU hmem, NNReal.coe_zero, sigmaTime_zero (hU.cont ω) hz', argPath_zero,
    argInit_eq (hU.cont ω) z, argInit_eq continuous_const z, h0]

end Start

/-! ### `θ̂(e^{iu})` for any `β` with `β² = 2D` -/

section Solutions

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- `θ̂(e^{iu})` solves the martingale problem for `(µ, β)` for any `β` with `β² = 2D`. -/
theorem isDiffusionSolution_thetaHat_of_sq [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {β : ℝ → ℝ} (hβsq : ∀ u, β u ^ 2 = 2 * diffusionD a b c u) (u : ℝ) :
    IsDiffusionSolution (sigmaFiltration hU (unitPt u)) (mu a b c) β (thetaHat hU (unitPt u)) P :=
  (isDiffusionSolution_congr_sq (α := mu a b c) (β := fun v => √(2 * diffusionD a b c v))
    (β' := β) (ℱ := sigmaFiltration hU (unitPt u)) (X := thetaHat hU (unitPt u)) (P := P)
    fun v => by
      rw [hβsq v, Real.sq_sqrt (by have := diffusionD_nonneg ha hb hc v; positivity)]).2
    (isDiffusionSolution_thetaHat hU ha hc (unitPt_ne_zero u))

end Solutions

end ComplexSLE.Internal

end
