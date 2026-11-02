/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.KernelBasic
public import ComplexSLE.Internal.Stationary.Coefficients
public import ComplexSLE.Internal.Polar.PolarThetaHat
public import ComplexSLE.Internal.Polar.PolarContMeas

/-!
# `θ̂(e^{iu})` as a solution of the one-noise martingale problem

For `a, b > 0`, `c² ≤ ab` and an adapted SLE_Σ driver `U`, the time-changed argument
`θ̂ = θ̂(e^{iu})` (`Polar.thetaHat`) solves the martingale problem `(2.25)` for the periodic
coefficients `α = µ`, `β² = 2D` (`Polar.isDiffusionSolution_thetaHat`).

* `IsDiffusionSolution` only depends on `β` through `β²` (`isDiffusionSolution_congr_sq`), and is
  invariant under a shift of the process by a period (`IsDiffusionSolution.add_const`);
* `ae_thetaHat_zero`: `θ̂_0(e^{iu}) = [u]_{2π}` a.s.;
* `isDiffusionSolution_thetaHat_of_sq`, `exists_thetaHat_solution`: `θ̂ + 2πk` solves the martingale
  problem from every real starting point.

Uses no external input beyond those of the polar layer.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set Function Real

namespace ComplexSLE.Internal

/-! ### `IsDiffusionSolution`: dependence on `β²` and period shifts -/

section Solution

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m} {P : Measure Ω}
  {α β β' : ℝ → ℝ} {X : ℝ≥0 → Ω → ℝ}

/-- `IsDiffusionSolution` depends on `β` only through `β²`. -/
theorem isDiffusionSolution_congr_sq (h : ∀ u, β' u ^ 2 = β u ^ 2) :
    IsDiffusionSolution ℱ α β' X P ↔ IsDiffusionSolution ℱ α β X P := by
  unfold IsDiffusionSolution
  simp only [h]

/-- A period shift of a solution is a solution (for `α` and `β²` periodic with that period). -/
theorem IsDiffusionSolution.add_const {d : ℝ} (hα : ∀ x, α (x + d) = α x)
    (hβ : ∀ x, β (x + d) ^ 2 = β x ^ 2) (hX : IsDiffusionSolution ℱ α β X P) :
    IsDiffusionSolution ℱ α β (fun t ω => X t ω + d) P := by
  obtain ⟨h1, h2, h3, h4⟩ := hX
  refine ⟨h1.add (isStronglyProgressive_const ℱ d), ?_, ?_, ?_⟩
  · filter_upwards [h2] with ω hω
    exact hω.add continuous_const
  · convert h3 using 2
    simp only [hα, add_sub_add_right_eq_sub]
  · convert h4 using 2
    simp only [hα, hβ, add_sub_add_right_eq_sub]

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

end Start

/-! ### A solution from every real starting point -/

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

/-- `θ̂` shifted by a period is a solution from `u`:
`θ̂(e^{iu}) + (u - [u]_{2π})` solves `dX = µ(X) dt + β(X) dB`, `X_0 = u` a.s. -/
theorem exists_thetaHat_solution [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {β : ℝ → ℝ} (hβsq : ∀ u, β u ^ 2 = 2 * diffusionD a b c u) (u : ℝ) :
    ∃ (𝒢 : Filtration ℝ≥0 m) (X : ℝ≥0 → Ω → ℝ),
      IsDiffusionSolution 𝒢 (mu a b c) β X P ∧ ∀ᵐ ω ∂P, X 0 ω = u := by
  have hsol := isDiffusionSolution_thetaHat_of_sq hU ha hb hc hβsq u
  -- the shift `d = u - [u]_{2π}` is a multiple of `2π`
  set d : ℝ := u - toIcoMod Real.two_pi_pos 0 u with hd
  have hdk : d = ((2 * toIcoDiv Real.two_pi_pos 0 u : ℤ) : ℝ) * π := by
    rw [hd, self_sub_toIcoMod, zsmul_eq_mul]
    push_cast; ring
  refine ⟨sigmaFiltration hU (unitPt u), fun t ω => thetaHat hU (unitPt u) t ω + d,
    IsDiffusionSolution.add_const (fun x => ?_) (fun x => ?_) hsol, ?_⟩
  · rw [hdk]; exact (mu_periodic a b c).int_mul _ x
  · rw [hβsq, hβsq, hdk, (diffusionD_periodic a b c).int_mul _ x]
  · filter_upwards [ae_thetaHat_zero hU ha hc u] with ω hω
    simp only [hω, hd]
    ring

end Solutions

end ComplexSLE.Internal

end
