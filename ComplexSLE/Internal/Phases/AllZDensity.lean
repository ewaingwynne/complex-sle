/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.External.HormanderOneDim
public import ComplexSLE.Internal.Stationary.Coefficients
public import ComplexSLE.Internal.Polar.PolarThetaHat

/-!
# `θ̂_s(z)` has a density for `s > 0` (Lemma 3.2, the Hörmander step)

For `a, b > 0`, `c² ≤ ab`, an adapted `SLE_Σ` driver `U` and `z ≠ 0`, the time-changed argument
`θ̂ = θ̂(z)` (`Polar.thetaHat`) solves the martingale problem (2.25) for `(µ, √(2D))`
(`Polar.isDiffusionSolution_thetaHat`), starts at a.s. one point, and for every `s > 0` its law
has a Lebesgue density, by the `law_eq` clause of the EXTERNAL `hormander_oneDim`:

* `thetaHat_zero_ae`: `θ̂_0 = [arg z]_{2π}` a.s.;
* `map_thetaHat_absolutelyContinuous`: `P.map (θ̂_s) ≪ volume` for `s > 0`.

The coefficient hypotheses of `hormander_oneDim` (paper's (A.1)/(A.2): `α = µ` smooth and
`π`-periodic, `β` smooth with `β²` `π`-periodic, and `β ≠ 0` or `β' α ≠ 0` at every point) hold
in both cases: `c² < ab` with `β = √(2D)` (never zero), and `c² = ab` with
`β = √a sin - (c/√a) cos` (`Stationary/Coefficients.lean`). `IsDiffusionSolution` depends on `β`
only through `β²`.

Consumes the EXTERNAL `hormander_oneDim` (and `ito_formula`, `timeChange` upstream).
-/

public section

open scoped NNReal ENNReal Topology Real
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Internal

section Solution

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m} {P : Measure Ω}
  {α β β' : ℝ → ℝ} {X : ℝ≥0 → Ω → ℝ}

/-- `IsDiffusionSolution` depends on `β` only through `β²`. -/
theorem allZ_isDiffusionSolution_congr_sq (h : ∀ u, β' u ^ 2 = β u ^ 2) :
    IsDiffusionSolution ℱ α β' X P ↔ IsDiffusionSolution ℱ α β X P := by
  unfold IsDiffusionSolution
  simp only [h]

end Solution

open Polar

section Processes

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- `θ̂_0` is almost surely the deterministic representative of `arg z` in `[0, 2π)`
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

/-- **Density of `θ̂_s(z)`.** For `a, b > 0`, `c² ≤ ab`, `z ≠ 0` and `s > 0`, the law of `θ̂_s(z)`
is absolutely continuous with respect to Lebesgue measure (EXTERNAL `hormander_oneDim`). -/
theorem map_thetaHat_absolutelyContinuous [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {z : ℂ} (hz : z ≠ 0) {s : ℝ≥0} (hs : 0 < s) :
    P.map (thetaHat hU z s) ≪ volume := by
  -- coefficients `α = µ`, `β` with `β² = 2D` and the Hörmander condition
  have key : ∃ β : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) β ∧ (∀ u, β u ^ 2 = 2 * diffusionD a b c u) ∧
      ∀ u, β u ≠ 0 ∨ deriv β u * mu a b c u ≠ 0 := by
    rcases hc.lt_or_eq with hlt | heq
    · exact ⟨fun u => √(2 * diffusionD a b c u), contDiff_sqrt_two_mul_diffusionD ha hb hlt,
        sq_sqrt_two_mul_diffusionD ha hb hc, hormander_sqrt_two_mul_diffusionD ha hb hlt⟩
    · exact ⟨betaCrit a c, contDiff_betaCrit a c, sq_betaCrit ha heq,
        hormander_betaCrit ha hb heq⟩
  obtain ⟨β, hβ, hβsq, hH⟩ := key
  have hsol : IsDiffusionSolution (sigmaFiltration hU z) (mu a b c) β (thetaHat hU z) P :=
    (allZ_isDiffusionSolution_congr_sq (α := mu a b c)
      (β := fun v => √(2 * diffusionD a b c v)) (β' := β) fun v => by
        rw [hβsq v, Real.sq_sqrt (by have := diffusionD_nonneg ha hb hc v; positivity)]).2
      (isDiffusionSolution_thetaHat hU ha hc hz)
  obtain ⟨p, -, -, -, hlaw⟩ := External.hormander_oneDim (mu a b c) β (contDiff_mu a b c) hβ
    (mu_periodic a b c) (fun u => sq_periodic_of_sq_eq_two_mul_diffusionD hβsq u) hH
  rw [hlaw Ω P (sigmaFiltration hU z) (thetaHat hU z) _ hsol
    (thetaHat_zero_ae hU ha hc hz) s hs]
  exact withDensity_absolutelyContinuous _ _

end Processes

end ComplexSLE.Internal

end
