/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.KolmogorovDensity

/-!
# The measure `ν = p(u) 1_{[0,2π]}(u) du` of an admissible density

* `admissibleMeasure p`, with `integral_admissibleMeasure` and `isProbabilityMeasure_admissibleMeasure`;
* `integral_two_pi_eq_two_mul_pi`: for continuous `π`-periodic `G`, `∫₀^{2π} G = 2 ∫₀^π G`
  (the factor 2 of ruling R9: `2p` is the Kolmogorov density on `[0, π]`).
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set Function Real intervalIntegral

namespace ComplexSLE.Internal

variable {a b c : ℝ}

/-! ### The measure `ν = p(u) 1_{[0,2π]}(u) du` -/

/-- The measure `ν = p(u) 1_{[0,2π]}(u) du` for an admissible density `p`. -/
@[expose] noncomputable def admissibleMeasure (p : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Icc 0 (2 * π))).withDensity fun u => ENNReal.ofReal (p u)

theorem integral_admissibleMeasure {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) {G : ℝ → ℝ} :
    ∫ u, G u ∂(admissibleMeasure p) = ∫ u in (0)..(2 * π), G u * p u := by
  rw [admissibleMeasure, integral_withDensity_eq_integral_toReal_smul (f := fun v =>
      ENNReal.ofReal (p v)) (ENNReal.measurable_ofReal.comp hp.1.measurable)
      (Eventually.of_forall fun v => ENNReal.ofReal_lt_top),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by positivity)]
  congr 1
  funext v
  rw [ENNReal.toReal_ofReal (hp.2.1 v), smul_eq_mul, mul_comm]

theorem isProbabilityMeasure_admissibleMeasure {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) :
    IsProbabilityMeasure (admissibleMeasure p) := by
  refine ⟨?_⟩
  rw [admissibleMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hp.1.integrableOn_Icc
      (Eventually.of_forall hp.2.1), integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity), hp.2.2.2.1, ENNReal.ofReal_one]

/-- For a continuous `π`-periodic `G`, `∫₀^{2π} G = 2 ∫₀^π G`. -/
theorem integral_two_pi_eq_two_mul_pi {G : ℝ → ℝ} (hG : Continuous G) (hper : Periodic G π) :
    ∫ u in (0)..(2 * π), G u = 2 * ∫ u in (0)..π, G u := by
  have hsplit : ∫ u in (0)..(2 * π), G u =
      (∫ u in (0)..π, G u) + ∫ u in π..(2 * π), G u := by
    rw [integral_add_adjacent_intervals (hG.intervalIntegrable _ _)
      (hG.intervalIntegrable _ _)]
  have hshift : ∫ u in π..(2 * π), G u = ∫ u in (0)..π, G u := by
    have := hper.intervalIntegral_add_eq π 0
    rw [two_mul]
    simpa using this
  rw [hsplit, hshift]
  ring

/-! ### Invariance of `ν` under the semigroup -/

end ComplexSLE.Internal

end
