/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.PeriodicODE.Poisson
public import ComplexSLE.Infrastructure.PeriodicODE.DoubleZero
public import ComplexSLE.Internal.Stationary.CriticalCoefficients
public import ComplexSLE.Internal.Stationary.AdmissibleMeasure
public import ComplexSLE.Internal.Stationary.ItoReal

/-!
# The periodic Poisson equation for the generator of `θ̂` (M10-R4, steps 1–2)

Write `L g = generator µ β g = g' µ + ½ g'' β²` for `β² = 2D`, i.e. `L g = µ g' + D g''`.

* `exists_contDiff_beta_sq`: a smooth `β` with `β² = 2D` (`√(2D)` if `c² < ab`, `betaCrit` if
  `c² = ab`); only `β²` enters `L`, so this is used for transport only.
* `exists_poisson_generator`: for `C²` `π`-periodic `f` there are a constant `C` and a `C²`
  `π`-periodic `g` with `L g = f - C`. The non-critical case is
  `exists_periodic_poisson_of_pos`; in the critical case `D` has the double zero lattice
  `x₀ + πℤ` with `µ(x₀) ≠ 0` (`exists_zero_lattice_diffusionD`), so
  `exists_periodic_solution_of_doubleZero` solves `D h' + µ h = r` for `r = f` and `r = 1` and
  `exists_periodic_poisson_of_solutions` finishes (maximum principle).
* `poisson_const_eq`: the constant is `C = ∫ f dν` for `ν = admissibleMeasure p`, by the
  Kolmogorov equation `∫₀^π (L g) 2p = 0` (`IsKolmogorovDensity.integral_generator_eq_zero`).

No transition kernel, no Hörmander smoothing and no Markov external is used.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory Set Function Real intervalIntegral

namespace ComplexSLE.Internal

variable {a b c : ℝ}

/-- A smooth `β` with `β² = 2D`: `√(2D)` if `c² < ab`, `betaCrit a c` if `c² = ab`. -/
theorem exists_contDiff_beta_sq (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b) :
    ∃ β : ℝ → ℝ, ContDiff ℝ 2 β ∧ ∀ u, β u ^ 2 = 2 * diffusionD a b c u := by
  rcases hc.lt_or_eq with h | h
  · exact ⟨fun u => √(2 * diffusionD a b c u),
      (contDiff_sqrt_two_mul_diffusionD ha hb h).of_le (by simp),
      sq_sqrt_two_mul_diffusionD ha hb hc⟩
  · exact ⟨betaCrit a c, (contDiff_betaCrit a c).of_le (by simp), sq_betaCrit ha h⟩

/-- The generator of `(µ, β)` with `β² = 2D` is `µ g' + D g''`. -/
theorem generator_eq_of_sq {β : ℝ → ℝ} (hβ : ∀ u, β u ^ 2 = 2 * diffusionD a b c u) (g : ℝ → ℝ)
    (u : ℝ) :
    generator (mu a b c) β g u =
      mu a b c u * deriv g u + diffusionD a b c u * deriv (deriv g) u := by
  unfold generator
  rw [hβ u]
  ring

/-- **The periodic Poisson equation for the generator of `θ̂`.** For `β² = 2D` and a `C²`
`π`-periodic `f` there are a constant `C` and a `C²` `π`-periodic `g` with `L g = f - C`. -/
theorem exists_poisson_generator (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b) {β : ℝ → ℝ}
    (hβ : ∀ u, β u ^ 2 = 2 * diffusionD a b c u) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfper : Function.Periodic f π) :
    ∃ C : ℝ, ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ Function.Periodic g π ∧
      ∀ u, generator (mu a b c) β g u = f u - C := by
  have key : ∃ C : ℝ, ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ Function.Periodic g π ∧
      ∀ u, mu a b c u * deriv g u + diffusionD a b c u * deriv (deriv g) u = f u - C := by
    rcases hc.lt_or_eq with h | h
    · exact Infrastructure.exists_periodic_poisson_of_pos pi_pos (continuous_mu a b c)
        (continuous_diffusionD a b c) (diffusionD_pos ha hb h) hf.continuous (mu_periodic a b c)
        (diffusionD_periodic a b c) hfper
    · obtain ⟨x₀, hz, hD2, hμ⟩ := exists_zero_lattice_diffusionD ha hb h
      have hμ2 : ContDiff ℝ 2 (mu a b c) := (contDiff_mu a b c).of_le (by simp)
      have hD2c : ContDiff ℝ 2 (diffusionD a b c) := (contDiff_diffusionD a b c).of_le (by simp)
      obtain ⟨hr, hrc, hrper, hreq⟩ := Infrastructure.exists_periodic_solution_of_doubleZero
        (T := π) (x₀ := x₀) pi_pos hμ2 hD2c hf (mu_periodic a b c) (diffusionD_periodic a b c)
        hfper (diffusionD_nonneg ha hb hc) hz hD2 hμ
      obtain ⟨h₁, h₁c, h₁per, h₁eq⟩ := Infrastructure.exists_periodic_solution_of_doubleZero
        (T := π) (x₀ := x₀) (r := fun _ => (1 : ℝ)) pi_pos hμ2 hD2c contDiff_const
        (mu_periodic a b c) (diffusionD_periodic a b c) (fun _ => rfl)
        (diffusionD_nonneg ha hb hc) hz hD2 hμ
      exact Infrastructure.exists_periodic_poisson_of_solutions (r := f) (h₁ := h₁) (hr := hr)
        pi_pos (diffusionD_nonneg ha hb hc) h₁c h₁per
        h₁eq hrc hrper hreq
  obtain ⟨C, g, hgc, hgper, hg⟩ := key
  exact ⟨C, g, hgc, hgper, fun u => by rw [generator_eq_of_sq hβ]; exact hg u⟩

/-- **The constant of the Poisson equation is `∫ f dν`.** If `L g = f - C` with `g` a `C²`
`π`-periodic function and `ν = admissibleMeasure p`, then `C = ∫ f dν`, by the Kolmogorov
equation `∫₀^π (L g) · 2p = 0`. -/
theorem poisson_const_eq (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b) {β : ℝ → ℝ}
    (hβ : ∀ u, β u ^ 2 = 2 * diffusionD a b c u) {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfper : Function.Periodic f π) {C : ℝ} {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgper : Function.Periodic g π)
    (hgen : ∀ u, generator (mu a b c) β g u = f u - C) :
    C = ∫ u, f u ∂(admissibleMeasure p) := by
  obtain ⟨β', hβ'c, hβ'⟩ := exists_contDiff_beta_sq ha hb hc
  have hp₀ : IsKolmogorovDensity (mu a b c) β' (fun u => 2 * p u) :=
    IsAdmissibleDensity.isKolmogorovDensity hp hβ'
  have hβ'per : Function.Periodic (fun u => β' u ^ 2) π := fun u => by
    simp only [hβ', diffusionD_periodic a b c u]
  have hK := hp₀.integral_generator_eq_zero ((contDiff_mu a b c).of_le (by simp)) hβ'c
    (mu_periodic a b c) hβ'per hg hgper
  have hgen' : ∀ u, deriv g u * mu a b c u + (1 / 2) * deriv (deriv g) u * β' u ^ 2 =
      f u - C := fun u => by
    have := hgen u
    rw [generator_eq_of_sq hβ] at this
    rw [hβ' u]
    linear_combination this
  simp only [hgen'] at hK
  have hfc : Continuous f := hf.continuous
  have hpc : Continuous p := hp.1
  have hint1 : IntervalIntegrable (fun u => f u * (2 * p u)) volume 0 π :=
    (hfc.mul (continuous_const.mul hpc)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun u => C * (2 * p u)) volume 0 π :=
    (continuous_const.mul (continuous_const.mul hpc)).intervalIntegrable _ _
  have hsplit : ∫ u in (0)..π, (f u - C) * (2 * p u) =
      (∫ u in (0)..π, f u * (2 * p u)) - C * ∫ u in (0)..π, 2 * p u := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hint1 hint2]
    congr 1
    funext u
    ring
  rw [hsplit, hp₀.integral_eq_one, mul_one, sub_eq_zero] at hK
  rw [integral_admissibleMeasure hp,
    integral_two_pi_eq_two_mul_pi (G := fun u => f u * p u) (hfc.mul hpc) (fun u => by
      simp only [hfper u, hp.2.2.1 u]),
    ← hK, ← intervalIntegral.integral_const_mul]
  congr 1
  funext u
  ring

end ComplexSLE.Internal

end
