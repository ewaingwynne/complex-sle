/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.SLEStatKernel
public import ComplexSLE.Internal.Stationary.AdmissibleMeasure

/-!
# One-time stationarity of `θ̂(𝐳)` on the product space (M7/A4a): the measure `ν` and invariance

Let `p` be an admissible density for `(a, b, c)` (`IsAdmissibleDensity`, `∫₀^{2π} p = 1`), and
`ν = p(u) 1_{[0,2π]}(u) du` (`admissibleMeasure p`), a probability measure on `ℝ`.

* `integral_admissibleMeasure`, `isProbabilityMeasure_admissibleMeasure`: `ν` in integral form.
* `integral_two_pi_eq_two_mul_pi`: for continuous `π`-periodic `G`, `∫₀^{2π} G = 2 ∫₀^π G`
  (the factor 2 of ruling R9: `2p` is the Kolmogorov density on `[0, π]`).
* `integral_kernelOp_admissibleMeasure`: for a diffusion kernel `p'` of `(µ, β)` (`β² = 2D`) and a
  continuous `π`-periodic `f`, `∫ T_s f dν = ∫ f dν` for every `s ≥ 0`
  (`IsDiffusionKernel.integral_kernelOp_mul_eq_of_periodic` for `2p`, then `∫₀^{2π} = 2 ∫₀^π`).
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set Function Real intervalIntegral

namespace ComplexSLE.Internal

variable {a b c : ℝ}

/-- **Invariance of `ν`** under the transition semigroup of a diffusion kernel `p'` for `(µ, β)`
with `β² = 2D`: `∫ T_s f dν = ∫ f dν` for every `s ≥ 0` and continuous `π`-periodic `f`. -/
theorem integral_kernelOp_admissibleMeasure {p : ℝ → ℝ} {β : ℝ → ℝ}
    {p' : ℝ≥0 → ℝ → ℝ → ℝ} (K : IsDiffusionKernel (mu a b c) β p')
    (hp : IsAdmissibleDensity a b c p) (hβ : ContDiff ℝ 2 β)
    (hβsq : ∀ u, β u ^ 2 = 2 * diffusionD a b c u) (s : ℝ≥0) {f : ℝ → ℝ}
    (hf : Continuous f) (hfper : Periodic f π) :
    ∫ u, kernelOp p' s f u ∂(admissibleMeasure p) = ∫ u, f u ∂(admissibleMeasure p) := by
  have hp₀ : IsKolmogorovDensity (mu a b c) β (fun u => 2 * p u) :=
    IsAdmissibleDensity.isKolmogorovDensity hp hβsq
  have hβper : Periodic (fun u => β u ^ 2) π := fun u => by
    simp only [hβsq, diffusionD_periodic a b c u]
  have hfb := hfper.exists_bound pi_ne_zero hf
  -- `F = T_s f` is continuous and `π`-periodic
  have hFc : Continuous (kernelOp p' s f) := by
    rcases eq_or_ne s 0 with rfl | hs
    · simpa using hf
    · have hs' := pos_iff_ne_zero.mpr hs
      rw [kernelOp_of_pos hs']
      exact (K.smooth s hs' f hf.measurable hfb).continuous
  have hFper : Periodic (kernelOp p' s f) π := by
    rcases eq_or_ne s 0 with rfl | hs
    · simpa using hfper
    · have hs' := pos_iff_ne_zero.mpr hs
      rw [kernelOp_of_pos hs']
      exact periodic_integral_mul_transition (K.equivariant s hs') hfper
  have hinv := K.integral_kernelOp_mul_eq_of_periodic s ((contDiff_mu a b c).of_le (by simp))
    hβ (mu_periodic a b c) hβper hp₀ hf.measurable hfb hfper
  rw [integral_admissibleMeasure hp, integral_admissibleMeasure hp,
    integral_two_pi_eq_two_mul_pi (G := fun u => kernelOp p' s f u * p u) (hFc.mul hp.1)
      (fun u => by
      simp only [hFper u, hp.2.2.1 u]),
    integral_two_pi_eq_two_mul_pi (G := fun u => f u * p u) (hf.mul hp.1) (fun u => by
      simp only [hfper u, hp.2.2.1 u])]
  have h2 : ∀ G : ℝ → ℝ, ∫ u in (0)..π, G u * (2 * p u) = 2 * ∫ u in (0)..π, G u * p u :=
    fun G => by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext u
      ring
  rw [h2, h2] at hinv
  linarith

end ComplexSLE.Internal

end
