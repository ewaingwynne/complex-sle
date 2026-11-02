/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.KernelLaw
public import ComplexSLE.Internal.Stationary.Coefficients
public import ComplexSLE.Internal.Polar.PolarThetaHat
public import ComplexSLE.Internal.Polar.PolarContMeas
public import ComplexSLE.Internal.Stationary.ThetaHatSolution
public import ComplexSLE.External.HormanderOneDim

/-!
# One-time stationarity of `θ̂(𝐳)` (M7/A4a): the transition kernel of `θ̂`

For `a, b > 0`, `c² ≤ ab` and an adapted SLE_Σ driver `U`, the time-changed argument
`θ̂ = θ̂(e^{iu})` (`Polar.thetaHat`) solves the martingale problem `(2.25)` for the periodic
coefficients `α = µ`, `β² = 2D` (`Polar.isDiffusionSolution_thetaHat`). This file packages the
transition-kernel input of `Stationary/KernelLaw.lean` for these coefficients:

* `MarkovOneDimFor α β` is the statement of the EXTERNAL `markov_oneDim` (R29)
  (`ComplexSLE/External/MarkovOneDim.lean`) for the coefficients `α, β`, with the
  coefficient hypotheses already discharged; `MarkovOneDim` is the full statement of that
  external. Neither is assumed here: they appear as explicit hypotheses of the consumers.
* `IsDiffusionSolution` only depends on `β` through `β²`
  (`isDiffusionSolution_congr_sq`), and is invariant under a shift of the process by a period
  (`IsDiffusionSolution.add_const`). So `θ̂ + 2πk` solves the martingale problem from every real
  starting point (`exists_thetaHat_solution`).
* `exists_isDiffusionKernel`: the transition density `p` of `External.hormander_oneDim` for
  `(µ, β)` together with the conclusions of `markov_oneDim` is an `IsDiffusionKernel (µ) β p`.

Consumes `hormander_oneDim` and `ito_formula` (through `IsDiffusionKernel`), so everything here is
`PROVED_REL` on those externals, plus the hypothesis `MarkovOneDimFor` where it appears.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set Function Real

namespace ComplexSLE.Internal

/-! ### The statement of the EXTERNAL `markov_oneDim` (R29) -/

/-- The conclusions of the EXTERNAL `markov_oneDim` (R29) for a transition kernel `p`:
`π`-equivariance of `p`, and the Markov property in conditional-expectation form. -/
@[expose] def MarkovOneDimConclusion (α β : ℝ → ℝ) (p : ℝ≥0 → ℝ → ℝ → ℝ) : Prop :=
  (∀ t : ℝ≥0, 0 < t → ∀ u v, p t (u + π) (v + π) = p t u v) ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ≥0 ‹_›) (X : ℝ≥0 → Ω → ℝ), IsDiffusionSolution ℱ α β X P →
        ∀ t s : ℝ≥0, 0 < s → ∀ f : ℝ → ℝ, Measurable f → (∃ C : ℝ, ∀ v, |f v| ≤ C) →
          P[fun ω => f (X (t + s) ω) | ℱ t] =ᵐ[P] fun ω => ∫ v, f v * p s (X t ω) v

/-- `markov_oneDim α β hα hβ hαper hβper hH` for fixed coefficients: every transition kernel `p`
satisfying the representation clause of `hormander_oneDim` is `π`-equivariant and has the Markov
property. (Pending external; here only an explicit hypothesis.) -/
@[expose] def MarkovOneDimFor (α β : ℝ → ℝ) : Prop :=
  ∀ p : ℝ≥0 → ℝ → ℝ → ℝ, (∀ t u v, 0 ≤ p t u v) →
    (∀ t : ℝ≥0, 0 < t → ∀ u, Continuous (p t u)) →
    (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ≥0 ‹_›) (X : ℝ≥0 → Ω → ℝ) (u : ℝ),
      IsDiffusionSolution ℱ α β X P → (∀ᵐ ω ∂P, X 0 ω = u) →
        ∀ t : ℝ≥0, 0 < t → P.map (X t) = volume.withDensity fun v => ENNReal.ofReal (p t u v)) →
    MarkovOneDimConclusion α β p

/-- The full statement of the EXTERNAL `markov_oneDim` (R29)
(`ComplexSLE/External/MarkovOneDim.lean`), as a `Prop`. -/
@[expose] def MarkovOneDim : Prop :=
  ∀ (α β : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) α → ContDiff ℝ (⊤ : ℕ∞) β →
    (∀ u, α (u + Real.pi) = α u) → (∀ u, β (u + Real.pi) ^ 2 = β u ^ 2) →
    (∀ u, β u ≠ 0 ∨ deriv β u * α u ≠ 0) → MarkovOneDimFor α β

/-! ### The transition kernel of `θ̂` -/

open Polar

section Solutions

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- **The transition kernel of `θ̂`.** Let `p` be the transition density of
`External.hormander_oneDim` for `(µ, β)` (`β² = 2D`, `β` smooth with (A.1)). If the conclusions of
the EXTERNAL `markov_oneDim` (R29) hold for `(µ, β)` (hypothesis `hMO`), then `p` is an
`IsDiffusionKernel`; existence of solutions from every start comes from `θ̂`. -/
theorem exists_isDiffusionKernel [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β) (hβsq : ∀ u, β u ^ 2 = 2 * diffusionD a b c u)
    (hH : ∀ u, β u ≠ 0 ∨ deriv β u * mu a b c u ≠ 0)
    (hMO : MarkovOneDimFor (mu a b c) β) :
    ∃ p : ℝ≥0 → ℝ → ℝ → ℝ, IsDiffusionKernel (mu a b c) β p := by
  obtain ⟨p, hsm, hnn, hT, hlaw⟩ := External.hormander_oneDim (mu a b c) β (contDiff_mu a b c) hβ
    (mu_periodic a b c) (fun u => sq_periodic_of_sq_eq_two_mul_diffusionD hβsq u) hH
  have hpc : ∀ t : ℝ≥0, 0 < t → ∀ u, Continuous (p t u) := fun t ht u =>
    ((hsm t ht).continuous).comp (continuous_const.prodMk continuous_id)
  obtain ⟨hequi, hmarkov⟩ := hMO p hnn hpc hlaw
  refine ⟨p, hnn, hpc, hlaw, fun u => ?_, fun t ht f hf hfb => (hT t ht f hf hfb).of_le ?_,
    hequi, hmarkov⟩
  · obtain ⟨𝒢, X, hX, h0⟩ := exists_thetaHat_solution hU ha hb hc hβsq u
    exact ⟨Ω, m, P, inferInstance, 𝒢, X, hX, h0⟩
  · exact WithTop.coe_le_coe.mpr le_top

end Solutions

end ComplexSLE.Internal

end
