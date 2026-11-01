/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.Lemma38
public import ComplexSLE.Internal.Stationary.SLEStatLaw

/-!
# Lemma 3.10 for the random point `𝐳 = e^{iu}`, `u ∼ ν = p(u) 1_{[0,2π]}(u) du` (M7/E2)

The specialization of `integrable_log_inv_distSigma` (`Lemma38.lean`, valid for every probability
measure `ν` on `ℝ`) to the admissible measure `ν = admissibleMeasure p` of an admissible density `p`
(`isProbabilityMeasure_admissibleMeasure`), i.e. to `μ = P.prod (admissibleMeasure p)`. This is the
form of Lemma 3.10 (`lem-log-finite-exp`, paper.tex:L1550-1630) consumed by the proof of
Proposition 3.2(b).
-/

public section

open scoped NNReal ENNReal
open MeasureTheory

namespace ComplexSLE.Internal

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-- **Lemma 3.10** on `μ = P ⊗ ν_p` with the random point `𝐳 = e^{iu}`: for every `t̃ ≥ 0`,
`E log (1 / dist(𝐳, L_{σ_𝐳(t̃)})) < ∞`. -/
theorem integrable_log_inv_distSigma_admissible [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hc : c ^ 2 ≤ a * b) {p : ℝ → ℝ}
    (hp : IsAdmissibleDensity a b c p) (tt : ℝ≥0) :
    Integrable (fun q : Ω × ℝ => Real.log (1 / distSigma hU tt q))
      (P.prod (admissibleMeasure p)) := by
  have := isProbabilityMeasure_admissibleMeasure hp
  exact integrable_log_inv_distSigma hU tt ha hc (admissibleMeasure p)

/-- **Lemma 3.10**, lintegral form on `μ = P ⊗ ν_p`. -/
theorem lintegral_log_inv_distSigma_admissible_lt_top [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hc : c ^ 2 ≤ a * b) {p : ℝ → ℝ}
    (hp : IsAdmissibleDensity a b c p) (tt : ℝ≥0) :
    ∫⁻ q, ENNReal.ofReal (Real.log (1 / distSigma hU tt q)) ∂(P.prod (admissibleMeasure p))
      < ⊤ := by
  have := isProbabilityMeasure_admissibleMeasure hp
  exact lintegral_log_inv_distSigma_lt_top hU tt ha hc (admissibleMeasure p)

/-- `dist(𝐳, L_{σ_𝐳(t̃)})` is `P ⊗ ν_p`-a.s. positive (`ae_distSigma_pos` for admissible `p`). -/
theorem ae_distSigma_pos_admissible [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hc : c ^ 2 ≤ a * b) {p : ℝ → ℝ}
    (hp : IsAdmissibleDensity a b c p) (tt : ℝ≥0) :
    ∀ᵐ q ∂(P.prod (admissibleMeasure p)), 0 < distSigma hU tt q := by
  have := isProbabilityMeasure_admissibleMeasure hp
  exact ae_distSigma_pos hU tt ha hc (admissibleMeasure p)

end ComplexSLE.Internal

end
