/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.Prop31Core

/-!
# Proposition 3.1(b), assembled (M7/C2)

`proposition_3_1_b_core` has exactly the type of the frozen anchor
`ComplexSLE.proposition_3_1_b` (paper.tex:L1265-1270): if `(I) < 0` then a.s. `T_z < ∞`, for every
`z ≠ 0`.

Proof (paper.tex:L1401-1418): by Lemma 3.3 (`lemma_3_3`, event family `{T_z < ∞}`) it suffices to
treat the random point `𝐳 = e^{i𝐮}`. By the driver bridge we may work with an adapted version.
By Lemma 3.4 (`tendsto_logFHat_div_of_integralI_neg`) a.s. `log |f̂_s(𝐳)| / s → (I) < 0`, and the
ODE comparison (`ae_absorbingTime_lt_top_of_tendsto_sigmaLogNorm_div`, with `α = -(I)`) gives
`T_z < ∞` (`ae_ae_absorbingTime_lt_top`).
-/

public section

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace ComplexSLE.Internal

/-- **Proposition 3.1(b)** (paper.tex:L1265-1270): the statement of
`ComplexSLE.proposition_3_1_b`. -/
theorem proposition_3_1_b_core (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : c ^ 2 ≤ a * b) (p : ℝ → ℝ) (hp : IsAdmissibleDensity a b c p)
    (hI : integralI a b c p < 0) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (U : ℝ≥0 → Ω → ℂ) (hU : IsSLEDriver a b c U P) (z : ℂ)
    (hz : z ≠ 0) : ∀ᵐ ω ∂P, absorbingTime (U · ω) z < ∞ :=
  ae_event_of_ae_ae_unit ha hb hc hU hp (E := fun u z => absorbingTime u z < ⊤)
    measurableEvents_absorbingTime_lt_top scaleInvariantEvents_absorbingTime_lt_top
    futureDependentEvents_absorbingTime_lt_top
    (fun _ _ hU' => ae_ae_absorbingTime_lt_top hU' ha hb hc hp hI) z hz

end ComplexSLE.Internal

end
