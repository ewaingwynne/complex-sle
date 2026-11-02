/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.Prop31Core

/-!
# Proposition 3.1(a), assembled (M7/C2)

`proposition_3_1_a_core` has exactly the type of the frozen anchor
`ComplexSLE.proposition_3_1_a` (paper.tex:L1265-1269): if `(I) ≥ 0` then a.s. `T_z = ∞`, for every
`z ≠ 0`.

Proof (paper.tex:L1401-1418): by Lemma 3.3 (`lemma_3_3`, event family `{T_z = ∞}`) it suffices to
treat the random point `𝐳 = e^{i𝐮}`. By the driver bridge we may work with an adapted version.
By Lemma 3.4 (`not_tendsto_atBot_logFHat`) a.s. `log |f̂_s(𝐳)| ↛ -∞`, while by Lemma 3.6
(`ae_tendsto_sigmaLogNorm_atBot`) `T_z < ∞` forces `log |f̂_s(z)| → -∞`
(`ae_ae_absorbingTime_eq_top`).
-/

public section

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace ComplexSLE.Internal

/-- **Proposition 3.1(a)** (paper.tex:L1265-1269): the statement of
`ComplexSLE.proposition_3_1_a`. -/
theorem proposition_3_1_a_core (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : c ^ 2 ≤ a * b) (p : ℝ → ℝ) (hp : IsAdmissibleDensity a b c p)
    (hI : 0 ≤ integralI a b c p) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (U : ℝ≥0 → Ω → ℂ) (hU : IsSLEDriver a b c U P) (z : ℂ)
    (hz : z ≠ 0) : ∀ᵐ ω ∂P, absorbingTime (U · ω) z = ∞ :=
  ae_event_of_ae_ae_unit ha hb hc hU hp (E := fun u z => absorbingTime u z = ⊤)
    measurableEvents_absorbingTime_eq_top scaleInvariantEvents_absorbingTime_eq_top
    futureDependentEvents_absorbingTime_eq_top
    (fun _ _ hU' => ae_ae_absorbingTime_eq_top hU' ha hb hc hp hI) z hz

end ComplexSLE.Internal

end
