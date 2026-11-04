/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.SwallowDistance
public import ComplexSLE.Internal.Phases.SwallowODE
public import ComplexSLE.Internal.Polar.PolarDerivSigma
public import ComplexSLE.Internal.Polar.PolarSigmaTop

/-!
# Lemma 3.6 and the Proposition 3.1(b) comparison, almost surely (M7/C1)

Almost sure forms, for an adapted `SLE_Σ` driver (`0 < a`, `c² ≤ ab`) and `z ≠ 0`, of the
deterministic results `tendsto_log_norm_fPath_sigmaTime` (Lemma 3.6, `lem-swallow-distance`,
paper.tex:L1389-1398) and `absorbingTime_ne_top_of_tendsto_log_norm_div` (the ODE comparison of
Proposition 3.1(b), paper.tex:L1405-1418) in terms of the process
`sigmaLogNorm hU z s ω = log|f̂_s(z)|` of `PolarDerivSigma.lean`.

The only input beyond the deterministic files is Remark 2.12 (`ae_sigmaDom_eq_Ici`: a.s.
`sigmaDom = [0, ∞)`), whose proof uses the Itô formula (`ito_formula`, proved in-project), while the
deterministic files `EndpointCont`, `SwallowDistance` and `SwallowODE` use no classical input.
-/

public section

open scoped NNReal ENNReal Topology
open Set Filter MeasureTheory

namespace ComplexSLE.Internal.Polar

section Adapted

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

variable (hU : IsSLEDriverAdapted a b c U P ℱ) [IsProbabilityMeasure P] {z : ℂ}

/-- **Lemma 3.6** (`lem-swallow-distance`, paper.tex:L1389-1398): for an adapted `SLE_Σ` driver
and `z ≠ 0`, almost surely, if `T_z < ∞` then `log|f̂_s(z)| → -∞` as `s → ∞`. -/
theorem ae_tendsto_sigmaLogNorm_atBot (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, absorbingTime (fun s => U s ω) z < ⊤ →
      Tendsto (fun s : ℝ≥0 => sigmaLogNorm hU z s ω) atTop atBot := by
  filter_upwards [ae_sigmaDom_eq_Ici hU z ha hc hz] with ω hω hT
  exact tendsto_log_norm_fPath_sigmaTime_nnreal (hU.cont ω) hω hT.ne

/-- **Proposition 3.1(b), ODE comparison, almost surely** (paper.tex:L1405-1418): for an adapted
`SLE_Σ` driver, `z ≠ 0` and `α > 0`, almost surely, if `log|f̂_s(z)| / s → -α` as `s → ∞` then
`T_z < ∞`. -/
theorem ae_absorbingTime_lt_top_of_tendsto_sigmaLogNorm_div (ha : 0 < a) (hc : c ^ 2 ≤ a * b)
    (hz : z ≠ 0) {α : ℝ} (hα : 0 < α) :
    ∀ᵐ ω ∂P, Tendsto (fun s : ℝ≥0 => sigmaLogNorm hU z s ω / (s : ℝ)) atTop (𝓝 (-α)) →
      absorbingTime (fun s => U s ω) z < ⊤ := by
  filter_upwards [ae_sigmaDom_eq_Ici hU z ha hc hz] with ω hω h
  exact lt_top_iff_ne_top.2
    (absorbingTime_ne_top_of_tendsto_log_norm_div_nnreal (hU.cont ω) hω hα h)

end Adapted

end ComplexSLE.Internal.Polar

end
