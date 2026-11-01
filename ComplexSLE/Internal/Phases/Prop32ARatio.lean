/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.Prop31Core
public import ComplexSLE.Internal.Phases.ErgodicRatioConst
public import ComplexSLE.Internal.Phases.KoebeHitSigma
public import ComplexSLE.Frozen.Defs.IntegralII

/-!
# Lemma 3.7: the limit of `log(|f̂'_s|/|f̂_s|) / s` and the fibrewise `ε`-form (M7/D2)

Source: paper.tex:L1430-1455 (`lem-integral-ii`). On `(Ω × ℝ, P ⊗ ν)`, `ν = p(u) 1_{[0,2π]}(u) du`,
let `R_s = log(|f̂'_s(e^{iu})| / |f̂_s(e^{iu})|)` (`sigmaLogRatio`). By (2.27) in σ-time
(`sigmaLogDeriv_eq`), `log |f̂'_s| = -2 ∫₀ˢ cos 2θ̂_v dv = -2 C_s`, hence

  `R_s = -2 C_s - Y_s`,  `Y_s = log |f̂_s|`   (`sigmaLogRatio_eq_cos_sub_logFHat`).

* `integralII_eq`: `(II) = (I) + 2 ∫ cos(2u) dν`;
* `ae_tendsto_sigmaLogRatio_div`: `P ⊗ ν`-a.s. `R_s / s → -(II)`, by the Birkhoff limits
  `Y_s / s → (I)` (`birkhoff_logFHat_const`) and `C_s / s → ∫ cos(2u) dν`
  (`birkhoff_cosInt_const`);
* `ae_ae_hull_approach`: if `(II) < 0` then `R_s → +∞` and, by the Koebe hitting bound in σ-time
  (`ae_exists_infDist_leftHull_lt_of_tendsto`), for `ν`-a.e. `u`, a.s.
  `∀ ε > 0, ∃ t < T_z, dist(z, L_t) < ε` at `z = e^{iu}` (the R14 `ε`-form of Proposition 3.2(a)).

Consumes the EXTERNALs consumed by `ErgodicRatioConst.lean`; the EXTERNAL
`markov_oneDim` (R29) is the hypothesis `hMO : MarkovOneDim`.
-/

public section

open scoped NNReal ENNReal Topology Real
open Set Metric MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal

open Polar

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-- `(II) = (I) + 2 ∫ cos(2u) dν`. -/
theorem integralII_eq {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) :
    integralII a b c p = integralI a b c p + 2 * cosMean p := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  have hnu : Integrable (nu a b c) (admissibleMeasure p) :=
    Integrable.of_bound (continuous_nu a b c).aestronglyMeasurable (|2 - a / 2 + b / 2| + |c|)
      (Eventually.of_forall fun u => by simpa [Real.norm_eq_abs] using abs_nu_le a b c u)
  have hcos : Integrable (fun u : ℝ => 2 * Real.cos (2 * u)) (admissibleMeasure p) :=
    Integrable.of_bound
      (by fun_prop : Continuous fun u : ℝ => 2 * Real.cos (2 * u)).aestronglyMeasurable
      2 (Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_mul, abs_two]
        exact mul_le_of_le_one_right (by norm_num) (Real.abs_cos_le_one _))
  have h1 : integralII a b c p =
      ∫ u, (nu a b c u + 2 * Real.cos (2 * u)) ∂(admissibleMeasure p) := by
    rw [integral_admissibleMeasure hp]
    rfl
  rw [h1, integral_add hnu hcos, integral_nu_admissibleMeasure hp, integral_const_mul]
  rfl

variable (hU : IsSLEDriverAdapted a b c U P ℱ)

/-- On the good set, `R_s = -2 C_s - Y_s`:
`log(|f̂'_s|/|f̂_s|) = -2 ∫₀ˢ cos 2θ̂_v dv - log |f̂_s|`. -/
theorem sigmaLogRatio_eq_cos_sub_logFHat {q : Ω × ℝ} (hq : q ∈ goodSet hU) (s : ℝ≥0) :
    sigmaLogRatio hU (unitPt q.2) s q.1 = -2 * cosIntU hU s q - logFHat hU s q := by
  have hs := mem_sigmaDom_of_mem_goodSet hU hq s
  have h1 : sigmaLogDeriv hU (unitPt q.2) s q.1 = -2 * cosIntU hU s q := by
    rw [sigmaLogDeriv_eq hU hs]
    congr 1
    simp only [cosIntU, cosInt_eq]
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le s.coe_nonneg] at hv
    have hv' := mem_sigmaDom_of_mem_goodSet hU hq v.toNNReal
    simp only [cosTwoHat, cosHatF, thetaHat_of_mem hU hv', Real.coe_toNNReal _ hv.1]
  have h2 : sigmaLogNorm hU (unitPt q.2) s q.1 = logFHat hU s q := by
    simp only [logFHat, fHat_of_mem hU hs, sigmaLogNorm]
  rw [sigmaLogRatio, h1, h2]

variable [IsProbabilityMeasure P]

/-- **Lemma 3.7 (`lem-integral-ii`): `R_s / s → -(II)`** (paper.tex:L1430-1455). Under
`hMO : MarkovOneDim`: `P ⊗ ν`-a.s.,
`log(|f̂'_s(e^{iu})| / |f̂_s(e^{iu})|) / s → -(II)` as `s → ∞` along `ℝ≥0`. -/
theorem ae_tendsto_sigmaLogRatio_div (hMO : MarkovOneDim) (ha : 0 < a) (hb : 0 < b)
    (hc : c ^ 2 ≤ a * b) {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) :
    ∀ᵐ q ∂(P.prod (admissibleMeasure p)),
      Tendsto (fun s : ℝ≥0 => sigmaLogRatio hU (unitPt q.2) s q.1 / s) atTop
        (𝓝 (-integralII a b c p)) := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  filter_upwards [birkhoff_logFHat_const hMO hU ha hb hc hp,
    birkhoff_cosInt_const hMO hU ha hb hc hp,
    ae_mem_goodSet hU ha hc (ν := admissibleMeasure p)] with q h1 h2 hq
  have h3 := ((h2.const_mul (-2)).sub h1)
  have e : -integralII a b c p = -2 * cosMean p - integralI a b c p := by
    rw [integralII_eq hp]; ring
  rw [e]
  refine h3.congr fun s => ?_
  rw [sigmaLogRatio_eq_cos_sub_logFHat hU hq s]
  ring

include hU in
/-- **Proposition 3.2(a) at the unit points.** If `(II) < 0` then for `ν`-a.e. `u`, almost surely
`∀ ε > 0, ∃ t < T_z, dist(z, L_t) < ε` at `z = e^{iu}`. (Lemma 3.7: `R_s / s → -(II) > 0`, so
`R_s → +∞`; the Koebe hitting bound in σ-time turns this into the `ε`-form.) -/
theorem ae_ae_hull_approach (hMO : MarkovOneDim) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (hII : integralII a b c p < 0) :
    ∀ᵐ u ∂(admissibleMeasure p), ∀ᵐ ω ∂P, ∀ ε > 0, ∃ t : ℝ≥0,
      (t : ℝ≥0∞) < absorbingTime (fun s => U s ω) (unitPt u) ∧
        infDist (unitPt u) (leftHull (fun s => U s ω) t) < ε := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  have hfib := ae_ae_of_ae_prod_snd (ae_tendsto_sigmaLogRatio_div hU hMO ha hb hc hp)
  filter_upwards [hfib] with u hu
  refine ae_exists_infDist_leftHull_lt_of_tendsto hU ha hc (unitPt_ne_zero u) ?_
  filter_upwards [hu] with ω hω
  have hpos : 0 < -integralII a b c p := neg_pos.2 hII
  have hs : Tendsto (fun s : ℝ≥0 => (s : ℝ)) atTop atTop := NNReal.tendsto_coe_atTop.2 tendsto_id
  have h := hω.pos_mul_atTop hpos hs
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with s hs0
  have hs0' : (0 : ℝ) < s := by exact_mod_cast hs0
  field_simp

end ComplexSLE.Internal

end
