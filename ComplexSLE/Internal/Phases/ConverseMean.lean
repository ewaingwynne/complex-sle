/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.Prop32ARatio

/-!
# The mean of `log(|f̂'_t̃|/|f̂_t̃|)` (Lemma 3.6 in expectation, M7/E4)

Source: paper.tex:L1430-1440 (the first part of `lem-integral-ii`) and Step 2 of the proof of
`lem-converse-w-o-upgrade` (paper.tex:L1677-1690). On `(Ω × ℝ, P ⊗ ν)`, `ν = p(u) 1_{[0,2π]}(u) du`,
`R_t̃ = log(|f̂'_t̃(e^{iu})| / |f̂_t̃(e^{iu})|)` (`sigmaLogRatio`) is integrable and

  `E R_t̃ = - t̃ · (II)`.

The proof is the decomposition `R_t̃ = -2 C_t̃ - Y_t̃` (`sigmaLogRatio_eq_cos_sub_logFHat`) with
`C_t̃ = ∫₀^t̃ cos 2θ̂_v dv` (`cosIntU`) and `Y_t̃ = log |f̂_t̃|` (`logFHat`):

* `E Y_t̃ = t̃ (I)` (`integrable_integral_logFHat`);
* `E C_t̃ = t̃ ∫ cos(2u) dν` (`integral_cosIntU`): `C_t̃` is the limit of its Riemann sums, whose
  means are `t̃ ∫ cos 2u dν` by one-time stationarity (`integral_cos_thetaHat`), and which are
  bounded by `t̃` (dominated convergence);
* `(II) = (I) + 2 ∫ cos(2u) dν` (`integralII_eq`).

The EXTERNAL `markov_oneDim` (R29) enters as the hypothesis `hMO : MarkovOneDim`, as in
`Lemma37.lean` (it is discharged with `External.markov_oneDim` in `ConverseMain.lean`).
-/

public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal

open Polar

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-! ### Riemann sums of `C_t̃` -/

/-- The Riemann sums `∑_{k<N} (t̃/N) cos 2θ̂_{k t̃/N}` of `C_t̃`. -/
noncomputable def cosRiemann (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) (N : ℕ)
    (q : Ω × ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, ((t : ℝ) / N) *
    Real.cos (2 * thetaHat hU (unitPt q.2) (((k : ℝ) * t / N).toNNReal) q.1)

theorem measurable_cosRiemann (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) (N : ℕ) :
    Measurable (cosRiemann hU t N) :=
  Finset.measurable_sum _ fun _ _ =>
    measurable_const.mul
      (Real.measurable_cos.comp (measurable_const.mul (measurable_thetaHat_unit hU _)))

theorem abs_cosRiemann_le (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) (N : ℕ)
    (q : Ω × ℝ) : |cosRiemann hU t N q| ≤ t := by
  unfold cosRiemann
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  calc |∑ k ∈ Finset.range N, ((t : ℝ) / N) *
        Real.cos (2 * thetaHat hU (unitPt q.2) (((k : ℝ) * t / N).toNNReal) q.1)|
      ≤ ∑ k ∈ Finset.range N, |((t : ℝ) / N) *
        Real.cos (2 * thetaHat hU (unitPt q.2) (((k : ℝ) * t / N).toNNReal) q.1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range N, ((t : ℝ) / N) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t : ℝ) / N)]
        exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
    _ = t := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

theorem tendsto_cosRiemann (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) {q : Ω × ℝ}
    (hq : q ∈ goodSet hU) :
    Tendsto (fun N : ℕ => cosRiemann hU t N q) atTop (𝓝 (cosIntU hU t q)) := by
  have hc : Continuous (cosHatF hU (unitPt q.2) q.1) :=
    continuous_cosHatF hU (continuous_thetaHat_of_mem_goodSet hU hq)
  have h := tendsto_riemannSum (φ := cosHatF hU (unitPt q.2) q.1) t.coe_nonneg hc.continuousOn
  simpa only [cosRiemann, cosHatF, cosIntU, cosInt_eq] using h

theorem integrable_cos_comp_thetaHat [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) {ν : Measure ℝ} [IsProbabilityMeasure ν] (s : ℝ≥0) :
    Integrable (fun q : Ω × ℝ => Real.cos (2 * thetaHat hU (unitPt q.2) s q.1)) (P.prod ν) :=
  (integrable_const (1 : ℝ)).mono'
    (Real.measurable_cos.comp
      (measurable_const.mul (measurable_thetaHat_unit hU s))).aestronglyMeasurable
    (Eventually.of_forall fun q => by simpa [Real.norm_eq_abs] using Real.abs_cos_le_one _)

/-- **The mean of `C_t̃`**: `E C_t̃ = t̃ ∫ cos(2u) dν`; `C_t̃` is a.e. strongly measurable. -/
theorem integral_cosIntU [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (t : ℝ≥0) :
    AEStronglyMeasurable (cosIntU hU t) (P.prod (admissibleMeasure p)) ∧
      ∫ q, cosIntU hU t q ∂(P.prod (admissibleMeasure p)) = t * cosMean p := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  have hlim : ∀ᵐ q ∂(P.prod (admissibleMeasure p)),
      Tendsto (fun N : ℕ => cosRiemann hU t N q) atTop (𝓝 (cosIntU hU t q)) :=
    (ae_mem_goodSet hU ha hc).mono fun q hq => tendsto_cosRiemann hU t hq
  have hm : ∀ N, AEStronglyMeasurable (cosRiemann hU t N) (P.prod (admissibleMeasure p)) :=
    fun N => (measurable_cosRiemann hU t N).aestronglyMeasurable
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop hm hlim, ?_⟩
  have hDCT := tendsto_integral_of_dominated_convergence
    (μ := P.prod (admissibleMeasure p)) (fun _ => (t : ℝ)) hm
    (integrable_const _) (fun N => Eventually.of_forall fun q => by
      simpa [Real.norm_eq_abs] using abs_cosRiemann_le hU t N q) hlim
  have hmean : ∀ N : ℕ, 0 < N → ∫ q, cosRiemann hU t N q ∂(P.prod (admissibleMeasure p)) =
      t * cosMean p := fun N hN => by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    unfold cosRiemann
    rw [integral_finsetSum _ fun k _ => (integrable_cos_comp_thetaHat hU _).const_mul _]
    simp only [integral_const_mul, integral_cos_thetaHat hMO hU ha hb hc hp]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have hev : ∀ᶠ N : ℕ in atTop, ∫ q, cosRiemann hU t N q ∂(P.prod (admissibleMeasure p)) =
      t * cosMean p := by
    filter_upwards [eventually_gt_atTop 0] with N hN using hmean N hN
  exact tendsto_nhds_unique hDCT (tendsto_const_nhds.congr' (hev.mono fun N h => h.symm))

theorem abs_cosIntU_le_of_mem_goodSet (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0)
    {q : Ω × ℝ} (hq : q ∈ goodSet hU) : |cosIntU hU t q| ≤ t :=
  abs_cosInt_le hU (continuous_thetaHat_of_mem_goodSet hU hq) t

theorem integrable_cosIntU [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (t : ℝ≥0) :
    Integrable (cosIntU hU t) (P.prod (admissibleMeasure p)) := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  refine (integrable_const (t : ℝ)).mono' (integral_cosIntU hMO hU ha hb hc hp t).1 ?_
  filter_upwards [ae_mem_goodSet hU ha hc (ν := admissibleMeasure p)] with q hq
  simpa [Real.norm_eq_abs] using abs_cosIntU_le_of_mem_goodSet hU t hq

/-! ### The mean of `R_t̃` -/

/-- **`R_t̃ = log(|f̂'_t̃|/|f̂_t̃|)` is `P ⊗ ν`-a.e. equal to `-2 C_t̃ - Y_t̃`.** -/
theorem ae_sigmaLogRatio_eq [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ)
    (ha : 0 < a) (hc : c ^ 2 ≤ a * b) {ν : Measure ℝ} [SFinite ν] (t : ℝ≥0) :
    (fun q : Ω × ℝ => sigmaLogRatio hU (unitPt q.2) t q.1) =ᵐ[P.prod ν]
      fun q => -2 * cosIntU hU t q - logFHat hU t q :=
  (ae_mem_goodSet hU ha hc (ν := ν)).mono fun _ hq => sigmaLogRatio_eq_cos_sub_logFHat hU hq t

theorem aestronglyMeasurable_sigmaLogRatio [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (t : ℝ≥0) :
    AEStronglyMeasurable (fun q : Ω × ℝ => sigmaLogRatio hU (unitPt q.2) t q.1)
      (P.prod (admissibleMeasure p)) := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  have h1 := (integral_cosIntU hMO hU ha hb hc hp t).1
  have h2 := (measurable_logFHat hU t).aestronglyMeasurable (μ := P.prod (admissibleMeasure p))
  exact ((h1.const_mul (-2)).sub h2).congr (ae_sigmaLogRatio_eq hU ha hc t).symm

/-- **`R_t̃` is integrable** (Step 2 of paper.tex:L1677-1690: `E |log(|f_t'|/|f_t|)| < ∞`). -/
theorem integrable_sigmaLogRatio [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (t : ℝ≥0) :
    Integrable (fun q : Ω × ℝ => sigmaLogRatio hU (unitPt q.2) t q.1)
      (P.prod (admissibleMeasure p)) := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  have h1 := integrable_cosIntU hMO hU ha hb hc hp t
  have h2 := (integrable_integral_logFHat hMO hU ha hb hc hp t).1
  exact ((h1.const_mul (-2)).sub h2).congr (ae_sigmaLogRatio_eq hU ha hc t).symm

/-- **Lemma 3.6 in expectation: `E log(|f̂'_t̃|/|f̂_t̃|) = - t̃ · (II)`** (paper.tex:L1430-1440). -/
theorem integral_sigmaLogRatio [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (t : ℝ≥0) :
    ∫ q, sigmaLogRatio hU (unitPt q.2) t q.1 ∂(P.prod (admissibleMeasure p)) =
      -(t * integralII a b c p) := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  have h1 := integrable_cosIntU hMO hU ha hb hc hp t
  have h2 := integrable_integral_logFHat hMO hU ha hb hc hp t
  rw [integral_congr_ae (ae_sigmaLogRatio_eq hU ha hc t),
    integral_sub (h1.const_mul (-2)) h2.1, integral_const_mul,
    (integral_cosIntU hMO hU ha hb hc hp t).2, h2.2, integralII_eq hp]
  ring

end ComplexSLE.Internal

end
