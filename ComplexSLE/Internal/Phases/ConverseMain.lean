/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.ConverseChain
public import ComplexSLE.Internal.Phases.ConverseMean
public import ComplexSLE.Internal.Phases.ConverseLemma38
public import ComplexSLE.Internal.Phases.Lemma37
import ComplexSLE.External.MarkovOneDim

/-!
# Lemma 3.9 (`lem-converse-w-o-upgrade`): the converse, Step 2 of the proof (M7/E4)

Source: paper.tex:L1475-1480 (statement), L1640-1700 (Steps 1-2). Let `a, b > 0`, `c² ≤ ab`,
`hU : IsSLEDriverAdapted a b c U P ℱ`, `p` an admissible density with `(II) > 0`,
`ν = admissibleMeasure p`, `μ = P ⊗ ν` and `𝐳 = e^{iu}`, `u ∼ ν`. Then

  `μ(∃ ε > 0, ∀ t < T_𝐳, ε ≤ dist(𝐳, L_t)) > 0`

(the R14 ε-form of "the probability that `lim_{t → T_𝐳⁻} dist(𝐳, L_t) = 0` is strictly less than
`1`"; `t ↦ dist(𝐳, L_t)` is antitone, so the limit is positive iff it is bounded below).

## Proof (the contrapositive of the paper, paper.tex:L1655-1700)

Assume `lim dist = 0` `μ`-a.s. Fix `t̃, s̃ ≥ 0`, `t = σ(t̃)`, `s = σ(s̃ + t̃) - σ(t̃)`, and let
`X_s̃ = dist(f_t 𝐳, L_{t,s+t}) / |f_t 𝐳|` (`futureDistRatioRV`), `R = log(|f_t'|/|f_t|)`
(`sigmaLogRatio`), `L = log(1/dist(𝐳, L_t))`.

* `eqn-dist-3` (`ConverseChain.lean`, the deterministic Koebe chain): pointwise
  `log X_s̃ - log dist(𝐳, L_{s+t}) ≤ 1_{E_s̃} R + 1_{E_s̃^c} L + log 16`.
* `E_s̃` is replaced by the null-measurable event `F_s̃ = {X_s̃ ≤ |f_t'| dist(𝐳, L_t) / (4 |f_t|)}`
  `⊆ E_s̃` (this avoids the measurability of `dist(f_t 𝐳, R_t)`), and on `F_s̃^c` the cruder bound
  `log X_s̃ - log dist(𝐳, L_{s+t}) ≤ L + log 64` is used (`chain_sigma_le`).
  Thus `log X_s̃ - log dist ≤ H_s̃ := 1_{F} (R + log 16) + 1_{F^c} (L + log 64)`.
* Left side: by Lemma 3.7 (`integral_comp_lemma_3_7`), `E log X_s̃ = E log dist(𝐳, L_{σ(s̃)}) ≥
  E log dist(𝐳, L_{σ(s̃ + t̃)})`, all integrable by Lemma 3.8; so `E[LHS] ≥ 0`, hence `E H_s̃ ≥ 0`.
* Right side: as `s̃ → ∞` the `μ`-a.s. assumption gives `1_{F_s̃} → 1`
  (`eventually_le_koebeBound`), and
  `|H_s̃| ≤ |R| + |L| + log 64` is integrable (Lemma 3.6 mean, `integrable_sigmaLogRatio`), so by
  dominated convergence `E H_s̃ → E R + log 16 = -t̃ (II) + log 16` (`integral_sigmaLogRatio`).
* So `t̃ (II) ≤ log 16` for all `t̃`, contradicting `(II) > 0`.

The proof consumes the EXTERNALs consumed by Lemmas 3.7, 3.6 and 3.8 and by `koebe_chain`
(`koebe_quarter`, `strongMarkov_sleDriver`, `hormander_oneDim`, `ito_formula`,
`timeChange_isContLocalMartingale`, `markov_oneDim`). Lemma 3.8 is taken from the import-clash copy
`ConverseLemma38.lean`.
-/

public section

open scoped NNReal ENNReal Topology Real
open Set Metric MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal

open Polar

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-! ### The Koebe bound along the driver, and measurability -/

/-- The threshold of the event `F_s̃` along the random point:
`|f_t'(𝐳)| dist(𝐳, L_t) / (4 |f_t(𝐳)|)` at `t = σ_𝐳(t̃)`. -/
@[expose] noncomputable def koebeBoundRV (hU : IsSLEDriverAdapted a b c U P ℱ) (tt : ℝ≥0)
    (q : Ω × ℝ) : ℝ :=
  koebeBound (fun r => U r q.1) (hU.cont q.1) (unitPt q.2) tt

/-- The event `F_s̃ = {X_s̃ ≤ koebeBound}` (a subset of `E_s̃`). -/
@[expose] def eventF (hU : IsSLEDriverAdapted a b c U P ℱ) (tt ss : ℝ≥0) : Set (Ω × ℝ) :=
  {q | futureDistRatioRV hU tt ss q ≤ koebeBoundRV hU tt q}

theorem koebeBoundRV_eq (hU : IsSLEDriverAdapted a b c U P ℱ) (tt : ℝ≥0) (q : Ω × ℝ) :
    koebeBoundRV hU tt q =
      Real.exp (sigmaLogRatio hU (unitPt q.2) tt q.1) * distSigma hU tt q / 4 := rfl

/-- On the good set `σ_𝐳` is defined on all of `[0, ∞)`. -/
theorem sigmaDom_eq_Ici_of_mem_goodSet (hU : IsSLEDriverAdapted a b c U P ℱ) {q : Ω × ℝ}
    (hq : q ∈ goodSet hU) :
    sigmaDom (fun r => U r q.1) (hU.cont q.1) (unitPt q.2) = Ici 0 := by
  ext s
  refine ⟨fun h => h.1, fun hs => ?_⟩
  have := mem_sigmaDom_of_mem_goodSet hU hq s.toNNReal
  rwa [Real.coe_toNNReal _ hs] at this

theorem aemeasurable_distSigma [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ)
    (ha : 0 < a) (hc : c ^ 2 ≤ a * b) {ν : Measure ℝ} [SFinite ν] (s : ℝ≥0) :
    AEMeasurable (distSigma hU s) (P.prod ν) := by
  refine (measurable_distSigmaTilde hU s).aemeasurable.congr ?_
  filter_upwards [ae_mem_goodSet hU ha hc (ν := ν)] with q hq
  simp only [distSigmaTilde, mem_sigmaDom_of_mem_goodSet hU hq s, ↓reduceIte]

theorem aestronglyMeasurable_koebeBoundRV [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (tt : ℝ≥0) :
    AEMeasurable (koebeBoundRV hU tt) (P.prod (admissibleMeasure p)) := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  have hR := (aestronglyMeasurable_sigmaLogRatio hMO hU ha hb hc hp tt).aemeasurable
  have hD := aemeasurable_distSigma hU ha hc (ν := admissibleMeasure p) tt
  exact ((Real.measurable_exp.comp_aemeasurable hR).mul hD).div_const 4

theorem nullMeasurableSet_eventF [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (tt ss : ℝ≥0) :
    NullMeasurableSet (eventF hU tt ss) (P.prod (admissibleMeasure p)) := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  exact nullMeasurableSet_le
    (aemeasurable_futureDistRatioRV hU ha hc (ν := admissibleMeasure p) tt ss)
    (aestronglyMeasurable_koebeBoundRV hMO hU ha hb hc hp tt)


/-! ### The pointwise bound -/

/-- `H_s̃ = 1_{F_s̃} (R + log 16) + 1_{F_s̃^c} (L + log 64)`, the integrable majorant of
`log X_s̃ - log dist(𝐳, L_{σ(s̃ + t̃)})`. -/
@[expose] noncomputable def boundH (hU : IsSLEDriverAdapted a b c U P ℱ) (tt ss : ℝ≥0)
    (q : Ω × ℝ) : ℝ :=
  (eventF hU tt ss).indicator
      (fun q => sigmaLogRatio hU (unitPt q.2) tt q.1 + Real.log 16) q +
    (eventF hU tt ss)ᶜ.indicator
      (fun q => Real.log (1 / distSigma hU tt q) + Real.log 64) q

/-- `|H_s̃| ≤ |R| + |L| + log 64`. -/
theorem abs_boundH_le (hU : IsSLEDriverAdapted a b c U P ℱ) (tt ss : ℝ≥0) (q : Ω × ℝ) :
    |boundH hU tt ss q| ≤ |sigmaLogRatio hU (unitPt q.2) tt q.1| +
      |Real.log (1 / distSigma hU tt q)| + Real.log 64 := by
  have h16 : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
  have h64 : 0 ≤ Real.log 64 := Real.log_nonneg (by norm_num)
  have h1664 : Real.log 16 ≤ Real.log 64 := Real.log_le_log (by norm_num) (by norm_num)
  have hR := abs_nonneg (sigmaLogRatio hU (unitPt q.2) tt q.1)
  have hL := abs_nonneg (Real.log (1 / distSigma hU tt q))
  unfold boundH
  by_cases hF : q ∈ eventF hU tt ss
  · rw [Set.indicator_of_mem hF, Set.indicator_of_notMem (by simpa using hF), add_zero]
    calc |sigmaLogRatio hU (unitPt q.2) tt q.1 + Real.log 16|
        ≤ |sigmaLogRatio hU (unitPt q.2) tt q.1| + |Real.log 16| := abs_add_le _ _
      _ ≤ _ := by rw [abs_of_nonneg h16]; linarith
  · rw [Set.indicator_of_notMem hF, Set.indicator_of_mem (by simpa using hF), zero_add]
    calc |Real.log (1 / distSigma hU tt q) + Real.log 64|
        ≤ |Real.log (1 / distSigma hU tt q)| + |Real.log 64| := abs_add_le _ _
      _ ≤ _ := by rw [abs_of_nonneg h64]; linarith

/-- **`eqn-dist-3` majorization**: on the good set, for all `t̃, s̃`,
`log X_s̃ - log dist(𝐳, L_{σ(s̃ + t̃)}) ≤ H_s̃`. -/
theorem log_sub_le_boundH (hU : IsSLEDriverAdapted a b c U P ℱ) {q : Ω × ℝ} (hq : q ∈ goodSet hU)
    (tt ss : ℝ≥0) :
    Real.log (futureDistRatioRV hU tt ss q) - Real.log (distSigma hU (ss + tt) q) ≤
      boundH hU tt ss q := by
  have hdom := sigmaDom_eq_Ici_of_mem_goodSet hU hq
  have htt : (tt : ℝ) ∈ sigmaDom (fun r => U r q.1) (hU.cont q.1) (unitPt q.2) := by
    rw [hdom]; exact tt.coe_nonneg
  have hts : (ss : ℝ) + tt ∈ sigmaDom (fun r => U r q.1) (hU.cont q.1) (unitPt q.2) := by
    rw [hdom]; exact add_nonneg ss.coe_nonneg tt.coe_nonneg
  unfold boundH
  by_cases hF : q ∈ eventF hU tt ss
  · rw [Set.indicator_of_mem hF, Set.indicator_of_notMem (by simpa using hF), add_zero]
    have hE := koebeEventSigma_of_le (hU.cont q.1) htt (ss := ss) hF
    exact chain_sigma_of_event (hU.cont q.1) htt hts hE
  · rw [Set.indicator_of_notMem hF, Set.indicator_of_mem (by simpa using hF), zero_add]
    exact chain_sigma_le (hU.cont q.1) htt hts

/-- `dist(𝐳, L_{σ(s̃ + t̃)}) ≤ dist(𝐳, L_{σ(s̃)})` on the good set. -/
theorem distSigma_add_le (hU : IsSLEDriverAdapted a b c U P ℱ) {q : Ω × ℝ} (hq : q ∈ goodSet hU)
    (tt ss : ℝ≥0) : distSigma hU (ss + tt) q ≤ distSigma hU ss q := by
  have h1 := mem_sigmaDom_of_mem_goodSet hU hq ss
  have h2 := mem_sigmaDom_of_mem_goodSet hU hq (ss + tt)
  have hmono := sigmaTime_monotoneOn (hU.cont q.1) (unitPt q.2) h1 h2 (by simp)
  have hsub : leftHull (fun r => U r q.1)
      (sigmaTime (fun r => U r q.1) (hU.cont q.1) (unitPt q.2) (ss : ℝ)).toNNReal ⊆
      leftHull (fun r => U r q.1)
        (sigmaTime (fun r => U r q.1) (hU.cont q.1) (unitPt q.2) ((ss + tt : ℝ≥0) : ℝ)).toNNReal :=
    leftHull_mono (Real.toNNReal_le_toNNReal hmono)
  exact infDist_le_infDist_of_subset hsub (leftHull_nonempty _ _)


/-! ### Integrability and the nonnegativity of `E H_s̃` -/

section Integrals

variable [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b)
  (hc : c ^ 2 ≤ a * b) {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p)

include ha hc hp in
/-- **Lemma 3.8** for `log dist` (rather than `log (1/dist)`). -/
theorem integrable_log_distSigma (s : ℝ≥0) :
    Integrable (fun q : Ω × ℝ => Real.log (distSigma hU s q)) (P.prod (admissibleMeasure p)) := by
  refine (Converse38.integrable_log_inv_distSigma_admissible hU ha hc hp s).neg.congr
    (Eventually.of_forall fun q => ?_)
  simp [Real.log_inv]

include ha hb hc hp in
/-- `log X_s̃` is integrable: by Lemma 3.7 it has the law of `log dist(𝐳, L_{σ(s̃)})`. -/
theorem integrable_log_futureDistRatioRV (hMO : MarkovOneDim) (tt ss : ℝ≥0) :
    Integrable (fun q : Ω × ℝ => Real.log (futureDistRatioRV hU tt ss q))
      (P.prod (admissibleMeasure p)) := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  have hXae := aemeasurable_futureDistRatioRV hU ha hc (ν := admissibleMeasure p) tt ss
  have hYae := aemeasurable_hullDistRV hU ha hc (ν := admissibleMeasure p) ss
  have hY : Integrable Real.log ((P.prod (admissibleMeasure p)).map (hullDistRV hU ss)) :=
    (integrable_map_measure Real.measurable_log.aestronglyMeasurable hYae).2
      (integrable_log_distSigma hU ha hc hp ss)
  rw [← lemma_3_7_of_markov hMO hU ha hb hc hp tt ss] at hY
  exact (integrable_map_measure Real.measurable_log.aestronglyMeasurable hXae).1 hY

include ha hb hc hp in
/-- **Step 2, left side**: `E[log X_s̃ - log dist(𝐳, L_{σ(s̃ + t̃)})] ≥ 0` (Lemma 3.7 and
`dist(𝐳, L_{σ(s̃ + t̃)}) ≤ dist(𝐳, L_{σ(s̃)})`). -/
theorem integral_log_sub_nonneg (hMO : MarkovOneDim) (tt ss : ℝ≥0) :
    0 ≤ ∫ q, (Real.log (futureDistRatioRV hU tt ss q) - Real.log (distSigma hU (ss + tt) q))
      ∂(P.prod (admissibleMeasure p)) := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  have hA := integrable_log_futureDistRatioRV hU ha hb hc hp hMO tt ss
  have hB := integrable_log_distSigma hU ha hc hp (ss + tt)
  have hC := integrable_log_distSigma hU ha hc hp ss
  have hAC : ∫ q, Real.log (futureDistRatioRV hU tt ss q) ∂(P.prod (admissibleMeasure p)) =
      ∫ q, Real.log (distSigma hU ss q) ∂(P.prod (admissibleMeasure p)) :=
    integral_comp_lemma_3_7_of_markov hMO hU ha hb hc hp tt ss Real.measurable_log
  have hBC : ∫ q, Real.log (distSigma hU (ss + tt) q) ∂(P.prod (admissibleMeasure p)) ≤
      ∫ q, Real.log (distSigma hU ss q) ∂(P.prod (admissibleMeasure p)) := by
    refine integral_mono_ae hB hC ?_
    filter_upwards [Converse38.ae_distSigma_pos_admissible hU ha hc hp (ss + tt),
      ae_mem_goodSet hU ha hc (ν := admissibleMeasure p)] with q hpos hq
    exact Real.log_le_log hpos (distSigma_add_le hU hq tt ss)
  rw [integral_sub hA hB, hAC]
  linarith


include ha hb hc hp in
theorem aestronglyMeasurable_boundH (hMO : MarkovOneDim) (tt ss : ℝ≥0) :
    AEStronglyMeasurable (boundH hU tt ss) (P.prod (admissibleMeasure p)) := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  have hFn := nullMeasurableSet_eventF hMO hU ha hb hc hp tt ss
  have hR := aestronglyMeasurable_sigmaLogRatio hMO hU ha hb hc hp tt
  have hL :=
    (Converse38.integrable_log_inv_distSigma_admissible hU ha hc hp tt).aestronglyMeasurable
  exact ((hR.add aestronglyMeasurable_const).indicator₀ hFn).add
    ((hL.add aestronglyMeasurable_const).indicator₀ hFn.compl)

include ha hb hc hp in
/-- The dominating function `|R| + |L| + log 64` is integrable (Lemmas 3.6 and 3.8). -/
theorem integrable_boundH_bound (hMO : MarkovOneDim) (tt : ℝ≥0) :
    Integrable (fun q : Ω × ℝ => |sigmaLogRatio hU (unitPt q.2) tt q.1| +
      |Real.log (1 / distSigma hU tt q)| + Real.log 64) (P.prod (admissibleMeasure p)) := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  exact ((integrable_sigmaLogRatio hMO hU ha hb hc hp tt).abs.add
    (Converse38.integrable_log_inv_distSigma_admissible hU ha hc hp tt).abs).add
    (integrable_const _)

include ha hb hc hp in
theorem integrable_boundH (hMO : MarkovOneDim) (tt ss : ℝ≥0) :
    Integrable (boundH hU tt ss) (P.prod (admissibleMeasure p)) :=
  (integrable_boundH_bound hU ha hb hc hp hMO tt).mono'
    (aestronglyMeasurable_boundH hU ha hb hc hp hMO tt ss)
    (Eventually.of_forall fun q => by
      simpa only [Real.norm_eq_abs] using abs_boundH_le hU tt ss q)

include ha hb hc hp in
/-- **Step 2, in expectation**: `0 ≤ E H_s̃` for every `t̃, s̃`. -/
theorem integral_boundH_nonneg (hMO : MarkovOneDim) (tt ss : ℝ≥0) :
    0 ≤ ∫ q, boundH hU tt ss q ∂(P.prod (admissibleMeasure p)) := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  refine (integral_log_sub_nonneg hU ha hb hc hp hMO tt ss).trans (integral_mono_ae ?_
    (integrable_boundH hU ha hb hc hp hMO tt ss) ?_)
  · exact (integrable_log_futureDistRatioRV hU ha hb hc hp hMO tt ss).sub
      (integrable_log_distSigma hU ha hc hp (ss + tt))
  · filter_upwards [ae_mem_goodSet hU ha hc (ν := admissibleMeasure p)] with q hq
    exact log_sub_le_boundH hU hq tt ss

include ha hb hc hp in
/-- **Step 2, the limit `s̃ → ∞`** (dominated convergence): under the a.s. assumption
`lim_{t → T_𝐳} dist(𝐳, L_t) = 0` (R14 ε-form), `E H_s̃ → E (R + log 16)`. -/
theorem tendsto_integral_boundH (hMO : MarkovOneDim)
    (hlim : ∀ᵐ q ∂(P.prod (admissibleMeasure p)), ∀ ε > 0, ∃ t : ℝ≥0,
      (t : ℝ≥0∞) < absorbingTime (fun s => U s q.1) (unitPt q.2) ∧
        infDist (unitPt q.2) (leftHull (fun s => U s q.1) t) < ε) (tt : ℝ≥0) :
    Tendsto (fun ss : ℝ≥0 => ∫ q, boundH hU tt ss q ∂(P.prod (admissibleMeasure p))) atTop
      (𝓝 (∫ q, (sigmaLogRatio hU (unitPt q.2) tt q.1 + Real.log 16)
        ∂(P.prod (admissibleMeasure p)))) := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  refine tendsto_integral_filter_of_dominated_convergence _
    (Eventually.of_forall fun ss => aestronglyMeasurable_boundH hU ha hb hc hp hMO tt ss)
    (Eventually.of_forall fun ss => Eventually.of_forall fun q => by
      simpa only [Real.norm_eq_abs] using abs_boundH_le hU tt ss q)
    (integrable_boundH_bound hU ha hb hc hp hMO tt) ?_
  filter_upwards [hlim, ae_mem_goodSet hU ha hc (ν := admissibleMeasure p)] with q hq1 hq2
  have hev := eventually_le_koebeBound (hU.cont q.1) tt
    (sigmaDom_eq_Ici_of_mem_goodSet hU hq2) hq1
  refine tendsto_const_nhds.congr' (hev.mono fun ss hss => ?_)
  have hF : q ∈ eventF hU tt ss := hss
  change _ = boundH hU tt ss q
  unfold boundH
  rw [Set.indicator_of_mem hF, Set.indicator_of_notMem (by simpa using hF), add_zero]

include hU ha hb hc hp in
/-- **Step 2, conclusion**: under the a.s. assumption, `0 ≤ -t̃ (II) + log 16` for every `t̃`. -/
theorem le_log_of_ae_hull_approach (hMO : MarkovOneDim)
    (hlim : ∀ᵐ q ∂(P.prod (admissibleMeasure p)), ∀ ε > 0, ∃ t : ℝ≥0,
      (t : ℝ≥0∞) < absorbingTime (fun s => U s q.1) (unitPt q.2) ∧
        infDist (unitPt q.2) (leftHull (fun s => U s q.1) t) < ε) (tt : ℝ≥0) :
    0 ≤ -(tt * integralII a b c p) + Real.log 16 := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  have h := ge_of_tendsto' (tendsto_integral_boundH hU ha hb hc hp hMO hlim tt)
    (integral_boundH_nonneg hU ha hb hc hp hMO tt)
  rw [integral_add (integrable_sigmaLogRatio hMO hU ha hb hc hp tt) (integrable_const _),
    integral_sigmaLogRatio hMO hU ha hb hc hp tt] at h
  simpa using h

end Integrals

/-! ### Lemma 3.9 -/

/-- **Lemma 3.9 (`lem-converse-w-o-upgrade`), with the EXTERNAL `markov_oneDim` as `hMO`.**
If `(II) > 0` then, on `μ = P ⊗ ν_p` with the random point `𝐳 = e^{iu}`, the event that
`dist(𝐳, L_t)` stays bounded away from `0` for `t < T_𝐳` (the R14 ε-form of `lim > 0`) has
positive probability. -/
theorem converse_of_markov [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (hII : 0 < integralII a b c p) :
    0 < (P.prod (admissibleMeasure p)) {q : Ω × ℝ | ∃ ε > 0, ∀ t : ℝ≥0,
      (t : ℝ≥0∞) < absorbingTime (fun s => U s q.1) (unitPt q.2) →
        ε ≤ infDist (unitPt q.2) (leftHull (fun s => U s q.1) t)} := by
  by_contra hcon
  have h0 := nonpos_iff_eq_zero.1 (not_lt.1 hcon)
  have hlim : ∀ᵐ q ∂(P.prod (admissibleMeasure p)), ∀ ε > 0, ∃ t : ℝ≥0,
      (t : ℝ≥0∞) < absorbingTime (fun s => U s q.1) (unitPt q.2) ∧
        infDist (unitPt q.2) (leftHull (fun s => U s q.1) t) < ε := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with q hq
    push Not at hq
    exact hq
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.log 16 / integralII a b c p)
  have key := le_log_of_ae_hull_approach hU ha hb hc hp hMO hlim (n : ℝ≥0)
  rw [div_lt_iff₀ hII] at hn
  simp only [NNReal.coe_natCast] at key
  linarith

/-- **Lemma 3.9 (`lem-converse-w-o-upgrade`)**, `markov_oneDim` discharged
(`PROVED_REL` the EXTERNALs consumed by Lemmas 3.7, 3.6, 3.8 and the Koebe chain). -/
theorem converse_w_o_upgrade [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (hII : 0 < integralII a b c p) :
    0 < (P.prod (admissibleMeasure p)) {q : Ω × ℝ | ∃ ε > 0, ∀ t : ℝ≥0,
      (t : ℝ≥0∞) < absorbingTime (fun s => U s q.1) (unitPt q.2) →
        ε ≤ infDist (unitPt q.2) (leftHull (fun s => U s q.1) t)} :=
  converse_of_markov External.markov_oneDim hU ha hb hc hp hII

end ComplexSLE.Internal

end
