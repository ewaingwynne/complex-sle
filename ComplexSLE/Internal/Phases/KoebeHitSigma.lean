/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.KoebeHit
public import ComplexSLE.Internal.Polar.PolarDerivSigma
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Data.EReal.Basic

/-!
# The Koebe hitting bound in σ-time and the hitting-phase closure clause (M7/D1)

Source: paper.tex:L1460-1466 (`eqn-hit-koebe`), the consequence used to prove Proposition 3.2(a)
and the closure clause of the hitting phase (Definition 1.7).

By the Koebe hitting bound (`norm_derivPath_mul_infDist_le`; Koebe constant `koebeK = 48`, see
`KoebeChainInv.lean`), for `s ∈ sigmaDom` and `t = σ_z(s)`,

  `dist(z, L_{σ_z(s)}) ≤ koebeK |f̂_s(z)| / |f̂'_s(z)|
     = koebeK exp(-(log|f̂'_s(z)| - log|f̂_s(z)|))`

(`infDist_leftHull_le_div`, `infDist_leftHull_le_exp`, `infDist_leftHull_sigmaTime_le_exp`).
Consequently, if `log(|f̂'_s(z)|/|f̂_s(z)|)` is unbounded above along `s ∈ sigmaDom`, then
`dist(z, L_t) < ε` for some `t < T_z`, for every `ε > 0`
(`exists_infDist_leftHull_lt_of_ratio_unbounded`). This is exactly:

* the closure clause of the hitting phase `z ∈ closure (⋃_{t < T_z} L_t)`
  (`mem_closure_iUnion_leftHull_of_ratio_unbounded`; the clause of
  `ComplexSLE.IsHittingPhase`, paper.tex:L414), and
* the R14 `ε`-form `∀ ε > 0, ∃ t < T_z, dist(z, L_t) < ε` of Proposition 3.2(a)
  (`exists_infDist_leftHull_lt_of_ratio_unbounded`).

The two conditions are equivalent (`mem_closure_iUnion_leftHull_iff`). For an adapted driver the
hypothesis "`sigmaLogRatio_s → +∞` as `s → ∞`" can be fed in a.s.
(`exists_infDist_leftHull_lt_of_tendsto_sigmaLogRatio`, `ae_exists_infDist_leftHull_lt_of_tendsto`):
Remark 2.12 gives `sigmaDom = [0, ∞)` a.s.
-/

public section

open scoped NNReal ENNReal Topology
open Set Metric Filter MeasureTheory

namespace ComplexSLE.Internal.Polar

open ComplexSLE.Internal.KoebeChain (koebeK koebeK_pos)

/-! ### Deterministic σ-time form -/

section Deterministic

variable {U : ℝ≥0 → ℂ}

/-- **Koebe hitting bound at the time `t = σ_z(s)`** (as a quotient): for `s ∈ sigmaDom` and
`t : ℝ≥0` with `t = σ_z(s)`,
`dist(z, L_t) ≤ koebeK ‖f̂_s(z)‖ / ‖f̂'_s(z)‖`, where `f̂_s(z) = f_{σ_z(s)}(z)` and
`f̂'_s(z) = f'_{σ_z(s)}(z) = derivPath`. -/
theorem infDist_leftHull_le_div (hU : Continuous U) {z : ℂ} {s : ℝ} {t : ℝ≥0}
    (hs : s ∈ sigmaDom U hU z) (ht : (t : ℝ) = sigmaTime U hU z s) :
    infDist z (leftHull U t) ≤
      koebeK * ‖fPath U hU z (sigmaTime U hU z s)‖ / ‖derivPath U hU z (sigmaTime U hU z s)‖ := by
  have hlife : (t : ℝ) ∈ lifeSet U z := by rw [ht]; exact sigmaTime_mem_lifeSet hU hs
  have hz : z ∈ (leftHull U t)ᶜ := coe_mem_lifeSet_iff.1 hlife
  have hDpos : 0 < ‖derivPath U hU z (sigmaTime U hU z s)‖ :=
    norm_pos_iff.2 (derivPath_ne_zero hU z _)
  rw [le_div_iff₀ hDpos, ← ht]
  exact norm_derivPath_mul_infDist_le_of_notMem hU hz |> fun h => by linarith

/-- **Koebe hitting bound at the time `t = σ_z(s)`** (exponential form): for `s ∈ sigmaDom` and
`t : ℝ≥0` with `t = σ_z(s)`,

  `dist(z, L_t) ≤ koebeK exp(-(log‖f̂'_s(z)‖ - log‖f̂_s(z)‖))`. -/
theorem infDist_leftHull_le_exp (hU : Continuous U) {z : ℂ} {s : ℝ} {t : ℝ≥0}
    (hs : s ∈ sigmaDom U hU z) (ht : (t : ℝ) = sigmaTime U hU z s) :
    infDist z (leftHull U t) ≤
      koebeK * Real.exp (-(Real.log ‖derivPath U hU z (sigmaTime U hU z s)‖ -
        Real.log ‖fPath U hU z (sigmaTime U hU z s)‖)) := by
  have hlife : sigmaTime U hU z s ∈ lifeSet U z := sigmaTime_mem_lifeSet hU hs
  have hDpos : 0 < ‖derivPath U hU z (sigmaTime U hU z s)‖ :=
    norm_pos_iff.2 (derivPath_ne_zero hU z _)
  have hFpos : 0 < ‖fPath U hU z (sigmaTime U hU z s)‖ := norm_fPath_pos hU hlife
  refine (infDist_leftHull_le_div hU hs ht).trans (le_of_eq ?_)
  rw [neg_sub, Real.exp_sub, Real.exp_log hFpos, Real.exp_log hDpos, mul_div_assoc]

/-- The same with `t = (σ_z(s)).toNNReal`. -/
theorem infDist_leftHull_sigmaTime_le_exp (hU : Continuous U) {z : ℂ} {s : ℝ}
    (hs : s ∈ sigmaDom U hU z) :
    infDist z (leftHull U (sigmaTime U hU z s).toNNReal) ≤
      koebeK * Real.exp (-(Real.log ‖derivPath U hU z (sigmaTime U hU z s)‖ -
        Real.log ‖fPath U hU z (sigmaTime U hU z s)‖)) :=
  infDist_leftHull_le_exp hU hs (Real.coe_toNNReal _ (sigmaTime_nonneg hU hs))

/-- The time `(σ_z(s)).toNNReal` is before the absorbing time `T_z`. -/
theorem sigmaTime_toNNReal_lt_absorbingTime (hU : Continuous U) {z : ℂ} {s : ℝ}
    (hs : s ∈ sigmaDom U hU z) :
    ((sigmaTime U hU z s).toNNReal : ℝ≥0∞) < absorbingTime U z := by
  have h := (sigmaTime_mem_lifeSet hU hs).2
  exact h

/-- **Membership in the closure of the hulls, `ε`-form.** `z ∈ closure (⋃_{t < T_z} L_t)` iff
for every `ε > 0` there is `t < T_z` with `dist(z, L_t) < ε`. -/
theorem mem_closure_iUnion_leftHull_iff {z : ℂ} :
    z ∈ closure (⋃ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < absorbingTime U z), leftHull U t) ↔
      ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < absorbingTime U z ∧ infDist z (leftHull U t) < ε := by
  rw [Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    obtain ⟨b, hb, hzb⟩ := h ε hε
    obtain ⟨t, ht⟩ := mem_iUnion.1 hb
    obtain ⟨ht, hbt⟩ := mem_iUnion.1 ht
    exact ⟨t, ht, lt_of_le_of_lt (infDist_le_dist_of_mem hbt) hzb⟩
  · intro h ε hε
    obtain ⟨t, ht, hlt⟩ := h ε hε
    obtain ⟨b, hb, hzb⟩ := (infDist_lt_iff (leftHull_nonempty U t)).1 hlt
    exact ⟨b, mem_iUnion.2 ⟨t, mem_iUnion.2 ⟨ht, hb⟩⟩, hzb⟩

/-- **The `ε`-form from unboundedness of `log(|f̂'|/|f̂|)`** (deterministic core). If for every
`M` there is `s ∈ [0, clockSup)` with `log‖f̂'_s(z)‖ - log‖f̂_s(z)‖ ≥ M`, then for every `ε > 0`
there is `t < T_z` with `dist(z, L_t) < ε`. -/
theorem exists_infDist_leftHull_lt_of_ratio_unbounded (hU : Continuous U) {z : ℂ}
    (h : ∀ M : ℝ, ∃ s ∈ sigmaDom U hU z,
      M ≤ Real.log ‖derivPath U hU z (sigmaTime U hU z s)‖ -
        Real.log ‖fPath U hU z (sigmaTime U hU z s)‖) :
    ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < absorbingTime U z ∧ infDist z (leftHull U t) < ε := by
  intro ε hε
  have hK := koebeK_pos
  obtain ⟨s, hs, hM⟩ := h (-Real.log (ε / koebeK) + 1)
  refine ⟨(sigmaTime U hU z s).toNNReal, sigmaTime_toNNReal_lt_absorbingTime hU hs, ?_⟩
  refine lt_of_le_of_lt (infDist_leftHull_sigmaTime_le_exp hU hs) ?_
  have hεK : 0 < ε / koebeK := by positivity
  have h1 : Real.exp (-(Real.log ‖derivPath U hU z (sigmaTime U hU z s)‖ -
        Real.log ‖fPath U hU z (sigmaTime U hU z s)‖)) < ε / koebeK := by
    rw [← Real.exp_log hεK]
    refine Real.exp_lt_exp.2 ?_
    linarith
  calc koebeK * Real.exp (-(Real.log ‖derivPath U hU z (sigmaTime U hU z s)‖ -
        Real.log ‖fPath U hU z (sigmaTime U hU z s)‖)) < koebeK * (ε / koebeK) :=
        mul_lt_mul_of_pos_left h1 hK
    _ = ε := by field_simp

/-- **The closure clause of the hitting phase from unboundedness of `log(|f̂'|/|f̂|)`**
(deterministic): under the hypothesis of `exists_infDist_leftHull_lt_of_ratio_unbounded`,
`z ∈ closure (⋃_{t < T_z} L_t)`. -/
theorem mem_closure_iUnion_leftHull_of_ratio_unbounded (hU : Continuous U) {z : ℂ}
    (h : ∀ M : ℝ, ∃ s ∈ sigmaDom U hU z,
      M ≤ Real.log ‖derivPath U hU z (sigmaTime U hU z s)‖ -
        Real.log ‖fPath U hU z (sigmaTime U hU z s)‖) :
    z ∈ closure (⋃ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < absorbingTime U z), leftHull U t) :=
  mem_closure_iUnion_leftHull_iff.2 (exists_infDist_leftHull_lt_of_ratio_unbounded hU h)

/-- If `sigmaDom = [0, ∞)` (a.s. for an `SLE_Σ` driver, Remark 2.12) and
`log‖f̂'_s(z)‖ - log‖f̂_s(z)‖ → +∞` as `s → ∞`, then the hypothesis of
`exists_infDist_leftHull_lt_of_ratio_unbounded` holds. -/
theorem ratio_unbounded_of_tendsto (hU : Continuous U) {z : ℂ}
    (hdom : sigmaDom U hU z = Ici 0)
    (h : Tendsto (fun s : ℝ≥0 => Real.log ‖derivPath U hU z (sigmaTime U hU z s)‖ -
      Real.log ‖fPath U hU z (sigmaTime U hU z s)‖) atTop atTop) :
    ∀ M : ℝ, ∃ s ∈ sigmaDom U hU z,
      M ≤ Real.log ‖derivPath U hU z (sigmaTime U hU z s)‖ -
        Real.log ‖fPath U hU z (sigmaTime U hU z s)‖ := by
  intro M
  obtain ⟨s, hs⟩ := (h.eventually_ge_atTop M).exists
  exact ⟨s, by rw [hdom]; exact s.coe_nonneg, hs⟩

end Deterministic

/-! ### Adapted drivers: the process `sigmaLogRatio` -/

section Adapted

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

variable (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ)

/-- **The `ε`-form of Proposition 3.2(a) from the limit `sigmaLogRatio_s → +∞`**, for a fixed `ω`
with `sigmaDom = [0, ∞)`. -/
theorem exists_infDist_leftHull_lt_of_tendsto_sigmaLogRatio {ω : Ω}
    (hdom : sigmaDom (fun r => U r ω) (hU.cont ω) z = Ici 0)
    (h : Tendsto (fun s : ℝ≥0 => sigmaLogRatio hU z s ω) atTop atTop) :
    ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < absorbingTime (fun r => U r ω) z ∧
      infDist z (leftHull (fun r => U r ω) t) < ε :=
  exists_infDist_leftHull_lt_of_ratio_unbounded (hU.cont ω)
    (ratio_unbounded_of_tendsto (hU.cont ω) hdom h)

section Martingales

variable [IsProbabilityMeasure P] {z}

/-- The R14 `ε`-form a.s. from the almost sure limit `sigmaLogRatio_s → +∞`. -/
theorem ae_exists_infDist_leftHull_lt_of_tendsto (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0)
    (h : ∀ᵐ ω ∂P, Tendsto (fun s : ℝ≥0 => sigmaLogRatio hU z s ω) atTop atTop) :
    ∀ᵐ ω ∂P, ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < absorbingTime (fun r => U r ω) z ∧
      infDist z (leftHull (fun r => U r ω) t) < ε := by
  filter_upwards [ae_sigmaDom_eq_Ici hU z ha hc hz, h] with ω hω hlim
  exact exists_infDist_leftHull_lt_of_tendsto_sigmaLogRatio hU z hω hlim

end Martingales

end Adapted

end ComplexSLE.Internal.Polar

end
