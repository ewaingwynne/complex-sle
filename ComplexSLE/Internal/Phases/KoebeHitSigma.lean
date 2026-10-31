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

By the Koebe hitting bound (`norm_derivPath_mul_infDist_le`, EXTERNAL `koebe_quarter`), for
`s ∈ sigmaDom` and `t = σ_z(s)`,

  `dist(z, L_{σ_z(s)}) ≤ 4 |f̂_s(z)| / |f̂'_s(z)| = 4 exp(-(log|f̂'_s(z)| - log|f̂_s(z)|))`

(`infDist_leftHull_sigmaTime_le_div`, `infDist_leftHull_sigmaTime_le_exp`; for an adapted driver
the exponent is `-sigmaLogRatio hU z s ω`, `infDist_leftHull_sigmaTime_le_exp_sigmaLogRatio`).
Consequently, if `log(|f̂'_s(z)|/|f̂_s(z)|)` is unbounded above along `s ∈ sigmaDom`, then
`dist(z, L_t) < ε` for some `t < T_z`, for every `ε > 0`
(`exists_infDist_leftHull_lt_of_ratio_unbounded`). This is exactly:

* the closure clause of the hitting phase `z ∈ closure (⋃_{t < T_z} L_t)`
  (`mem_closure_iUnion_leftHull_of_ratio_unbounded`; the clause of
  `ComplexSLE.IsHittingPhase`, paper.tex:L414), and
* the R14 `ε`-form `∀ ε > 0, ∃ t < T_z, dist(z, L_t) < ε` of Proposition 3.2(a)
  (`ae_exists_infDist_leftHull_lt_of_limsup_eq_top`).

The two conditions are equivalent (`mem_closure_iUnion_leftHull_iff`), and by monotonicity of `L_t`
the `ε`-form upgrades to the genuine limit `lim_{t → T_z⁻} dist(z, L_t) = 0`
(`eventually_infDist_leftHull_lt`). For an adapted driver the hypothesis "`limsup_{s → ∞}
sigmaLogRatio = +∞`" (or the limit `= +∞`) can be fed in a.s.: Remark 2.12 gives
`sigmaDom = [0, ∞)` a.s. Every result here that consumes the Koebe bound is
`PROVED_REL{koebe_quarter}`.
-/

public section

open scoped NNReal ENNReal Topology
open Set Metric Filter MeasureTheory

namespace ComplexSLE.Internal.Polar

/-! ### Deterministic σ-time form -/

section Deterministic

variable {U : ℝ≥0 → ℂ}

/-- **Koebe hitting bound at the time `t = σ_z(s)`** (as a quotient): for `s ∈ sigmaDom` and
`t : ℝ≥0` with `t = σ_z(s)`,
`dist(z, L_t) ≤ 4 ‖f̂_s(z)‖ / ‖f̂'_s(z)‖`, where `f̂_s(z) = f_{σ_z(s)}(z)` and
`f̂'_s(z) = f'_{σ_z(s)}(z) = derivPath`. -/
theorem infDist_leftHull_le_div (hU : Continuous U) {z : ℂ} {s : ℝ} {t : ℝ≥0}
    (hs : s ∈ sigmaDom U hU z) (ht : (t : ℝ) = sigmaTime U hU z s) :
    infDist z (leftHull U t) ≤
      4 * ‖fPath U hU z (sigmaTime U hU z s)‖ / ‖derivPath U hU z (sigmaTime U hU z s)‖ := by
  have hlife : (t : ℝ) ∈ lifeSet U z := by rw [ht]; exact sigmaTime_mem_lifeSet hU hs
  have hz : z ∈ (leftHull U t)ᶜ := coe_mem_lifeSet_iff.1 hlife
  have hDpos : 0 < ‖derivPath U hU z (sigmaTime U hU z s)‖ :=
    norm_pos_iff.2 (derivPath_ne_zero hU z _)
  rw [le_div_iff₀ hDpos, ← ht]
  exact norm_derivPath_mul_infDist_le_of_notMem hU hz |> fun h => by linarith

/-- **Koebe hitting bound at the time `t = σ_z(s)`** (exponential form): for `s ∈ sigmaDom` and
`t : ℝ≥0` with `t = σ_z(s)`,

  `dist(z, L_t) ≤ 4 exp(-(log‖f̂'_s(z)‖ - log‖f̂_s(z)‖))`. -/
theorem infDist_leftHull_le_exp (hU : Continuous U) {z : ℂ} {s : ℝ} {t : ℝ≥0}
    (hs : s ∈ sigmaDom U hU z) (ht : (t : ℝ) = sigmaTime U hU z s) :
    infDist z (leftHull U t) ≤
      4 * Real.exp (-(Real.log ‖derivPath U hU z (sigmaTime U hU z s)‖ -
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
      4 * Real.exp (-(Real.log ‖derivPath U hU z (sigmaTime U hU z s)‖ -
        Real.log ‖fPath U hU z (sigmaTime U hU z s)‖)) :=
  infDist_leftHull_le_exp hU hs (Real.coe_toNNReal _ (sigmaTime_nonneg hU hs))

/-- The same with `t = (σ_z(s)).toNNReal`, as a quotient. -/
theorem infDist_leftHull_sigmaTime_le_div (hU : Continuous U) {z : ℂ} {s : ℝ}
    (hs : s ∈ sigmaDom U hU z) :
    infDist z (leftHull U (sigmaTime U hU z s).toNNReal) ≤
      4 * ‖fPath U hU z (sigmaTime U hU z s)‖ / ‖derivPath U hU z (sigmaTime U hU z s)‖ :=
  infDist_leftHull_le_div hU hs (Real.coe_toNNReal _ (sigmaTime_nonneg hU hs))

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

/-- **The `ε`-form upgrades to the limit** `lim_{t → T_z⁻} dist(z, L_t) = 0`: since `L_t` is
increasing in `t`, `dist(z, L_t)` is decreasing, so once `< ε` it stays `< ε` up to `T_z`. -/
theorem eventually_infDist_leftHull_lt {z : ℂ}
    (h : ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < absorbingTime U z ∧ infDist z (leftHull U t) < ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ t₀ : ℝ≥0, (t₀ : ℝ≥0∞) < absorbingTime U z ∧
      ∀ t : ℝ≥0, t₀ ≤ t → infDist z (leftHull U t) < ε := by
  obtain ⟨t₀, ht₀, hlt⟩ := h ε hε
  refine ⟨t₀, ht₀, fun t ht => lt_of_le_of_lt ?_ hlt⟩
  exact infDist_le_infDist_of_subset (leftHull_mono ht) (leftHull_nonempty U t₀)

/-- **The `ε`-form from unboundedness of `log(|f̂'|/|f̂|)`** (deterministic core). If for every
`M` there is `s ∈ [0, clockSup)` with `log‖f̂'_s(z)‖ - log‖f̂_s(z)‖ ≥ M`, then for every `ε > 0`
there is `t < T_z` with `dist(z, L_t) < ε`. -/
theorem exists_infDist_leftHull_lt_of_ratio_unbounded (hU : Continuous U) {z : ℂ}
    (h : ∀ M : ℝ, ∃ s ∈ sigmaDom U hU z,
      M ≤ Real.log ‖derivPath U hU z (sigmaTime U hU z s)‖ -
        Real.log ‖fPath U hU z (sigmaTime U hU z s)‖) :
    ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < absorbingTime U z ∧ infDist z (leftHull U t) < ε := by
  intro ε hε
  obtain ⟨s, hs, hM⟩ := h (-Real.log (ε / 4) + 1)
  refine ⟨(sigmaTime U hU z s).toNNReal, sigmaTime_toNNReal_lt_absorbingTime hU hs, ?_⟩
  refine lt_of_le_of_lt (infDist_leftHull_sigmaTime_le_exp hU hs) ?_
  have hε4 : 0 < ε / 4 := by positivity
  have h1 : Real.exp (-(Real.log ‖derivPath U hU z (sigmaTime U hU z s)‖ -
        Real.log ‖fPath U hU z (sigmaTime U hU z s)‖)) < ε / 4 := by
    rw [← Real.exp_log hε4]
    refine Real.exp_lt_exp.2 ?_
    linarith
  linarith

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

/-- If `sigmaDom = [0, ∞)` and `limsup_{s → ∞} (log‖f̂'_s(z)‖ - log‖f̂_s(z)‖) = +∞` (in `EReal`),
then the hypothesis of `exists_infDist_leftHull_lt_of_ratio_unbounded` holds. -/
theorem ratio_unbounded_of_limsup_eq_top (hU : Continuous U) {z : ℂ}
    (hdom : sigmaDom U hU z = Ici 0)
    (h : limsup (fun s : ℝ≥0 => ((Real.log ‖derivPath U hU z (sigmaTime U hU z s)‖ -
      Real.log ‖fPath U hU z (sigmaTime U hU z s)‖ : ℝ) : EReal)) atTop = ⊤) :
    ∀ M : ℝ, ∃ s ∈ sigmaDom U hU z,
      M ≤ Real.log ‖derivPath U hU z (sigmaTime U hU z s)‖ -
        Real.log ‖fPath U hU z (sigmaTime U hU z s)‖ := by
  intro M
  have hM : ((M : ℝ) : EReal) < limsup (fun s : ℝ≥0 => ((Real.log ‖derivPath U hU z
      (sigmaTime U hU z s)‖ - Real.log ‖fPath U hU z (sigmaTime U hU z s)‖ : ℝ) : EReal))
      atTop := by
    rw [h]; exact EReal.coe_lt_top M
  obtain ⟨s, hs⟩ := (frequently_lt_of_lt_limsup (by isBoundedDefault) hM).exists
  exact ⟨s, by rw [hdom]; exact s.coe_nonneg, (EReal.coe_lt_coe_iff.1 hs).le⟩

end Deterministic

/-! ### Adapted drivers: the process `sigmaLogRatio` -/

section Adapted

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

variable (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ)

/-- **Koebe hitting bound in σ-time for an adapted driver** (paper.tex:L1460-1466): for
`s ∈ sigmaDom`,

  `dist(z, L_{σ_z(s)}) ≤ 4 exp(-log(|f̂'_s(z)| / |f̂_s(z)|)) = 4 exp(-sigmaLogRatio_s)`. -/
theorem infDist_leftHull_le_exp_sigmaLogRatio {s : ℝ≥0} {ω : Ω} {t : ℝ≥0}
    (hs : (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z)
    (ht : (t : ℝ) = sigmaTime (fun r => U r ω) (hU.cont ω) z s) :
    infDist z (leftHull (fun r => U r ω) t) ≤ 4 * Real.exp (-(sigmaLogRatio hU z s ω)) :=
  infDist_leftHull_le_exp (hU.cont ω) hs ht

/-- The closure clause of the hitting phase, for an adapted driver and a fixed `ω` with
`sigmaDom = [0, ∞)`: if `sigmaLogRatio_s → +∞` as `s → ∞` then
`z ∈ closure (⋃_{t < T_z} L_t)`. -/
theorem mem_closure_iUnion_leftHull_of_tendsto_sigmaLogRatio {ω : Ω}
    (hdom : sigmaDom (fun r => U r ω) (hU.cont ω) z = Ici 0)
    (h : Tendsto (fun s : ℝ≥0 => sigmaLogRatio hU z s ω) atTop atTop) :
    z ∈ closure (⋃ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < absorbingTime (fun r => U r ω) z),
      leftHull (fun r => U r ω) t) :=
  mem_closure_iUnion_leftHull_of_ratio_unbounded (hU.cont ω)
    (ratio_unbounded_of_tendsto (hU.cont ω) hdom h)

/-- **The `ε`-form of Proposition 3.2(a) from the limit `sigmaLogRatio_s → +∞`**, for a fixed `ω`
with `sigmaDom = [0, ∞)`. -/
theorem exists_infDist_leftHull_lt_of_tendsto_sigmaLogRatio {ω : Ω}
    (hdom : sigmaDom (fun r => U r ω) (hU.cont ω) z = Ici 0)
    (h : Tendsto (fun s : ℝ≥0 => sigmaLogRatio hU z s ω) atTop atTop) :
    ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < absorbingTime (fun r => U r ω) z ∧
      infDist z (leftHull (fun r => U r ω) t) < ε :=
  exists_infDist_leftHull_lt_of_ratio_unbounded (hU.cont ω)
    (ratio_unbounded_of_tendsto (hU.cont ω) hdom h)

/-- The closure clause of the hitting phase from `limsup_{s → ∞} sigmaLogRatio_s = +∞`, for a fixed
`ω` with `sigmaDom = [0, ∞)`. -/
theorem mem_closure_iUnion_leftHull_of_limsup_sigmaLogRatio {ω : Ω}
    (hdom : sigmaDom (fun r => U r ω) (hU.cont ω) z = Ici 0)
    (h : limsup (fun s : ℝ≥0 => ((sigmaLogRatio hU z s ω : ℝ) : EReal)) atTop = ⊤) :
    z ∈ closure (⋃ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < absorbingTime (fun r => U r ω) z),
      leftHull (fun r => U r ω) t) :=
  mem_closure_iUnion_leftHull_of_ratio_unbounded (hU.cont ω)
    (ratio_unbounded_of_limsup_eq_top (hU.cont ω) hdom h)

/-- The `ε`-form from `limsup_{s → ∞} sigmaLogRatio_s = +∞`, for a fixed `ω` with
`sigmaDom = [0, ∞)`. -/
theorem exists_infDist_leftHull_lt_of_limsup_sigmaLogRatio {ω : Ω}
    (hdom : sigmaDom (fun r => U r ω) (hU.cont ω) z = Ici 0)
    (h : limsup (fun s : ℝ≥0 => ((sigmaLogRatio hU z s ω : ℝ) : EReal)) atTop = ⊤) :
    ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < absorbingTime (fun r => U r ω) z ∧
      infDist z (leftHull (fun r => U r ω) t) < ε :=
  exists_infDist_leftHull_lt_of_ratio_unbounded (hU.cont ω)
    (ratio_unbounded_of_limsup_eq_top (hU.cont ω) hdom h)

section Martingales

variable [IsProbabilityMeasure P] {z}

/-- **Closure clause of the hitting phase, a.s.** (paper.tex:L414, via L1460-1466): for an adapted
`SLE_Σ` driver with `0 < a`, `c² ≤ ab`, `z ≠ 0`, a.s. on the event
`{limsup_{s → ∞} log(|f̂'_s(z)|/|f̂_s(z)|) = +∞}` we have
`z ∈ closure (⋃_{t < T_z} L_t)`. -/
theorem ae_mem_closure_iUnion_leftHull_of_limsup (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) :
    ∀ᵐ ω ∂P,
      limsup (fun s : ℝ≥0 => ((sigmaLogRatio hU z s ω : ℝ) : EReal)) atTop = ⊤ →
        z ∈ closure (⋃ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < absorbingTime (fun r => U r ω) z),
          leftHull (fun r => U r ω) t) := by
  filter_upwards [ae_sigmaDom_eq_Ici hU z ha hc hz] with ω hω h
  exact mem_closure_iUnion_leftHull_of_limsup_sigmaLogRatio hU z hω h

/-- **The R14 `ε`-form of Proposition 3.2(a), a.s.** (paper.tex:L1276-1281, via L1460-1466): for an
adapted `SLE_Σ` driver with `0 < a`, `c² ≤ ab`, `z ≠ 0`, a.s. on the event
`{limsup_{s → ∞} log(|f̂'_s(z)|/|f̂_s(z)|) = +∞}` we have
`∀ ε > 0, ∃ t < T_z, dist(z, L_t) < ε`. -/
theorem ae_exists_infDist_leftHull_lt_of_limsup_eq_top (ha : 0 < a) (hc : c ^ 2 ≤ a * b)
    (hz : z ≠ 0) :
    ∀ᵐ ω ∂P,
      limsup (fun s : ℝ≥0 => ((sigmaLogRatio hU z s ω : ℝ) : EReal)) atTop = ⊤ →
        ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < absorbingTime (fun r => U r ω) z ∧
          infDist z (leftHull (fun r => U r ω) t) < ε := by
  filter_upwards [ae_sigmaDom_eq_Ici hU z ha hc hz] with ω hω h
  exact exists_infDist_leftHull_lt_of_limsup_sigmaLogRatio hU z hω h

/-- The closure clause a.s. from the almost sure limit `sigmaLogRatio_s → +∞`. -/
theorem ae_mem_closure_iUnion_leftHull_of_tendsto (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0)
    (h : ∀ᵐ ω ∂P, Tendsto (fun s : ℝ≥0 => sigmaLogRatio hU z s ω) atTop atTop) :
    ∀ᵐ ω ∂P, z ∈ closure (⋃ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < absorbingTime (fun r => U r ω) z),
      leftHull (fun r => U r ω) t) := by
  filter_upwards [ae_sigmaDom_eq_Ici hU z ha hc hz, h] with ω hω hlim
  exact mem_closure_iUnion_leftHull_of_tendsto_sigmaLogRatio hU z hω hlim

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
