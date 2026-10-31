/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.Lemma38Rec
public import ComplexSLE.Internal.Phases.Lemma38Joint

/-!
# Lemma 3.8 (`lem-log-finite-exp`): `E log (1 / dist(z, L_{σ_z(t̃)})) < ∞` (M7/E2)

Source: paper.tex:L1550-1630. Let `U` be an adapted `SLE_Σ` driver (`a > 0`, `c² ≤ ab`), `t̃ ≥ 0`,
and `ν` a probability measure on `ℝ` (for the paper, `ν = p(u) 1_{[0,2π]}(u) du` with the random
point `𝐳 = e^{iu}`, see `Lemma38Admissible.lean`). With `z = e^{iu}` and `μ = P ⊗ ν`:

* `lintegral_log_inv_distSigma_lt_top` and `integrable_log_inv_distSigma`:
  `∫ log (1 / dist(z, L_{σ_z(t̃)})) dμ < ∞` (the integrand is `≥ 0` a.e., `|z| = 1`, `0 ∈ L_t`).

This follows from the geometric tail bound `P(dist(z, L_{σ_z(t̃)}) ≤ 16^{-k}) ≤ e^{t̃} r^k`
(`tail_bound`, uniformly over unit `z`), which is proved by the paper's multi-scale argument with
two repairs, reported in the handoff:

1. **uniformity over the restart direction** (the paper glosses that the restart point
   `f_{τ_k}(z)/|f_{τ_k}(z)|` is a random unit vector on which the exit clock may depend): the good
   event is defined through the restarted *driver only*: `|V_s| ≤ 1/16` for `s ≤ u₀`, which has
   probability `≥ 1/2` for a fixed `u₀` by path continuity at `0`, and on it a deterministic
   estimate (`lifeSet_and_norm_bounds_of_small`) gives `1/2 < |f^V_s(w)| ≤ 2` for **every** unit `w`,
   hence a clock increment `≥ u₀/4` uniformly in the restart direction;
2. the paper's i.i.d. binomial count is replaced by an exponential moment
   `E[1_{τ_k ≤ θ} e^{-A(τ̂_k)}] ≤ r^k`, using only the conditional probability
   `P(V_k ∈ 𝒢 | ℱ_{τ̂_k}) = Λ(𝒢) ≥ 1/2` from the strong Markov property.

The tacit "no swallowing jump at `τ_k`" (`dist(z, L_{τ_k}) ≥ 16^{-k}`) is proved
(`ball_subset_compl_leftHull_of_forall_lt`). Uses the EXTERNALs `koebe_quarter` and
`strongMarkov_sleDriver`; `koebe_distortion` is not needed.
-/

public section

open scoped NNReal ENNReal Topology Real
open Set Metric Filter MeasureTheory ProbabilityTheory

namespace ComplexSLE.Internal

open Polar

/-- The elementary bound: for `d ∈ [0, 1]`, `log (1/d) ≤ log 16 · #{k | d ≤ 16^{-k}}`. -/
theorem ofReal_log_inv_le_tsum (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (g : ℕ → ℝ≥0∞)
    (hg : ∀ k, d ≤ lvl k → g k = 1) :
    ENNReal.ofReal (Real.log (1 / d)) ≤ ENNReal.ofReal (Real.log 16) * ∑' k, g k := by
  rcases hd0.eq_or_lt with h | hpos
  · subst h; simp
  · set L : ℝ := Real.log 16 with hL
    have hLpos : 0 < L := Real.log_pos (by norm_num)
    set x : ℝ := Real.log (1 / d) with hx
    have hx0 : 0 ≤ x := by
      rw [hx]; apply Real.log_nonneg
      rw [le_div_iff₀ hpos]; linarith
    set n : ℕ := ⌊x / L⌋₊ with hn
    have h1 : x < L * ((n : ℝ) + 1) := by
      have := Nat.lt_floor_add_one (x / L)
      rw [← hn, div_lt_iff₀ hLpos] at this
      linarith
    have h2 : ∀ k ∈ Finset.range (n + 1), g k = 1 := by
      intro k hk
      apply hg
      have hkn : (k : ℝ) ≤ x / L := by
        have : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
        exact (Nat.cast_le.2 this).trans (Nat.floor_le (div_nonneg hx0 hLpos.le))
      have hkx : (k : ℝ) * L ≤ x := by rwa [le_div_iff₀ hLpos] at hkn
      have hlog : Real.log d ≤ -((k : ℝ) * L) := by
        have : Real.log (1 / d) = -Real.log d := by rw [one_div, Real.log_inv]
        rw [hx, this] at hkx
        linarith
      have := (Real.log_le_iff_le_exp hpos).1 hlog
      refine this.trans (le_of_eq ?_)
      unfold lvl
      rw [Real.exp_neg, Real.exp_nat_mul, hL, Real.exp_log (by norm_num), one_div,
        inv_pow]
    calc ENNReal.ofReal x ≤ ENNReal.ofReal (L * ((n : ℝ) + 1)) := ENNReal.ofReal_le_ofReal h1.le
      _ = ENNReal.ofReal L * ∑ k ∈ Finset.range (n + 1), g k := by
        rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
          ENNReal.ofReal_mul hLpos.le]
        congr 1
        rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
      _ ≤ _ := by gcongr; exact sum_le_tsum _

section Final

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

variable (hU : IsSLEDriverAdapted a b c U P ℱ) (tt : ℝ≥0)

/-- The measurable set where `σ_z(t̃)` is defined and `U 0 = 0`. -/
@[expose] def goodSet (hU : IsSLEDriverAdapted a b c U P ℱ) (tt : ℝ≥0) : Set (Ω × ℝ) :=
  {p | (tt : ℝ) ∈ sigmaDom (fun s => U s p.1) (hU.cont p.1) (unitPt p.2) ∧ U 0 p.1 = 0}

theorem measurableSet_goodSet : MeasurableSet (goodSet hU tt) := by
  have hd : MeasurableSet {p : Ω × ℝ | (tt : ℝ) ∈ sigmaDom (fun s => U s p.1) (hU.cont p.1)
      (unitPt p.2)} := measurableSet_sigmaDom_unit hU.cont hU.adapted tt
  have : Measurable fun p : Ω × ℝ => U 0 p.1 :=
    (hU.adapted.measurable (i := 0)).comp measurable_fst
  have h2 : MeasurableSet {p : Ω × ℝ | U 0 p.1 = 0} :=
    measurableSet_eq_fun this measurable_const
  exact hd.inter h2

theorem ae_goodSet [IsProbabilityMeasure P] (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (ν : Measure ℝ)
    [SFinite ν] : ∀ᵐ p ∂(P.prod ν), p ∈ goodSet hU tt := by
  rw [Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_goodSet hU tt)]
  have hU0 := hU.toIsSLEDriver.zero
  rw [Measure.ae_ae_comm (μ := P) (ν := ν)
    (p := fun ω u => (ω, u) ∈ goodSet hU tt) (measurableSet_goodSet hU tt)]
  refine Eventually.of_forall fun u => ?_
  have hz : unitPt u ≠ 0 := by
    unfold unitPt; exact Complex.exp_ne_zero _
  filter_upwards [Polar.ae_sigmaDom_eq_Ici hU (unitPt u) ha hc hz, hU0] with ω hω hω0
  refine ⟨?_, hω0⟩
  show (tt : ℝ) ∈ sigmaDom (fun s => U s ω) (hU.cont ω) (unitPt u)
  rw [hω]; exact tt.coe_nonneg

theorem norm_unitPt (u : ℝ) : ‖unitPt u‖ = 1 := by
  unfold unitPt; exact Complex.norm_exp_ofReal_mul_I u

theorem distSigma_le_one {p : Ω × ℝ} (hp : p ∈ goodSet hU tt) : distSigma hU tt p ≤ 1 := by
  obtain ⟨hdom, h0⟩ := hp
  unfold distSigma
  have hmem : (0 : ℂ) ∈ leftHull (fun s => U s p.1)
      (sigmaTime (fun s => U s p.1) (hU.cont p.1) (unitPt p.2) tt).toNNReal := by
    have := driver_zero_mem_leftHull (fun s => U s p.1) (sigmaTime (fun s => U s p.1)
      (hU.cont p.1) (unitPt p.2) tt).toNNReal
    simpa [h0] using this
  calc _ ≤ dist (unitPt p.2) 0 := infDist_le_dist_of_mem hmem
    _ = 1 := by rw [dist_zero_right, norm_unitPt]

/-- The level sets `E_k = {t̃ ∈ sigmaDom, dist(z, L_{σ_z(t̃)}) ≤ 16^{-k}}` are measurable. -/
theorem measurableSet_level (k : ℕ) :
    MeasurableSet {p : Ω × ℝ | (tt : ℝ) ∈ sigmaDom (fun s => U s p.1) (hU.cont p.1) (unitPt p.2) ∧
      distSigma hU tt p ≤ lvl k} :=
  measurableSet_distSigma_le hU tt (lvl k)

/-- **The measure of the level sets** (the tail bound integrated over the random point). -/
theorem measure_level_le [IsProbabilityMeasure P] (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ k : ℕ,
      P.prod ν {p : Ω × ℝ | (tt : ℝ) ∈ sigmaDom (fun s => U s p.1) (hU.cont p.1) (unitPt p.2) ∧
        distSigma hU tt p ≤ lvl k} ≤ ENNReal.ofReal (Real.exp tt) * ENNReal.ofReal r ^ k := by
  obtain ⟨r, hr0, hr1, hbound⟩ := tail_bound hU ha hc
  refine ⟨r, hr0, hr1, fun k => ?_⟩
  rw [Measure.prod_apply_symm (measurableSet_level hU tt k)]
  calc ∫⁻ u, P ((fun ω => (ω, u)) ⁻¹' {p : Ω × ℝ | (tt : ℝ) ∈
        sigmaDom (fun s => U s p.1) (hU.cont p.1) (unitPt p.2) ∧ distSigma hU tt p ≤ lvl k}) ∂ν
      ≤ ∫⁻ _u, ENNReal.ofReal (Real.exp tt) * ENNReal.ofReal r ^ k ∂ν := by
        refine lintegral_mono fun u => ?_
        refine le_trans (measure_mono ?_) (hbound (unitPt u) tt (norm_unitPt u) k)
        intro ω hω
        exact hω.2
    _ = _ := by simp

theorem log_inv_distSigma_nonneg {p : Ω × ℝ} (hp : p ∈ goodSet hU tt) :
    0 ≤ Real.log (1 / distSigma hU tt p) := by
  have h1 := distSigma_le_one hU tt hp
  have h0 : 0 ≤ distSigma hU tt p := infDist_nonneg
  rcases h0.eq_or_lt with h | hpos
  · rw [← h]; simp
  · apply Real.log_nonneg
    rw [le_div_iff₀ hpos]; linarith

/-- **Lemma 3.8, lintegral form**: `∫ log (1 / dist(z, L_{σ_z(t̃)})) d(P ⊗ ν) < ∞`. -/
theorem lintegral_log_inv_distSigma_lt_top [IsProbabilityMeasure P] (ha : 0 < a)
    (hc : c ^ 2 ≤ a * b) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∫⁻ p, ENNReal.ofReal (Real.log (1 / distSigma hU tt p)) ∂(P.prod ν) < ⊤ := by
  obtain ⟨r, hr0, hr1, hmeas⟩ := measure_level_le hU tt ha hc ν
  set E : ℕ → Set (Ω × ℝ) := fun k => {p : Ω × ℝ | (tt : ℝ) ∈
    sigmaDom (fun s => U s p.1) (hU.cont p.1) (unitPt p.2) ∧ distSigma hU tt p ≤ lvl k} with hE
  have hpt : ∀ᵐ p ∂(P.prod ν), ENNReal.ofReal (Real.log (1 / distSigma hU tt p)) ≤
      ENNReal.ofReal (Real.log 16) * ∑' k, (E k).indicator (fun _ => (1 : ℝ≥0∞)) p := by
    filter_upwards [ae_goodSet hU tt ha hc ν] with p hp
    refine ofReal_log_inv_le_tsum _ infDist_nonneg (distSigma_le_one hU tt hp) _ fun k hk => ?_
    exact Set.indicator_of_mem (show p ∈ E k from ⟨hp.1, hk⟩) _
  have hg : ∀ k, MeasurableSet (E k) := fun k => measurableSet_level hU tt k
  calc ∫⁻ p, ENNReal.ofReal (Real.log (1 / distSigma hU tt p)) ∂(P.prod ν)
      ≤ ∫⁻ p, ENNReal.ofReal (Real.log 16) *
          ∑' k, (E k).indicator (fun _ => (1 : ℝ≥0∞)) p ∂(P.prod ν) := lintegral_mono_ae hpt
    _ = ENNReal.ofReal (Real.log 16) * ∑' k, P.prod ν (E k) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_tsum fun k => (measurable_const.indicator (hg k)).aemeasurable]
        congr 1
        refine tsum_congr fun k => ?_
        rw [lintegral_indicator_const (hg k), one_mul]
    _ ≤ ENNReal.ofReal (Real.log 16) * ∑' k : ℕ,
          ENNReal.ofReal (Real.exp tt) * ENNReal.ofReal r ^ k := by
        gcongr with k
        exact hmeas k
    _ < ⊤ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
        rw [ENNReal.inv_lt_top]
        exact tsub_pos_of_lt (by rw [← ENNReal.ofReal_one]; exact
          (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hr1)

/-- **Lemma 3.8** (`lem-log-finite-exp`, paper.tex:L1550-1630): for an adapted `SLE_Σ` driver
(`a > 0`, `c² ≤ ab`), every `t̃ ≥ 0` and every probability measure `ν` for the random point
`𝐳 = e^{iu}`, the random variable `log (1 / dist(𝐳, L_{σ_𝐳(t̃)}))` is integrable for `P ⊗ ν`. -/
theorem integrable_log_inv_distSigma [IsProbabilityMeasure P] (ha : 0 < a) (hc : c ^ 2 ≤ a * b)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    Integrable (fun p : Ω × ℝ => Real.log (1 / distSigma hU tt p)) (P.prod ν) := by
  have hgood := ae_goodSet hU tt ha hc ν
  have hmeasf : Measurable fun p : Ω × ℝ => Real.log (1 / distSigmaTilde hU tt p) :=
    Real.measurable_log.comp (measurable_const.div (measurable_distSigmaTilde hU tt))
  have hae : (fun p : Ω × ℝ => Real.log (1 / distSigma hU tt p)) =ᵐ[P.prod ν]
      fun p : Ω × ℝ => Real.log (1 / distSigmaTilde hU tt p) := by
    filter_upwards [hgood] with p hp
    simp only [distSigmaTilde, hp.1, ↓reduceIte]
  refine ⟨(hmeasf.aestronglyMeasurable.congr hae.symm), ?_⟩
  rw [hasFiniteIntegral_iff_ofReal]
  · exact lintegral_log_inv_distSigma_lt_top hU tt ha hc ν
  · filter_upwards [hgood] with p hp
    exact log_inv_distSigma_nonneg hU tt hp

/-- **The distance `dist(z, L_{σ_z(t̃)})` is a.s. positive** (so the junk value `log (1/0) = 0` of the
integrand is on a null set): `P ⊗ ν (dist ≤ 16^{-k}) → 0`. -/
theorem ae_distSigma_pos [IsProbabilityMeasure P] (ha : 0 < a) (hc : c ^ 2 ≤ a * b)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] : ∀ᵐ p ∂(P.prod ν), 0 < distSigma hU tt p := by
  obtain ⟨r, hr0, hr1, hmeas⟩ := measure_level_le hU tt ha hc ν
  set S : Set (Ω × ℝ) := {p | (tt : ℝ) ∈ sigmaDom (fun s => U s p.1) (hU.cont p.1) (unitPt p.2) ∧
    distSigma hU tt p ≤ 0} with hS
  have hlt : ENNReal.ofReal r < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hr1
  have hSle : ∀ k : ℕ, P.prod ν S ≤ ENNReal.ofReal (Real.exp tt) * ENNReal.ofReal r ^ k :=
    fun k => le_trans (measure_mono (fun p (hp : p ∈ S) =>
      (⟨hp.1, hp.2.trans (lvl_pos k).le⟩ : (tt : ℝ) ∈ sigmaDom (fun s => U s p.1) (hU.cont p.1)
        (unitPt p.2) ∧ distSigma hU tt p ≤ lvl k))) (hmeas k)
  have htend : Filter.Tendsto (fun k : ℕ => ENNReal.ofReal (Real.exp tt) * ENNReal.ofReal r ^ k)
      Filter.atTop (nhds (ENNReal.ofReal (Real.exp tt) * 0)) :=
    ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt)
      (Or.inr ENNReal.ofReal_ne_top)
  have hS0 : P.prod ν S = 0 := by
    have := ge_of_tendsto' htend hSle
    rw [mul_zero] at this
    exact le_antisymm this bot_le
  filter_upwards [ae_goodSet hU tt ha hc ν, measure_eq_zero_iff_ae_notMem.1 hS0] with p hp hpS
  by_contra hcon
  exact hpS ⟨hp.1, not_lt.1 hcon⟩

end Final

end ComplexSLE.Internal

end
