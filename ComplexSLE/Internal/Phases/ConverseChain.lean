/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.KoebeChainDisplays
public import ComplexSLE.Internal.Phases.Lemma37Hull

/-!
# The Koebe chain in σ-time (`eqn-dist-3` for `t = σ_z(t̃)`, `s = σ_z(s̃ + t̃) - σ_z(t̃)`), M7/E4

Source: paper.tex:L1650-1672 (Step 1), L1740-1790 (Steps 3-4). Deterministic half of the proof of
`lem-converse-w-o-upgrade`: for a continuous driver `U`, a point `z` and `t̃, s̃ ≥ 0` with `t̃` and
`s̃ + t̃` in the domain of `σ_z`, put `t = σ_z(t̃)` and `s = σ_z(s̃ + t̃) - σ_z(t̃)`, so that
`s + t = σ_z(s̃ + t̃)`. The quantities of `Lemma37Hull.lean` are

* `futureDistRatio U hU z t̃ s̃ = dist(f_t z, L_{t,s+t}) / |f_t z|`,
* `hullDist U hU z s̃ = dist(z, L_{σ_z(s̃)})`,
* `sigmaRatioDet U hU z t̃ = log(|f_t'(z)| / |f_t z|)` (the value of `sigmaLogRatio` on a path).

Results (all deterministic, `PROVED_REL{koebe_quarter}` through `KoebeChain.koebe_chain`):

* `chain_sigma_of_event`, `chain_sigma_of_not_event` (`eqn-dist-3` in σ-time, with the event
  `koebeEventSigma` of `eqn-dist-event` and the explicit constant `log 16`), and the unconditional
  consequence `chain_sigma_le` (`≤ log(1/dist(z, L_t)) + log 64`);
* `sigmaRatioDet_le` (`eqn-hit-koebe`): `log(|f_t'|/|f_t|) ≤ log(1/dist(z, L_t)) + log 4`;
* `koebeEventSigma_of_le` and `eventually_le_koebeBound`: the measurable surrogate
  `X_s̃ ≤ koebeBound` of the event `E_s̃` (`dist(f_t z, L_{t,s+t}) ≤ |f_t'(z)| dist(z, L_t) / 4 ≤
  dist(f_t z, R_t)`), which holds for all large `s̃` under the assumption
  `lim_{u → T_z} dist(z, L_u) = 0` in the R14 ε-form (`step:converse-event-converges`).
-/

public section

open scoped NNReal ENNReal Topology
open Set Metric Filter ComplexSLE.Internal.KoebeChain ComplexSLE.Internal.Polar

namespace ComplexSLE.Internal

variable {U : ℝ≥0 → ℂ}

/-- `log(|f_t'(z)| / |f_t(z)|)` at `t = σ_z(t̃)` (the value of `sigmaLogRatio` on a path). -/
@[expose] noncomputable def sigmaRatioDet (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) (s : ℝ≥0) :
    ℝ :=
  Real.log ‖derivPath U hU z (sigmaTime U hU z s)‖ - Real.log ‖fPath U hU z (sigmaTime U hU z s)‖

/-- The event `E_s̃` of `eqn-dist-event` (paper.tex:L1744-1747) in σ-time:
`dist(f_t z, L_{t,s+t}) ≤ dist(f_t z, R_t)` for `t = σ_z(t̃)`, `s = σ_z(s̃ + t̃) - σ_z(t̃)`. -/
@[expose] noncomputable def koebeEventSigma (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ)
    (tt ss : ℝ≥0) : Prop :=
  koebeEvent U hU (sigmaTime U hU z tt).toNNReal
    (sigmaTime U hU z ((ss : ℝ) + tt) - sigmaTime U hU z tt).toNNReal z

/-- The threshold `|f_t'(z)| dist(z, L_t) / (4 |f_t z|)` for `futureDistRatio`
(`= exp(sigmaRatioDet) · dist(z, L_t) / 4`). -/
@[expose] noncomputable def koebeBound (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) (tt : ℝ≥0) :
    ℝ :=
  Real.exp (sigmaRatioDet U hU z tt) * hullDist U hU z tt / 4

section Basic

variable (hU : Continuous U) {z : ℂ} {tt ss : ℝ≥0}

theorem coe_toNNReal_sigmaTime {s : ℝ} (htt : s ∈ sigmaDom U hU z) :
    (((sigmaTime U hU z s).toNNReal : ℝ≥0) : ℝ) = sigmaTime U hU z s :=
  Real.coe_toNNReal _ (sigmaTime_nonneg hU htt)

theorem sigmaTime_le_add (htt : (tt : ℝ) ∈ sigmaDom U hU z)
    (hts : (ss : ℝ) + tt ∈ sigmaDom U hU z) :
    sigmaTime U hU z tt ≤ sigmaTime U hU z ((ss : ℝ) + tt) :=
  sigmaTime_monotoneOn hU z htt hts (by simp)

theorem toNNReal_sub_add_toNNReal (htt : (tt : ℝ) ∈ sigmaDom U hU z)
    (hts : (ss : ℝ) + tt ∈ sigmaDom U hU z) :
    (sigmaTime U hU z ((ss : ℝ) + tt) - sigmaTime U hU z tt).toNNReal +
        (sigmaTime U hU z tt).toNNReal = (sigmaTime U hU z ((ss : ℝ) + tt)).toNNReal := by
  apply NNReal.coe_injective
  have h1 := sigmaTime_nonneg hU htt
  have h2 := sigmaTime_nonneg hU hts
  have h3 := sigmaTime_le_add hU htt hts
  rw [NNReal.coe_add, Real.coe_toNNReal _ (sub_nonneg.2 h3), Real.coe_toNNReal _ h1,
    Real.coe_toNNReal _ h2]
  ring

theorem notMem_leftHull_sigmaTime {s : ℝ} (htt : s ∈ sigmaDom U hU z) :
    z ∉ leftHull U (sigmaTime U hU z s).toNNReal := by
  have h := sigmaTime_mem_lifeSet hU htt
  rw [← coe_toNNReal_sigmaTime hU htt, coe_mem_lifeSet_iff] at h
  exact h

theorem notMem_leftHull_sigmaTime_add (htt : (tt : ℝ) ∈ sigmaDom U hU z)
    (hts : (ss : ℝ) + tt ∈ sigmaDom U hU z) :
    z ∉ leftHull U ((sigmaTime U hU z ((ss : ℝ) + tt) - sigmaTime U hU z tt).toNNReal +
      (sigmaTime U hU z tt).toNNReal) := by
  rw [toNNReal_sub_add_toNNReal hU htt hts]
  exact notMem_leftHull_sigmaTime hU hts

theorem futureDistRatio_eq (htt : (tt : ℝ) ∈ sigmaDom U hU z) :
    futureDistRatio U hU z tt ss =
      infDist (fPath U hU z (((sigmaTime U hU z tt).toNNReal : ℝ≥0) : ℝ))
          (leftHull (futureDriver U (sigmaTime U hU z tt).toNNReal)
            (sigmaTime U hU z ((ss : ℝ) + tt) - sigmaTime U hU z tt).toNNReal) /
        ‖fPath U hU z (((sigmaTime U hU z tt).toNNReal : ℝ≥0) : ℝ)‖ := by
  unfold futureDistRatio
  rw [coe_toNNReal_sigmaTime hU htt]
  rfl

theorem hullDist_add_eq (htt : (tt : ℝ) ∈ sigmaDom U hU z)
    (hts : (ss : ℝ) + tt ∈ sigmaDom U hU z) :
    hullDist U hU z (ss + tt) =
      infDist z (leftHull U ((sigmaTime U hU z ((ss : ℝ) + tt) - sigmaTime U hU z tt).toNNReal +
        (sigmaTime U hU z tt).toNNReal)) := by
  rw [toNNReal_sub_add_toNNReal hU htt hts]
  unfold hullDist
  push_cast
  rfl

theorem derivNorm_pos (z : ℂ) (t : ℝ) : 0 < ‖derivPath U hU z t‖ :=
  norm_pos_iff.2 (derivPath_ne_zero hU z t)

theorem exp_sigmaRatioDet (htt : (tt : ℝ) ∈ sigmaDom U hU z) :
    Real.exp (sigmaRatioDet U hU z tt) =
      ‖derivPath U hU z (sigmaTime U hU z tt)‖ / ‖fPath U hU z (sigmaTime U hU z tt)‖ := by
  have hf := norm_fPath_pos hU (sigmaTime_mem_lifeSet hU htt)
  unfold sigmaRatioDet
  rw [Real.exp_sub, Real.exp_log (derivNorm_pos hU z _), Real.exp_log hf]

theorem hullDist_pos (htt : (tt : ℝ) ∈ sigmaDom U hU z) : 0 < hullDist U hU z tt :=
  infDist_leftHull_pos hU (notMem_leftHull_sigmaTime hU htt)

end Basic

/-! ### `eqn-dist-3` in σ-time -/

section Chain

variable (hU : Continuous U) {z : ℂ} {tt ss : ℝ≥0}
  (htt : (tt : ℝ) ∈ sigmaDom U hU z) (hts : (ss : ℝ) + tt ∈ sigmaDom U hU z)

include htt hts

/-- **`eqn-dist-3` in σ-time on the event `E_s̃`** (paper.tex:L1668-1672), constant `log 16`:
`log X_s̃ - log dist(z, L_{σ(s̃ + t̃)}) ≤ log(|f_t'|/|f_t|) + log 16`. -/
theorem chain_sigma_of_event (hE : koebeEventSigma U hU z tt ss) :
    Real.log (futureDistRatio U hU z tt ss) - Real.log (hullDist U hU z (ss + tt)) ≤
      sigmaRatioDet U hU z tt + Real.log 16 := by
  classical
  have h := koebe_chain hU (notMem_leftHull_sigmaTime_add hU htt hts)
  have hE' : koebeEvent U hU (sigmaTime U hU z tt).toNNReal
      (sigmaTime U hU z ((ss : ℝ) + tt) - sigmaTime U hU z tt).toNNReal z := hE
  simp only [hE', ↓reduceIte] at h
  rw [← hullDist_add_eq hU htt hts, ← futureDistRatio_eq hU htt] at h
  have hf := norm_fPath_pos hU (sigmaTime_mem_lifeSet hU htt)
  have hc := coe_toNNReal_sigmaTime hU htt
  rw [hc] at h
  rw [sigmaRatioDet, ← Real.log_div (derivNorm_pos hU z _).ne' hf.ne']
  exact h

/-- **`eqn-dist-3` in σ-time off the event `E_s̃`**:
`log X_s̃ - log dist(z, L_{σ(s̃ + t̃)}) ≤ log(1/dist(z, L_t)) + log 16`. -/
theorem chain_sigma_of_not_event (hE : ¬ koebeEventSigma U hU z tt ss) :
    Real.log (futureDistRatio U hU z tt ss) - Real.log (hullDist U hU z (ss + tt)) ≤
      Real.log (1 / hullDist U hU z tt) + Real.log 16 := by
  classical
  have h := koebe_chain hU (notMem_leftHull_sigmaTime_add hU htt hts)
  have hE' : ¬ koebeEvent U hU (sigmaTime U hU z tt).toNNReal
      (sigmaTime U hU z ((ss : ℝ) + tt) - sigmaTime U hU z tt).toNNReal z := hE
  simp only [hE', ↓reduceIte] at h
  rw [← hullDist_add_eq hU htt hts, ← futureDistRatio_eq hU htt] at h
  exact h

omit hts in
/-- `eqn-hit-koebe` (paper.tex:L1463): `log(|f_t'|/|f_t|) ≤ log(1/dist(z, L_t)) + log 4`
(`|f_t'(z)| dist(z, L_t) ≤ 4 dist(f_t z, R_t) ≤ 4 |f_t z|` as `0 ∈ R_t`). -/
theorem sigmaRatioDet_le :
    sigmaRatioDet U hU z tt ≤ Real.log (1 / hullDist U hU z tt) + Real.log 4 := by
  have hf := norm_fPath_pos hU (sigmaTime_mem_lifeSet hU htt)
  have hd := hullDist_pos hU htt
  have hc := coe_toNNReal_sigmaTime hU htt
  have hz := notMem_leftHull_sigmaTime hU htt
  have h1 := norm_derivPath_mul_infDist_le_infDist_rightHull hU hz
  rw [hc] at h1
  have h2 : infDist (fPath U hU z (sigmaTime U hU z tt))
      (rightHull U hU (sigmaTime U hU z tt).toNNReal) ≤
        ‖fPath U hU z (sigmaTime U hU z tt)‖ := by
    have := infDist_le_dist_of_mem (x := fPath U hU z (sigmaTime U hU z tt))
      (zero_mem_rightHull hU (sigmaTime U hU z tt).toNNReal)
    simpa [dist_eq_norm] using this
  have h3 : ‖derivPath U hU z (sigmaTime U hU z tt)‖ * hullDist U hU z tt ≤
      4 * ‖fPath U hU z (sigmaTime U hU z tt)‖ := by
    have : hullDist U hU z tt = infDist z (leftHull U (sigmaTime U hU z tt).toNNReal) := rfl
    rw [this]
    linarith
  rw [← Real.log_mul (by positivity) (by norm_num), sigmaRatioDet,
    ← Real.log_div (derivNorm_pos hU z _).ne' hf.ne']
  refine Real.log_le_log (div_pos (derivNorm_pos hU z _) hf) ?_
  rw [div_le_iff₀ hf]
  have : 1 / hullDist U hU z tt * 4 * ‖fPath U hU z (sigmaTime U hU z tt)‖ =
      4 * ‖fPath U hU z (sigmaTime U hU z tt)‖ / hullDist U hU z tt := by field_simp
  rw [this, le_div_iff₀ hd]
  exact h3

/-- **Unconditional form of `eqn-dist-3`**: `log X_s̃ - log dist(z, L_{σ(s̃ + t̃)}) ≤
log(1/dist(z, L_t)) + log 64`. -/
theorem chain_sigma_le :
    Real.log (futureDistRatio U hU z tt ss) - Real.log (hullDist U hU z (ss + tt)) ≤
      Real.log (1 / hullDist U hU z tt) + Real.log 64 := by
  have h64 : Real.log 64 = Real.log 4 + Real.log 16 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  by_cases hE : koebeEventSigma U hU z tt ss
  · have := chain_sigma_of_event hU htt hts hE
    have h2 := sigmaRatioDet_le hU htt
    linarith
  · have := chain_sigma_of_not_event hU htt hts hE
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith

omit hts in
/-- If `X_s̃ ≤ koebeBound` then the event `E_s̃` holds. -/
theorem koebeEventSigma_of_le (h : futureDistRatio U hU z tt ss ≤ koebeBound U hU z tt) :
    koebeEventSigma U hU z tt ss := by
  have hf := norm_fPath_pos hU (sigmaTime_mem_lifeSet hU htt)
  have hc := coe_toNNReal_sigmaTime hU htt
  have hz := notMem_leftHull_sigmaTime hU htt
  have h1 := norm_derivPath_mul_infDist_le_infDist_rightHull hU hz
  rw [hc] at h1
  unfold koebeEventSigma koebeEvent
  rw [hc]
  rw [futureDistRatio_eq hU htt, hc, div_le_iff₀ hf] at h
  refine h.trans ?_
  unfold koebeBound
  rw [exp_sigmaRatioDet hU htt]
  have : ‖derivPath U hU z (sigmaTime U hU z tt)‖ / ‖fPath U hU z (sigmaTime U hU z tt)‖ *
      hullDist U hU z tt / 4 * ‖fPath U hU z (sigmaTime U hU z tt)‖ =
      ‖derivPath U hU z (sigmaTime U hU z tt)‖ * hullDist U hU z tt / 4 := by field_simp
  rw [this]
  have : hullDist U hU z tt = infDist z (leftHull U (sigmaTime U hU z tt).toNNReal) := rfl
  rw [this]
  linarith

end Chain

/-! ### `step:converse-event-converges` -/

section Eventually

variable (hU : Continuous U) {z : ℂ} (tt : ℝ≥0)

/-- **`1_{E_s̃} → 1` (in the form `X_s̃ ≤ koebeBound` eventually)**
(`step:converse-event-converges`, paper.tex:L1748). If `σ_z` is defined on `[0, ∞)` and
`lim_{u → T_z} dist(z, L_u) = 0` in the R14 ε-form, then for every `t̃`, eventually in `s̃`
`dist(f_t z, L_{t,s+t}) / |f_t z| ≤ |f_t'(z)| dist(z, L_t) / (4 |f_t z|)`, hence `E_s̃` holds. -/
theorem eventually_le_koebeBound (hdom : sigmaDom U hU z = Ici 0)
    (hlim : ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < absorbingTime U z ∧ infDist z (leftHull U t) < ε) :
    ∀ᶠ ss : ℝ≥0 in atTop, futureDistRatio U hU z tt ss ≤ koebeBound U hU z tt := by
  have htt : (tt : ℝ) ∈ sigmaDom U hU z := by rw [hdom]; exact tt.coe_nonneg
  have hc := coe_toNNReal_sigmaTime hU htt
  have hz := notMem_leftHull_sigmaTime hU htt
  have hf := norm_fPath_pos hU (sigmaTime_mem_lifeSet hU htt)
  have hd := hullDist_pos hU htt
  have hD := derivNorm_pos hU z (sigmaTime U hU z tt)
  set ε₀ : ℝ := ‖derivPath U hU z (sigmaTime U hU z tt)‖ * hullDist U hU z tt / 4 with hε₀
  have hε₀pos : 0 < ε₀ := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := exists_infDist_futureHull_lt hU hz hε₀pos
  obtain ⟨t₀, ht₀, hd₀⟩ := hlim δ hδ
  have ht₀life : (t₀ : ℝ) ∈ lifeSet U z := by
    rw [mem_lifeSet]
    exact ⟨t₀.coe_nonneg, by rwa [ENNReal.ofReal_coe_nnreal]⟩
  have hcdom : clock U hU z t₀ ∈ sigmaDom U hU z := clock_mem_sigmaDom hU ht₀life
  rw [eventually_atTop]
  refine ⟨(clock U hU z t₀).toNNReal, fun ss hss => ?_⟩
  have hss' : clock U hU z t₀ ≤ ss := by
    have := Real.le_coe_toNNReal (clock U hU z t₀)
    exact this.trans (by exact_mod_cast hss)
  have hts : (ss : ℝ) + tt ∈ sigmaDom U hU z := by
    rw [hdom]; exact add_nonneg ss.coe_nonneg tt.coe_nonneg
  have hcle : clock U hU z t₀ ≤ (ss : ℝ) + tt := hss'.trans (by simp)
  have hσ : (t₀ : ℝ) ≤ sigmaTime U hU z ((ss : ℝ) + tt) := by
    have := sigmaTime_monotoneOn hU z hcdom hts hcle
    rwa [sigmaTime_clock hU ht₀life] at this
  have hsub : leftHull U t₀ ⊆ leftHull U ((sigmaTime U hU z ((ss : ℝ) + tt) -
      sigmaTime U hU z tt).toNNReal + (sigmaTime U hU z tt).toNNReal) := by
    refine leftHull_mono ?_
    rw [toNNReal_sub_add_toNNReal hU htt hts]
    exact (Real.le_toNNReal_iff_coe_le (sigmaTime_nonneg hU hts)).2 hσ
  have hlt : infDist z (leftHull U ((sigmaTime U hU z ((ss : ℝ) + tt) -
      sigmaTime U hU z tt).toNNReal + (sigmaTime U hU z tt).toNNReal)) < δ :=
    lt_of_le_of_lt (infDist_le_infDist_of_subset hsub (leftHull_nonempty U t₀)) hd₀
  have h1 := hδ' _ hlt
  rw [futureDistRatio_eq hU htt, hc, div_le_iff₀ hf]
  unfold koebeBound
  rw [exp_sigmaRatioDet hU htt]
  have : ‖derivPath U hU z (sigmaTime U hU z tt)‖ / ‖fPath U hU z (sigmaTime U hU z tt)‖ *
      hullDist U hU z tt / 4 * ‖fPath U hU z (sigmaTime U hU z tt)‖ = ε₀ := by
    rw [hε₀]; field_simp
  rw [this]
  rw [hc] at h1
  exact h1.le

end Eventually

end ComplexSLE.Internal

end
