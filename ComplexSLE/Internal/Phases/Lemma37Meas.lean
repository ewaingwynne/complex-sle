/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.Lemma37Hull
public import ComplexSLE.Internal.Phases.EventMeasDist
public import ComplexSLE.Internal.Stationary.PathStatMeas

/-!
# Lemma 3.7, measurability on the canonical path space (M7/E1)

The two sides of Lemma 3.7 (`futureDistRatio`, `hullDist`, `Lemma37Hull.lean`) are evaluated at the
random time `σ_z(s̃)` of the hull, so their measurability in (driver path, direction) needs

* **right continuity of the hull distance in time** (`tendsto_infDist_leftHull`): if `t_n → t` with
  `t_n ≥ t` then `dist(z, L_{t_n}) → dist(z, L_t)`. Nearest points of `L_{t_n}` to `z` stay in a
  compact ball; a limit point lies in `L_{t + ε}` for every `ε > 0` (closed hulls, monotone in
  time), hence in `L_t = ⋂_ε L_{t + ε}`;
* **joint measurability of the hull distance in (path, point, time)**
  (`measurable_infDist_leftHull_time`): the dyadic-from-above approximation of the time and the
  fixed-time measurability of `EventMeasDist.lean`;
* **measurability of `σ_z(s̃)` in (path, `u`)** for `z = e^{iu}` (`measurable_sigmaTimeC`), by the
  Carathéodory lemma of `PolarContMeas.lean` applied to the canonical driver (`PathStatCanon.lean`),
  continuity of `σ` in the initial point (`continuousOn_sigmaTime_initial`) and the stopping time
  `sigmaTop`.

Consequently `hullDistC s̃ v z = dist(z, L_{σ_z(s̃)}(v))` is jointly measurable in `(v, e^{iu})`
(`measurable_hullDistC_unit`), and the left side of Lemma 3.7 agrees with a jointly measurable
function on the event that `σ_z` is defined at `t̃` and `t̃ + s̃`
(`exists_measurable_futureDistRatio`).
-/

@[expose] public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory Filter Metric

namespace ComplexSLE.Internal

open Polar

/-! ### Right continuity of the hull distance in time -/

theorem isClosed_leftHull_of_continuous {u : ℝ≥0 → ℂ} (hu : Continuous u) (t : ℝ≥0) :
    IsClosed (leftHull u t) :=
  isOpen_compl_iff.1 (Polar.isOpen_compl_leftHull u hu t)

/-- **Right continuity of `t ↦ dist(z, L_t)`** along sequences `t_n ≥ t`, `t_n → t`. -/
theorem tendsto_infDist_leftHull {u : ℝ≥0 → ℂ} (hu : Continuous u) (z : ℂ) {t : ℝ≥0}
    {tn : ℕ → ℝ≥0} (hge : ∀ n, t ≤ tn n) (hlim : Tendsto tn atTop (𝓝 t)) :
    Tendsto (fun n => infDist z (leftHull u (tn n))) atTop (𝓝 (infDist z (leftHull u t))) := by
  set D := infDist z (leftHull u t) with hD
  have hle : ∀ n, infDist z (leftHull u (tn n)) ≤ D := fun n =>
    infDist_le_infDist_of_subset (leftHull_mono (hge n)) (leftHull_nonempty u t)
  refine tendsto_order.2 ⟨fun a ha => ?_,
    fun b hb => Eventually.of_forall fun n => (hle n).trans_lt hb⟩
  by_contra hcon
  have hfreq : ∃ᶠ n in atTop, infDist z (leftHull u (tn n)) ≤ a := by
    rw [Filter.Eventually] at hcon
    simpa [Filter.Frequently, Filter.Eventually, not_lt] using hcon
  obtain ⟨φ, hφ, hφle⟩ := Filter.extraction_of_frequently_atTop hfreq
  have hex : ∀ n, ∃ w ∈ leftHull u (tn n), infDist z (leftHull u (tn n)) = dist z w := fun n =>
    (isClosed_leftHull_of_continuous hu (tn n)).exists_infDist_eq_dist
      (leftHull_nonempty u _) z
  choose w hwmem hwdist using hex
  have hwb : ∀ k, w (φ k) ∈ closedBall z a := fun k => by
    rw [mem_closedBall']
    rw [← hwdist (φ k)]
    exact hφle k
  obtain ⟨y, -, ψ, hψ, hy⟩ := (isCompact_closedBall z a).tendsto_subseq hwb
  have hyhull : y ∈ leftHull u t := by
    rw [mem_leftHull_iff]
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨t', ht1, ht2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
    have ht1' : t < t' := by exact_mod_cast ht1
    have hev : ∀ᶠ k in atTop, tn (φ (ψ k)) < t' :=
      (hlim.comp (hφ.comp hψ).tendsto_atTop).eventually (gt_mem_nhds ht1')
    have hmem : y ∈ leftHull u t' := by
      refine (isClosed_leftHull_of_continuous hu t').mem_of_tendsto hy ?_
      filter_upwards [hev] with k hk
      exact leftHull_mono hk.le (hwmem (φ (ψ k)))
    exact absurd (mem_leftHull_iff.1 hmem) (not_le.2 ht2)
  have h1 : D ≤ dist z y := infDist_le_dist_of_mem hyhull
  have h2 : dist z y ≤ a := by
    refine le_of_tendsto (tendsto_const_nhds.dist hy) (Eventually.of_forall fun k => ?_)
    change dist z (w (φ (ψ k))) ≤ a
    rw [← hwdist (φ (ψ k))]
    exact hφle _
  linarith

/-! ### Joint measurability in (path, point, time) -/

/-- The dyadic-type grid `(k + 1) / (n + 1)` approximating times from above. -/
noncomputable def timeGrid (n k : ℕ) : ℝ≥0 := ((k : ℝ≥0) + 1) / ((n : ℝ≥0) + 1)

/-- The index of the grid point just above `t`. -/
noncomputable def timeGridIdx (n : ℕ) (t : ℝ≥0) : ℕ := ⌊((n : ℝ≥0) + 1) * t⌋₊

theorem le_timeGrid_idx (n : ℕ) (t : ℝ≥0) : t ≤ timeGrid n (timeGridIdx n t) := by
  have hn0 : (0 : ℝ≥0) < (n : ℝ≥0) + 1 := by positivity
  unfold timeGrid timeGridIdx
  rw [le_div_iff₀ hn0, mul_comm]
  exact (Nat.lt_floor_add_one _).le

theorem timeGrid_idx_le (n : ℕ) (t : ℝ≥0) :
    timeGrid n (timeGridIdx n t) ≤ t + 1 / ((n : ℝ≥0) + 1) := by
  have hn0 : (0 : ℝ≥0) < (n : ℝ≥0) + 1 := by positivity
  unfold timeGrid timeGridIdx
  have h1 : ((⌊((n : ℝ≥0) + 1) * t⌋₊ : ℝ≥0) + 1) ≤ ((n : ℝ≥0) + 1) * t + 1 :=
    add_le_add_left (Nat.floor_le (bot_le : (0 : ℝ≥0) ≤ ((n : ℝ≥0) + 1) * t)) 1
  calc ((⌊((n : ℝ≥0) + 1) * t⌋₊ : ℝ≥0) + 1) / ((n : ℝ≥0) + 1)
      ≤ (((n : ℝ≥0) + 1) * t + 1) / ((n : ℝ≥0) + 1) :=
        div_le_div_of_nonneg_right h1 hn0.le
    _ = t + 1 / ((n : ℝ≥0) + 1) := by
        rw [add_div, mul_div_cancel_left₀ _ hn0.ne']

theorem tendsto_timeGrid_idx (t : ℝ≥0) :
    Tendsto (fun n => timeGrid n (timeGridIdx n t)) atTop (𝓝 t) := by
  have hu : Tendsto (fun n : ℕ => t + 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 t) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 0) := by
      rw [← NNReal.tendsto_coe]
      simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_add, NNReal.coe_natCast,
        NNReal.coe_zero] using tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using tendsto_const_nhds.add h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun n => le_timeGrid_idx n t) (fun n => timeGrid_idx_le n t)

theorem measurable_timeGridIdx (n : ℕ) : Measurable (timeGridIdx n) :=
  Nat.measurable_floor.comp (measurable_const.mul measurable_id)

/-- **`(u, z, t) ↦ dist(z, L_t(u))` is jointly measurable** (it is right continuous in `t`). -/
theorem measurable_infDist_leftHull_time :
    Measurable fun p : (ContPath × ℂ) × ℝ≥0 => infDist p.1.2 (leftHull p.1.1.1 p.2) := by
  have hmeas_n : ∀ n, Measurable fun p : (ContPath × ℂ) × ℝ≥0 =>
      infDist p.1.2 (leftHull p.1.1.1 (timeGrid n (timeGridIdx n p.2))) := by
    intro n
    have h1 : Measurable fun x : (ContPath × ℂ) × ℕ =>
        infDist x.1.2 (leftHull x.1.1.1 (timeGrid n x.2)) := by
      refine measurable_from_prod_countable_left (f := fun x : (ContPath × ℂ) × ℕ =>
        infDist x.1.2 (leftHull x.1.1.1 (timeGrid n x.2))) fun k => ?_
      exact measurable_infDist_leftHull (timeGrid n k)
    have h2 : Measurable fun p : (ContPath × ℂ) × ℝ≥0 => (p.1, timeGridIdx n p.2) :=
      measurable_fst.prodMk ((measurable_timeGridIdx n).comp measurable_snd)
    have h3 := h1.comp h2
    simp only [Function.comp_def] at h3
    exact h3
  refine measurable_of_tendsto_metrizable
    (f := fun n (p : (ContPath × ℂ) × ℝ≥0) =>
      infDist p.1.2 (leftHull p.1.1.1 (timeGrid n (timeGridIdx n p.2))))
    (g := fun p : (ContPath × ℂ) × ℝ≥0 => infDist p.1.2 (leftHull p.1.1.1 p.2))
    hmeas_n (tendsto_pi_nhds.2 fun p => ?_)
  exact tendsto_infDist_leftHull p.1.1.2 p.1.2 (fun n => le_timeGrid_idx n p.2)
    (tendsto_timeGrid_idx p.2)

/-! ### The σ-time as a function on the canonical path space -/

open Classical in
/-- `σ_z(s̃)` as an element of `ℝ≥0` for the chain driven by the continuous path `v` (`0` off the
domain of `σ_z`). -/
noncomputable def sigmaTimeC (ss : ℝ≥0) (v : CPath) (z : ℂ) : ℝ≥0 :=
  if (ss : ℝ) ∈ sigmaDom v.1 v.2 z then (sigmaTime v.1 v.2 z ss).toNNReal else 0

/-- `dist(z, L_{σ_z(s̃)})` for the chain driven by the continuous path `v` (the left hull at the
time `sigmaTimeC`). -/
noncomputable def hullDistC (ss : ℝ≥0) (v : CPath) (z : ℂ) : ℝ :=
  infDist z (leftHull v.1 (sigmaTimeC ss v z))

theorem sigmaTimeC_of_mem {ss : ℝ≥0} {v : CPath} {z : ℂ}
    (h : (ss : ℝ) ∈ sigmaDom v.1 v.2 z) :
    sigmaTimeC ss v z = (sigmaTime v.1 v.2 z ss).toNNReal := by
  unfold sigmaTimeC; exact ite_eq_left h

theorem coe_sigmaTimeC_of_mem {ss : ℝ≥0} {v : CPath} {z : ℂ}
    (h : (ss : ℝ) ∈ sigmaDom v.1 v.2 z) :
    (sigmaTimeC ss v z : ℝ) = sigmaTime v.1 v.2 z ss := by
  rw [sigmaTimeC_of_mem h, Real.coe_toNNReal _ (sigmaTime_nonneg v.2 h)]

theorem sigmaTimeC_of_notMem {ss : ℝ≥0} {v : CPath} {z : ℂ}
    (h : (ss : ℝ) ∉ sigmaDom v.1 v.2 z) : sigmaTimeC ss v z = 0 := by
  unfold sigmaTimeC; exact ite_eq_right h

theorem hullDistC_of_mem {ss : ℝ≥0} {v : CPath} {z : ℂ}
    (h : (ss : ℝ) ∈ sigmaDom v.1 v.2 z) :
    hullDistC ss v z = hullDist v.1 v.2 z ss := by
  unfold hullDistC hullDist
  rw [sigmaTimeC_of_mem h]

theorem sigmaTimeC_neg (ss : ℝ≥0) (v : CPath) (ξ : ℂ) :
    sigmaTimeC ss (CPath.neg v) ξ = sigmaTimeC ss v (-ξ) := by
  have hV' : Continuous fun s => -v.1 s := v.2.neg
  have hdom : sigmaDom (CPath.neg v).1 (CPath.neg v).2 ξ = sigmaDom v.1 v.2 (-ξ) :=
    sigmaDom_neg v.2 hV' ξ
  unfold sigmaTimeC
  by_cases h : (ss : ℝ) ∈ sigmaDom v.1 v.2 (-ξ)
  · have h' : (ss : ℝ) ∈ sigmaDom (CPath.neg v).1 (CPath.neg v).2 ξ := by rwa [hdom]
    rw [ite_eq_left h, ite_eq_left h']
    exact congrArg Real.toNNReal (sigmaTime_neg v.2 hV' ξ ss)
  · have h' : (ss : ℝ) ∉ sigmaDom (CPath.neg v).1 (CPath.neg v).2 ξ := by rwa [hdom]
    rw [ite_eq_right h, ite_eq_right h']

/-- **Negation (reflection) of the hull distance in σ-time**, unconditional:
`dist(ξ, L_{σ_ξ(s̃)}(-v)) = dist(-ξ, L_{σ_{-ξ}(s̃)}(v))`. -/
theorem hullDistC_neg (ss : ℝ≥0) (v : CPath) (ξ : ℂ) :
    hullDistC ss (CPath.neg v) ξ = hullDistC ss v (-ξ) := by
  unfold hullDistC
  rw [sigmaTimeC_neg]
  change infDist ξ (leftHull (fun s => -v.1 s) _) = _
  rw [leftHull_neg]
  have h := infDist_image (x := -ξ) (t := leftHull v.1 (sigmaTimeC ss v (-ξ)))
    (Φ := (Neg.neg : ℂ → ℂ)) isometry_neg
  rwa [neg_neg] at h

section Meas

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-- **Joint measurability of `σ_{e^{iu}}(s̃)` on `CPath × ℝ`.** -/
theorem measurable_sigmaTimeC (hU : IsSLEDriverAdapted a b c U P ℱ) (ss : ℝ≥0) :
    Measurable fun q : CPath × ℝ => sigmaTimeC ss q.1 (unitPt q.2) := by
  classical
  obtain ⟨ℱc, hUc⟩ := exists_isSLEDriverAdapted_eval hU.toIsSLEDriver hU.cont
    (fun t => hU.adapted.measurable)
  have hS := measurableSet_sigmaDomUnit hUc (ss : ℝ)
  refine measurable_of_continuousOn_sections (S := sigmaDomUnit hUc (ss : ℝ))
    (F := fun q : CPath × ℝ => sigmaTimeC ss q.1 (unitPt q.2)) (G := fun _ => 0)
    hS (isOpen_sigmaDomUnit_section hUc (ss : ℝ)) measurable_const ?_ ?_ ?_
  · intro p hp
    exact sigmaTimeC_of_notMem hp
  · intro v
    have hc : ContinuousOn (fun u : ℝ => (sigmaTime v.1 v.2 (unitPt u) ss).toNNReal)
        {u | (ss : ℝ) ∈ sigmaDom v.1 v.2 (unitPt u)} := by
      refine continuous_real_toNNReal.comp_continuousOn ?_
      intro u hu
      exact ((continuousAt_sigmaTime_initial v.2 hu).comp (f := unitPt)
        continuous_unitPt.continuousAt).continuousWithinAt
    refine hc.congr fun u hu => ?_
    exact sigmaTimeC_of_mem hu
  · intro u
    have hτ := (isStoppingTime_sigmaTop hUc (unitPt u) ss).measurable'
    have h1 : Measurable fun v : CPath => (sigmaTop hUc (unitPt u) ss v).untopA := hτ.untopA
    have hS' : MeasurableSet {v : CPath | (ss : ℝ) ∈ sigmaDom v.1 v.2 (unitPt u)} :=
      measurable_prodMk_right hS
    have h2 : Measurable fun v : CPath =>
        if (ss : ℝ) ∈ sigmaDom v.1 v.2 (unitPt u) then (sigmaTop hUc (unitPt u) ss v).untopA
        else 0 := Measurable.ite hS' h1 measurable_const
    convert h2 using 1
    funext v
    by_cases hv : (ss : ℝ) ∈ sigmaDom v.1 v.2 (unitPt u)
    · rw [ite_eq_left hv, sigmaTimeC_of_mem hv]
      have := sigmaTop_of_mem hUc (z := unitPt u) (s := ss) (ω := v) hv
      rw [this]
      rfl
    · rw [ite_eq_right hv, sigmaTimeC_of_notMem hv]

/-- **Joint measurability of `dist(e^{iu}, L_{σ_{e^{iu}}(s̃)}(v))` on `CPath × ℝ`.** -/
theorem measurable_hullDistC_unit (hU : IsSLEDriverAdapted a b c U P ℱ) (ss : ℝ≥0) :
    Measurable fun q : CPath × ℝ => hullDistC ss q.1 (unitPt q.2) := by
  have h : Measurable fun q : CPath × ℝ =>
      ((q.1, unitPt q.2), sigmaTimeC ss q.1 (unitPt q.2)) :=
    (measurable_fst.prodMk (continuous_unitPt.measurable.comp measurable_snd)).prodMk
      (measurable_sigmaTimeC hU ss)
  have h3 := measurable_infDist_leftHull_time.comp h
  simp only [Function.comp_def] at h3
  exact h3

end Meas

/-! ### The left side of Lemma 3.7 as a measurable function -/

/-- The time shift `v ↦ v(· + t) - v(t)` of a continuous path. -/
def CPath.shift (v : CPath) (t : ℝ≥0) : CPath :=
  ⟨fun r => v.1 (r + t) - v.1 t,
    (v.2.comp (continuous_id.add continuous_const)).sub continuous_const⟩

theorem CPath.measurable_shift : Measurable fun p : CPath × ℝ≥0 => CPath.shift p.1 p.2 := by
  refine Measurable.subtype_mk (measurable_pi_iff.2 fun r => ?_)
  have h1 : Measurable fun p : CPath × ℝ≥0 => CPath.eval (r + p.2) p.1 :=
    CPath.measurable_eval_uncurry.comp ((measurable_const.add measurable_snd).prodMk measurable_fst)
  have h2 : Measurable fun p : CPath × ℝ≥0 => CPath.eval p.2 p.1 :=
    CPath.measurable_eval_uncurry.comp (measurable_snd.prodMk measurable_fst)
  exact h1.sub h2

/-- A measurable representative of the left side of Lemma 3.7:
`dist(f̂, L^{shift}_{(σ(s̃ + t̃) - σ(t̃))}) / |f̂|` written through `θ̂`, `log |f̂|` and `σ`. -/
noncomputable def futureDistRatioC (tt ss : ℝ≥0) (v : CPath) (z : ℂ) : ℝ :=
  infDist (Complex.exp ((logfC tt v z : ℝ) + (thetaC tt v z : ℝ) * Complex.I))
      (leftHull (CPath.shift v (sigmaTimeC tt v z)).1
        (((sigmaTimeC (ss + tt) v z : ℝ) - (sigmaTimeC tt v z : ℝ)).toNNReal)) /
    Real.exp (logfC tt v z)

theorem futureDistRatio_eq_C {tt ss : ℝ≥0} {v : CPath} {z : ℂ}
    (ht : (tt : ℝ) ∈ sigmaDom v.1 v.2 z) (hts : (ss : ℝ) + tt ∈ sigmaDom v.1 v.2 z) :
    futureDistRatio v.1 v.2 z tt ss = futureDistRatioC tt ss v z := by
  have hts' : ((ss + tt : ℝ≥0) : ℝ) ∈ sigmaDom v.1 v.2 z := by rwa [NNReal.coe_add]
  have hlife := sigmaTime_mem_lifeSet v.2 ht
  have hf := fPath_eq_norm_mul_exp v.2 hlife
  have hpos := norm_fPath_pos v.2 hlife
  have hlog : logfC tt v z = Real.log ‖fPath v.1 v.2 z (sigmaTime v.1 v.2 z tt)‖ :=
    logfC_of_mem ht
  have hth : thetaC tt v z = argPath v.1 v.2 z (sigmaTime v.1 v.2 z tt) := thetaC_of_mem ht
  have hexp : Real.exp (logfC tt v z) = ‖fPath v.1 v.2 z (sigmaTime v.1 v.2 z tt)‖ := by
    rw [hlog, Real.exp_log hpos]
  have hcexp : Complex.exp ((logfC tt v z : ℝ) + (thetaC tt v z : ℝ) * Complex.I) =
      fPath v.1 v.2 z (sigmaTime v.1 v.2 z tt) := by
    rw [Complex.exp_add, ← Complex.ofReal_exp, hexp, hth]
    exact hf.symm
  unfold futureDistRatio futureDistRatioC
  rw [hcexp, hexp, coe_sigmaTimeC_of_mem ht, coe_sigmaTimeC_of_mem hts', NNReal.coe_add,
    sigmaTimeC_of_mem ht]
  rfl

section Meas2

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-- **Joint measurability of the representative of the left side of Lemma 3.7.** -/
theorem measurable_futureDistRatioC_unit (hU : IsSLEDriverAdapted a b c U P ℱ) (tt ss : ℝ≥0) :
    Measurable fun q : CPath × ℝ => futureDistRatioC tt ss q.1 (unitPt q.2) := by
  have hlog := measurable_logfC_unit hU tt
  have hth := measurable_thetaC_unit hU tt
  have hσ1 := measurable_sigmaTimeC hU tt
  have hσ2 := measurable_sigmaTimeC hU (ss + tt)
  have hz : Measurable fun q : CPath × ℝ => Complex.exp ((logfC tt q.1 (unitPt q.2) : ℝ) +
      (thetaC tt q.1 (unitPt q.2) : ℝ) * Complex.I) := by
    refine Complex.measurable_exp.comp ?_
    exact (Complex.measurable_ofReal.comp hlog).add
      ((Complex.measurable_ofReal.comp hth).mul measurable_const)
  have hW : Measurable fun q : CPath × ℝ => CPath.shift q.1 (sigmaTimeC tt q.1 (unitPt q.2)) :=
    CPath.measurable_shift.comp (measurable_fst.prodMk hσ1)
  have hT : Measurable fun q : CPath × ℝ =>
      ((sigmaTimeC (ss + tt) q.1 (unitPt q.2) : ℝ) -
        (sigmaTimeC tt q.1 (unitPt q.2) : ℝ)).toNNReal :=
    ((measurable_coe_nnreal_real.comp hσ2).sub (measurable_coe_nnreal_real.comp hσ1)).real_toNNReal
  have hnum : Measurable fun q : CPath × ℝ =>
      infDist (Complex.exp ((logfC tt q.1 (unitPt q.2) : ℝ) +
        (thetaC tt q.1 (unitPt q.2) : ℝ) * Complex.I))
      (leftHull (CPath.shift q.1 (sigmaTimeC tt q.1 (unitPt q.2))).1
        (((sigmaTimeC (ss + tt) q.1 (unitPt q.2) : ℝ) -
          (sigmaTimeC tt q.1 (unitPt q.2) : ℝ)).toNNReal)) := by
    have h := measurable_infDist_leftHull_time.comp ((hW.prodMk hz).prodMk hT)
    simp only [Function.comp_def] at h
    exact h
  exact hnum.div (Real.measurable_exp.comp hlog)

end Meas2

end ComplexSLE.Internal

end
