/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.ExitTimes
public import ComplexSLE.Internal.Polar.ClockArg
public import ComplexSLE.Internal.Polar.Sigma

/-!
# Exit times with separate time and clock caps (M6/S12, input to Remark 2.12)

For the proof of Remark 2.12 (`remark-sigma`: a.s. `clockSup = ∞`) we need the first time at
which the path leaves the annulus `1/n < |f_t(z)| < n`, capped at a deterministic time `m` and at
the first time the clock `A(t) = ∫₀ᵗ |f_s(z)|⁻² ds` reaches `T`:

  `capExitTime U hU z n m T = inf {t ∈ [0, T_z) | |f_t| ≤ 1/n ∨ |f_t| ≥ n ∨ t ≥ m ∨ A(t) ≥ T}`.

The annulus exit times `exitTime` of `Path.lean` carry the cap `t ≥ n` tied to the level `n`,
which is not enough for the argument: on `{T_z = ∞}` the annulus may be left only after time `n`.
With `n ≤ N` and `m ≤ N` the capped time is at most `exitTime N`, so the martingales of
`PolarItoLog.lean` (built from `exitTime N`) stopped at it have brackets bounded by a multiple of
`T`. The clock cap also makes it a *strict* clock cap on the event `{sup A < T}`: there it is not
active.

Deterministically (`0 < T_z`): the capped time lies in the life set, is at most `m`, attains its
exit condition, and before it the path stays in the open annulus with `t < m` and `A(t) < T`
(`lt_capExitTime_iff`). Probabilistically it is an `ℱ`-stopping time
(`isStoppingTime_capExitTime`), by the same dense-set argument as in `ExitTimes.lean`.
-/

public section

open scoped NNReal ENNReal
open Set MeasureTheory

namespace ComplexSLE.Internal.Polar

/-! ### Deterministic layer -/

section Deterministic

variable {U : ℝ≥0 → ℂ}

/-- The capped exit condition: `|f_t(z)| ≤ 1/n`, or `|f_t(z)| ≥ n`, or `t ≥ m`, or `A(t) ≥ T`. -/
@[expose] def CapExitCond (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) (n : ℕ) (m T : ℝ) (t : ℝ) :
    Prop :=
  ‖fPath U hU z t‖ ≤ 1 / n ∨ (n : ℝ) ≤ ‖fPath U hU z t‖ ∨ m ≤ t ∨ T ≤ clock U hU z t

/-- The times in the life set satisfying the capped exit condition. -/
@[expose] def capExitSet (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) (n : ℕ) (m T : ℝ) : Set ℝ :=
  {t | t ∈ lifeSet U z ∧ CapExitCond U hU z n m T t}

/-- **The capped exit time**: the first time in `[0, T_z)` at which `|f| ≤ 1/n`, `|f| ≥ n`,
`t = m` or `A(t) = T`. -/
@[expose] noncomputable def capExitTime (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) (n : ℕ)
    (m T : ℝ) : ℝ :=
  sInf (capExitSet U hU z n m T)

/-- The exit set at level `N ≥ n, m` is contained in the capped exit set. -/
theorem exitSet_subset_capExitSet (hU : Continuous U) (z : ℂ) {n N : ℕ} (hn : n ≤ N) {m : ℝ}
    (hm : m ≤ N) (T : ℝ) : exitSet U hU z N ⊆ capExitSet U hU z n m T := by
  rintro t ⟨ht, hc⟩
  refine ⟨ht, ?_⟩
  rcases hc with h | h | h
  · rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · exact Or.inr (Or.inl (by simp [hn0]))
    · have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
      exact Or.inl (h.trans (one_div_le_one_div_of_le hnr (by exact_mod_cast hn)))
  · exact Or.inr (Or.inl ((by exact_mod_cast hn : (n : ℝ) ≤ N).trans h))
  · exact Or.inr (Or.inr (Or.inl (hm.trans h)))

theorem capExitSet_nonempty (hU : Continuous U) {z : ℂ} (hz : 0 < absorbingTime U z) (n : ℕ)
    (m T : ℝ) : (capExitSet U hU z n m T).Nonempty := by
  obtain ⟨t, ht⟩ := exitSet_nonempty hU hz (max n ⌈m⌉₊)
  exact ⟨t, exitSet_subset_capExitSet hU z (le_max_left _ _)
    ((Nat.le_ceil m).trans (by exact_mod_cast le_max_right n ⌈m⌉₊)) T ht⟩

theorem capExitSet_bddBelow (hU : Continuous U) (z : ℂ) (n : ℕ) (m T : ℝ) :
    BddBelow (capExitSet U hU z n m T) :=
  ⟨0, fun _ ht => ht.1.1⟩

theorem capExitTime_le_of_mem (hU : Continuous U) {z : ℂ} {n : ℕ} {m T t : ℝ}
    (ht : t ∈ capExitSet U hU z n m T) : capExitTime U hU z n m T ≤ t :=
  csInf_le (capExitSet_bddBelow hU z n m T) ht

theorem capExitTime_nonneg (hU : Continuous U) {z : ℂ} (hz : 0 < absorbingTime U z) (n : ℕ)
    (m T : ℝ) : 0 ≤ capExitTime U hU z n m T :=
  le_csInf (capExitSet_nonempty hU hz n m T) fun _ ht => ht.1.1

/-- The capped exit time is nonnegative also when `T_z = 0` (where it is `sInf ∅ = 0`). -/
theorem capExitTime_nonneg' (hU : Continuous U) (z : ℂ) (n : ℕ) (m T : ℝ) :
    0 ≤ capExitTime U hU z n m T := by
  by_cases h : (capExitSet U hU z n m T).Nonempty
  · exact le_csInf h fun _ ht => ht.1.1
  · rw [not_nonempty_iff_eq_empty] at h
    simp [capExitTime, h]

/-- When `T_z = 0` the capped exit time is `0`. -/
theorem capExitTime_eq_zero_of_not_pos (hU : Continuous U) {z : ℂ}
    (hz : ¬ 0 < absorbingTime U z) (n : ℕ) (m T : ℝ) : capExitTime U hU z n m T = 0 := by
  have : capExitSet U hU z n m T = ∅ := by
    ext t
    simp only [capExitSet, Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro ht _
    exact hz (zero_mem_lifeSet_iff.1 (mem_lifeSet_of_le ht le_rfl ht.1))
  simp [capExitTime, this]

theorem capExitTime_mem_lifeSet (hU : Continuous U) {z : ℂ} (hz : 0 < absorbingTime U z) (n : ℕ)
    (m T : ℝ) : capExitTime U hU z n m T ∈ lifeSet U z := by
  obtain ⟨t, ht⟩ := capExitSet_nonempty hU hz n m T
  exact mem_lifeSet_of_le ht.1 (capExitTime_nonneg hU hz n m T) (capExitTime_le_of_mem hU ht)

/-- The capped exit time is at most the annulus exit time at any level `N ≥ n, m`. -/
theorem capExitTime_le_exitTime (hU : Continuous U) {z : ℂ} (hz : 0 < absorbingTime U z)
    {n N : ℕ} (hn : n ≤ N) {m : ℝ} (hm : m ≤ N) (T : ℝ) :
    capExitTime U hU z n m T ≤ exitTime U hU z N :=
  csInf_le_csInf (capExitSet_bddBelow hU z n m T) (exitSet_nonempty hU hz N)
    (exitSet_subset_capExitSet hU z hn hm T)

theorem capExitTime_le (hU : Continuous U) {z : ℂ} (hz : 0 < absorbingTime U z) (n : ℕ) {m : ℝ}
    (hm : 0 ≤ m) (T : ℝ) : capExitTime U hU z n m T ≤ m := by
  by_cases hmT : ENNReal.ofReal m < absorbingTime U z
  · exact capExitTime_le_of_mem hU ⟨⟨hm, hmT⟩, Or.inr (Or.inr (Or.inl le_rfl))⟩
  · push Not at hmT
    have h := (capExitTime_mem_lifeSet hU hz n m T).2
    by_contra hlt
    push Not at hlt
    exact absurd (lt_of_lt_of_le h hmT) (not_lt.2 (ENNReal.ofReal_le_ofReal hlt.le))

/-- Before the capped exit time: in the life set, in the open annulus, before `m`, clock below
`T`. -/
theorem of_lt_capExitTime (hU : Continuous U) {z : ℂ} {n : ℕ} {m T t : ℝ} (h0 : 0 ≤ t)
    (ht : t < capExitTime U hU z n m T) :
    t ∈ lifeSet U z ∧ (1 / (n : ℝ) < ‖fPath U hU z t‖ ∧ ‖fPath U hU z t‖ < n) ∧ t < m ∧
      clock U hU z t < T := by
  have hz : 0 < absorbingTime U z := by
    by_contra hz
    rw [capExitTime_eq_zero_of_not_pos hU hz] at ht
    linarith
  have hmem : t ∈ lifeSet U z :=
    mem_lifeSet_of_le (capExitTime_mem_lifeSet hU hz n m T) h0 ht.le
  have hnot : ¬ CapExitCond U hU z n m T t := fun hc =>
    not_lt.2 (capExitTime_le_of_mem hU ⟨hmem, hc⟩) ht
  simp only [CapExitCond, not_or, not_le] at hnot
  exact ⟨hmem, ⟨hnot.1, hnot.2.1⟩, hnot.2.2.1, hnot.2.2.2⟩

/-- The capped exit condition is closed on the life set, so the infimum is attained. -/
theorem capExitTime_mem_capExitSet (hU : Continuous U) {z : ℂ} (hz : 0 < absorbingTime U z)
    (n : ℕ) (m T : ℝ) : capExitTime U hU z n m T ∈ capExitSet U hU z n m T := by
  set τ := capExitTime U hU z n m T with hτ
  have hτmem : τ ∈ lifeSet U z := capExitTime_mem_lifeSet hU hz n m T
  refine ⟨hτmem, ?_⟩
  by_contra hc
  simp only [CapExitCond, not_or, not_le] at hc
  obtain ⟨h1, h2, h3, h4⟩ := hc
  have hcont : ContinuousWithinAt (fun t => ‖fPath U hU z t‖) (lifeSet U z) τ :=
    continuousOn_norm_fPath hU z τ hτmem
  have hcontA : ContinuousWithinAt (clock U hU z) (lifeSet U z) τ :=
    continuousOn_clock hU z τ hτmem
  have hev : ∀ᶠ t in nhdsWithin τ (lifeSet U z), ¬ CapExitCond U hU z n m T t := by
    have e1 : ∀ᶠ t in nhdsWithin τ (lifeSet U z), 1 / (n : ℝ) < ‖fPath U hU z t‖ :=
      hcont.eventually (lt_mem_nhds h1)
    have e2 : ∀ᶠ t in nhdsWithin τ (lifeSet U z), ‖fPath U hU z t‖ < n :=
      hcont.eventually (gt_mem_nhds h2)
    have e3 : ∀ᶠ t : ℝ in nhdsWithin τ (lifeSet U z), t < m :=
      eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds h3)
    have e4 : ∀ᶠ t in nhdsWithin τ (lifeSet U z), clock U hU z t < T :=
      hcontA.eventually (gt_mem_nhds h4)
    filter_upwards [e1, e2, e3, e4] with t ht1 ht2 ht3 ht4
    simp only [CapExitCond, not_or, not_le]
    exact ⟨ht1, ht2, ht3, ht4⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  obtain ⟨s, hs, hsε⟩ := exists_lt_of_csInf_lt (capExitSet_nonempty hU hz n m T)
    (show sInf (capExitSet U hU z n m T) < τ + ε by
      change capExitTime U hU z n m T < τ + ε; rw [← hτ]; linarith)
  have hτs : τ ≤ s := capExitTime_le_of_mem hU hs
  have : s ∈ Metric.ball τ ε ∩ lifeSet U z :=
    ⟨by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith, hs.1⟩
  exact hball this hs.2

/-- The clock at the capped exit time is at most `T` (for `0 ≤ T`). -/
theorem clock_capExitTime_le (hU : Continuous U) {z : ℂ} (hz : 0 < absorbingTime U z) (n : ℕ)
    (m : ℝ) {T : ℝ} (hT : 0 ≤ T) : clock U hU z (capExitTime U hU z n m T) ≤ T := by
  set τ := capExitTime U hU z n m T with hτ
  have hτmem : τ ∈ lifeSet U z := capExitTime_mem_lifeSet hU hz n m T
  rcases eq_or_lt_of_le (capExitTime_nonneg hU hz n m T) with h0 | h0
  · rw [hτ, ← h0, clock_zero]; exact hT
  · have hsub : Ico 0 τ ⊆ lifeSet U z := fun t ht => mem_lifeSet_of_le hτmem ht.1 ht.2.le
    refine ContinuousWithinAt.closure_le (f := clock U hU z) (g := fun _ => T) ?_
      ((continuousOn_clock hU z τ hτmem).mono hsub) continuousWithinAt_const fun t ht =>
      (of_lt_capExitTime hU ht.1 ht.2).2.2.2.le
    rw [closure_Ico h0.ne]
    exact right_mem_Icc.2 h0.le

/-- **`{s < capExitTime}` in terms of the path.** -/
theorem lt_capExitTime_iff (hU : Continuous U) {z : ℂ} {n : ℕ} {m T s : ℝ} (hs : 0 ≤ s) :
    s < capExitTime U hU z n m T ↔ s ∈ lifeSet U z ∧ s < m ∧ clock U hU z s < T ∧
      ∀ r ∈ Icc (0 : ℝ) s, 1 / (n : ℝ) < ‖fPath U hU z r‖ ∧ ‖fPath U hU z r‖ < n := by
  constructor
  · intro hlt
    obtain ⟨hsl, -, hsm, hsT⟩ := of_lt_capExitTime hU hs hlt
    exact ⟨hsl, hsm, hsT, fun r hr => (of_lt_capExitTime hU hr.1 (lt_of_le_of_lt hr.2 hlt)).2.1⟩
  · rintro ⟨hsl, hsm, hsT, hr⟩
    have hz : 0 < absorbingTime U z :=
      zero_mem_lifeSet_iff.1 (mem_lifeSet_of_le hsl le_rfl hs)
    by_contra hle
    push Not at hle
    obtain ⟨hmem, hc⟩ := capExitTime_mem_capExitSet hU hz n m T
    have hτ0 := capExitTime_nonneg hU hz n m T
    have hann := hr (capExitTime U hU z n m T) ⟨hτ0, hle⟩
    have hτm : capExitTime U hU z n m T < m := lt_of_le_of_lt hle hsm
    have hτT : clock U hU z (capExitTime U hU z n m T) < T :=
      lt_of_le_of_lt (clock_monotoneOn hU z hmem hsl hle) hsT
    rcases hc with h | h | h | h
    · exact absurd hann.1 (not_lt.2 h)
    · exact absurd hann.2 (not_lt.2 h)
    · exact absurd hτm (not_lt.2 h)
    · exact absurd hτT (not_lt.2 h)

/-- On the event `{A(t) < T for all t < T_z}`, the capped exit time exits the annulus
(rather than being stopped by a cap) as soon as the annulus is left before time `m`. -/
theorem norm_fPath_capExitTime_of_exit (hU : Continuous U) {z : ℂ}
    (hz : 0 < absorbingTime U z) {n : ℕ} {m T : ℝ}
    (hE : ∀ t ∈ lifeSet U z, clock U hU z t < T) {t : ℝ} (ht : t ∈ lifeSet U z) (htm : t < m)
    (hex : ‖fPath U hU z t‖ ≤ 1 / n ∨ (n : ℝ) ≤ ‖fPath U hU z t‖) :
    ‖fPath U hU z (capExitTime U hU z n m T)‖ ≤ 1 / n ∨
      (n : ℝ) ≤ ‖fPath U hU z (capExitTime U hU z n m T)‖ := by
  have hτt : capExitTime U hU z n m T ≤ t := by
    refine capExitTime_le_of_mem hU ⟨ht, ?_⟩
    rcases hex with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  obtain ⟨hmem, hc⟩ := capExitTime_mem_capExitSet hU hz n m T
  rcases hc with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (lt_of_le_of_lt hτt htm) (not_lt.2 h)
  · exact absurd (hE _ hmem) (not_lt.2 h)

/-- On `{A(t) < T for all t < T_z}` (`T_z > 0`), the annulus `1/n < |f| < n` is left at some time
of the life set, for every `n ≥ 1`: if `T_z < ∞` because `liminf |f| = 0`, and if `T_z = ∞`
because `|f|` bounded would force `sup A = ∞`. -/
theorem exists_annulus_exit (hU : Continuous U) {z : ℂ} (hz : 0 < absorbingTime U z) {n : ℕ}
    (hn : 1 ≤ n) {T : ℝ} (hE : ∀ t ∈ lifeSet U z, clock U hU z t < T) :
    ∃ t ∈ lifeSet U z, ‖fPath U hU z t‖ ≤ 1 / n ∨ (n : ℝ) ≤ ‖fPath U hU z t‖ := by
  by_cases hT : absorbingTime U z = ⊤
  · by_contra hcon
    push Not at hcon
    have hsup : clockSup U hU z ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ENNReal.ofReal T) ENNReal.ofReal_ne_top
        (iSup₂_le fun t ht => ?_)
      exact ENNReal.ofReal_le_ofReal (hE t ht).le
    refine hsup (clockSup_eq_top_of_norm_le hU hT (M := n) fun t ht => ?_)
    have htl : t ∈ lifeSet U z := by rw [lifeSet_eq_Ici hT]; exact ht
    exact (hcon t htl).2.le
  · have hη : (0 : ℝ) < 1 / n := by
      have : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    obtain ⟨s, hs, -, hlt⟩ := exists_norm_fPath_lt hU hT hη (zero_mem_lifeSet_iff.2 hz)
    exact ⟨s, hs, Or.inl hlt.le⟩

end Deterministic

/-! ### Stopping times -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {U : ℝ≥0 → Ω → ℂ} {ℱ : Filtration ℝ≥0 mΩ}

open Classical in
/-- `{s < capExitTime}` is `ℱ s`-measurable. -/
theorem measurableSet_lt_capExitTime (hc : ∀ ω, Continuous fun t => U t ω) (had : Adapted ℱ U)
    (z : ℂ) (n : ℕ) (m T : ℝ) (s : ℝ≥0) :
    MeasurableSet[ℱ s] {ω | (s : ℝ) < capExitTime (fun r => U r ω) (hc ω) z n m T} := by
  obtain ⟨D', hD'c, hD'd⟩ := TopologicalSpace.exists_countable_dense (Icc (0 : ℝ) s)
  set D : Set ℝ := Subtype.val '' D' with hD
  have hDsub : D ⊆ Icc (0 : ℝ) s := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hDcl : Icc (0 : ℝ) s ⊆ closure D := by
    intro x hx
    have h1 : (⟨x, hx⟩ : Icc (0 : ℝ) s) ∈ closure D' := by rw [hD'd.closure_eq]; trivial
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image] at h1
    exact h1
  have hDc : D.Countable := hD'c.image _
  have key : {ω | (s : ℝ) < capExitTime (fun r => U r ω) (hc ω) z n m T} =
      {ω | (s : ℝ) ∈ lifeSet (fun r => U r ω) z} ∩ ({ω | (s : ℝ) < m} ∩
        ({ω | (if (s : ℝ) ∈ lifeSet (fun r => U r ω) z then
            clock (fun r => U r ω) (hc ω) z s else 0) < T} ∩
        ⋃ k : ℕ, ⋂ r ∈ D, {ω | 1 / (n : ℝ) + 1 / ((k : ℝ) + 1) ≤
            ‖if (r.toNNReal : ℝ) ∈ lifeSet (fun s => U s ω) z then
              fPath (fun s => U s ω) (hc ω) z r.toNNReal else 0‖ ∧
          ‖if (r.toNNReal : ℝ) ∈ lifeSet (fun s => U s ω) z then
              fPath (fun s => U s ω) (hc ω) z r.toNNReal else 0‖ ≤ n - 1 / ((k : ℝ) + 1)})) := by
    ext ω
    simp only [Set.mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_iInter]
    rw [lt_capExitTime_iff (hc ω) s.coe_nonneg]
    constructor
    · rintro ⟨hsl, hsm, hsT, hr⟩
      refine ⟨hsl, hsm, by simpa [hsl] using hsT, ?_⟩
      obtain ⟨k, hk⟩ := (forall_Icc_iff_exists_forall_dense (hc ω) hsl hDsub hDcl).1 hr
      refine ⟨k, fun r hr' => ?_⟩
      have hrI := hDsub hr'
      have hrl : r ∈ lifeSet (fun s => U s ω) z := mem_lifeSet_of_le hsl hrI.1 hrI.2
      simp only [Real.coe_toNNReal r hrI.1, hrl, ↓reduceIte]
      exact hk r hr'
    · rintro ⟨hsl, hsm, hsT, k, hk⟩
      refine ⟨hsl, hsm, by simpa [hsl] using hsT,
        (forall_Icc_iff_exists_forall_dense (hc ω) hsl hDsub hDcl).2 ⟨k, ?_⟩⟩
      intro r hr'
      have hrI := hDsub hr'
      have hrl : r ∈ lifeSet (fun s => U s ω) z := mem_lifeSet_of_le hsl hrI.1 hrI.2
      have := hk r hr'
      simp only [Real.coe_toNNReal r hrI.1, hrl, ↓reduceIte] at this
      exact this
  rw [key]
  refine (measurableSet_mem_lifeSet hc had s z).inter ((MeasurableSet.const _).inter
    (((measurable_clock hc had s z) measurableSet_Iio).inter ?_))
  refine MeasurableSet.iUnion fun k => MeasurableSet.biInter hDc fun r hr => ?_
  have hF := (measurable_centeredPath hc had r.toNNReal z).mono
    (ℱ.mono (show r.toNNReal ≤ s by rw [Real.toNNReal_le_iff_le_coe]; exact (hDsub hr).2)) le_rfl
  have hFn : Measurable[ℱ s] fun ω => ‖if (r.toNNReal : ℝ) ∈ lifeSet (fun s => U s ω) z then
      fPath (fun s => U s ω) (hc ω) z r.toNNReal else 0‖ := measurable_norm.comp hF
  exact (hFn measurableSet_Ici).inter (hFn measurableSet_Iic)

/-- `{capExitTime ≤ s}` is `ℱ s`-measurable. -/
theorem measurableSet_capExitTime_le (hc : ∀ ω, Continuous fun t => U t ω) (had : Adapted ℱ U)
    (z : ℂ) (n : ℕ) (m T : ℝ) (s : ℝ≥0) :
    MeasurableSet[ℱ s] {ω | capExitTime (fun r => U r ω) (hc ω) z n m T ≤ s} := by
  have : {ω | capExitTime (fun r => U r ω) (hc ω) z n m T ≤ s} =
      {ω | (s : ℝ) < capExitTime (fun r => U r ω) (hc ω) z n m T}ᶜ := by
    ext ω; simp
  rw [this]
  exact (measurableSet_lt_capExitTime hc had z n m T s).compl

/-- **The capped exit times are `ℱ`-stopping times.** -/
theorem isStoppingTime_capExitTime (hc : ∀ ω, Continuous fun t => U t ω) (had : Adapted ℱ U)
    (z : ℂ) (n : ℕ) (m T : ℝ) :
    IsStoppingTime ℱ fun ω =>
      (((capExitTime (fun r => U r ω) (hc ω) z n m T).toNNReal : ℝ≥0) : WithTop ℝ≥0) := by
  intro s
  have : {ω | (((capExitTime (fun r => U r ω) (hc ω) z n m T).toNNReal : ℝ≥0) : WithTop ℝ≥0)
      ≤ s} = {ω | capExitTime (fun r => U r ω) (hc ω) z n m T ≤ s} := by
    ext ω
    simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe]
    exact Real.toNNReal_le_iff_le_coe
  rw [this]
  exact measurableSet_capExitTime_le hc had z n m T s

end ComplexSLE.Internal.Polar

end
