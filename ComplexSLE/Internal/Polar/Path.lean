/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.CenteredLoewnerMap
public import ComplexSLE.Frozen.LoewnerMap_ExistsSolution
public import ComplexSLE.Internal.Hull.LocalExistence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Polar decomposition of SLE_Σ (§2.6): deterministic layer, the path `t ↦ f_t(z)`

## Design note (M6/S2, Lemma 2.11 in martingale form)

The polar layer is built in three strata.

1. **Deterministic stratum** (this file, `Argument.lean`, `Sigma.lean`): for a continuous driver
   `U` and a point `z`, the path `t ↦ f_t(z) = g_t(z) - U_t` is realised as a function `ℝ → ℂ`
   (`fPath`), meaningful on the *life set* `[0, T_z)` (`lifeSet`), via the solution supplied by the
   sealed anchor `loewnerMap_exists_solution`; off the life set it is junk and every statement is
   restricted to `lifeSet` explicitly. On the life set we prove: `f_t(z) ≠ 0`, continuity, the ODE
   `ġ = 2/f`, the deterministic `liminf_{t → T_z} |f_t(z)| = 0` when `T_z < ∞`
   (`step:endpt-liminf`, from `lt_absorbingTime_of_norm_sub_ge`), the annulus exit times
   (`exitTime`: the first time `|f| ≤ 1/n` or `|f| ≥ n` or `t = n`; they are finite, lie in the
   life set and exhaust it), the clock `A(t) = ∫₀ᵗ |f_s(z)|⁻² ds` of Definition 2.9 (`clock`,
   continuous, strictly increasing, `A(0) = 0`) and its inverse `σ_z` (`sigmaTime`, `Sigma.lean`),
   characterised on the honest domain `[0, sup A)`; and the continuous argument `θ_t(z)` of
   Definition 2.10 (`argPath`, `Argument.lean`), the unique continuous lift on `[0, T_z)` with
   `θ_0 ∈ [0, 2π)` (`step:arg-lift`), obtained from Mathlib's path lifting for the covering
   `Circle.exp`.
2. **Stochastic infrastructure** (`ComplexSLE/Infrastructure/Stochastic/`): source-independent
   facts about `IsContLocalMartingale` (algebra; stopping, obtained from the external E2c with
   `σ s = s ∧ ρ` and a filtration-transfer argument).
3. **Probabilistic stratum** (`DriverBridge.lean` and the martingale-form Lemma 2.11): for an
   `IsSLEDriverAdapted` driver, `Re U`, `Im U` are `ℱ`-martingales with brackets `a t`, `b t`,
   `c t`; Itô (E1) applied to `log|f|` and to a branch of `arg` between successive sector exit
   times gives (2.25)–(2.26) in original time, and the time change (E2c) by `σ_z` gives Lemma 2.11.
   Remark 2.12 (`σ_z` defined on all of `[0, ∞)` a.s.) follows from the `L²` bound of the stopped
   martingale part of `log|f|`: on `{∫₀^{T_z} |f|⁻² ≤ T}` the bracket is `≤ C T` while
   `|log|f|| → ∞` along the exit times, which has probability `0`. Lévy's characterisation
   (`step:polar-W-law`) is not needed in martingale form: the brackets are the content.

Conventions: times in the deterministic stratum are real (`t : ℝ`, the driver is read at
`t.toNNReal`, as in `IsLoewnerSolution`); the absorbing time is `absorbingTime U z : ℝ≥0∞`.
-/

public section

open scoped NNReal ENNReal
open Set

namespace ComplexSLE.Internal.Polar

variable {U : ℝ≥0 → ℂ}

/-! ### The life set `[0, T_z)` -/

/-- The life set `[0, T_z)` of the point `z`, as a set of real times. -/
@[expose] def lifeSet (U : ℝ≥0 → ℂ) (z : ℂ) : Set ℝ :=
  {t | 0 ≤ t ∧ ENNReal.ofReal t < absorbingTime U z}

theorem mem_lifeSet {z : ℂ} {t : ℝ} :
    t ∈ lifeSet U z ↔ 0 ≤ t ∧ ENNReal.ofReal t < absorbingTime U z := Iff.rfl

theorem lifeSet_subset_Ici (z : ℂ) : lifeSet U z ⊆ Ici 0 := fun _ ht => ht.1

theorem mem_lifeSet_of_le {z : ℂ} {s t : ℝ} (ht : t ∈ lifeSet U z) (hs : 0 ≤ s) (hst : s ≤ t) :
    s ∈ lifeSet U z :=
  ⟨hs, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hst) ht.2⟩

theorem Icc_subset_lifeSet {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) : Icc 0 t ⊆ lifeSet U z :=
  fun _ hs => mem_lifeSet_of_le ht hs.1 hs.2

theorem zero_mem_lifeSet_iff {z : ℂ} : (0 : ℝ) ∈ lifeSet U z ↔ 0 < absorbingTime U z := by
  simp [mem_lifeSet]

theorem coe_mem_lifeSet_iff {z : ℂ} {t : ℝ≥0} :
    (t : ℝ) ∈ lifeSet U z ↔ z ∈ (leftHull U t)ᶜ := by
  rw [mem_lifeSet, ENNReal.ofReal_coe_nnreal, mem_compl_iff, notMem_leftHull_iff]
  simp

/-- The life set has no largest element: every `t ∈ [0, T_z)` has a right neighbour in it. -/
theorem exists_gt_mem_lifeSet {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    ∃ t' ∈ lifeSet U z, t < t' := by
  obtain ⟨x, hx1, hx2⟩ := exists_between ht.2
  have hxtop : x ≠ ⊤ := ne_top_of_lt hx2
  refine ⟨x.toReal, ⟨ENNReal.toReal_nonneg, by rwa [ENNReal.ofReal_toReal hxtop]⟩, ?_⟩
  have := (ENNReal.ofReal_lt_iff_lt_toReal ht.1 hxtop).1 hx1
  exact this

/-- For `T_z < ∞`, the life set is `[0, T_z)`. -/
theorem lifeSet_eq_Ico {z : ℂ} (hT : absorbingTime U z ≠ ⊤) :
    lifeSet U z = Ico 0 (absorbingTime U z).toReal := by
  ext t
  simp only [mem_lifeSet, mem_Ico]
  constructor
  · rintro ⟨h0, hlt⟩
    exact ⟨h0, (ENNReal.ofReal_lt_iff_lt_toReal h0 hT).1 hlt⟩
  · rintro ⟨h0, hlt⟩
    exact ⟨h0, (ENNReal.ofReal_lt_iff_lt_toReal h0 hT).2 hlt⟩

/-- For `T_z = ∞`, the life set is `[0, ∞)`. -/
theorem lifeSet_eq_Ici {z : ℂ} (hT : absorbingTime U z = ⊤) : lifeSet U z = Ici 0 := by
  ext t
  simp [mem_lifeSet, hT]

/-! ### The paths `g_t(z)` and `f_t(z)` -/

/-- The solution path `t ↦ g_t(z)` of the Loewner problem from `z` on `[0, T_z)` (junk off the
life set). -/
@[expose] noncomputable def solPath (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) : ℝ → ℂ :=
  Classical.choose (loewnerMap_exists_solution U hU z)

theorem solPath_isLoewnerSolution (hU : Continuous U) (z : ℂ) :
    IsLoewnerSolution U z (absorbingTime U z) (solPath U hU z) :=
  (Classical.choose_spec (loewnerMap_exists_solution U hU z)).1

theorem loewnerMap_eq_solPath (hU : Continuous U) {z : ℂ} (t : ℝ≥0) (h : z ∈ (leftHull U t)ᶜ) :
    loewnerMap U hU t ⟨z, h⟩ = solPath U hU z t :=
  (Classical.choose_spec (loewnerMap_exists_solution U hU z)).2 t h

/-- The centered path `t ↦ f_t(z) = g_t(z) - U_t` (junk off the life set). -/
@[expose] noncomputable def fPath (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) (t : ℝ) : ℂ :=
  solPath U hU z t - U t.toNNReal

theorem centeredLoewnerMap_eq_fPath (hU : Continuous U) {z : ℂ} (t : ℝ≥0)
    (h : z ∈ (leftHull U t)ᶜ) : centeredLoewnerMap U hU t ⟨z, h⟩ = fPath U hU z t := by
  rw [centeredLoewnerMap, loewnerMap_eq_solPath, fPath, Real.toNNReal_coe]

theorem solPath_zero (hU : Continuous U) (z : ℂ) : solPath U hU z 0 = z :=
  (solPath_isLoewnerSolution hU z).1

theorem fPath_zero (hU : Continuous U) (z : ℂ) : fPath U hU z 0 = z - U 0 := by
  simp [fPath, solPath_zero]

theorem fPath_ne_zero (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    fPath U hU z t ≠ 0 :=
  sub_ne_zero.2 ((solPath_isLoewnerSolution hU z).2 t ht.1 ht.2).1

theorem norm_fPath_pos (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    0 < ‖fPath U hU z t‖ :=
  norm_pos_iff.2 (fPath_ne_zero hU ht)

theorem hasDerivWithinAt_solPath (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    HasDerivWithinAt (solPath U hU z) (2 / fPath U hU z t) (Ici 0) t :=
  ((solPath_isLoewnerSolution hU z).2 t ht.1 ht.2).2

theorem hasDerivAt_solPath (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z)
    (h0 : 0 < t) : HasDerivAt (solPath U hU z) (2 / fPath U hU z t) t :=
  (hasDerivWithinAt_solPath hU ht).hasDerivAt (Ici_mem_nhds h0)

theorem continuousOn_solPath (hU : Continuous U) (z : ℂ) :
    ContinuousOn (solPath U hU z) (lifeSet U z) := fun _ ht =>
  ((hasDerivWithinAt_solPath hU ht).continuousWithinAt).mono (lifeSet_subset_Ici z)

theorem continuousOn_fPath (hU : Continuous U) (z : ℂ) :
    ContinuousOn (fPath U hU z) (lifeSet U z) :=
  (continuousOn_solPath hU z).sub (hU.comp continuous_real_toNNReal).continuousOn

theorem continuousOn_norm_fPath (hU : Continuous U) (z : ℂ) :
    ContinuousOn (fun t => ‖fPath U hU z t‖) (lifeSet U z) :=
  (continuousOn_fPath hU z).norm

/-- The life set is a neighbourhood of each of its points within `[0, ∞)`. -/
theorem lifeSet_mem_nhdsWithin {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    lifeSet U z ∈ nhdsWithin t (Ici 0) := by
  obtain ⟨t', ht', hlt⟩ := exists_gt_mem_lifeSet ht
  have : Ico 0 t' ∈ nhdsWithin t (Ici 0) := by
    refine mem_nhdsWithin.2 ⟨Iio t', isOpen_Iio, hlt, ?_⟩
    rintro s ⟨hs1, hs2⟩
    exact ⟨hs2, hs1⟩
  exact Filter.mem_of_superset this fun s hs => mem_lifeSet_of_le ht' hs.1 hs.2.le

/-- Continuity of `f` within `[0, ∞)` at points of the life set. -/
theorem continuousWithinAt_fPath_Ici (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    ContinuousWithinAt (fPath U hU z) (Ici 0) t :=
  ((continuousOn_fPath hU z) t ht).mono_of_mem_nhdsWithin (lifeSet_mem_nhdsWithin ht)

/-- On a compact `[0, T] ⊆ [0, T_z)` the path `f` is bounded below in norm. -/
theorem exists_pos_le_norm_fPath (hU : Continuous U) {z : ℂ} {T : ℝ} (hT : T ∈ lifeSet U z) :
    ∃ δ > 0, ∀ t ∈ Icc 0 T, δ ≤ ‖fPath U hU z t‖ :=
  exists_pos_le_norm_Icc hT.1 ((continuousOn_fPath hU z).mono (Icc_subset_lifeSet hT))
    fun _ ht => fPath_ne_zero hU (Icc_subset_lifeSet hT ht)

/-- On a compact `[0, T] ⊆ [0, T_z)` the path `f` is bounded above in norm. -/
theorem exists_norm_fPath_le (hU : Continuous U) {z : ℂ} {T : ℝ} (hT : T ∈ lifeSet U z) :
    ∃ M, ∀ t ∈ Icc 0 T, ‖fPath U hU z t‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn
    ((continuousOn_norm_fPath hU z).mono (Icc_subset_lifeSet hT))).isBounded.bddAbove
  exact ⟨M, fun t ht => hM ⟨t, ht, rfl⟩⟩

/-! ### `step:endpt-liminf`: `liminf_{t → T_z} |f_t(z)| = 0` when `T_z < ∞` (deterministic) -/

/-- **Deterministic liminf.** If `T_z < ∞` then for every `η > 0` and every `a < T_z` there is a
time `s ∈ [a, T_z)` with `|f_s(z)| < η`: a solution staying at distance `≥ η` from the driver on a
final segment could be continued past `T_z` (`lt_absorbingTime_of_norm_sub_ge`). -/
theorem exists_norm_fPath_lt (hU : Continuous U) {z : ℂ} (hT : absorbingTime U z ≠ ⊤)
    {η : ℝ} (hη : 0 < η) {a : ℝ} (ha : a ∈ lifeSet U z) :
    ∃ s ∈ lifeSet U z, a ≤ s ∧ ‖fPath U hU z s‖ < η := by
  by_contra hcon
  push Not at hcon
  set τ := (absorbingTime U z).toReal with hτ
  have hτpos : 0 < τ := by
    rw [hτ, ENNReal.toReal_pos_iff]
    exact ⟨lt_of_le_of_lt bot_le ha.2, lt_top_iff_ne_top.2 hT⟩
  have haτ : a < τ := (ENNReal.ofReal_lt_iff_lt_toReal ha.1 hT).1 ha.2
  have hsol : IsLoewnerSolution U z (ENNReal.ofReal τ) (solPath U hU z) := by
    rw [hτ, ENNReal.ofReal_toReal hT]
    exact solPath_isLoewnerSolution hU z
  have h : ∀ s ∈ Ico a τ, η ≤ ‖solPath U hU z s - U s.toNNReal‖ := by
    intro s hs
    have hs' : s ∈ lifeSet U z := by
      rw [lifeSet_eq_Ico hT]
      exact ⟨ha.1.trans hs.1, hs.2⟩
    exact hcon s hs' hs.1
  have := lt_absorbingTime_of_norm_sub_ge hU hτpos hsol haτ hη h
  rw [hτ, ENNReal.ofReal_toReal hT] at this
  exact lt_irrefl _ this

/-! ### Annulus exit times -/

/-- The exit condition at level `n`: `|f_t(z)| ≤ 1/n`, or `|f_t(z)| ≥ n`, or `t ≥ n`. -/
@[expose] def ExitCond (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) (n : ℕ) (t : ℝ) : Prop :=
  ‖fPath U hU z t‖ ≤ 1 / n ∨ (n : ℝ) ≤ ‖fPath U hU z t‖ ∨ (n : ℝ) ≤ t

/-- The set of times in the life set satisfying the exit condition at level `n`. -/
@[expose] def exitSet (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) (n : ℕ) : Set ℝ :=
  {t | t ∈ lifeSet U z ∧ ExitCond U hU z n t}

/-- The exit time `τ_n`: the first time in `[0, T_z)` at which `|f| ≤ 1/n`, `|f| ≥ n` or `t = n`.
It is finite, lies in the life set, is at most `n`, and `τ_n → T_z`. -/
@[expose] noncomputable def exitTime (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) (n : ℕ) : ℝ :=
  sInf (exitSet U hU z n)

theorem exitSet_nonempty (hU : Continuous U) {z : ℂ} (hz : 0 < absorbingTime U z) (n : ℕ) :
    (exitSet U hU z n).Nonempty := by
  by_cases hn : ENNReal.ofReal n < absorbingTime U z
  · exact ⟨n, ⟨n.cast_nonneg, hn⟩, Or.inr (Or.inr le_rfl)⟩
  · have hT : absorbingTime U z ≠ ⊤ := by
      intro h; rw [h] at hn; exact hn (ENNReal.ofReal_lt_top)
    have h0 : (0 : ℝ) ∈ lifeSet U z := zero_mem_lifeSet_iff.2 hz
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · exact ⟨0, h0, Or.inr (Or.inl (by simp [hn0]))⟩
    have hη : (0 : ℝ) < 1 / n := by positivity
    obtain ⟨s, hs, -, hlt⟩ := exists_norm_fPath_lt hU hT hη h0
    exact ⟨s, hs, Or.inl hlt.le⟩

theorem exitSet_bddBelow (hU : Continuous U) (z : ℂ) (n : ℕ) : BddBelow (exitSet U hU z n) :=
  ⟨0, fun _ ht => ht.1.1⟩

theorem exitTime_nonneg (hU : Continuous U) {z : ℂ} (hz : 0 < absorbingTime U z) (n : ℕ) :
    0 ≤ exitTime U hU z n :=
  le_csInf (exitSet_nonempty hU hz n) fun _ ht => ht.1.1

theorem exitTime_le_of_mem (hU : Continuous U) {z : ℂ} {n : ℕ} {t : ℝ}
    (ht : t ∈ exitSet U hU z n) : exitTime U hU z n ≤ t :=
  csInf_le (exitSet_bddBelow hU z n) ht

/-- The exit time lies in the life set. -/
theorem exitTime_mem_lifeSet (hU : Continuous U) {z : ℂ} (hz : 0 < absorbingTime U z) (n : ℕ) :
    exitTime U hU z n ∈ lifeSet U z := by
  obtain ⟨t, ht⟩ := exitSet_nonempty hU hz n
  exact mem_lifeSet_of_le ht.1 (exitTime_nonneg hU hz n) (exitTime_le_of_mem hU ht)

theorem exitTime_le_nat (hU : Continuous U) {z : ℂ} (hz : 0 < absorbingTime U z) (n : ℕ) :
    exitTime U hU z n ≤ n := by
  by_cases hn : ENNReal.ofReal n < absorbingTime U z
  · exact exitTime_le_of_mem hU ⟨⟨n.cast_nonneg, hn⟩, Or.inr (Or.inr le_rfl)⟩
  · have := (exitTime_mem_lifeSet hU hz n).2
    by_contra hlt
    push Not at hlt
    exact hn (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hlt.le) this)

/-- Before the exit time the path stays in the open annulus `1/n < |f| < n`. -/
theorem norm_fPath_mem_Ioo_of_lt_exitTime (hU : Continuous U) {z : ℂ} {n : ℕ} {t : ℝ} (h0 : 0 ≤ t)
    (ht : t < exitTime U hU z n) :
    ‖fPath U hU z t‖ ∈ Ioo (1 / (n : ℝ)) n ∧ t < n := by
  have hz : 0 < absorbingTime U z := by
    by_contra hz
    push Not at hz
    have h0' : absorbingTime U z = 0 := le_antisymm hz bot_le
    have : exitSet U hU z n = ∅ := by
      ext s
      simp only [exitSet, mem_ofPred_eq, mem_lifeSet, h0', mem_empty_iff_false, iff_false]
      rintro ⟨⟨-, hlt⟩, -⟩
      exact not_lt_bot hlt
    simp [exitTime, this] at ht
    linarith
  have hmem : t ∈ lifeSet U z :=
    mem_lifeSet_of_le (exitTime_mem_lifeSet hU hz n) h0 ht.le
  have hnot : ¬ ExitCond U hU z n t := fun hc => not_lt.2 (exitTime_le_of_mem hU ⟨hmem, hc⟩) ht
  simp only [ExitCond, not_or, not_le] at hnot
  exact ⟨⟨hnot.1, hnot.2.1⟩, hnot.2.2⟩

/-- The exit condition is closed on the life set, so the infimum is attained. -/
theorem exitTime_mem_exitSet (hU : Continuous U) {z : ℂ} (hz : 0 < absorbingTime U z) (n : ℕ) :
    exitTime U hU z n ∈ exitSet U hU z n := by
  set τ := exitTime U hU z n with hτ
  have hτmem : τ ∈ lifeSet U z := exitTime_mem_lifeSet hU hz n
  refine ⟨hτmem, ?_⟩
  by_contra hc
  simp only [ExitCond, not_or, not_le] at hc
  obtain ⟨h1, h2, h3⟩ := hc
  -- the complement of the exit condition is open around `τ` within the life set
  have hcont : ContinuousWithinAt (fun t => ‖fPath U hU z t‖) (lifeSet U z) τ :=
    continuousOn_norm_fPath hU z τ hτmem
  have hev : ∀ᶠ t in nhdsWithin τ (lifeSet U z), ¬ ExitCond U hU z n t := by
    have e1 : ∀ᶠ t in nhdsWithin τ (lifeSet U z), 1 / (n : ℝ) < ‖fPath U hU z t‖ :=
      hcont.eventually (lt_mem_nhds h1)
    have e2 : ∀ᶠ t in nhdsWithin τ (lifeSet U z), ‖fPath U hU z t‖ < n :=
      hcont.eventually (gt_mem_nhds h2)
    have e3 : ∀ᶠ t : ℝ in nhdsWithin τ (lifeSet U z), t < n :=
      eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds h3)
    filter_upwards [e1, e2, e3] with t ht1 ht2 ht3
    simp only [ExitCond, not_or, not_le]
    exact ⟨ht1, ht2, ht3⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  -- there is a point of the exit set within `ε` above `τ`
  obtain ⟨s, hs, hsε⟩ := exists_lt_of_csInf_lt (exitSet_nonempty hU hz n)
    (show sInf (exitSet U hU z n) < τ + ε by
      change exitTime U hU z n < τ + ε; rw [← hτ]; linarith)
  have hτs : τ ≤ s := exitTime_le_of_mem hU hs
  have : s ∈ Metric.ball τ ε ∩ lifeSet U z :=
    ⟨by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith, hs.1⟩
  exact hball this hs.2

/-- Exit times are monotone in the level. -/
theorem exitTime_mono (hU : Continuous U) {z : ℂ} (hz : 0 < absorbingTime U z) {m n : ℕ}
    (hmn : m ≤ n) : exitTime U hU z m ≤ exitTime U hU z n := by
  obtain ⟨hmem, hc⟩ := exitTime_mem_exitSet hU hz n
  refine exitTime_le_of_mem hU ⟨hmem, ?_⟩
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · exact Or.inr (Or.inl (by simp [hm0]))
  have hm : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hn : (0 : ℝ) < n := lt_of_lt_of_le hm (by exact_mod_cast hmn)
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  rcases hc with h | h | h
  · exact Or.inl (h.trans (one_div_le_one_div_of_le hm hmn'))
  · exact Or.inr (Or.inl (hmn'.trans h))
  · exact Or.inr (Or.inr (hmn'.trans h))

/-- The exit times exhaust the life set: every `t < T_z` is before some `τ_n`. -/
theorem exists_lt_exitTime (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    ∃ n : ℕ, t < exitTime U hU z n := by
  have hz : 0 < absorbingTime U z := lt_of_le_of_lt bot_le ht.2
  obtain ⟨t', ht', hlt⟩ := exists_gt_mem_lifeSet ht
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_norm_fPath hU ht'
  obtain ⟨M, hM⟩ := exists_norm_fPath_le hU ht'
  obtain ⟨n, hn⟩ := exists_nat_gt (max (max t' M) (1 / δ))
  have hnt : t' < n := lt_of_le_of_lt (le_max_left _ _ |>.trans (le_max_left _ _)) hn
  have hnM : M < n := lt_of_le_of_lt (le_max_right _ _ |>.trans (le_max_left _ _)) hn
  have hnδ : 1 / δ < n := lt_of_le_of_lt (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hnδ
  refine ⟨n, lt_of_lt_of_le hlt (le_csInf (exitSet_nonempty hU hz n) ?_)⟩
  rintro s ⟨hs, hc⟩
  by_contra hlt'
  push Not at hlt'
  have hsI : s ∈ Icc 0 t' := ⟨hs.1, hlt'.le⟩
  rcases hc with h | h | h
  · have : 1 / (n : ℝ) < δ := by
      rw [div_lt_iff₀ hnpos]
      rw [div_lt_iff₀ hδ] at hnδ
      linarith
    linarith [hδle s hsI]
  · linarith [hM s hsI]
  · linarith

/-! ### The clock `A(t) = ∫₀ᵗ |f_s(z)|⁻² ds` of Definition 2.9 -/

/-- The integrand `|f_s(z)|⁻²` of the clock (junk off the life set). -/
@[expose] noncomputable def clockRate (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) (s : ℝ) : ℝ :=
  (‖fPath U hU z s‖ ^ 2)⁻¹

/-- The clock `A(t) = ∫₀ᵗ |f_s(z)|⁻² ds` (Definition 2.9, `eqn-defn-sigma`; meaningful for
`t ∈ [0, T_z)`). -/
@[expose] noncomputable def clock (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, clockRate U hU z s

theorem clockRate_pos (hU : Continuous U) {z : ℂ} {s : ℝ} (hs : s ∈ lifeSet U z) :
    0 < clockRate U hU z s := by
  unfold clockRate
  have := norm_fPath_pos hU hs
  positivity

theorem continuousOn_clockRate (hU : Continuous U) (z : ℂ) :
    ContinuousOn (clockRate U hU z) (lifeSet U z) := by
  unfold clockRate
  exact ((continuousOn_norm_fPath hU z).pow 2).inv₀ fun s hs =>
    pow_ne_zero 2 (norm_fPath_pos hU hs).ne'

theorem clock_zero (hU : Continuous U) (z : ℂ) : clock U hU z 0 = 0 := by
  simp [clock]

theorem intervalIntegrable_clockRate (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    IntervalIntegrable (clockRate U hU z) MeasureTheory.volume 0 t := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le ht.1]
  exact (continuousOn_clockRate hU z).mono (Icc_subset_lifeSet ht)

/-- The life set is measurable (it is `[0, T_z)` or `[0, ∞)`). -/
theorem lifeSet_measurableSet (U : ℝ≥0 → ℂ) (z : ℂ) : MeasurableSet (lifeSet U z) := by
  by_cases hT : absorbingTime U z = ⊤
  · rw [lifeSet_eq_Ici hT]; exact measurableSet_Ici
  · rw [lifeSet_eq_Ico hT]; exact measurableSet_Ico

/-- For `t > 0` in the life set, the life set is a (two-sided) neighbourhood of `t`. -/
theorem lifeSet_mem_nhds {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) (h0 : 0 < t) :
    lifeSet U z ∈ nhds t := by
  obtain ⟨t', ht', hlt⟩ := exists_gt_mem_lifeSet ht
  exact Filter.mem_of_superset (Ioo_mem_nhds h0 hlt) fun s hs =>
    mem_lifeSet_of_le ht' hs.1.le hs.2.le

/-- The clock is differentiable within `[0, ∞)` on the life set, with derivative `|f_t(z)|⁻²`. -/
theorem hasDerivWithinAt_clock (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    HasDerivWithinAt (clock U hU z) (clockRate U hU z t) (Ici 0) t := by
  have hint := intervalIntegrable_clockRate hU ht
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0
    have hcont : ContinuousWithinAt (clockRate U hU z) (Ioi 0) 0 :=
      ((continuousOn_clockRate hU z) 0 ht).mono_of_mem_nhdsWithin
        (nhdsWithin_mono (0 : ℝ) Ioi_subset_Ici_self (lifeSet_mem_nhdsWithin ht))
    have hmeas : StronglyMeasurableAtFilter (clockRate U hU z) (nhdsWithin 0 (Ioi 0))
        MeasureTheory.volume := by
      refine ⟨lifeSet U z, ?_, ?_⟩
      · exact nhdsWithin_mono (0 : ℝ) Ioi_subset_Ici_self (lifeSet_mem_nhdsWithin ht)
      · exact (continuousOn_clockRate hU z).aestronglyMeasurable (lifeSet_measurableSet U z)
    exact intervalIntegral.integral_hasDerivWithinAt_right hint hmeas hcont
  · have hnhds := lifeSet_mem_nhds ht h0
    have hcont : ContinuousAt (clockRate U hU z) t :=
      (continuousOn_clockRate hU z).continuousAt hnhds
    have hmeas : StronglyMeasurableAtFilter (clockRate U hU z) (nhds t) MeasureTheory.volume :=
      ⟨lifeSet U z, hnhds,
        (continuousOn_clockRate hU z).aestronglyMeasurable (lifeSet_measurableSet U z)⟩
    exact (intervalIntegral.integral_hasDerivAt_right hint hmeas hcont).hasDerivWithinAt

theorem continuousOn_clock (hU : Continuous U) (z : ℂ) :
    ContinuousOn (clock U hU z) (lifeSet U z) := fun _ ht =>
  ((hasDerivWithinAt_clock hU ht).continuousWithinAt).mono (lifeSet_subset_Ici z)

theorem continuousWithinAt_clock_Ici (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    ContinuousWithinAt (clock U hU z) (Ici 0) t :=
  (hasDerivWithinAt_clock hU ht).continuousWithinAt

/-- The clock is strictly increasing on the life set. -/
theorem clock_lt_clock (hU : Continuous U) {z : ℂ} {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (ht : t ∈ lifeSet U z) : clock U hU z s < clock U hU z t := by
  have hsmem : s ∈ lifeSet U z := mem_lifeSet_of_le ht hs hst.le
  have hint_s := intervalIntegrable_clockRate hU hsmem
  have hint_t := intervalIntegrable_clockRate hU ht
  have hint_st : IntervalIntegrable (clockRate U hU z) MeasureTheory.volume s t :=
    hint_s.symm.trans hint_t
  have hsplit : clock U hU z t = clock U hU z s + ∫ u in s..t, clockRate U hU z u := by
    unfold clock
    rw [intervalIntegral.integral_add_adjacent_intervals hint_s hint_st]
  rw [hsplit, lt_add_iff_pos_right]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on hint_st
    (fun u hu => clockRate_pos hU (mem_lifeSet_of_le ht (hs.trans hu.1.le) hu.2.le)) hst

theorem clock_nonneg (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    0 ≤ clock U hU z t := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h, clock_zero]
  · exact (clock_zero hU z ▸ clock_lt_clock hU le_rfl h ht).le

theorem clock_strictMonoOn (hU : Continuous U) (z : ℂ) :
    StrictMonoOn (clock U hU z) (lifeSet U z) := fun _ hs _ ht hst =>
  clock_lt_clock hU hs.1 hst ht

theorem clock_monotoneOn (hU : Continuous U) (z : ℂ) :
    MonotoneOn (clock U hU z) (lifeSet U z) :=
  (clock_strictMonoOn hU z).monotoneOn

end ComplexSLE.Internal.Polar

end
