/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# The maximal ergodic lemma

Let `T` be a measure preserving map of a measure space `(α, μ)` and `f` an integrable real function.
Write `S n x = birkhoffSum T f n x = ∑ k < n, f (T^[k] x)`.

* `maxFn T f n` is Garsia's maximal function `x ↦ max (S 0 x, …, S n x)`, defined by the recursion
  `maxFn T f 0 = 0`, `maxFn T f (n + 1) x = max 0 (f x + maxFn T f n (T x))`.
* `setIntegral_maxFn_pos_nonneg`: `∫_{maxFn T f n > 0} f ≥ 0` (Garsia's proof of the maximal
  ergodic lemma).
* `setIntegral_exists_birkhoffSum_pos_nonneg`: `∫_{∃ n, S n > 0} f ≥ 0`.
* `mul_measureReal_le_setIntegral`: for a measurable `T`-invariant set `E`,
  `c * μ(E ∩ {∃ n, n c < S n}) ≤ ∫_{E ∩ {∃ n, n c < S n}} f`.
-/

public section

open MeasureTheory Filter Set Function

namespace ComplexSLE.Infrastructure.Ergodic

variable {α : Type*} {T : α → α} {f : α → ℝ}

/-- Garsia's maximal function: `maxFn T f n x = max (S 0 x, …, S n x)` where
`S k x = ∑ j < k, f (T^[j] x)` (see `le_maxFn`, `exists_maxFn_eq`). -/
@[expose] def maxFn (T : α → α) (f : α → ℝ) : ℕ → α → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => max 0 (f x + maxFn T f n (T x))

theorem maxFn_zero (T : α → α) (f : α → ℝ) (x : α) : maxFn T f 0 x = 0 := rfl

theorem maxFn_succ (T : α → α) (f : α → ℝ) (n : ℕ) (x : α) :
    maxFn T f (n + 1) x = max 0 (f x + maxFn T f n (T x)) := rfl

theorem maxFn_nonneg (n : ℕ) (x : α) : 0 ≤ maxFn T f n x := by
  cases n with
  | zero => exact le_rfl
  | succ n => rw [maxFn_succ]; exact le_max_left _ _

theorem le_maxFn : ∀ (n k : ℕ) (x : α), k ≤ n → birkhoffSum T f k x ≤ maxFn T f n x := by
  intro n
  induction n with
  | zero =>
    intro k x hk
    obtain rfl : k = 0 := Nat.le_zero.1 hk
    simp [birkhoffSum_zero_apply, maxFn_zero]
  | succ n ih =>
    intro k x hk
    cases k with
    | zero => rw [birkhoffSum_zero_apply]; exact maxFn_nonneg _ _
    | succ j =>
      rw [birkhoffSum_succ_apply', maxFn_succ]
      refine le_trans ?_ (le_max_right _ _)
      exact add_le_add le_rfl (ih j (T x) (Nat.le_of_succ_le_succ hk))

theorem exists_maxFn_eq : ∀ (n : ℕ) (x : α), ∃ k ≤ n, maxFn T f n x = birkhoffSum T f k x := by
  intro n
  induction n with
  | zero => intro x; exact ⟨0, le_rfl, by simp [birkhoffSum_zero_apply, maxFn_zero]⟩
  | succ n ih =>
    intro x
    rw [maxFn_succ]
    rcases max_choice (0 : ℝ) (f x + maxFn T f n (T x)) with h | h
    · exact ⟨0, Nat.zero_le _, by rw [h, birkhoffSum_zero_apply]⟩
    · obtain ⟨j, hj, hj'⟩ := ih (T x)
      exact ⟨j + 1, Nat.succ_le_succ hj, by rw [h, hj', birkhoffSum_succ_apply']⟩

theorem maxFn_le_maxFn_succ : ∀ (n : ℕ) (x : α), maxFn T f n x ≤ maxFn T f (n + 1) x := by
  intro n
  induction n with
  | zero => intro x; rw [maxFn_zero]; exact maxFn_nonneg _ _
  | succ n ih =>
    intro x
    rw [maxFn_succ _ _ n, maxFn_succ _ _ (n + 1)]
    exact max_le_max le_rfl (add_le_add le_rfl (ih (T x)))

theorem maxFn_mono (x : α) : Monotone fun n => maxFn T f n x :=
  monotone_nat_of_le_succ fun n => maxFn_le_maxFn_succ n x

theorem maxFn_pos_iff (n : ℕ) (x : α) :
    0 < maxFn T f n x ↔ ∃ k ≤ n, 0 < birkhoffSum T f k x := by
  constructor
  · intro h
    obtain ⟨k, hk, hk'⟩ := exists_maxFn_eq (T := T) (f := f) n x
    exact ⟨k, hk, hk' ▸ h⟩
  · rintro ⟨k, hk, hk'⟩
    exact lt_of_lt_of_le hk' (le_maxFn n k x hk)

theorem iterate_mem_iff {E : Set α} (hEinv : ∀ x, T x ∈ E ↔ x ∈ E) :
    ∀ (k : ℕ) (x : α), T^[k] x ∈ E ↔ x ∈ E := by
  intro k
  induction k with
  | zero => intro x; exact Iff.rfl
  | succ k ih => intro x; rw [iterate_succ_apply, ih, hEinv]

variable [MeasurableSpace α] {μ : Measure α}

theorem measurable_birkhoffSum (hT : Measurable T) (hf : Measurable f) (n : ℕ) :
    Measurable (birkhoffSum T f n) :=
  Finset.measurable_sum _ fun k _ => hf.comp (hT.iterate k)

theorem measurable_maxFn (hT : Measurable T) (hf : Measurable f) :
    ∀ n : ℕ, Measurable (maxFn T f n)
  | 0 => measurable_const
  | n + 1 => by
    have h : Measurable fun x => max 0 (f x + maxFn T f n (T x)) :=
      measurable_const.max (hf.add ((measurable_maxFn hT hf n).comp hT))
    exact h

theorem integrable_maxFn (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    ∀ n : ℕ, Integrable (maxFn T f n) μ
  | 0 => integrable_zero _ _ _
  | n + 1 => by
    have h1 : Integrable (maxFn T f n ∘ T) μ :=
      hT.integrable_comp_of_integrable (integrable_maxFn hT hf n)
    have h2 := (hf.add h1).pos_part
    refine h2.congr (Eventually.of_forall fun x => ?_)
    simp [maxFn_succ, max_comm]

/-- Integrals of real functions are invariant under measure preserving maps. -/
theorem integral_comp_eq (hT : MeasurePreserving T μ μ) {g : α → ℝ}
    (hg : AEStronglyMeasurable g μ) : ∫ x, g (T x) ∂μ = ∫ x, g x ∂μ := by
  have hg' : AEStronglyMeasurable g (Measure.map T μ) := by rwa [hT.map_eq]
  rw [← integral_map hT.measurable.aemeasurable hg', hT.map_eq]

/-- Garsia's maximal ergodic lemma for the truncated maximal function:
`∫_{maxFn T f n > 0} f ≥ 0`. -/
theorem setIntegral_maxFn_pos_nonneg (hT : MeasurePreserving T μ μ) (hfm : Measurable f)
    (hf : Integrable f μ) (n : ℕ) : 0 ≤ ∫ x in {x | 0 < maxFn T f n x}, f x ∂μ := by
  cases n with
  | zero => simp [maxFn_zero]
  | succ n =>
    set M : α → ℝ := maxFn T f (n + 1) with hM
    have hMint : Integrable M μ := integrable_maxFn hT hf (n + 1)
    have hMTint : Integrable (M ∘ T) μ := hT.integrable_comp_of_integrable hMint
    have hMmeas : Measurable M := measurable_maxFn hT.measurable hfm (n + 1)
    have hs : MeasurableSet {x | 0 < M x} := measurableSet_lt measurable_const hMmeas
    have h1 : ∀ x ∈ {x | 0 < M x}, M x - (M ∘ T) x ≤ f x := by
      intro x hx
      have hx' : 0 < M x := hx
      have h2 : M x = f x + maxFn T f n (T x) := by
        rw [hM, maxFn_succ] at hx' ⊢
        exact max_eq_right (le_of_lt ((lt_max_iff.1 hx').resolve_left (lt_irrefl _)))
      have h3 : maxFn T f n (T x) ≤ (M ∘ T) x := maxFn_le_maxFn_succ n (T x)
      simp only [Function.comp_apply] at h3 ⊢
      linarith
    have h2 : ∫ x in {x | 0 < M x}, (M x - (M ∘ T) x) ∂μ ≤ ∫ x in {x | 0 < M x}, f x ∂μ :=
      setIntegral_mono_on (hMint.sub hMTint).integrableOn hf.integrableOn hs h1
    have h3 : ∫ x in {x | 0 < M x}, M x ∂μ = ∫ x, M x ∂μ := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
      exact le_antisymm (not_lt.1 hx) (maxFn_nonneg _ _)
    have h4 : ∫ x in {x | 0 < M x}, (M ∘ T) x ∂μ ≤ ∫ x, (M ∘ T) x ∂μ :=
      setIntegral_le_integral hMTint (Eventually.of_forall fun x => maxFn_nonneg _ _)
    have h5 : ∫ x, (M ∘ T) x ∂μ = ∫ x, M x ∂μ := integral_comp_eq hT hMint.aestronglyMeasurable
    have h6 : ∫ x in {x | 0 < M x}, (M x - (M ∘ T) x) ∂μ =
        ∫ x in {x | 0 < M x}, M x ∂μ - ∫ x in {x | 0 < M x}, (M ∘ T) x ∂μ :=
      integral_sub hMint.integrableOn hMTint.integrableOn
    linarith

/-- The maximal ergodic lemma: `∫_{∃ n, S n > 0} f ≥ 0`. -/
theorem setIntegral_exists_birkhoffSum_pos_nonneg (hT : MeasurePreserving T μ μ)
    (hfm : Measurable f) (hf : Integrable f μ) :
    0 ≤ ∫ x in {x | ∃ n, 0 < birkhoffSum T f n x}, f x ∂μ := by
  have hs : ∀ n, MeasurableSet {x | 0 < maxFn T f n x} := fun n =>
    measurableSet_lt measurable_const (measurable_maxFn hT.measurable hfm n)
  have hmono : Monotone fun n => {x | 0 < maxFn T f n x} := by
    refine monotone_nat_of_le_succ fun n x hx => ?_
    exact lt_of_lt_of_le hx (maxFn_le_maxFn_succ n x)
  have hU : (⋃ n, {x | 0 < maxFn T f n x}) = {x | ∃ n, 0 < birkhoffSum T f n x} := by
    ext x
    simp only [mem_iUnion, mem_ofPred_eq, maxFn_pos_iff]
    exact ⟨fun ⟨n, k, _, hk⟩ => ⟨k, hk⟩, fun ⟨k, hk⟩ => ⟨k, k, le_rfl, hk⟩⟩
  have hlim := tendsto_setIntegral_of_monotone hs hmono (f := f) (μ := μ) (hf.integrableOn)
  rw [hU] at hlim
  exact ge_of_tendsto' hlim fun n => setIntegral_maxFn_pos_nonneg hT hfm hf n

theorem measurableSet_exists_lt_birkhoffSum (hT : Measurable T) (hf : Measurable f) (c : ℝ) :
    MeasurableSet {x | ∃ n : ℕ, (n : ℝ) * c < birkhoffSum T f n x} := by
  have : {x | ∃ n : ℕ, (n : ℝ) * c < birkhoffSum T f n x} =
      ⋃ n : ℕ, {x | (n : ℝ) * c < birkhoffSum T f n x} := by ext x; simp
  rw [this]
  exact MeasurableSet.iUnion fun n =>
    measurableSet_lt measurable_const (measurable_birkhoffSum hT hf n)

/-- The maximal ergodic inequality on a measurable `T`-invariant set `E`:
`c μ(E ∩ {∃ n, n c < S n}) ≤ ∫_{E ∩ {∃ n, n c < S n}} f`. -/
theorem mul_measureReal_le_setIntegral [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hfm : Measurable f) (hf : Integrable f μ) {E : Set α} (hE : MeasurableSet E)
    (hEinv : ∀ x, T x ∈ E ↔ x ∈ E) (c : ℝ) :
    c * μ.real (E ∩ {x | ∃ n : ℕ, (n : ℝ) * c < birkhoffSum T f n x}) ≤
      ∫ x in E ∩ {x | ∃ n : ℕ, (n : ℝ) * c < birkhoffSum T f n x}, f x ∂μ := by
  set G : Set α := E ∩ {x | ∃ n : ℕ, (n : ℝ) * c < birkhoffSum T f n x} with hG
  have hGm : MeasurableSet G := hE.inter (measurableSet_exists_lt_birkhoffSum hT.measurable hfm c)
  set g : α → ℝ := E.indicator (fun x => f x - c) with hg
  have hgm : Measurable g := (hfm.sub measurable_const).indicator hE
  have hgi : Integrable g μ := (hf.sub (integrable_const c)).indicator hE
  have hS : ∀ (n : ℕ) (x : α), birkhoffSum T g n x =
      E.indicator (fun x => birkhoffSum T f n x - n * c) x := by
    intro n x
    by_cases hx : x ∈ E
    · have hk : ∀ k : ℕ, T^[k] x ∈ E := fun k => (iterate_mem_iff hEinv k x).2 hx
      simp only [indicator_of_mem hx, birkhoffSum, hg, indicator_of_mem (hk _)]
      rw [Finset.sum_sub_distrib]
      simp
    · have hk : ∀ k : ℕ, T^[k] x ∉ E := fun k h => hx ((iterate_mem_iff hEinv k x).1 h)
      simp [indicator_of_notMem hx, birkhoffSum, hg, indicator_of_notMem (hk _)]
  have hset : {x | ∃ n, 0 < birkhoffSum T g n x} = G := by
    ext x
    simp only [mem_ofPred_eq, hS, hG, mem_inter_iff]
    by_cases hx : x ∈ E
    · simp [hx]
    · simp [hx]
  have h0 := setIntegral_exists_birkhoffSum_pos_nonneg hT hgm hgi
  rw [hset] at h0
  have h1 : ∫ x in G, g x ∂μ = ∫ x in G, (f x - c) ∂μ := by
    refine setIntegral_congr_fun hGm fun x hx => ?_
    simp [hg, indicator_of_mem hx.1]
  rw [h1, integral_sub hf.integrableOn (integrable_const c).integrableOn, setIntegral_const] at h0
  simp only [smul_eq_mul] at h0
  linarith

/-- If every point of the invariant measurable set `E` has `n c < S n` for some `n`, then
`c μ(E) ≤ ∫_E f`. -/
theorem mul_measureReal_le_setIntegral_of_forall [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hfm : Measurable f) (hf : Integrable f μ) {E : Set α}
    (hE : MeasurableSet E) (hEinv : ∀ x, T x ∈ E ↔ x ∈ E) (c : ℝ)
    (hc : ∀ x ∈ E, ∃ n : ℕ, (n : ℝ) * c < birkhoffSum T f n x) :
    c * μ.real E ≤ ∫ x in E, f x ∂μ := by
  have hEq : E ∩ {x | ∃ n : ℕ, (n : ℝ) * c < birkhoffSum T f n x} = E :=
    inter_eq_left.2 fun x hx => hc x hx
  have := mul_measureReal_le_setIntegral hT hfm hf hE hEinv c
  rwa [hEq] at this

/-- If every point of the invariant measurable set `E` has `S n < n c` for some `n`, then
`∫_E f ≤ c μ(E)`. -/
theorem setIntegral_le_mul_measureReal_of_forall [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hfm : Measurable f) (hf : Integrable f μ) {E : Set α}
    (hE : MeasurableSet E) (hEinv : ∀ x, T x ∈ E ↔ x ∈ E) (c : ℝ)
    (hc : ∀ x ∈ E, ∃ n : ℕ, birkhoffSum T f n x < n * c) :
    ∫ x in E, f x ∂μ ≤ c * μ.real E := by
  have hc' : ∀ x ∈ E, ∃ n : ℕ, (n : ℝ) * (-c) < birkhoffSum T (-f) n x := by
    intro x hx
    obtain ⟨n, hn⟩ := hc x hx
    refine ⟨n, ?_⟩
    rw [birkhoffSum_neg_apply]
    linarith
  have := mul_measureReal_le_setIntegral_of_forall hT hfm.neg hf.neg hE hEinv (-c) hc'
  have h2 : ∫ x in E, (-f) x ∂μ = -∫ x in E, f x ∂μ := integral_neg _
  rw [h2] at this
  linarith

end ComplexSLE.Infrastructure.Ergodic

end
