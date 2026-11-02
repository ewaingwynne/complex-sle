/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Recurrence.HittingTime
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Lemma 2.16: recurrence of the argument process, the renewal argument

Abstract form of paper.tex:L1164-1190 (`step:rec-reduction-to-x`, `step:rec-renewal`,
`step:rec-tau-finite`), for a process `X : ℝ≥0 → Ω → ℝ` with everywhere-continuous paths,
adapted to `ℱ`. The target is the lattice `Z = x + πℤ` (`latticeSet x`; `X_t ∈ Z` iff
`e^{2iX_t} = e^{2ix}`, `mem_latticeSet_iff_exp`), and `C_ε = ⋃_n [x+nπ, x+nπ+π-ε]`
(`goodSet x ε`) is the set of points whose representative in `[x, x+π)` lies in `[x, x+π-ε]`.

`ae_frequently_mem_latticeSet`: a.s. `X` visits `Z` at arbitrarily large times, given

* `hstat` — the stationarity / non-atomicity input of L1187-1189: for every `η > 0` there is
  `ε > 0` with `P(X_t ∉ C_ε) ≤ η` for all `t` (the law of `e^{2iX_t}` is stationary with a density,
  so the mass of `(x+π-ε, x+π)` is uniformly small);
* `hren` — the Markov transport of claim (2.45) (`sle_angle_hit_unif`) to deterministic times:
  for every `ε > 0` there are `T, δ > 0` with
  `δ · P(A ∩ {X_s ∈ C_ε}) ≤ P(A ∩ {X_s ∈ C_ε} ∩ {∃ t ≤ T, X_{s+t} ∈ Z})` for all `s` and
  `A ∈ ℱ_s`. This is the conditional statement "given `ℱ_s`, on `{X_s ∈ C_ε}` the process hits
  `Z` within time `T` with probability `≥ δ`", which follows from (2.45), the `π`-periodicity of
  the coefficients and the Markov property at the fixed time `s` (paper.tex:L1181-1183; the paper
  uses the strong Markov property at the stopping times `τ_k^ε`, but windows at the deterministic
  times `kT` suffice, see below). It is an explicit hypothesis here; for `θ̂` it is discharged
  through the strong Markov restart (`Phases/ErgodicConstRec.lean`, `Phases/ErgodicConstStop.lean`).

The argument replaces the paper's `τ_k^ε` by the windows `[kT, (k+1)T]`: with
`N_k = {X_{kT} ∉ C_ε}` and `W_k = {∃ t ≤ T, X_{kT+t} ∈ Z}`, the events
`E_j = ⋂_{k₀ ≤ k ≤ k₀+j} (N_k ∪ W_kᶜ)` satisfy `P(E_{j+1}) ≤ (1-δ) P(E_j) + δ η`, so
`P(E_j) ≤ η + (1-δ)^j`, and the event "no visit to `Z` after time `k₀T`" is contained in every
`E_j`; hence it has probability `≤ η` for every `η`. This also absorbs `step:rec-tau-finite`
(L1185-1190). No external input is used.
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory Filter Set

namespace ComplexSLE.Recurrence

/-! ### The lattice `x + πℤ` and the good set `C_ε` -/

/-- `x + πℤ`, as the zero set of `sin(· - x)`. -/
def latticeSet (x : ℝ) : Set ℝ := {v | Real.sin (v - x) = 0}

theorem isClosed_latticeSet (x : ℝ) : IsClosed (latticeSet x) :=
  isClosed_eq (Real.continuous_sin.comp (continuous_id.sub continuous_const)) continuous_const

theorem mem_latticeSet_iff {x v : ℝ} : v ∈ latticeSet x ↔ ∃ n : ℤ, v = x + n * Real.pi := by
  simp only [latticeSet, mem_ofPred_eq, Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, by linarith⟩
  · rintro ⟨n, hn⟩; exact ⟨n, by linarith⟩

/-- `v ∈ x + πℤ` iff `e^{2iv} = e^{2ix}`. -/
theorem mem_latticeSet_iff_exp {x v : ℝ} :
    v ∈ latticeSet x ↔
      Complex.exp (2 * Complex.I * v) = Complex.exp (2 * Complex.I * x) := by
  rw [mem_latticeSet_iff, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hn]; push_cast; ring
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have := congrArg Complex.im hn
    simp [Complex.mul_im, Complex.mul_re] at this
    linarith

/-- `C_ε = ⋃_n [x + nπ, x + nπ + π - ε]`. -/
noncomputable def goodSet (x ε : ℝ) : Set ℝ :=
  ⋃ n : ℤ, Icc (x + n * Real.pi) (x + n * Real.pi + Real.pi - ε)

theorem measurableSet_goodSet (x ε : ℝ) : MeasurableSet (goodSet x ε) :=
  MeasurableSet.iUnion fun _ => measurableSet_Icc

/-- `C_ε` shrinks as `ε` grows. -/
theorem goodSet_subset_goodSet {x ε ε' : ℝ} (h : ε' ≤ ε) : goodSet x ε ⊆ goodSet x ε' := by
  intro v hv
  simp only [goodSet, mem_iUnion, mem_Icc] at hv ⊢
  obtain ⟨n, h1, h2⟩ := hv
  exact ⟨n, h1, by linarith⟩

/-! ### The renewal argument -/

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ≥0 m} {X : ℝ≥0 → Ω → ℝ} {x : ℝ}

omit [IsProbabilityMeasure P] in
/-- The window event `{∃ t ≤ T, X_{s+t} ∈ Z}` is `ℱ_{s+T}`-measurable. -/
theorem measurableSet_window (hX : StronglyAdapted ℱ X) (hXc : ∀ ω, Continuous fun t => X t ω)
    (s T : ℝ≥0) :
    MeasurableSet[ℱ (s + T)] {ω | ∃ t ≤ T, X (s + t) ω ∈ latticeSet x} := by
  have h := isStoppingTime_hittingAfter_of_isClosed hX hXc (isClosed_latticeSet x) s (s + T)
  convert h using 1
  ext ω
  simp only [mem_ofPred_eq]
  rw [hittingAfter_le_iff_exists (isClosed_latticeSet x) (hXc ω)]
  constructor
  · rintro ⟨t, ht, hmem⟩
    exact ⟨s + t, ⟨le_self_add, by gcongr⟩, hmem⟩
  · rintro ⟨j, ⟨hsj, hjT⟩, hmem⟩
    refine ⟨j - s, tsub_le_iff_left.2 hjT, ?_⟩
    rwa [add_tsub_cancel_of_le hsj]

/-- **Lemma 2.16, renewal form.** Given the stationarity input `hstat` and the Markov transport
`hren` of claim (2.45), a.s. `X` visits `x + πℤ` at arbitrarily large times. -/
theorem ae_frequently_mem_latticeSet (hX : StronglyAdapted ℱ X)
    (hXc : ∀ ω, Continuous fun t => X t ω)
    (hstat : ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ≥0, P.real {ω | X t ω ∉ goodSet x ε} ≤ η)
    (hren : ∀ ε : ℝ, 0 < ε → ∃ (T : ℝ≥0) (δ : ℝ), 0 < T ∧ 0 < δ ∧
      ∀ (s : ℝ≥0) (A : Set Ω), MeasurableSet[ℱ s] A →
        δ * P.real (A ∩ {ω | X s ω ∈ goodSet x ε}) ≤
          P.real (A ∩ {ω | X s ω ∈ goodSet x ε} ∩
            {ω | ∃ t ≤ T, X (s + t) ω ∈ latticeSet x})) :
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0, ∃ t : ℝ≥0, s ≤ t ∧ X t ω ∈ latticeSet x := by
  rw [ae_iff]
  set B := {ω | ¬ ∀ s : ℝ≥0, ∃ t : ℝ≥0, s ≤ t ∧ X t ω ∈ latticeSet x} with hB
  suffices h : ∀ η : ℝ, 0 < η → P.real B ≤ η by
    have h0 : P.real B ≤ 0 := le_of_forall_gt_imp_ge_of_dense fun c hc => h c hc
    exact (measureReal_eq_zero_iff (measure_ne_top P B)).1 (le_antisymm h0 measureReal_nonneg)
  intro η hη
  obtain ⟨ε, hε, hstatε⟩ := hstat η hη
  obtain ⟨T, δ₀, hT, hδ₀, hrenε⟩ := hren ε hε
  -- normalise `δ ≤ 1`
  set δ := min δ₀ 1 with hδdef
  have hδ : 0 < δ := lt_min hδ₀ one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hren' : ∀ (s : ℝ≥0) (A : Set Ω), MeasurableSet[ℱ s] A →
      δ * P.real (A ∩ {ω | X s ω ∈ goodSet x ε}) ≤
        P.real (A ∩ {ω | X s ω ∈ goodSet x ε} ∩ {ω | ∃ t ≤ T, X (s + t) ω ∈ latticeSet x}) :=
    fun s A hA => le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) measureReal_nonneg)
      (hrenε s A hA)
  -- windows and bad starts
  set W : ℕ → Set Ω := fun k => {ω | ∃ t ≤ T, X ((k : ℝ≥0) * T + t) ω ∈ latticeSet x} with hW
  set N : ℕ → Set Ω := fun k => {ω | X ((k : ℝ≥0) * T) ω ∉ goodSet x ε} with hN
  have hWmeas : ∀ k, MeasurableSet[ℱ (((k + 1 : ℕ) : ℝ≥0) * T)] (W k) := by
    intro k
    have := measurableSet_window (x := x) hX hXc ((k : ℝ≥0) * T) T
    rwa [show (k : ℝ≥0) * T + T = ((k + 1 : ℕ) : ℝ≥0) * T by push_cast; ring] at this
  have hNmeas : ∀ k : ℕ, MeasurableSet[ℱ ((k : ℝ≥0) * T)] (N k) := fun k =>
    ((hX _).measurable (measurableSet_goodSet x ε)).compl
  -- `B ⊆ ⋃ k₀, F k₀` with `F k₀ = ⋂ k ≥ k₀, (W k)ᶜ`
  set F : ℕ → Set Ω := fun k₀ => ⋂ k, ⋂ (_ : k₀ ≤ k), (W k)ᶜ with hF
  have hBF : B ⊆ ⋃ k₀, F k₀ := by
    intro ω hω
    simp only [hB, mem_ofPred_eq, not_forall, not_exists, not_and] at hω
    obtain ⟨s, hs⟩ := hω
    refine mem_iUnion.2 ⟨⌈(s : ℝ) / T⌉₊, ?_⟩
    simp only [hF, mem_iInter, mem_compl_iff, hW, mem_ofPred_eq, not_exists, not_and]
    intro k hk t ht hmem
    refine hs ((k : ℝ≥0) * T + t) ?_ hmem
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
    have h1 : (s : ℝ) ≤ ⌈(s : ℝ) / T⌉₊ * T := by
      rw [← div_le_iff₀ hTpos]; exact Nat.le_ceil _
    have h2 : (⌈(s : ℝ) / T⌉₊ : ℝ) * T ≤ (k : ℝ) * T := by
      gcongr
    have h3 : (s : ℝ) ≤ (((k : ℝ≥0) * T + t : ℝ≥0) : ℝ) := by
      push_cast
      linarith [NNReal.coe_nonneg t]
    exact_mod_cast h3
  have hFmono : Monotone F := fun k₀ k₁ hk ω hω => by
    simp only [hF, mem_iInter] at hω ⊢
    exact fun k hk1 => hω k (hk.trans hk1)
  -- the events of the recursion
  set E : ℕ → ℕ → Set Ω := fun k₀ j => ⋂ k, ⋂ (_ : k ∈ Icc k₀ (k₀ + j)), (N k ∪ (W k)ᶜ) with hE
  have hFE : ∀ k₀ j, F k₀ ⊆ E k₀ j := by
    intro k₀ j ω hω
    simp only [hF, mem_iInter] at hω
    simp only [hE, mem_iInter, mem_union, mem_compl_iff]
    exact fun k hk => Or.inr (hω k hk.1)
  have hEmeas : ∀ k₀ j, MeasurableSet[ℱ (((k₀ + j + 1 : ℕ) : ℝ≥0) * T)] (E k₀ j) := by
    intro k₀ j
    refine MeasurableSet.iInter fun k => MeasurableSet.iInter fun hk => ?_
    refine (ℱ.mono ?_ _ (hNmeas k)).union (ℱ.mono ?_ _ (hWmeas k)).compl
    · gcongr
      exact_mod_cast (hk.2.trans (Nat.le_succ _))
    · gcongr
      exact hk.2
  have hEsucc : ∀ k₀ j, E k₀ (j + 1) = E k₀ j ∩ (N (k₀ + j + 1) ∪ (W (k₀ + j + 1))ᶜ) := by
    intro k₀ j
    ext ω
    simp only [hE, mem_iInter, mem_inter_iff]
    constructor
    · intro h
      exact ⟨fun k hk => h k ⟨hk.1, hk.2.trans (Nat.le_succ _)⟩, h _ ⟨by omega, by omega⟩⟩
    · rintro ⟨h1, h2⟩ k hk
      rcases hk.2.lt_or_eq with hlt | heq
      · exact h1 k ⟨hk.1, by omega⟩
      · rw [show k = k₀ + j + 1 by omega]; exact h2
  -- one step of the recursion
  have hstep : ∀ k₀ j, P.real (E k₀ (j + 1)) ≤ (1 - δ) * P.real (E k₀ j) + δ * η := by
    intro k₀ j
    have hAmeas : MeasurableSet[ℱ (((k₀ + j + 1 : ℕ) : ℝ≥0) * T)] (E k₀ j) := hEmeas k₀ j
    set k := k₀ + j + 1 with hk
    set s : ℝ≥0 := (k : ℝ≥0) * T with hs
    set A := E k₀ j with hA
    set G := {ω | X s ω ∈ goodSet x ε} with hG
    have hGmeas : MeasurableSet G :=
      ((hX s).mono (ℱ.le s)).measurable (measurableSet_goodSet x ε)
    have hWmeas' : MeasurableSet (W k) := ℱ.le _ _ (hWmeas k)
    rw [hEsucc]
    have hsub : A ∩ (N k ∪ (W k)ᶜ) ⊆ (A ∩ Gᶜ) ∪ ((A ∩ G) \ W k) := by
      rintro ω ⟨hA', hNW⟩
      by_cases hG' : ω ∈ G
      · rcases hNW with hN' | hW'
        · exact absurd hG' hN'
        · exact Or.inr ⟨⟨hA', hG'⟩, hW'⟩
      · exact Or.inl ⟨hA', hG'⟩
    have hmain : δ * P.real (A ∩ G) ≤ P.real (A ∩ G ∩ W k) := hren' s A hAmeas
    have hsplit : P.real (A ∩ G ∩ W k) + P.real ((A ∩ G) \ W k) = P.real (A ∩ G) :=
      measureReal_inter_add_sdiff hWmeas'
    have hsplit2 : P.real (A ∩ G) + P.real (A \ G) = P.real A :=
      measureReal_inter_add_sdiff hGmeas
    rw [Set.sdiff_eq] at hsplit2
    have hNη : P.real (A ∩ Gᶜ) ≤ η :=
      le_trans (measureReal_mono inter_subset_right) (hstatε s)
    calc P.real (A ∩ (N k ∪ (W k)ᶜ))
        ≤ P.real ((A ∩ Gᶜ) ∪ ((A ∩ G) \ W k)) := measureReal_mono hsub
      _ ≤ P.real (A ∩ Gᶜ) + P.real ((A ∩ G) \ W k) := measureReal_union_le _ _
      _ ≤ P.real (A ∩ Gᶜ) + (1 - δ) * P.real (A ∩ G) := by linarith
      _ = (1 - δ) * P.real A + δ * P.real (A ∩ Gᶜ) := by rw [← hsplit2]; ring
      _ ≤ (1 - δ) * P.real A + δ * η := by gcongr
  -- iterate
  have hiter : ∀ k₀ j, P.real (E k₀ j) ≤ η + (1 - δ) ^ j := by
    intro k₀ j
    induction j with
    | zero =>
      simp only [pow_zero]
      linarith [measureReal_le_one (μ := P) (s := E k₀ 0)]
    | succ j ih =>
      have h1δ : 0 ≤ 1 - δ := by linarith
      calc P.real (E k₀ (j + 1)) ≤ (1 - δ) * P.real (E k₀ j) + δ * η := hstep k₀ j
        _ ≤ (1 - δ) * (η + (1 - δ) ^ j) + δ * η := by gcongr
        _ = η + (1 - δ) ^ (j + 1) := by ring
  -- hence `P (F k₀) ≤ η`
  have hFη : ∀ k₀, P.real (F k₀) ≤ η := by
    intro k₀
    refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (sub_pos.2 hc) (show 1 - δ < 1 by linarith)
    calc P.real (F k₀) ≤ P.real (E k₀ j) := measureReal_mono (hFE k₀ j)
      _ ≤ η + (1 - δ) ^ j := hiter k₀ j
      _ ≤ c := by linarith
  -- continuity from below
  have hU : P (⋃ k₀, F k₀) = ⨆ k₀, P (F k₀) := hFmono.measure_iUnion
  have hUle : P (⋃ k₀, F k₀) ≤ ENNReal.ofReal η := by
    rw [hU]
    refine iSup_le fun k₀ => ?_
    rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal (hFη k₀)
  calc P.real B ≤ P.real (⋃ k₀, F k₀) := measureReal_mono hBF
    _ ≤ η := by
      calc P.real (⋃ k₀, F k₀) = (P (⋃ k₀, F k₀)).toReal := rfl
        _ ≤ (ENNReal.ofReal η).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hUle
        _ = η := ENNReal.toReal_ofReal hη.le

end ComplexSLE.Recurrence

end
