/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Stochastic.ContinuousModification
public import ComplexSLE.Infrastructure.Stochastic.LocalMartingaleAlgebra
public import ComplexSLE.Infrastructure.Zipper.QuantumZipper.Proofs.ItoLite.OptionalStopping
public import Mathlib.MeasureTheory.Integral.Indicator

/-!
# A continuous local martingale with bracket tending to infinity oscillates

Source-independent stochastic calculus, external-free. This replaces the use of the
Dambis–Dubins–Schwarz theorem for the oscillation `liminf N = -∞` of a continuous local martingale
`N` whose bracket `A` (with `N² - A` a continuous local martingale) tends to infinity.

The proof is the classical gambler's-ruin argument. For `K, L > 0` let `ρ n` be the exit time of
`(-K, L)` capped at the time `n` (`intervalExitTime`, a stopping time, being the capped hitting
time of the closed set `exitRegion K L = {x ≤ -K} ∪ {L ≤ x}`).

* `IsContLocalMartingale.exists_localizing_seq`: at a bounded stopping time `ρ`, the localising
  sequence of a local martingale `M` produces stopping times `T k ≤ ρ`, eventually equal to `ρ`,
  with `E[M_{T k}] = E[M_0]` (optional stopping for the true martingales `M^{τ k}`,
  `Infrastructure.setIntegral_apply_stoppingTime_eq_min`).
* `IsContLocalMartingale.integral_apply_eq_of_dominated`: `E[N_ρ] = E[N_0] = 0` when `N` is bounded
  up to `ρ` (dominated convergence). Here `-K ≤ N ≤ L` up to the exit time.
* `lintegral_ofReal_sq_sub_le`: `E[A_ρ] ≤ C²` for `A = N² - Q` and `|N| ≤ C` up to `ρ` (Fatou along
  the localising sequence of `Q = N² - A`, using `E[Q_{T k}] = 0`).
* `measure_forall_lt_le`: `P(N > -K forever) ≤ K / (K + L)`. If `N_{ρ n} ≥ L` has probability at
  most `K / (K + L)` (from `E[N_{ρ n}] = 0`), and `N_{ρ n} ∈ (-K, L)` forces `ρ n = n`, where
  `A_{ρ n} = A_n`; Markov's inequality `P(A_{ρ n} ≥ c) ≤ C² / c` and `P(A_n < c) → 0`
  (because `A → ∞`) then give the bound.
* `ae_forall_exists_le_of_bracket_tendsto_atTop`: a.s. `∀ K, ∃ s, N_s ≤ -K`. The hypotheses of
  `IsContLocalMartingale` only provide almost sure path continuity; the hitting-time arguments need
  everywhere continuous paths, so the proof first passes to the everywhere continuous versions of
  `N` and `N² - A` for the completed filtration (`IsContLocalMartingale.exists_continuous_version`).

No external input is used.
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Infrastructure

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}

/-! ### The finite part of `ρ ∧ τ` -/

/-- The finite part of the stopping time `ρ ∧ τ`, where `ρ` is finite. -/
noncomputable def finMin (ρ : Ω → ℝ≥0) (τ : Ω → WithTop ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (min (ρ ω : WithTop ℝ≥0) (τ ω)).untopA

theorem coe_finMin (ρ : Ω → ℝ≥0) (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    (finMin ρ τ ω : WithTop ℝ≥0) = min (ρ ω : WithTop ℝ≥0) (τ ω) := by
  have hne : min (ρ ω : WithTop ℝ≥0) (τ ω) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  simp only [finMin]
  rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop]

theorem finMin_le (ρ : Ω → ℝ≥0) (τ : Ω → WithTop ℝ≥0) (ω : Ω) : finMin ρ τ ω ≤ ρ ω := by
  rw [← WithTop.coe_le_coe, coe_finMin]; exact min_le_left _ _

theorem finMin_eq_of_le {ρ : Ω → ℝ≥0} {τ : Ω → WithTop ℝ≥0} {ω : Ω} {n : ℝ≥0}
    (hρ : ρ ω ≤ n) (hτ : (n : WithTop ℝ≥0) ≤ τ ω) : finMin ρ τ ω = ρ ω := by
  rw [← WithTop.coe_inj, coe_finMin]
  exact min_eq_left ((WithTop.coe_le_coe.2 hρ).trans hτ)

theorem isStoppingTime_finMin {ρ : Ω → ℝ≥0} {τ : Ω → WithTop ℝ≥0}
    (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0)) (hτ : IsStoppingTime ℱ τ) :
    IsStoppingTime ℱ fun ω => (finMin ρ τ ω : WithTop ℝ≥0) := by
  have : (fun ω => (finMin ρ τ ω : WithTop ℝ≥0)) = fun ω => min (ρ ω : WithTop ℝ≥0) (τ ω) :=
    funext (coe_finMin ρ τ)
  rw [this]; exact hρ.min hτ

end ComplexSLE.Infrastructure

namespace ComplexSLE

open Infrastructure

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}

/-! ### Localisation at a bounded stopping time -/

section Localization

variable [IsFiniteMeasure P]

/-- **Localisation at a bounded stopping time.** Let `M` be a continuous local martingale with
everywhere continuous paths and `ρ ≤ n` a bounded stopping time. Then there are stopping times
`T k ≤ ρ`, equal to `ρ` eventually (a.s.), such that `M_{T k}` is integrable with
`E[M_{T k}] = E[M_0]`. -/
theorem IsContLocalMartingale.exists_localizing_seq {M : ℝ≥0 → Ω → ℝ}
    (hM : IsContLocalMartingale ℱ M P) (hMc : ∀ ω, Continuous fun t => M t ω)
    {ρ : Ω → ℝ≥0} (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0)) {n : ℝ≥0}
    (hρn : ∀ ω, ρ ω ≤ n) :
    ∃ T : ℕ → Ω → ℝ≥0, (∀ k ω, T k ω ≤ ρ ω) ∧
      (∀ k, IsStoppingTime ℱ fun ω => (T k ω : WithTop ℝ≥0)) ∧
      (∀ k, Integrable (fun ω => M (T k ω) ω) P) ∧
      (∀ k, ∫ ω, M (T k ω) ω ∂P = ∫ ω, M 0 ω ∂P) ∧
      (∀ᵐ ω ∂P, ∀ᶠ k in atTop, T k ω = ρ ω) := by
  obtain ⟨hprog, -, τ, hτ, hτev, hmart⟩ := hM
  refine ⟨fun k => finMin ρ (τ k), fun k ω => finMin_le ρ (τ k) ω,
    fun k => isStoppingTime_finMin hρ (hτ k), fun k => ?_, fun k => ?_, ?_⟩
  · exact integrable_apply_stoppingTime (hmart k) (continuous_stoppedProcess hMc (τ k)) hρ hρn
  · have h := setIntegral_apply_stoppingTime_eq_min (hmart k)
      (continuous_stoppedProcess hMc (τ k)) hρ hρn (s := 0) (A := univ)
      (@MeasurableSet.univ _ (ℱ 0))
    simp only [setIntegral_univ] at h
    have h0 : ∀ ω, min (0 : ℝ≥0) (ρ ω) = 0 := fun ω => min_eq_left bot_le
    simp only [h0] at h
    have h1 : ∀ ω, stoppedProcess M (τ k) 0 ω = M 0 ω := fun ω => by
      simp only [stoppedProcess]
      congr 1
      rw [WithTop.coe_zero, min_eq_left zero_le]
      rfl
    simp only [h1] at h
    exact h
  · filter_upwards [hτev] with ω hω
    filter_upwards [hω n] with k hk
    exact finMin_eq_of_le (hρn ω) hk

/-- **Optional stopping at a bounded stopping time** for a continuous local martingale that is
dominated by an integrable `Z` up to the stopping time: `E[M_ρ] = E[M_0]`. -/
theorem IsContLocalMartingale.integral_apply_eq_of_dominated {M : ℝ≥0 → Ω → ℝ}
    (hM : IsContLocalMartingale ℱ M P) (hMc : ∀ ω, Continuous fun t => M t ω)
    {ρ : Ω → ℝ≥0} (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0)) {n : ℝ≥0}
    (hρn : ∀ ω, ρ ω ≤ n) {Z : Ω → ℝ} (hZ : Integrable Z P)
    (hMZ : ∀ᵐ ω ∂P, ∀ u ≤ ρ ω, |M u ω| ≤ Z ω) :
    ∫ ω, M (ρ ω) ω ∂P = ∫ ω, M 0 ω ∂P := by
  obtain ⟨T, hTρ, -, hTint, hTeq, hTev⟩ := hM.exists_localizing_seq hMc hρ hρn
  have hlim : Tendsto (fun k => ∫ ω, M (T k ω) ω ∂P) atTop (𝓝 (∫ ω, M (ρ ω) ω ∂P)) := by
    refine tendsto_integral_of_dominated_convergence Z (fun k => (hTint k).aestronglyMeasurable)
      hZ (fun k => ?_) ?_
    · filter_upwards [hMZ] with ω hω
      rw [Real.norm_eq_abs]
      exact hω _ (hTρ k ω)
    · filter_upwards [hTev] with ω hω
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hω] with k hk
      rw [hk]
  simp only [hTeq] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

end Localization

end ComplexSLE

namespace ComplexSLE.Infrastructure

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}

section Bracket

variable [IsProbabilityMeasure P]

/-- The value of a progressive process at a finite stopping time is measurable. -/
theorem measurable_apply_stoppingTime {X : ℝ≥0 → Ω → ℝ} (hX : IsStronglyProgressive ℱ X)
    {ρ : Ω → ℝ≥0} (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0)) :
    Measurable fun ω => X (ρ ω) ω := by
  have h := (measurable_stoppedValue hX hρ).mono hρ.measurableSpace_le le_rfl
  rwa [stoppedValue_coe] at h

/-- **Second moment bound at a bounded stopping time.** Let `N` be progressive and `Q` a continuous
local martingale with everywhere continuous paths and `Q_0 = 0`, so that `A = N² - Q` is
a.s. nonnegative. If `|N_u| ≤ C` for `u ≤ ρ`, where `ρ ≤ n` is a stopping time, then
`E[A_ρ] ≤ C²` (Fatou along the localising sequence of `Q`). -/
theorem lintegral_ofReal_sq_sub_le {N Q : ℝ≥0 → Ω → ℝ} (hN : IsStronglyProgressive ℱ N)
    (hQ : IsContLocalMartingale ℱ Q P) (hQc : ∀ ω, Continuous fun t => Q t ω)
    (hQ0 : ∀ᵐ ω ∂P, Q 0 ω = 0) {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0)) {n : ℝ≥0} (hρn : ∀ ω, ρ ω ≤ n) {C : ℝ}
    (hNC : ∀ᵐ ω ∂P, ∀ u ≤ ρ ω, |N u ω| ≤ C) (hA : ∀ᵐ ω ∂P, ∀ u, 0 ≤ N u ω ^ 2 - Q u ω) :
    ∫⁻ ω, ENNReal.ofReal (N (ρ ω) ω ^ 2 - Q (ρ ω) ω) ∂P ≤ ENNReal.ofReal (C ^ 2) := by
  obtain ⟨T, hTρ, hTst, hTint, hTeq, hTev⟩ := hQ.exists_localizing_seq hQc hρ hρn
  have hNm : ∀ k, Measurable fun ω => N (T k ω) ω := fun k =>
    measurable_apply_stoppingTime hN (hTst k)
  have hQm : ∀ k, Measurable fun ω => Q (T k ω) ω := fun k =>
    measurable_apply_stoppingTime hQ.1 (hTst k)
  -- the bound at the localised times
  have hbound : ∀ k, ∫⁻ ω, ENNReal.ofReal (N (T k ω) ω ^ 2 - Q (T k ω) ω) ∂P ≤
      ENNReal.ofReal (C ^ 2) := by
    intro k
    have hN2int : Integrable (fun ω => N (T k ω) ω ^ 2) P := by
      refine Integrable.mono' (integrable_const (C ^ 2))
        ((hNm k).pow_const 2).aestronglyMeasurable ?_
      filter_upwards [hNC] with ω hω
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hω _ (hTρ k ω)) 2
    have hAint : Integrable (fun ω => N (T k ω) ω ^ 2 - Q (T k ω) ω) P := hN2int.sub (hTint k)
    have hAnn : 0 ≤ᵐ[P] fun ω => N (T k ω) ω ^ 2 - Q (T k ω) ω := by
      filter_upwards [hA] with ω hω using hω _
    rw [← ofReal_integral_eq_lintegral_ofReal hAint hAnn]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [integral_sub hN2int (hTint k), hTeq k, integral_eq_zero_of_ae hQ0, sub_zero]
    calc ∫ ω, N (T k ω) ω ^ 2 ∂P ≤ ∫ _ω, C ^ 2 ∂P := by
          refine integral_mono_ae hN2int (integrable_const _) ?_
          filter_upwards [hNC] with ω hω
          have := hω _ (hTρ k ω)
          calc N (T k ω) ω ^ 2 = |N (T k ω) ω| ^ 2 := (sq_abs _).symm
            _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ ≤ C ^ 2 := by
          rw [integral_const]
          simp
  calc ∫⁻ ω, ENNReal.ofReal (N (ρ ω) ω ^ 2 - Q (ρ ω) ω) ∂P
      = ∫⁻ ω, liminf (fun k => ENNReal.ofReal (N (T k ω) ω ^ 2 - Q (T k ω) ω)) atTop ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hTev] with ω hω
        symm
        refine Tendsto.liminf_eq (tendsto_const_nhds.congr' ?_)
        filter_upwards [hω] with k hk
        rw [hk]
    _ ≤ liminf (fun k => ∫⁻ ω, ENNReal.ofReal (N (T k ω) ω ^ 2 - Q (T k ω) ω) ∂P) atTop :=
        lintegral_liminf_le fun k =>
          ENNReal.measurable_ofReal.comp (((hNm k).pow_const 2).sub (hQm k))
    _ ≤ ENNReal.ofReal (C ^ 2) :=
        liminf_le_of_frequently_le' (Eventually.of_forall hbound).frequently

end Bracket

/-! ### Exit times of an interval -/

section ExitTime

variable {N Q : ℝ≥0 → Ω → ℝ}

/-- The complement `{x ≤ -K} ∪ {L ≤ x}` of the open interval `(-K, L)`. -/
def exitRegion (K L : ℝ) : Set ℝ := {x | x ≤ -K ∨ L ≤ x}

theorem isClosed_exitRegion (K L : ℝ) : IsClosed (exitRegion K L) :=
  (isClosed_le continuous_id continuous_const).union (isClosed_le continuous_const continuous_id)

/-- The capped exit time of `(-K, L)`: the first time `t ≤ n` with `N t ∉ (-K, L)`, and `n` if
there is none. -/
noncomputable def intervalExitTime (N : ℝ≥0 → Ω → ℝ) (K L : ℝ) (n : ℕ) : Ω → ℝ≥0 :=
  hittingBtwn N (exitRegion K L) 0 (n : ℝ≥0)

theorem isStoppingTime_intervalExitTime (hN : StronglyAdapted ℱ N)
    (hNc : ∀ ω, Continuous fun t => N t ω) (K L : ℝ) (n : ℕ) :
    IsStoppingTime ℱ fun ω => (intervalExitTime N K L n ω : WithTop ℝ≥0) :=
  QuantumZipper.ItoLite.isStoppingTime_hittingBtwn_of_isClosed (U := N)
    (fun t => (hN t).measurable) hNc (isClosed_exitRegion K L) (n : ℝ≥0)

theorem intervalExitTime_le (K L : ℝ) (n : ℕ) (ω : Ω) : intervalExitTime N K L n ω ≤ n :=
  hittingBtwn_le ω

/-- At the exit time, either the process has left `(-K, L)`, or the time cap was reached. -/
theorem apply_intervalExitTime_mem_or_eq (hNc : ∀ ω, Continuous fun t => N t ω) (K L : ℝ) (n : ℕ)
    (ω : Ω) :
    N (intervalExitTime N K L n ω) ω ∈ exitRegion K L ∨ intervalExitTime N K L n ω = n := by
  by_cases hex : ∃ j ∈ Set.Icc (0 : ℝ≥0) (n : ℝ≥0), N j ω ∈ exitRegion K L
  · left
    have heq : intervalExitTime N K L n ω =
        sInf (Set.Icc (0 : ℝ≥0) (n : ℝ≥0) ∩ {i | N i ω ∈ exitRegion K L}) := by
      simp only [intervalExitTime, hittingBtwn, hex, ↓reduceIte]
    have hSc : IsClosed (Set.Icc (0 : ℝ≥0) (n : ℝ≥0) ∩ {i | N i ω ∈ exitRegion K L}) :=
      isClosed_Icc.inter ((isClosed_exitRegion K L).preimage (hNc ω))
    have hSne : (Set.Icc (0 : ℝ≥0) (n : ℝ≥0) ∩ {i | N i ω ∈ exitRegion K L}).Nonempty := by
      obtain ⟨j, hj, hjK⟩ := hex
      exact ⟨j, hj, hjK⟩
    have hmem := hSc.csInf_mem hSne (OrderBot.bddBelow _)
    rw [← heq] at hmem
    exact hmem.2
  · right
    simp only [intervalExitTime, hittingBtwn, hex, ↓reduceIte]

/-- Up to and including the exit time of `(-K, L)`, a path started at `0` stays in `[-K, L]`. -/
theorem bounds_of_le_intervalExitTime (hNc : ∀ ω, Continuous fun t => N t ω) {K L : ℝ} (hK : 0 < K)
    (hL : 0 < L) (n : ℕ) {ω : Ω} (h0 : N 0 ω = 0) {u : ℝ≥0} (hu : u ≤ intervalExitTime N K L n ω) :
    -K ≤ N u ω ∧ N u ω ≤ L := by
  rcases eq_or_ne u 0 with rfl | hu0
  · rw [h0]; exact ⟨by linarith, hL.le⟩
  · have hupos : 0 < u := pos_iff_ne_zero.2 hu0
    have hsub : Iio u ⊆ {k : ℝ≥0 | -K ≤ N k ω ∧ N k ω ≤ L} := fun k hk => by
      have h := notMem_of_lt_hittingBtwn (u := N) (s := exitRegion K L) (n := 0)
        (m := (n : ℝ≥0)) (ω := ω) (k := k) (hk.trans_le hu) zero_le
      simp only [exitRegion, mem_ofPred_eq, not_or, not_le] at h
      exact ⟨h.1.le, h.2.le⟩
    have hcl : IsClosed {k : ℝ≥0 | -K ≤ N k ω ∧ N k ω ≤ L} :=
      (isClosed_le continuous_const (hNc ω)).inter (isClosed_le (hNc ω) continuous_const)
    have hmem : u ∈ closure (Iio u) := by
      rw [closure_Iio' (a := u) ⟨0, hupos⟩]; exact mem_Iic.2 le_rfl
    exact hcl.closure_subset_iff.2 hsub hmem

end ExitTime

/-! ### Gambler's ruin -/

section GamblersRuin

variable [IsProbabilityMeasure P] {N Q : ℝ≥0 → Ω → ℝ}

/-- The probability that `N` stays above `-K` forever is at most `K / (K + L)`: the core of the
gambler's-ruin argument, for a continuous local martingale `N` and a continuous local martingale
`Q` (both with everywhere continuous paths) such that `A = N² - Q` is nonnegative with
`A → ∞` a.s. and `N₀ = Q₀ = 0` a.s. -/
theorem measure_forall_lt_le (hN : IsContLocalMartingale ℱ N P)
    (hNc : ∀ ω, Continuous fun t => N t ω) (hQ : IsContLocalMartingale ℱ Q P)
    (hQc : ∀ ω, Continuous fun t => Q t ω) (hN0 : ∀ᵐ ω ∂P, N 0 ω = 0)
    (hQ0 : ∀ᵐ ω ∂P, Q 0 ω = 0) (hA : ∀ᵐ ω ∂P, ∀ u, 0 ≤ N u ω ^ 2 - Q u ω)
    (hAtop : ∀ᵐ ω ∂P, Tendsto (fun t => N t ω ^ 2 - Q t ω) atTop atTop) {K L : ℝ}
    (hK : 0 < K) (hL : 0 < L) :
    P {ω | ∀ s, -K < N s ω} ≤ ENNReal.ofReal (K / (K + L)) := by
  set C : ℝ := max K L with hCdef
  have hCpos : 0 < C := lt_max_of_lt_left hK
  set ρ : ℕ → Ω → ℝ≥0 := intervalExitTime N K L with hρdef
  have hρst : ∀ n, IsStoppingTime ℱ fun ω => (ρ n ω : WithTop ℝ≥0) := fun n =>
    isStoppingTime_intervalExitTime hN.1.stronglyAdapted hNc K L n
  have hbd : ∀ᵐ ω ∂P, ∀ n, ∀ u ≤ ρ n ω, -K ≤ N u ω ∧ N u ω ≤ L := by
    filter_upwards [hN0] with ω h0 n u hu
    exact bounds_of_le_intervalExitTime hNc hK hL n h0 hu
  have hbdC : ∀ᵐ ω ∂P, ∀ n, ∀ u ≤ ρ n ω, |N u ω| ≤ C := by
    filter_upwards [hbd] with ω h n u hu
    obtain ⟨h1, h2⟩ := h n u hu
    exact abs_le.2 ⟨by linarith [le_max_left K L], h2.trans (le_max_right K L)⟩
  -- (1) `E[N_{ρ n}] = 0`
  have hN0int : ∀ n, ∫ ω, N (ρ n ω) ω ∂P = 0 := fun n => by
    rw [hN.integral_apply_eq_of_dominated hNc (hρst n) (intervalExitTime_le K L n)
      (integrable_const C) (by filter_upwards [hbdC] with ω h using h n)]
    exact integral_eq_zero_of_ae hN0
  -- (2) `P(N_{ρ n} ≥ L) ≤ K / (K + L)`
  have hCn : ∀ n, P {ω | L ≤ N (ρ n ω) ω} ≤ ENNReal.ofReal (K / (K + L)) := by
    intro n
    have hmeas : Measurable fun ω => N (ρ n ω) ω := measurable_apply_stoppingTime hN.1 (hρst n)
    have hset : MeasurableSet {ω | L ≤ N (ρ n ω) ω} := measurableSet_le measurable_const hmeas
    have hint : Integrable (fun ω => N (ρ n ω) ω) P := by
      refine Integrable.mono' (integrable_const C) hmeas.aestronglyMeasurable ?_
      filter_upwards [hbdC] with ω h
      rw [Real.norm_eq_abs]
      exact h n _ le_rfl
    have hle : ∫ ω, ({ω | L ≤ N (ρ n ω) ω}.indicator (fun _ => K + L) ω - K) ∂P ≤
        ∫ ω, N (ρ n ω) ω ∂P := by
      refine integral_mono_ae ((integrable_const _).indicator hset |>.sub (integrable_const _))
        hint ?_
      filter_upwards [hbd] with ω h
      by_cases hω : ω ∈ {ω | L ≤ N (ρ n ω) ω}
      · rw [indicator_of_mem hω]
        have : L ≤ N (ρ n ω) ω := hω
        linarith
      · rw [indicator_of_notMem hω]
        have := (h n (ρ n ω) le_rfl).1
        linarith
    rw [hN0int n, integral_sub ((integrable_const _).indicator hset) (integrable_const _),
      integral_indicator_const _ hset] at hle
    simp only [integral_const, probReal_univ, smul_eq_mul] at hle
    have hreal : P.real {ω | L ≤ N (ρ n ω) ω} ≤ K / (K + L) := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    calc P {ω | L ≤ N (ρ n ω) ω} = ENNReal.ofReal (P.real {ω | L ≤ N (ρ n ω) ω}) :=
          (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
  -- (3) Markov: `P(A_{ρ n} ≥ c) ≤ C² / c`
  have hEc : ∀ n, ∀ c : ℝ, 0 < c →
      P {ω | c ≤ N (ρ n ω) ω ^ 2 - Q (ρ n ω) ω} ≤ ENNReal.ofReal (C ^ 2 / c) := by
    intro n c hc
    have hmeas : Measurable fun ω => N (ρ n ω) ω ^ 2 - Q (ρ n ω) ω :=
      ((measurable_apply_stoppingTime hN.1 (hρst n)).pow_const 2).sub
        (measurable_apply_stoppingTime hQ.1 (hρst n))
    have hint := lintegral_ofReal_sq_sub_le hN.1 hQ hQc hQ0 (hρst n) (intervalExitTime_le K L n)
      (C := C) (by filter_upwards [hbdC] with ω h using h n) hA
    have hmk := mul_meas_ge_le_lintegral₀ (μ := P)
      (f := fun ω => ENNReal.ofReal (N (ρ n ω) ω ^ 2 - Q (ρ n ω) ω))
      (ENNReal.measurable_ofReal.comp hmeas).aemeasurable (ENNReal.ofReal c)
    have hsub : {ω | c ≤ N (ρ n ω) ω ^ 2 - Q (ρ n ω) ω} ⊆
        {ω | ENNReal.ofReal c ≤ ENNReal.ofReal (N (ρ n ω) ω ^ 2 - Q (ρ n ω) ω)} :=
      fun ω hω => ENNReal.ofReal_le_ofReal hω
    rw [ENNReal.ofReal_div_of_pos hc]
    refine (measure_mono hsub).trans ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hc)) (Or.inl ENNReal.ofReal_ne_top),
      mul_comm]
    exact hmk.trans hint
  -- (4) `P(A_n < c) → 0`
  have hFn : ∀ c : ℝ, Tendsto (fun n : ℕ => P {ω | N n ω ^ 2 - Q n ω < c}) atTop (𝓝 0) := by
    intro c
    have hm : ∀ n : ℕ, MeasurableSet {ω | N n ω ^ 2 - Q n ω < c} := fun n => by
      have h1 : Measurable (N n) := (hN.1.stronglyAdapted n).measurable.mono (ℱ.le _) le_rfl
      have h2 : Measurable (Q n) := (hQ.1.stronglyAdapted n).measurable.mono (ℱ.le _) le_rfl
      exact measurableSet_lt ((h1.pow_const 2).sub h2) measurable_const
    have := tendsto_measure_of_ae_tendsto_indicator (μ := P) (A := ∅) atTop MeasurableSet.empty
      (As := fun n : ℕ => {ω | N n ω ^ 2 - Q n ω < c}) hm (B := univ) MeasurableSet.univ
      (measure_ne_top _ _) (Eventually.of_forall fun _ => subset_univ _) ?_
    · simpa using this
    · filter_upwards [hAtop] with ω hω
      filter_upwards [(hω.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop c] with n hn
      simp only [mem_empty_iff_false, iff_false, not_lt]
      exact hn
  -- (5) the union bound
  have hunion : ∀ n : ℕ, ∀ c : ℝ, 0 < c → P {ω | ∀ s, -K < N s ω} ≤
      ENNReal.ofReal (K / (K + L)) + ENNReal.ofReal (C ^ 2 / c) +
        P {ω | N n ω ^ 2 - Q n ω < c} := by
    intro n c hc
    have hsub : {ω | ∀ s, -K < N s ω} ⊆
        ({ω | L ≤ N (ρ n ω) ω} ∪ {ω | c ≤ N (ρ n ω) ω ^ 2 - Q (ρ n ω) ω}) ∪
          {ω | N n ω ^ 2 - Q n ω < c} := by
      intro ω hω
      by_cases h1 : L ≤ N (ρ n ω) ω
      · exact Or.inl (Or.inl h1)
      · have h2 : -K < N (ρ n ω) ω := hω _
        have hρn : ρ n ω = n := by
          rcases apply_intervalExitTime_mem_or_eq hNc K L n ω with h | h
          · exfalso
            rcases h with h | h
            · exact absurd h (not_le.2 h2)
            · exact h1 h
          · exact h
        by_cases h3 : c ≤ N (ρ n ω) ω ^ 2 - Q (ρ n ω) ω
        · exact Or.inl (Or.inr h3)
        · refine Or.inr ?_
          rw [hρn] at h3
          exact not_le.1 h3
    calc P {ω | ∀ s, -K < N s ω}
        ≤ P (({ω | L ≤ N (ρ n ω) ω} ∪ {ω | c ≤ N (ρ n ω) ω ^ 2 - Q (ρ n ω) ω}) ∪
          {ω | N n ω ^ 2 - Q n ω < c}) := measure_mono hsub
      _ ≤ P ({ω | L ≤ N (ρ n ω) ω} ∪ {ω | c ≤ N (ρ n ω) ω ^ 2 - Q (ρ n ω) ω}) +
          P {ω | N n ω ^ 2 - Q n ω < c} := measure_union_le _ _
      _ ≤ (P {ω | L ≤ N (ρ n ω) ω} + P {ω | c ≤ N (ρ n ω) ω ^ 2 - Q (ρ n ω) ω}) +
          P {ω | N n ω ^ 2 - Q n ω < c} := add_le_add_left (measure_union_le _ _) _
      _ ≤ _ := add_le_add_left (add_le_add (hCn n) (hEc n c hc)) _
  -- (6) let `n → ∞`, then `c → ∞`
  have hc : ∀ c : ℝ, 0 < c → P {ω | ∀ s, -K < N s ω} ≤
      ENNReal.ofReal (K / (K + L)) + ENNReal.ofReal (C ^ 2 / c) := by
    intro c hc
    have h := ge_of_tendsto' (tendsto_const_nhds.add (hFn c)) (fun n => hunion n c hc)
    rwa [add_zero] at h
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hεpos : (0 : ℝ) < ε := by exact_mod_cast hε
  have h := hc (C ^ 2 / ε) (by positivity)
  have heq : C ^ 2 / (C ^ 2 / (ε : ℝ)) = ε := by field_simp
  rwa [heq, ENNReal.ofReal_coe_nnreal] at h

/-- **Core of the oscillation theorem** (everywhere continuous version). -/
theorem ae_forall_exists_le_core (hN : IsContLocalMartingale ℱ N P)
    (hNc : ∀ ω, Continuous fun t => N t ω) (hQ : IsContLocalMartingale ℱ Q P)
    (hQc : ∀ ω, Continuous fun t => Q t ω) (hN0 : ∀ᵐ ω ∂P, N 0 ω = 0)
    (hQ0 : ∀ᵐ ω ∂P, Q 0 ω = 0) (hA : ∀ᵐ ω ∂P, ∀ u, 0 ≤ N u ω ^ 2 - Q u ω)
    (hAtop : ∀ᵐ ω ∂P, Tendsto (fun t => N t ω ^ 2 - Q t ω) atTop atTop) :
    ∀ᵐ ω ∂P, ∀ K : ℝ, ∃ s, N s ω ≤ -K := by
  have hK : ∀ k : ℕ, ∀ᵐ ω ∂P, ∃ s, N s ω ≤ -((k : ℝ) + 1) := by
    intro k
    have hK0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hle : ∀ j : ℕ, P {ω | ∀ s, -((k : ℝ) + 1) < N s ω} ≤
        ENNReal.ofReal (((k : ℝ) + 1) / (((k : ℝ) + 1) + ((j : ℝ) + 1))) := fun j =>
      measure_forall_lt_le hN hNc hQ hQc hN0 hQ0 hA hAtop hK0 (L := (j : ℝ) + 1) (by positivity)
    have hlim : Tendsto (fun j : ℕ => ENNReal.ofReal
        (((k : ℝ) + 1) / (((k : ℝ) + 1) + ((j : ℝ) + 1)))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun j : ℕ => ((k : ℝ) + 1) / (((k : ℝ) + 1) + ((j : ℝ) + 1))) atTop
          (𝓝 0) := by
        refine tendsto_const_nhds.div_atTop ?_
        exact tendsto_atTop_add_const_left _ _
          (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
      simpa using ENNReal.tendsto_ofReal h1
    have h0 : P {ω | ∀ s, -((k : ℝ) + 1) < N s ω} = 0 :=
      le_antisymm (ge_of_tendsto' hlim hle) bot_le
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω
    by_contra hcon
    push Not at hcon
    exact hω hcon
  filter_upwards [ae_all_iff.2 hK] with ω hω x
  obtain ⟨k, hk⟩ := exists_nat_ge x
  obtain ⟨s, hs⟩ := hω k
  exact ⟨s, by linarith⟩

end GamblersRuin

/-! ### The oscillation theorem -/

section Oscillation

variable [IsProbabilityMeasure P]

/-- **A continuous local martingale with bracket tending to infinity is unbounded below.**
Let `N` be a continuous local martingale with `N₀ = 0` and `A` a process, a.s. nondecreasing with
`A₀ = 0` and `A → ∞`, such that `N² - A` is a continuous local martingale. Then a.s.
`liminf N = -∞`, in the form `∀ K, ∃ s, N_s ≤ -K`. This is the consequence of
Dambis–Dubins–Schwarz needed for the Brownian-type oscillation of `N`, proved directly by a
gambler's-ruin argument (optional stopping at the exit time of `(-K, L)`) without the external
time-change representation by a Brownian motion. Only almost sure path continuity is assumed:
the proof passes to everywhere continuous versions for the completed filtration. -/
theorem ae_forall_exists_le_of_bracket_tendsto_atTop (ℱ : Filtration ℝ≥0 m)
    (N A : ℝ≥0 → Ω → ℝ) (hN : IsContLocalMartingale ℱ N P) (hN0 : ∀ᵐ ω ∂P, N 0 ω = 0)
    (hAm : ∀ᵐ ω ∂P, Monotone (fun t => A t ω) ∧ A 0 ω = 0)
    (hNA : IsContLocalMartingale ℱ (fun t ω => N t ω ^ 2 - A t ω) P)
    (hAtop : ∀ᵐ ω ∂P, Tendsto (fun t => A t ω) atTop atTop) :
    ∀ᵐ ω ∂P, ∀ K : ℝ, ∃ s, N s ω ≤ -K := by
  let 𝒢 : Filtration ℝ≥0 m :=
    { seq := fun t => ℱ t ⊔ MeasurableSpace.generateFrom
        {N : Set Ω | MeasurableSet[m] N ∧ P N = 0}
      mono' := fun _ _ hst => sup_le_sup_right (ℱ.mono hst) _
      le' := fun t => sup_le (ℱ.le t)
        (MeasurableSpace.generateFrom_le fun _ hN => hN.1) }
  obtain ⟨N', hN'N, hN'c, hN'⟩ := hN.exists_continuous_version 𝒢 (fun t => rfl)
  obtain ⟨Q', hQ'Q, hQ'c, hQ'⟩ := hNA.exists_continuous_version 𝒢 (fun t => rfl)
  have hA' : ∀ᵐ ω ∂P, ∀ t, N' t ω ^ 2 - Q' t ω = A t ω := by
    filter_upwards [hN'N, hQ'Q] with ω h1 h2 t
    rw [h1 t, h2 t]
    ring
  have hcore := ae_forall_exists_le_core hN' hN'c hQ' hQ'c
    (by filter_upwards [hN'N, hN0] with ω h1 h2; rw [h1 0, h2])
    (by
      filter_upwards [hQ'Q, hN0, hAm] with ω h1 h2 h3
      rw [h1 0, h2, h3.2]
      ring)
    (by
      filter_upwards [hA', hAm] with ω h1 h2 u
      rw [h1 u]
      have : A 0 ω ≤ A u ω := h2.1 (zero_le : (0 : ℝ≥0) ≤ u)
      rwa [h2.2] at this)
    (by
      filter_upwards [hA', hAtop] with ω h1 h2
      have : (fun t => N' t ω ^ 2 - Q' t ω) = fun t => A t ω := funext (h1 · )
      rwa [this])
  filter_upwards [hcore, hN'N] with ω h1 h2 K
  obtain ⟨s, hs⟩ := h1 K
  exact ⟨s, by rwa [← h2 s]⟩

end Oscillation

end ComplexSLE.Infrastructure

end
