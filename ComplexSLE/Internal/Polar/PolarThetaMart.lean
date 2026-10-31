/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.PolarThetaIto

/-!
# The martingale part of `θ` stopped at `τ_n` is a continuous local martingale (M6/S11;
`step:polar-real-imag`, imaginary part; `eqn-theta-t-op`, paper.tex:L916-L920)

For an adapted `SLE_Σ` driver (`0 < a`, `c² ≤ ab`) and `z ≠ 0`,

  `Θ^n_t = θ_{t ∧ τ_n}(z) - θ_0(z) - ∫₀^{t ∧ τ_n} µ(θ_s) |f_s(z)|⁻² ds`

is a continuous `ℱ`-local martingale with everywhere continuous paths
(`isContLocalMartingale_thetaMart`). The proof sums the sector increments of
`PolarThetaIto.lean`: `Θ^n_{· ∧ S_K} = ∑_{k < K} (Θ^n_{· ∧ S_{k+1}} - Θ^n_{· ∧ S_k})` is a continuous
local martingale for every `K`, and the stopping times `ρ_K = S_K` on `{S_K < τ_n}`, `ρ_K = ∞` on
`{S_K = τ_n}` satisfy `Θ^{ρ_K} = Θ^{S_K}` (as `Θ^n` is constant after `τ_n`) and `ρ_K = ∞`
eventually (`exists_sectorTime_eq_exitNN`), so `IsContLocalMartingale.of_stopped_seq` applies.
-/

public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal.Polar

section

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

variable (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) (n : ℕ)

/-! ### `Θ^n` in the notation of the source -/

theorem muFn_itoState_eq {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) {s : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ exitR hU z n ω) :
    muFn a b c (itoState hU z n s.toNNReal ω) =
      mu a b c (argPath (fun r => U r ω) (hU.cont ω) z s) /
        ‖fPath (fun r => U r ω) (hU.cont ω) z s‖ ^ 2 := by
  have h := thetaDrift_eq_mu hU z n hz (t := s.toNNReal) (by rwa [Real.coe_toNNReal _ hs0])
  have h1 : beforeExit hU z n s.toNNReal ω = 1 := by
    simp [beforeExit, (le_exitNN_iff hU z n).2 (by rwa [Real.coe_toNNReal _ hs0] : _ ≤ _)]
  rw [thetaDrift, h1, one_mul, Real.coe_toNNReal _ hs0] at h
  exact h

/-- The drift integral of `Θ^n` in the form of the source: on `{T_z > 0}`,
`∫₀ᵗ 1_{s ≤ τ_n} µ̂(f_s) ds = ∫₀^{t ∧ τ_n} µ(θ_s) |f_s|⁻² ds`. -/
theorem pathIntegral_thetaDrift_eq_source {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z)
    (t : ℝ≥0) :
    pathIntegral (thetaDrift hU z n) t ω =
      ∫ s in (0 : ℝ)..(min (t : ℝ) (exitR hU z n ω)), mu a b c (argPath (fun r => U r ω)
        (hU.cont ω) z s) / ‖fPath (fun r => U r ω) (hU.cont ω) z s‖ ^ 2 := by
  rw [pathIntegral_thetaDrift]
  simp only [pathIntegral, NNReal.coe_min, coe_exitNN]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le (le_min t.coe_nonneg (exitR_nonneg hU z n ω))] at hs
  exact muFn_itoState_eq hU z n hz hs.1 (hs.2.trans (min_le_right _ _))

/-- **`Θ^n` in the notation of the source** (`eqn-theta-t-op`): on `{T_z > 0}`,
`Θ^n_t = θ_{t ∧ τ_n} - θ_0 - ∫₀^{t ∧ τ_n} µ(θ_s) |f_s|⁻² ds`. -/
theorem thetaMart_eq_source {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) (t : ℝ≥0) :
    thetaMart hU z n t ω =
      argPath (fun r => U r ω) (hU.cont ω) z (min (t : ℝ) (exitR hU z n ω)) -
        argPath (fun r => U r ω) (hU.cont ω) z 0 -
        ∫ s in (0 : ℝ)..(min (t : ℝ) (exitR hU z n ω)), mu a b c (argPath (fun r => U r ω)
          (hU.cont ω) z s) / ‖fPath (fun r => U r ω) (hU.cont ω) z s‖ ^ 2 := by
  rw [thetaMart, argStopped_eq hU z n hz, argStopped_eq hU z n hz,
    pathIntegral_thetaDrift_eq_source hU z n hz, NNReal.coe_zero,
    min_eq_left (exitR_nonneg hU z n ω)]

/-! ### Summation over the sectors -/

/-- Telescoping: `Θ^n_{t ∧ S_K} = ∑_{k < K} (Θ^n_{t ∧ S_{k+1}} - Θ^n_{t ∧ S_k})`. -/
theorem thetaMart_min_sectorTime_eq_sum (K : ℕ) (t : ℝ≥0) (ω : Ω) :
    thetaMart hU z n (min t (sectorTime hU z n K ω)) ω =
      ∑ k ∈ Finset.range K, (thetaMart hU z n (min t (sectorTime hU z n (k + 1) ω)) ω -
        thetaMart hU z n (min t (sectorTime hU z n k ω)) ω) := by
  rw [Finset.sum_range_sub (fun k => thetaMart hU z n (min t (sectorTime hU z n k ω)) ω) K]
  simp [sectorTime_zero, thetaMart_zero, min_eq_right (zero_le : (0 : ℝ≥0) ≤ t)]

variable [IsProbabilityMeasure P]

/-- `Θ^n` stopped at `S_K` is a continuous local martingale (sum of the sector increments). -/
theorem isContLocalMartingale_thetaMart_min_sectorTime (ha : 0 < a) (hc : c ^ 2 ≤ a * b)
    (hz : z ≠ 0) (K : ℕ) :
    IsContLocalMartingale ℱ (fun t ω => thetaMart hU z n (min t (sectorTime hU z n K ω)) ω) P := by
  induction K with
  | zero =>
    have : (fun t ω => thetaMart hU z n (min t (sectorTime hU z n 0 ω)) ω) =
        fun _ _ => (0 : ℝ) := by
      funext t ω
      simp [sectorTime_zero, thetaMart_zero, min_eq_right (zero_le : (0 : ℝ≥0) ≤ t)]
    rw [this]; exact isContLocalMartingale_zero
  | succ K ih =>
    have hc1 : ∀ ω, Continuous fun t => thetaMart hU z n (min t (sectorTime hU z n K ω)) ω :=
      fun ω => (continuous_thetaMart hU z n ω).comp (continuous_id.min continuous_const)
    have hc2 : ∀ ω, Continuous fun t => thetaMart hU z n (min t (sectorTime hU z n (K + 1) ω)) ω -
        thetaMart hU z n (min t (sectorTime hU z n K ω)) ω := fun ω =>
      ((continuous_thetaMart hU z n ω).comp (continuous_id.min continuous_const)).sub (hc1 ω)
    have h := ih.add (isContLocalMartingale_sectorIncrement hU z n K ha hc hz) hc1 hc2
    refine h.congr_fun' fun t ω => ?_
    simp only [Pi.add_apply]; ring

/-! ### Localisation -/

/-- The localising times `ρ_K`: `S_K` on `{S_K < τ_n}`, `∞` on `{S_K = τ_n}`. -/
@[expose] noncomputable def sectorLocalizer (K : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  if sectorTime hU z n K ω < exitNN hU z n ω then (sectorTime hU z n K ω : WithTop ℝ≥0) else ⊤

omit [IsProbabilityMeasure P] in
theorem isStoppingTime_sectorLocalizer (K : ℕ) :
    IsStoppingTime ℱ (sectorLocalizer hU z n K) := by
  intro u
  have hlt : MeasurableSet[(isStoppingTime_sectorTime hU z n K).measurableSpace]
      {ω | sectorTime hU z n K ω < exitNN hU z n ω} := by
    have h := IsStoppingTime.measurableSet_stopping_time_le (isStoppingTime_exitNN hU z n)
      (isStoppingTime_sectorTime hU z n K)
    have e : {ω | sectorTime hU z n K ω < exitNN hU z n ω} =
        {ω | (exitNN hU z n ω : WithTop ℝ≥0) ≤ (sectorTime hU z n K ω : WithTop ℝ≥0)}ᶜ := by
      ext ω
      simp only [mem_ofPred_eq, mem_compl_iff]
      constructor
      · intro h' h''
        exact absurd (WithTop.coe_le_coe.1 h'') (not_le.2 h')
      · intro h'
        exact lt_of_not_ge fun h'' => h' (WithTop.coe_le_coe.2 h'')
    rw [e]; exact h.compl
  have e : {ω | sectorLocalizer hU z n K ω ≤ u} =
      {ω | sectorTime hU z n K ω < exitNN hU z n ω} ∩
        {ω | (sectorTime hU z n K ω : WithTop ℝ≥0) ≤ u} := by
    ext ω
    simp only [sectorLocalizer, mem_ofPred_eq, mem_inter_iff]
    split_ifs with h
    · simp [h]
    · simp only [h, false_and, iff_false]
      exact WithTop.not_top_le_coe u
  rw [e]
  exact (((isStoppingTime_sectorTime hU z n K).measurableSet _).1 hlt).2 u

omit [IsProbabilityMeasure P] in
/-- `Θ^n` stopped at `ρ_K` is `Θ^n` stopped at `S_K` (`Θ^n` is constant after `τ_n`). -/
theorem stoppedProcess_thetaMart_sectorLocalizer (K : ℕ) :
    stoppedProcess (thetaMart hU z n) (sectorLocalizer hU z n K) =
      fun t ω => thetaMart hU z n (min t (sectorTime hU z n K ω)) ω := by
  funext t ω
  simp only [stoppedProcess, sectorLocalizer]
  split_ifs with h
  · rw [← WithTop.coe_min, untopA_coe']
  · rw [min_eq_left le_top, untopA_coe']
    have hK : sectorTime hU z n K ω = exitNN hU z n ω :=
      le_antisymm (sectorTime_le_exitNN hU z n K ω) (not_lt.1 h)
    rw [hK]
    by_cases ht : exitNN hU z n ω ≤ t
    · rw [min_eq_right ht]; exact thetaMart_eq_of_le hU z n ht le_rfl
    · rw [min_eq_left (le_of_lt (lt_of_not_ge ht))]

omit [IsProbabilityMeasure P] in
theorem eventually_le_sectorLocalizer (ω : Ω) (t : ℝ≥0) :
    ∀ᶠ K in atTop, (t : WithTop ℝ≥0) ≤ sectorLocalizer hU z n K ω := by
  obtain ⟨K₀, hK₀⟩ := exists_sectorTime_eq_exitNN hU z n ω
  filter_upwards [eventually_ge_atTop K₀] with K hK
  simp only [sectorLocalizer, hK₀ K hK, lt_self_iff_false, ↓reduceIte]
  exact le_top

/-- **`Θ^n` is a continuous local martingale** (`step:polar-real-imag`, imaginary part,
paper.tex:L916-L920 in martingale form). For `0 < a`, `c² ≤ ab`, `z ≠ 0`:
`Θ^n_t = θ_{t ∧ τ_n}(z) - θ_0(z) - ∫₀^{t ∧ τ_n} µ(θ_s) |f_s(z)|⁻² ds` is a continuous
`ℱ`-local martingale (with everywhere continuous paths, `continuous_thetaMart`). -/
theorem isContLocalMartingale_thetaMart (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) :
    IsContLocalMartingale ℱ (thetaMart hU z n) P := by
  refine IsContLocalMartingale.of_stopped_seq (isStronglyProgressive_thetaMart hU z n)
    (ae_of_all _ (continuous_thetaMart hU z n)) (isStoppingTime_sectorLocalizer hU z n)
    (ae_of_all _ fun ω t => eventually_le_sectorLocalizer hU z n ω t) fun K => ?_
  rw [stoppedProcess_thetaMart_sectorLocalizer]
  exact isContLocalMartingale_thetaMart_min_sectorTime hU z n ha hc hz K

end

end ComplexSLE.Internal.Polar

end
