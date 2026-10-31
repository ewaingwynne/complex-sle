/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.PolarThetaBrSector

/-!
# The bracket of `Θ^n` and its cross bracket with `N^n` (M6/S13; `step:polar-real-imag`,
brackets of `eqn-theta-t-op` and `eqn-abs-zt-op`, paper.tex:L911-L920)

For an adapted `SLE_Σ` driver (`0 < a`, `c² ≤ ab`) and `z ≠ 0`, with
`Θ^n_t = θ_{t ∧ τ_n} - θ_0 - ∫₀^{t ∧ τ_n} µ(θ_s)|f_s|⁻² ds` (`thetaMart`) and
`N^n_t = log|f_{t ∧ τ_n}| - log|f_0| - ∫₀^{t ∧ τ_n} ν(θ_s)|f_s|⁻² ds` (`logMart`):

* `(Θ^n_t)² - ∫₀^{t ∧ τ_n} (a sin² θ_s + b cos² θ_s - 2c sin θ_s cos θ_s)|f_s|⁻² ds` is a continuous
  `ℱ`-local martingale (`isContLocalMartingale_thetaMart_sq_sub`);
* `Θ^n_t N^n_t - ∫₀^{t ∧ τ_n} ((b - a) sin θ_s cos θ_s + c (cos² θ_s - sin² θ_s))|f_s|⁻² ds` is a
  continuous `ℱ`-local martingale (`isContLocalMartingale_thetaMart_mul_logMart_sub`).

The proofs sum the sector results of `PolarThetaBrSector.lean` by induction on the sector index:
with `Θ^K = Θ^n_{· ∧ S_K}`, `(Θ^{K+1})² = (Θ^K)² + Δ_K² + 2 Θ^n_{S_K} Δ_K`, where the last term is
an
`ℱ_{S_K}`-measurable multiplier times a post-`S_K` increment of the stopped local martingale
`Θ^n_{· ∧ S_{K+1}}` (`IsContLocalMartingale.mul_sub_min'`), and similarly for the product; then the
localisation along `ρ_K = S_K` on `{S_K < τ_n}` of `PolarThetaMart.lean`.
-/

public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal.Polar

section

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-! ### A progressive process evaluated at a finite stopping time -/

/-- For a progressive `N` and a finite stopping time `ρ`, the cut-off `N_ρ 1_{ρ ≤ u}` is
`ℱ_u`-measurable (so `N_ρ` is `ℱ_ρ`-measurable in the sense of
`IsContLocalMartingale.mul_sub_min'`). -/
theorem measurable_ite_le_apply {N : ℝ≥0 → Ω → ℝ} (hN : IsStronglyProgressive ℱ N)
    {ρ : Ω → ℝ≥0} (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0)) (u : ℝ≥0) :
    Measurable[ℱ u] fun ω => if ρ ω ≤ u then N (ρ ω) ω else 0 := by
  have h1 : StronglyMeasurable[ℱ u] fun ω => N (min u (ρ ω)) ω := by
    have h := hN.stronglyAdapted_stoppedProcess hρ u
    have e : stoppedProcess N (fun ω => (ρ ω : WithTop ℝ≥0)) u = fun ω => N (min u (ρ ω)) ω :=
      funext fun ω => stoppedProcess_coe_min N ρ u ω
    rw [e] at h
    exact h
  have : (fun ω => if ρ ω ≤ u then N (ρ ω) ω else 0) =
      fun ω => if ρ ω ≤ u then N (min u (ρ ω)) ω else 0 := by
    funext ω
    split_ifs with h
    · rw [min_eq_right h]
    · rfl
  rw [this]
  exact Measurable.ite (Infrastructure.measurableSet_nnreal_le hρ u) h1.measurable
    measurable_const

/-- The pointwise identity behind the cross terms: for `ρ ≤ σ`,
`Y_{t ∧ ρ} (M_{t ∧ σ} - M_{t ∧ ρ}) = Y_ρ (M_{t ∧ σ} - M_{(t ∧ ρ) ∧ σ})`. -/
theorem min_mul_sub_eq {Y M : ℝ≥0 → ℝ} {ρ σ : ℝ≥0} (hρσ : ρ ≤ σ) (t : ℝ≥0) :
    Y (min t ρ) * (M (min t σ) - M (min t ρ)) = Y ρ * (M (min t σ) - M (min (min t ρ) σ)) := by
  rw [min_assoc, min_eq_left hρσ]
  by_cases h : ρ ≤ t
  · rw [min_eq_right h]
  · have h' : t < ρ := lt_of_not_ge h
    rw [min_eq_left h'.le, min_eq_left (h'.le.trans hρσ), sub_self, mul_zero, mul_zero]

variable (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) (n : ℕ)

/-! ### Constancy after `τ_n` -/

theorem pathIntegral_thetaBracket_eq_of_le {ω : Ω} {s t : ℝ≥0} (hst : s ≤ t)
    (hs : exitNN hU z n ω ≤ s) :
    pathIntegral (thetaBracket hU z n) t ω = pathIntegral (thetaBracket hU z n) s ω := by
  rw [pathIntegral_thetaBracket, pathIntegral_thetaBracket, min_eq_right hs,
    min_eq_right (hs.trans hst)]

theorem pathIntegral_thetaLogCross_eq_of_le {ω : Ω} {s t : ℝ≥0} (hst : s ≤ t)
    (hs : exitNN hU z n ω ≤ s) :
    pathIntegral (thetaLogCross hU z n) t ω = pathIntegral (thetaLogCross hU z n) s ω := by
  rw [pathIntegral_thetaLogCross, pathIntegral_thetaLogCross, min_eq_right hs,
    min_eq_right (hs.trans hst)]

theorem continuous_pathIntegral_thetaBracket (ω : Ω) :
    Continuous fun t => pathIntegral (thetaBracket hU z n) t ω :=
  continuous_pathIntegral' (intervalIntegrable_thetaBracket hU z n ω)

theorem continuous_pathIntegral_thetaLogCross (ω : Ω) :
    Continuous fun t => pathIntegral (thetaLogCross hU z n) t ω :=
  continuous_pathIntegral' (intervalIntegrable_thetaLogCross hU z n ω)

/-! ### Summation over the sectors -/

variable [IsProbabilityMeasure P]

/-- `(Θ^n)² - B` stopped at `S_K` is a continuous local martingale (sum over the sectors). -/
theorem isContLocalMartingale_thetaMart_sq_sub_min_sectorTime (ha : 0 < a) (hc : c ^ 2 ≤ a * b)
    (hz : z ≠ 0) (K : ℕ) :
    IsContLocalMartingale ℱ (fun t ω => thetaMart hU z n (min t (sectorTime hU z n K ω)) ω ^ 2 -
      pathIntegral (thetaBracket hU z n) (min t (sectorTime hU z n K ω)) ω) P := by
  induction K with
  | zero =>
    have : (fun t ω => thetaMart hU z n (min t (sectorTime hU z n 0 ω)) ω ^ 2 -
        pathIntegral (thetaBracket hU z n) (min t (sectorTime hU z n 0 ω)) ω) =
        fun _ _ => (0 : ℝ) := by
      funext t ω
      simp [sectorTime_zero, thetaMart_zero, pathIntegral_zero_time]
    rw [this]; exact isContLocalMartingale_zero
  | succ K ih =>
    have hρσ : ∀ ω, sectorTime hU z n K ω ≤ sectorTime hU z n (K + 1) ω :=
      sectorTime_le_succ hU z n K
    have hρ := isStoppingTime_sectorTime hU z n K
    -- the cross term `2 Θ^n_{S_K} (Θ^n_{t ∧ S_{K+1}} - Θ^n_{t ∧ S_K})`
    have h3 := (isContLocalMartingale_thetaMart_min_sectorTime hU z n ha hc hz (K + 1)).mul_sub_min'
      (fun ω => (continuous_thetaMart hU z n ω).comp (continuous_id.min continuous_const)) hρ
      (V := fun ω => thetaMart hU z n (sectorTime hU z n K ω) ω)
      (measurable_ite_le_apply (isStronglyProgressive_thetaMart hU z n) hρ)
    have h2 := isContLocalMartingale_sectorIncrement_sq hU z n K ha hc hz
    have hc1 : ∀ ω, Continuous fun t => thetaMart hU z n (min t (sectorTime hU z n K ω)) ω ^ 2 -
        pathIntegral (thetaBracket hU z n) (min t (sectorTime hU z n K ω)) ω := fun ω =>
      (((continuous_thetaMart hU z n ω).comp (continuous_id.min continuous_const)).pow 2).sub
        ((continuous_pathIntegral_thetaBracket hU z n ω).comp (continuous_id.min continuous_const))
    have hc2 : ∀ ω, Continuous fun t =>
        (thetaMart hU z n (min t (sectorTime hU z n (K + 1) ω)) ω -
          thetaMart hU z n (min t (sectorTime hU z n K ω)) ω) ^ 2 -
        (pathIntegral (thetaBracket hU z n) (min t (sectorTime hU z n (K + 1) ω)) ω -
          pathIntegral (thetaBracket hU z n) (min t (sectorTime hU z n K ω)) ω) := fun ω =>
      ((((continuous_thetaMart hU z n ω).comp (continuous_id.min continuous_const)).sub
        ((continuous_thetaMart hU z n ω).comp (continuous_id.min continuous_const))).pow 2).sub
        (((continuous_pathIntegral_thetaBracket hU z n ω).comp
          (continuous_id.min continuous_const)).sub
          ((continuous_pathIntegral_thetaBracket hU z n ω).comp
            (continuous_id.min continuous_const)))
    have hc3 : ∀ ω, Continuous fun t => thetaMart hU z n (sectorTime hU z n K ω) ω *
        (thetaMart hU z n (min t (sectorTime hU z n (K + 1) ω)) ω -
          thetaMart hU z n (min (min t (sectorTime hU z n K ω)) (sectorTime hU z n (K + 1) ω)) ω) :=
      fun ω => continuous_const.mul
        (((continuous_thetaMart hU z n ω).comp (continuous_id.min continuous_const)).sub
          ((continuous_thetaMart hU z n ω).comp
            ((continuous_id.min continuous_const).min continuous_const)))
    have h := (ih.add h2 hc1 hc2).add (h3.const_mul 2) (fun ω => (hc1 ω).add (hc2 ω))
      (fun ω => continuous_const.mul (hc3 ω))
    refine h.congr_fun' fun t ω => ?_
    simp only [Pi.add_apply]
    rw [← min_mul_sub_eq (Y := fun r => thetaMart hU z n r ω) (M := fun r => thetaMart hU z n r ω)
      (hρσ ω) t]
    ring

/-- `Θ^n N^n - C` stopped at `S_K` is a continuous local martingale (sum over the sectors). -/
theorem isContLocalMartingale_thetaMart_mul_logMart_sub_min_sectorTime (ha : 0 < a)
    (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) (K : ℕ) :
    IsContLocalMartingale ℱ (fun t ω => thetaMart hU z n (min t (sectorTime hU z n K ω)) ω *
      logMart hU z n (min t (sectorTime hU z n K ω)) ω -
      pathIntegral (thetaLogCross hU z n) (min t (sectorTime hU z n K ω)) ω) P := by
  induction K with
  | zero =>
    have : (fun t ω => thetaMart hU z n (min t (sectorTime hU z n 0 ω)) ω *
        logMart hU z n (min t (sectorTime hU z n 0 ω)) ω -
        pathIntegral (thetaLogCross hU z n) (min t (sectorTime hU z n 0 ω)) ω) =
        fun _ _ => (0 : ℝ) := by
      funext t ω
      simp [sectorTime_zero, thetaMart_zero, pathIntegral_zero_time]
    rw [this]; exact isContLocalMartingale_zero
  | succ K ih =>
    have hρσ : ∀ ω, sectorTime hU z n K ω ≤ sectorTime hU z n (K + 1) ω :=
      sectorTime_le_succ hU z n K
    have hρ := isStoppingTime_sectorTime hU z n K
    have hσ := isStoppingTime_sectorTime hU z n (K + 1)
    have hN := isContLocalMartingale_logMart hU z n ha hc hz
    have hNσ := hN.stopped_min_of_continuous ℱ (continuous_logMart hU z n) hσ
    -- `Θ^n_{S_K} (N^n_{t ∧ S_{K+1}} - N^n_{t ∧ S_K})`
    have h3 := hNσ.mul_sub_min'
      (fun ω => (continuous_logMart hU z n ω).comp (continuous_id.min continuous_const)) hρ
      (V := fun ω => thetaMart hU z n (sectorTime hU z n K ω) ω)
      (measurable_ite_le_apply (isStronglyProgressive_thetaMart hU z n) hρ)
    -- `N^n_{S_K} (Θ^n_{t ∧ S_{K+1}} - Θ^n_{t ∧ S_K})`
    have h4 := (isContLocalMartingale_thetaMart_min_sectorTime hU z n ha hc hz (K + 1)).mul_sub_min'
      (fun ω => (continuous_thetaMart hU z n ω).comp (continuous_id.min continuous_const)) hρ
      (V := fun ω => logMart hU z n (sectorTime hU z n K ω) ω) (measurable_ite_le_apply hN.1 hρ)
    have h2 := isContLocalMartingale_sectorIncrement_mul hU z n K ha hc hz
    have hcΘ : ∀ ω (S : Ω → ℝ≥0), Continuous fun t => thetaMart hU z n (min t (S ω)) ω := fun ω S =>
      (continuous_thetaMart hU z n ω).comp (continuous_id.min continuous_const)
    have hcN : ∀ ω (S : Ω → ℝ≥0), Continuous fun t => logMart hU z n (min t (S ω)) ω := fun ω S =>
      (continuous_logMart hU z n ω).comp (continuous_id.min continuous_const)
    have hcC : ∀ ω (S : Ω → ℝ≥0),
        Continuous fun t => pathIntegral (thetaLogCross hU z n) (min t (S ω)) ω := fun ω S =>
      (continuous_pathIntegral_thetaLogCross hU z n ω).comp (continuous_id.min continuous_const)
    have hc1 : ∀ ω, Continuous fun t => thetaMart hU z n (min t (sectorTime hU z n K ω)) ω *
        logMart hU z n (min t (sectorTime hU z n K ω)) ω -
        pathIntegral (thetaLogCross hU z n) (min t (sectorTime hU z n K ω)) ω := fun ω =>
      ((hcΘ ω _).mul (hcN ω _)).sub (hcC ω _)
    have hc2 : ∀ ω, Continuous fun t =>
        (thetaMart hU z n (min t (sectorTime hU z n (K + 1) ω)) ω -
          thetaMart hU z n (min t (sectorTime hU z n K ω)) ω) *
        (logMart hU z n (min t (sectorTime hU z n (K + 1) ω)) ω -
          logMart hU z n (min t (sectorTime hU z n K ω)) ω) -
        (pathIntegral (thetaLogCross hU z n) (min t (sectorTime hU z n (K + 1) ω)) ω -
          pathIntegral (thetaLogCross hU z n) (min t (sectorTime hU z n K ω)) ω) := fun ω =>
      (((hcΘ ω _).sub (hcΘ ω _)).mul ((hcN ω _).sub (hcN ω _))).sub ((hcC ω _).sub (hcC ω _))
    have hc3 : ∀ ω, Continuous fun t => thetaMart hU z n (sectorTime hU z n K ω) ω *
        (logMart hU z n (min t (sectorTime hU z n (K + 1) ω)) ω -
          logMart hU z n (min (min t (sectorTime hU z n K ω)) (sectorTime hU z n (K + 1) ω)) ω) :=
      fun ω => continuous_const.mul ((hcN ω _).sub ((continuous_logMart hU z n ω).comp
        ((continuous_id.min continuous_const).min continuous_const)))
    have hc4 : ∀ ω, Continuous fun t => logMart hU z n (sectorTime hU z n K ω) ω *
        (thetaMart hU z n (min t (sectorTime hU z n (K + 1) ω)) ω -
          thetaMart hU z n (min (min t (sectorTime hU z n K ω)) (sectorTime hU z n (K + 1) ω)) ω) :=
      fun ω => continuous_const.mul ((hcΘ ω _).sub ((continuous_thetaMart hU z n ω).comp
        ((continuous_id.min continuous_const).min continuous_const)))
    have h := ((ih.add h2 hc1 hc2).add h3 (fun ω => (hc1 ω).add (hc2 ω)) hc3).add h4
      (fun ω => ((hc1 ω).add (hc2 ω)).add (hc3 ω)) hc4
    refine h.congr_fun' fun t ω => ?_
    simp only [Pi.add_apply]
    rw [← min_mul_sub_eq (Y := fun r => thetaMart hU z n r ω) (M := fun r => logMart hU z n r ω)
      (hρσ ω) t, ← min_mul_sub_eq (Y := fun r => logMart hU z n r ω)
      (M := fun r => thetaMart hU z n r ω) (hρσ ω) t]
    ring

/-! ### Localisation -/

omit [IsProbabilityMeasure P] in
/-- `(Θ^n)² - B` stopped at `ρ_K` is `(Θ^n)² - B` stopped at `S_K`. -/
theorem stoppedProcess_thetaMart_sq_sub_sectorLocalizer (K : ℕ) :
    stoppedProcess (fun t ω => thetaMart hU z n t ω ^ 2 - pathIntegral (thetaBracket hU z n) t ω)
      (sectorLocalizer hU z n K) =
      fun t ω => thetaMart hU z n (min t (sectorTime hU z n K ω)) ω ^ 2 -
        pathIntegral (thetaBracket hU z n) (min t (sectorTime hU z n K ω)) ω := by
  funext t ω
  simp only [stoppedProcess, sectorLocalizer]
  split_ifs with h
  · rw [← WithTop.coe_min, untopA_coe']
  · rw [min_eq_left le_top, untopA_coe']
    have hK : sectorTime hU z n K ω = exitNN hU z n ω :=
      le_antisymm (sectorTime_le_exitNN hU z n K ω) (not_lt.1 h)
    rw [hK]
    by_cases ht : exitNN hU z n ω ≤ t
    · rw [min_eq_right ht, thetaMart_eq_of_le hU z n ht le_rfl,
        pathIntegral_thetaBracket_eq_of_le hU z n ht le_rfl]
    · rw [min_eq_left (le_of_lt (lt_of_not_ge ht))]

omit [IsProbabilityMeasure P] in
/-- `Θ^n N^n - C` stopped at `ρ_K` is `Θ^n N^n - C` stopped at `S_K`. -/
theorem stoppedProcess_thetaMart_mul_logMart_sub_sectorLocalizer (K : ℕ) :
    stoppedProcess (fun t ω => thetaMart hU z n t ω * logMart hU z n t ω -
        pathIntegral (thetaLogCross hU z n) t ω) (sectorLocalizer hU z n K) =
      fun t ω => thetaMart hU z n (min t (sectorTime hU z n K ω)) ω *
        logMart hU z n (min t (sectorTime hU z n K ω)) ω -
        pathIntegral (thetaLogCross hU z n) (min t (sectorTime hU z n K ω)) ω := by
  funext t ω
  simp only [stoppedProcess, sectorLocalizer]
  split_ifs with h
  · rw [← WithTop.coe_min, untopA_coe']
  · rw [min_eq_left le_top, untopA_coe']
    have hK : sectorTime hU z n K ω = exitNN hU z n ω :=
      le_antisymm (sectorTime_le_exitNN hU z n K ω) (not_lt.1 h)
    rw [hK]
    by_cases ht : exitNN hU z n ω ≤ t
    · rw [min_eq_right ht, thetaMart_eq_of_le hU z n ht le_rfl, logMart_eq_of_le hU z n ht le_rfl,
        pathIntegral_thetaLogCross_eq_of_le hU z n ht le_rfl]
    · rw [min_eq_left (le_of_lt (lt_of_not_ge ht))]

/-- **The bracket of `Θ^n`** (`step:polar-real-imag`, imaginary part, bracket of
`eqn-theta-t-op`). For `0 < a`, `c² ≤ ab`, `z ≠ 0`:
`(Θ^n_t)² - ∫₀ᵗ 1_{s ≤ τ_n} (a sin² θ_s + b cos² θ_s - 2c sin θ_s cos θ_s) |f_s(z)|⁻² ds` is a
continuous `ℱ`-local martingale. -/
theorem isContLocalMartingale_thetaMart_sq_sub (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) :
    IsContLocalMartingale ℱ
      (fun t ω => thetaMart hU z n t ω ^ 2 - pathIntegral (thetaBracket hU z n) t ω) P := by
  refine IsContLocalMartingale.of_stopped_seq
    (fun i => ((isStronglyProgressive_thetaMart hU z n i).pow 2).sub
      (isStronglyProgressive_pathIntegral' (isStronglyProgressive_thetaBracket hU z n) i))
    (ae_of_all _ fun ω => ((continuous_thetaMart hU z n ω).pow 2).sub
      (continuous_pathIntegral_thetaBracket hU z n ω))
    (isStoppingTime_sectorLocalizer hU z n)
    (ae_of_all _ fun ω t => eventually_le_sectorLocalizer hU z n ω t) fun K => ?_
  rw [stoppedProcess_thetaMart_sq_sub_sectorLocalizer]
  exact isContLocalMartingale_thetaMart_sq_sub_min_sectorTime hU z n ha hc hz K

/-- **The cross bracket of `Θ^n` and `N^n`** (`step:polar-real-imag`, cross bracket of
`eqn-theta-t-op` and `eqn-abs-zt-op`). For `0 < a`, `c² ≤ ab`, `z ≠ 0`:
`Θ^n_t N^n_t - ∫₀ᵗ 1_{s ≤ τ_n} ((b - a) sin θ_s cos θ_s + c (cos² θ_s - sin² θ_s)) |f_s(z)|⁻² ds`
is a continuous `ℱ`-local martingale. -/
theorem isContLocalMartingale_thetaMart_mul_logMart_sub (ha : 0 < a) (hc : c ^ 2 ≤ a * b)
    (hz : z ≠ 0) :
    IsContLocalMartingale ℱ (fun t ω => thetaMart hU z n t ω * logMart hU z n t ω -
      pathIntegral (thetaLogCross hU z n) t ω) P := by
  have hN := isContLocalMartingale_logMart hU z n ha hc hz
  refine IsContLocalMartingale.of_stopped_seq
    (fun i => ((isStronglyProgressive_thetaMart hU z n i).mul (hN.1 i)).sub
      (isStronglyProgressive_pathIntegral' (isStronglyProgressive_thetaLogCross hU z n) i))
    (ae_of_all _ fun ω => ((continuous_thetaMart hU z n ω).mul (continuous_logMart hU z n ω)).sub
      (continuous_pathIntegral_thetaLogCross hU z n ω))
    (isStoppingTime_sectorLocalizer hU z n)
    (ae_of_all _ fun ω t => eventually_le_sectorLocalizer hU z n ω t) fun K => ?_
  rw [stoppedProcess_thetaMart_mul_logMart_sub_sectorLocalizer]
  exact isContLocalMartingale_thetaMart_mul_logMart_sub_min_sectorTime hU z n ha hc hz K

end

end ComplexSLE.Internal.Polar

end
