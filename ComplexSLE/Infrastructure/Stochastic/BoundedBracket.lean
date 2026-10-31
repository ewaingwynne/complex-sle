/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Stochastic.BoundedBracketMaximal
public import ComplexSLE.Infrastructure.Stochastic.LocalMartingaleAlgebra
public import ComplexSLE.Infrastructure.Stochastic.CondShift
public import ComplexSLE.Infrastructure.Stochastic.ContinuousModification
public import ComplexSLE.Infrastructure.Stochastic.ProgressiveTools
public import Mathlib.MeasureTheory.Integral.Indicator
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Continuous local martingales with bounded bracket are `L²`-martingales

Source-independent stochastic calculus. No external input is used; only Mathlib and the
project's local-martingale infrastructure.

Let `M` be a continuous local martingale (`ComplexSLE.IsContLocalMartingale`) with `M 0 = 0` such
that `M² - ∫₀ˢ Γ` is a continuous local martingale, where `|Γ| ≤ K`. Then

* `IsContLocalMartingale.bounded_bracket`: `M_t ∈ L²`, `E M_t² ≤ K t`, `E M_t = 0`, and
  `M_s / s → 0` almost surely (`s → ∞`);
* `martingale_of_bounded_bracket`: the everywhere-continuous version: `M` is a true martingale.

Route (Revuz–Yor IV.1): localise with the common sequence `ρ_k = τ_k ∧ σ_k` of the two local
martingales (`exists_localizing_pair`; stopping a martingale at a second stopping time is
`Martingale.stoppedProcess_of_continuous`, so everywhere continuous paths are needed), so
`E (M^{ρ_k}_t)² = E ∫₀^{ρ_k ∧ t} Γ ≤ K t` (`integral_sq_stopped_le`); Fatou
(`integrable_sq_of_eventually_eq`) gives `E M_t² ≤ K t`; the stopped marginals converge to `M_t` in
`L¹` (`tendsto_integral_abs_sub_of_sq_bound`, by `|y| 1_B ≤ y²/(2c) + c 1_B` and
`P(ρ_k < t) → 0`), so `M` is a martingale; the almost sure statement is the dyadic Doob estimate
of `BoundedBracketMaximal.lean`. Paths that are only a.s. continuous are handled through the
continuous version for the `P`-completed filtration
(`IsContLocalMartingale.exists_continuous_version`).
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Infrastructure

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}

/-- A common localising sequence for two everywhere continuous local martingales -/
theorem exists_localizing_pair [IsFiniteMeasure P] {M N : ℝ≥0 → Ω → ℝ}
    (hM : IsContLocalMartingale ℱ M P)
    (hN : IsContLocalMartingale ℱ N P) (hMc : ∀ ω, Continuous fun t => M t ω)
    (hNc : ∀ ω, Continuous fun t => N t ω) :
    ∃ ρ : ℕ → Ω → WithTop ℝ≥0, (∀ k, IsStoppingTime ℱ (ρ k)) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, ∀ᶠ k in atTop, (t : WithTop ℝ≥0) ≤ ρ k ω) ∧
      ∀ k, Martingale (stoppedProcess M (ρ k)) ℱ P ∧
        Martingale (stoppedProcess N (ρ k)) ℱ P := by
  obtain ⟨-, -, τ, hτ, hτev, hmartM⟩ := hM
  obtain ⟨-, -, σ, hσ, hσev, hmartN⟩ := hN
  refine ⟨fun n ω => min (τ n ω) (σ n ω), fun n => (hτ n).min (hσ n), ?_, fun n => ⟨?_, ?_⟩⟩
  · filter_upwards [hτev, hσev] with ω h1 h2 t
    filter_upwards [h1 t, h2 t] with n a b using le_min a b
  · have h := (hmartM n).stoppedProcess_of_continuous (continuous_stoppedProcess hMc (τ n)) (hσ n)
    rw [stoppedProcess_stoppedProcess_min, funext fun ω => min_comm (σ n ω) (τ n ω)] at h
    exact h
  · have h := (hmartN n).stoppedProcess_of_continuous (continuous_stoppedProcess hNc (σ n)) (hτ n)
    rw [stoppedProcess_stoppedProcess_min] at h
    exact h

/-- The bound `|∫₀ᵗ ξ_s ds| ≤ C t` for a path bounded by `C`. -/
theorem abs_pathIntegral_le_of_bound {Γ : ℝ≥0 → Ω → ℝ} {K : ℝ} {ω : Ω}
    (hΓ : ∀ s, |Γ s ω| ≤ K) (t : ℝ≥0) : |pathIntegral Γ t ω| ≤ K * t := by
  unfold pathIntegral
  have := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun s : ℝ => Γ (Real.toNNReal s) ω) (a := 0) (b := t) (C := K)
    fun s _ => by simpa [Real.norm_eq_abs] using hΓ (Real.toNNReal s)
  simpa [Real.norm_eq_abs, abs_of_nonneg t.2] using this

/-- **Second moment of a stopped process with bounded bracket.** -/
theorem integral_sq_stopped_le [IsProbabilityMeasure P] {M Γ : ℝ≥0 → Ω → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hΓ : ∀ s ω, |Γ s ω| ≤ K) {ρ : Ω → WithTop ℝ≥0}
    (hX : Martingale (stoppedProcess M ρ) ℱ P)
    (hZ : Martingale (stoppedProcess (fun t ω => M t ω ^ 2 - pathIntegral Γ t ω) ρ) ℱ P)
    (h0 : ∀ᵐ ω ∂P, M 0 ω = 0) (t : ℝ≥0) :
    Integrable (fun ω => stoppedProcess M ρ t ω ^ 2) P ∧
      ∫ ω, stoppedProcess M ρ t ω ^ 2 ∂P ≤ K * t := by
  set X := stoppedProcess M ρ with hXdef
  set Z := stoppedProcess (fun t ω => M t ω ^ 2 - pathIntegral Γ t ω) ρ with hZdef
  set I : Ω → ℝ := fun ω => pathIntegral Γ (min (t : WithTop ℝ≥0) (ρ ω)).untopA ω with hI
  have key : ∀ ω, X t ω ^ 2 = Z t ω + I ω := fun ω => by
    simp only [hXdef, hZdef, hI, stoppedProcess]; ring
  have hIb : ∀ ω, |I ω| ≤ K * t := fun ω => by
    refine (abs_pathIntegral_le_of_bound (hΓ · ω) _).trans ?_
    gcongr
    exact WithTop.untopA_le (min_le_left _ _)
  have hXm : Measurable (X t) := ((hX.stronglyAdapted t).mono (ℱ.le t)).measurable
  have hZm : Measurable (Z t) := ((hZ.stronglyAdapted t).mono (ℱ.le t)).measurable
  have hIm : Measurable I := by
    have : I = fun ω => X t ω ^ 2 - Z t ω := by funext ω; linarith [key ω]
    rw [this]; exact (hXm.pow_const 2).sub hZm
  have hIint : Integrable I P :=
    (integrable_const (K * t)).mono' hIm.aestronglyMeasurable
      (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hIb ω)
  have hint : Integrable (fun ω => X t ω ^ 2) P := by
    refine ((hZ.integrable t).add hIint).congr (Eventually.of_forall fun ω => ?_)
    simp [key ω]
  refine ⟨hint, ?_⟩
  have hZ0 : ∫ ω, Z t ω ∂P = 0 := by
    have h := hZ.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ t) MeasurableSet.univ
    simp only [Measure.restrict_univ] at h
    rw [← h]
    have : ∀ᵐ ω ∂P, Z 0 ω = 0 := by
      filter_upwards [h0] with ω hω
      simp [hZdef, stoppedProcess, hω, pathIntegral]
    rw [integral_congr_ae this, integral_zero]
  have e : ∫ ω, X t ω ^ 2 ∂P = ∫ ω, Z t ω ∂P + ∫ ω, I ω ∂P := by
    rw [← integral_add (hZ.integrable t) hIint]
    exact integral_congr_ae (Eventually.of_forall key)
  rw [e, hZ0, zero_add]
  have := norm_integral_le_of_norm_le_const (μ := P) (f := I) (C := K * t)
    (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hIb ω)
  simpa [Real.norm_eq_abs] using (le_abs_self _).trans this


/-- **Fatou for the second moment.** If `X_k = M_t` eventually (a.s.) and `E X_k² ≤ A`, then
`E M_t² ≤ A`. -/
theorem integrable_sq_of_eventually_eq [IsFiniteMeasure P] {Y : Ω → ℝ} {X : ℕ → Ω → ℝ} {A : ℝ}
    (hA : 0 ≤ A) (hev : ∀ᵐ ω ∂P, ∀ᶠ k in atTop, X k ω = Y ω) (hYm : Measurable Y)
    (hXm : ∀ k, Measurable (X k)) (hint : ∀ k, Integrable (fun ω => X k ω ^ 2) P)
    (hle : ∀ k, ∫ ω, X k ω ^ 2 ∂P ≤ A) :
    Integrable (fun ω => Y ω ^ 2) P ∧ ∫ ω, Y ω ^ 2 ∂P ≤ A := by
  have hl : ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂P ≤ ENNReal.ofReal A := by
    calc ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂P
        = ∫⁻ ω, liminf (fun k => ENNReal.ofReal (X k ω ^ 2)) atTop ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hev] with ω hω
          have : (fun k => ENNReal.ofReal (X k ω ^ 2)) =ᶠ[atTop]
              fun _ => ENNReal.ofReal (Y ω ^ 2) := hω.mono fun k hk => by simp only [hk]
          exact ((Filter.liminf_congr this).trans (Filter.liminf_const _)).symm
      _ ≤ liminf (fun k => ∫⁻ ω, ENNReal.ofReal (X k ω ^ 2) ∂P) atTop :=
          lintegral_liminf_le fun k => ENNReal.measurable_ofReal.comp ((hXm k).pow_const 2)
      _ ≤ ENNReal.ofReal A := by
          refine liminf_le_of_frequently_le' (Eventually.of_forall fun k => ?_).frequently
          rw [← ofReal_integral_eq_lintegral_ofReal (hint k)
            (Eventually.of_forall fun ω => sq_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (hle k)
  have hnn : 0 ≤ᵐ[P] fun ω => Y ω ^ 2 := Eventually.of_forall fun ω => sq_nonneg _
  have hint' : Integrable (fun ω => Y ω ^ 2) P :=
    ⟨(hYm.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hnn).2 (lt_of_le_of_lt hl ENNReal.ofReal_lt_top)⟩
  refine ⟨hint', ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn (hYm.pow_const 2).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hA hl


/-- **`L²`-bounded sequences that eventually coincide converge in `L¹`.** Let `X k = Y` off the
measurable sets `B k` with `P (B k) → 0`, and `E X_k² ≤ A`, `E Y² ≤ A`. Then `E |X_k - Y| → 0`. -/
theorem tendsto_integral_abs_sub_of_sq_bound [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    {A : ℝ} {B : ℕ → Set Ω} (hB : ∀ k, MeasurableSet (B k))
    (hXY : ∀ k, ∀ ω, ω ∉ B k → X k ω = Y ω)
    (hPB : Tendsto (fun k => (P (B k)).toReal) atTop (𝓝 0))
    (hXi : ∀ k, Integrable (fun ω => X k ω ^ 2) P) (hYi : Integrable (fun ω => Y ω ^ 2) P)
    (hXA : ∀ k, ∫ ω, X k ω ^ 2 ∂P ≤ A) (hYA : ∫ ω, Y ω ^ 2 ∂P ≤ A) :
    Tendsto (fun k => ∫ ω, |X k ω - Y ω| ∂P) atTop (𝓝 0) := by
  have hA : 0 ≤ A := le_trans (integral_nonneg fun _ => sq_nonneg _) hYA
  rw [Metric.tendsto_atTop]
  intro ε hε
  set c : ℝ := 2 * A / ε + 1 with hcdef
  have hc : 0 < c := by positivity
  obtain ⟨k₀, hk₀⟩ := Metric.tendsto_atTop.1 hPB (ε / (2 * c)) (by positivity)
  refine ⟨k₀, fun k hk => ?_⟩
  have hPk := hk₀ k hk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at hPk
  have hpt : ∀ ω, |X k ω - Y ω| ≤
      (X k ω ^ 2 + Y ω ^ 2) / (2 * c) + c * (B k).indicator (1 : Ω → ℝ) ω := by
    intro ω
    by_cases hω : ω ∈ B k
    · simp only [Set.indicator_of_mem hω, Pi.one_apply]
      have h1 : ∀ x : ℝ, |x| ≤ (x ^ 2 + c ^ 2) / (2 * c) := fun x => by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (|x| - c), sq_abs x]
      calc |X k ω - Y ω| ≤ |X k ω| + |Y ω| := abs_sub _ _
        _ ≤ (X k ω ^ 2 + c ^ 2) / (2 * c) + (Y ω ^ 2 + c ^ 2) / (2 * c) := add_le_add (h1 _) (h1 _)
        _ = (X k ω ^ 2 + Y ω ^ 2) / (2 * c) + c * 1 := by field_simp; ring
    · simp only [Set.indicator_of_notMem hω, mul_zero, add_zero]
      rw [hXY k ω hω, sub_self, abs_zero]
      positivity
  have hind : Integrable ((B k).indicator (1 : Ω → ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator (hB k)
  have hsum : Integrable (fun ω => X k ω ^ 2 + Y ω ^ 2) P := (hXi k).add hYi
  have hdiv : Integrable (fun ω => (X k ω ^ 2 + Y ω ^ 2) / (2 * c)) P := hsum.div_const _
  have hint : Integrable (fun ω => (X k ω ^ 2 + Y ω ^ 2) / (2 * c) +
      c * (B k).indicator (1 : Ω → ℝ) ω) P :=
    hdiv.add (hind.const_mul c)
  have h1 := integral_mono_of_nonneg (Eventually.of_forall fun ω => abs_nonneg (X k ω - Y ω))
    hint (Eventually.of_forall hpt)
  have h2 : ∫ ω, ((X k ω ^ 2 + Y ω ^ 2) / (2 * c) + c * (B k).indicator (1 : Ω → ℝ) ω) ∂P =
      ((∫ ω, X k ω ^ 2 ∂P) + ∫ ω, Y ω ^ 2 ∂P) / (2 * c) + c * (P (B k)).toReal := by
    rw [integral_add hdiv (hind.const_mul c), integral_div,
      integral_add (hXi k) hYi, integral_const_mul, integral_indicator_one (hB k)]
    rfl
  have h3 : ((∫ ω, X k ω ^ 2 ∂P) + ∫ ω, Y ω ^ 2 ∂P) / (2 * c) ≤ A / c := by
    rw [div_le_div_iff₀ (by positivity) hc]
    nlinarith [hXA k, hYA]
  have h4 : A / c ≤ ε / 2 := by
    rw [div_le_iff₀ hc, hcdef]
    have : ε / 2 * (2 * A / ε + 1) = A + ε / 2 := by field_simp
    rw [this]; linarith
  have h5 : c * (P (B k)).toReal < ε / 2 := by
    calc c * (P (B k)).toReal < c * (ε / (2 * c)) := by gcongr
      _ = ε / 2 := by field_simp
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun ω => abs_nonneg _)]
  rw [h2] at h1
  linarith


/-- **Bounded bracket gives a true `L²` martingale** (everywhere continuous paths). Let `M` be a
continuous local martingale with `M 0 = 0` such that `M² - ∫₀ˢ Γ` is a continuous local martingale
for a path-continuous integral of a process `Γ` with `|Γ| ≤ K`. Then `M` is a martingale with
`E M_t² ≤ K t`. -/
theorem martingale_of_bounded_bracket [IsProbabilityMeasure P] {M Γ : ℝ≥0 → Ω → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hΓ : ∀ s ω, |Γ s ω| ≤ K) (hM : IsContLocalMartingale ℱ M P)
    (hMc : ∀ ω, Continuous fun t => M t ω) (h0 : ∀ᵐ ω ∂P, M 0 ω = 0)
    (hIc : ∀ ω, Continuous fun t => pathIntegral Γ t ω)
    (hN : IsContLocalMartingale ℱ (fun t ω => M t ω ^ 2 - pathIntegral Γ t ω) P) :
    Martingale M ℱ P ∧ (∀ t, Integrable (fun ω => M t ω ^ 2) P) ∧
      ∀ t : ℝ≥0, ∫ ω, M t ω ^ 2 ∂P ≤ K * t := by
  obtain ⟨ρ, hρ, hρev, hmart⟩ := exists_localizing_pair hM hN hMc
    (fun ω => (hMc ω).pow 2 |>.sub (hIc ω))
  have hmom := fun k t => integral_sq_stopped_le hK hΓ (hmart k).1 (hmart k).2 h0 t
  have hMmeas : ∀ t, Measurable (M t) := fun t =>
    ((hM.1.stronglyAdapted t).mono (ℱ.le t)).measurable
  have hXmeas : ∀ k t, Measurable (stoppedProcess M (ρ k) t) := fun k t =>
    (((hmart k).1.stronglyAdapted t).mono (ℱ.le t)).measurable
  have hev : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ∀ᶠ k in atTop, stoppedProcess M (ρ k) t ω = M t ω := fun t => by
    filter_upwards [hρev] with ω hω
    filter_upwards [hω t] with k hk
    exact stoppedProcess_eq_of_le hk
  have hfat : ∀ t : ℝ≥0, Integrable (fun ω => M t ω ^ 2) P ∧ ∫ ω, M t ω ^ 2 ∂P ≤ K * t := fun t =>
    integrable_sq_of_eventually_eq (by positivity) (hev t) (hMmeas t) (fun k => hXmeas k t)
      (fun k => (hmom k t).1) fun k => (hmom k t).2
  -- `L¹` convergence of the stopped marginals
  have hl1 : ∀ t : ℝ≥0, Tendsto (fun k => ∫ ω, |stoppedProcess M (ρ k) t ω - M t ω| ∂P) atTop
      (𝓝 0) := fun t => by
    refine tendsto_integral_abs_sub_of_sq_bound (B := fun k => {ω | ρ k ω < t})
      (fun k => ℱ.le t _ ((hρ k).measurableSet_lt t)) (fun k ω hω => ?_) ?_
      (fun k => (hmom k t).1) (hfat t).1 (fun k => (hmom k t).2) (hfat t).2
    · exact stoppedProcess_eq_of_le (not_lt.1 hω)
    · have h := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
        (A := (∅ : Set Ω)) MeasurableSet.empty (fun k => ℱ.le t _ ((hρ k).measurableSet_lt t))
        (μ := P) (As := fun k => {ω | ρ k ω < t}) (by
          filter_upwards [hρev] with ω hω
          filter_upwards [hω t] with k hk
          simp only [not_lt.2 hk, mem_empty_iff_false])
      rw [measure_empty] at h
      exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  have hMint : ∀ t, Integrable (M t) P := fun t =>
    ((memLp_two_iff_integrable_sq (hMmeas t).aestronglyMeasurable).2 (hfat t).1).integrable
      one_le_two
  have hset : ∀ (t : ℝ≥0) (S : Set Ω), MeasurableSet S →
      Tendsto (fun k => ∫ ω in S, stoppedProcess M (ρ k) t ω ∂P) atTop
        (𝓝 (∫ ω in S, M t ω ∂P)) := fun t S hS => by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) (hl1 t)
    have hXi : Integrable (stoppedProcess M (ρ k) t) P := (hmart k).1.integrable t
    rw [← integral_sub hXi.integrableOn (hMint t).integrableOn]
    refine (norm_integral_le_integral_norm _).trans ?_
    simp only [Real.norm_eq_abs]
    exact setIntegral_le_integral (hXi.sub (hMint t)).abs
      (Eventually.of_forall fun ω => abs_nonneg _)
  have hmartM : Martingale M ℱ P := by
    refine martingale_of_setIntegral_eq (hM.1.stronglyAdapted) hMint fun i j hij S hS => ?_
    have h1 := hset j S (ℱ.le i S hS)
    have h2 := hset i S (ℱ.le i S hS)
    have e : ∀ k, ∫ ω in S, stoppedProcess M (ρ k) j ω ∂P =
        ∫ ω in S, stoppedProcess M (ρ k) i ω ∂P := fun k =>
      ((hmart k).1.setIntegral_eq hij hS).symm
    simp only [e] at h1
    exact tendsto_nhds_unique h1 h2
  exact ⟨hmartM, fun t => (hfat t).1, fun t => (hfat t).2⟩


/-- A martingale started at `0` (a.s.) has mean zero. -/
theorem integral_eq_zero_of_martingale [IsProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ P) (h0 : ∀ᵐ ω ∂P, M 0 ω = 0) (t : ℝ≥0) : ∫ ω, M t ω ∂P = 0 := by
  have h := hM.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ t) MeasurableSet.univ
  simp only [Measure.restrict_univ] at h
  rw [← h, integral_congr_ae h0, integral_zero]

end ComplexSLE.Infrastructure

namespace ComplexSLE

open Infrastructure

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}

/-- **Bounded bracket** (a.s. continuous paths). Let `M` be a continuous local martingale with
`M 0 = 0` such that `M² - ∫₀ˢ Γ` is a continuous local martingale, where `|Γ| ≤ K` and `∫₀ᵗ Γ` is
continuous in `t` and progressive. Then `M` is an `L²`-martingale (`E M_t² ≤ K t`, `E M_t = 0`)
and `M_s / s → 0` almost surely. -/
theorem IsContLocalMartingale.bounded_bracket [IsProbabilityMeasure P] {M Γ : ℝ≥0 → Ω → ℝ}
    {K : ℝ} (hK : 0 ≤ K) (hΓ : ∀ s ω, |Γ s ω| ≤ K)
    (hΓp : IsStronglyProgressive ℱ fun t ω => pathIntegral Γ t ω)
    (hIc : ∀ ω, Continuous fun t => pathIntegral Γ t ω) (hM : IsContLocalMartingale ℱ M P)
    (h0 : ∀ᵐ ω ∂P, M 0 ω = 0)
    (hN : IsContLocalMartingale ℱ (fun t ω => M t ω ^ 2 - pathIntegral Γ t ω) P) :
    (∀ t, Integrable (fun ω => M t ω ^ 2) P) ∧ (∀ t : ℝ≥0, ∫ ω, M t ω ^ 2 ∂P ≤ K * t) ∧
      (∀ t, ∫ ω, M t ω ∂P = 0) ∧
      ∀ᵐ ω ∂P, Tendsto (fun s : ℝ≥0 => M s ω / s) atTop (𝓝 0) := by
  let 𝒢 : Filtration ℝ≥0 m :=
    { seq := fun t => ℱ t ⊔ MeasurableSpace.generateFrom
        {N : Set Ω | MeasurableSet[m] N ∧ P N = 0}
      mono' := fun _ _ hst => sup_le_sup_right (ℱ.mono hst) _
      le' := fun t => sup_le (ℱ.le t) (MeasurableSpace.generateFrom_le fun _ hN => hN.1) }
  have h𝒢 : ∀ t, 𝒢 t = ℱ t ⊔ MeasurableSpace.generateFrom
      {N : Set Ω | MeasurableSet[m] N ∧ P N = 0} := fun t => rfl
  have hℱ𝒢 : ∀ t, ℱ t ≤ 𝒢 t := fun t => by rw [h𝒢]; exact le_sup_left
  obtain ⟨M', hMM', hM'c, hM'lm⟩ := hM.exists_continuous_version 𝒢 h𝒢
  -- the squared process is a local martingale for `𝒢`
  have hN𝒢 : IsContLocalMartingale 𝒢 (fun t ω => M t ω ^ 2 - pathIntegral Γ t ω) P :=
    IsContLocalMartingale.of_modification hℱ𝒢 (fun t => (h𝒢 t).le) (N := ∅)
      (@MeasurableSet.empty Ω (𝒢 0)) (measure_empty) hN (c := fun _ => 0) measurable_const
      (fun ω _ t => rfl) (fun ω hω => absurd hω (notMem_empty ω))
  have hpath𝒢 : IsStronglyProgressive 𝒢 fun t ω => pathIntegral Γ t ω :=
    StronglyAdapted.isStronglyProgressive_of_continuous
      (fun t => (hΓp.stronglyAdapted t).mono (hℱ𝒢 t)) hIc
  have hN' : IsContLocalMartingale 𝒢 (fun t ω => M' t ω ^ 2 - pathIntegral Γ t ω) P := by
    refine hN𝒢.congr_ae (fun i => ((hM'lm.1 i).pow 2).sub (hpath𝒢 i)) ?_
    filter_upwards [hMM'] with ω hω t
    rw [hω t]
  have h0' : ∀ᵐ ω ∂P, M' 0 ω = 0 := by
    filter_upwards [hMM', h0] with ω h1 h2
    rw [h1, h2]
  obtain ⟨hmart, hsq, hK2⟩ := martingale_of_bounded_bracket hK hΓ hM'lm hM'c h0' hIc hN'
  have hint : ∀ t, ∀ᵐ ω ∂P, M' t ω = M t ω := fun t => by
    filter_upwards [hMM'] with ω hω using hω t
  refine ⟨fun t => (hsq t).congr (by filter_upwards [hint t] with ω hω; rw [hω]), fun t => ?_,
    fun t => ?_, ?_⟩
  · have e : ∫ ω, M t ω ^ 2 ∂P = ∫ ω, M' t ω ^ 2 ∂P :=
      integral_congr_ae (by filter_upwards [hint t] with ω hω; rw [hω])
    rw [e]; exact hK2 t
  · have e : ∫ ω, M t ω ∂P = ∫ ω, M' t ω ∂P :=
      integral_congr_ae (by filter_upwards [hint t] with ω hω; rw [hω])
    rw [e]; exact integral_eq_zero_of_martingale hmart h0' t
  · have := ae_tendsto_div_of_second_moment hmart hsq hK2 (ae_of_all _ hM'c)
    filter_upwards [this, hMM'] with ω h1 h2
    simpa only [h2] using h1

end ComplexSLE

namespace ComplexSLE.Infrastructure

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}

/-- **Sections of a progressive process are measurable in time**: for every `ω`,
`s ↦ u s ω` is Borel measurable (on `[0, n]` by progressivity, then a countable union). -/
theorem measurable_time_of_isStronglyProgressive {u : ℝ≥0 → Ω → ℝ}
    (hu : IsStronglyProgressive ℱ u) (ω : Ω) : Measurable fun s : ℝ≥0 => u s ω := by
  have hn : ∀ n : ℕ, Measurable fun s : Set.Iic (n : ℝ≥0) => u s ω := fun n => by
    have h1 := (hu n).measurable
    have h2 : @Measurable (Set.Iic (n : ℝ≥0)) _ Subtype.instMeasurableSpace
        (Subtype.instMeasurableSpace.prod (ℱ n)) fun s : Set.Iic (n : ℝ≥0) => (s, ω) :=
      @Measurable.prodMk (Set.Iic (n : ℝ≥0)) Subtype.instMeasurableSpace (Set.Iic (n : ℝ≥0)) Ω
        Subtype.instMeasurableSpace (ℱ n) id (fun _ => ω) measurable_id measurable_const
    exact h1.comp h2
  intro B hB
  have : (fun s : ℝ≥0 => u s ω) ⁻¹' B =
      ⋃ n : ℕ, ((↑) : Set.Iic (n : ℝ≥0) → ℝ≥0) '' ((fun s : Set.Iic (n : ℝ≥0) => u s ω) ⁻¹' B) := by
    ext s
    simp only [mem_preimage, mem_iUnion, mem_image, Subtype.exists, mem_Iic, exists_and_right,
      exists_eq_right]
    constructor
    · intro hs
      exact ⟨⌈s⌉₊, Nat.le_ceil s, hs⟩
    · rintro ⟨n, hn, hs⟩
      exact hs
  rw [this]
  exact MeasurableSet.iUnion fun n => MeasurableSet.subtype_image measurableSet_Iic (hn n hB)

end ComplexSLE.Infrastructure
