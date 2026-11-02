/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.ItoReal
public import ComplexSLE.Infrastructure.Stochastic.LocalMartingaleAlgebra
public import ComplexSLE.Internal.Recurrence.HittingTime
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Exit of a diffusion from an interval: expectation bounds through the generator

Let `X` solve `dX = α(X) dt + β(X) dB` in martingale form (`IsDiffusionSolution`, everywhere
continuous paths) with `X₀ ∈ [l, u]` a.s., and let `R` be the exit time of `(l, u)`. For a `C²`
function `f` with generator `Lf = f'α + ½f''β²`, Itô's formula (`ito_formula`, through
`IsDiffusionSolution.isContLocalMartingale_generator`) and external-free optional stopping give

* `integral_stopped_generator_eq_zero`: `E[f(X_{t∧R}) - f(X₀) - ∫₀^{t∧R} Lf(X_s) ds] = 0`;
* `integral_comp_stopped_le` (`Lf ≤ 0` on `[l, u]`): `E f(X_{t∧R}) ≤ E f(X₀)`;
* `integral_min_exit_le` (`Lf ≤ -1` on `[l, u]`, `|f| ≤ C` there): `E[t ∧ R] ≤ 2C`, hence
  `P(R > T) ≤ 2C/T` (`measureReal_lt_exit_le`);
* `measureReal_exit_eq_right_le` (`Lf ≤ 0`, `f ≥ 0` on `[l, u]`):
  `f(u) · P(R ≤ T, X_R = u) ≤ E f(X₀)`;
* `measureReal_exit_eq_left_ge`: combining the last two,
  `P(R ≤ T, X_R = l) ≥ 1 - 2C/T - E f(X₀) / f(u)`.

This is the "work directly in `t̃`-time with the scale function and optional stopping" route of
ERRATA.md R27 for Lemma 2.16 (`step:rec-scale-function-hit`, `step:rec-hit-fixed-y`), replacing
the time change `ω(r)` of paper.tex:L1192-1208 and the finiteness of `ω(R)` omitted at L1226 by
the Lyapunov bound `E[R] ≤ 2C`. Everything uses `ito_formula` (proved in-project).
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
open ComplexSLE.Internal (generator continuous_generator)

namespace ComplexSLE.Recurrence

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ≥0 mΩ} {α β : ℝ → ℝ} {X : ℝ≥0 → Ω → ℝ} {l u : ℝ}

/-! ### Path integrals -/

omit [IsProbabilityMeasure P] in
/-- `t ↦ ∫₀ᵗ g(X_s) ds` is continuous along a continuous path. -/
theorem continuous_pathIntegral_comp {g : ℝ → ℝ} (hg : Continuous g) {ω : Ω}
    (hXc : Continuous fun t => X t ω) :
    Continuous fun t : ℝ≥0 => pathIntegral (fun s ω => g (X s ω)) t ω := by
  have hc : Continuous fun r : ℝ => g (X (Real.toNNReal r) ω) :=
    hg.comp (hXc.comp continuous_real_toNNReal)
  exact (intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) 0).comp
    NNReal.continuous_coe

omit [IsProbabilityMeasure P] in
/-- `|∫₀ᵗ ξ_s ds| ≤ C t` when `|ξ_s| ≤ C` for `s ≤ t`. -/
theorem abs_pathIntegral_le_of_le {ξ : ℝ≥0 → Ω → ℝ} {C : ℝ} {ω : Ω} {t : ℝ≥0}
    (hξ : ∀ s ≤ t, |ξ s ω| ≤ C) : |pathIntegral ξ t ω| ≤ C * t := by
  unfold pathIntegral
  have := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun s : ℝ => ξ (Real.toNNReal s) ω) (a := 0) (b := t) (C := C) fun s hs => by
      have hst : s ≤ t := by
        rcases Set.mem_uIoc.1 hs with h | h
        · exact h.2
        · linarith [h.1, NNReal.coe_nonneg t]
      simpa [Real.norm_eq_abs] using hξ _ (Real.toNNReal_le_iff_le_coe.2 hst)
  simpa [Real.norm_eq_abs, abs_of_nonneg t.2] using this

omit [IsProbabilityMeasure P] in
/-- `∫₀ᵗ g(X_s) ds ≤ C t` when `g(X_s) ≤ C` for `s ≤ t` (continuous `g`, continuous path). -/
theorem pathIntegral_comp_le_of_le {g : ℝ → ℝ} (hg : Continuous g) {ω : Ω}
    (hXc : Continuous fun t => X t ω) {C : ℝ} {t : ℝ≥0} (hξ : ∀ s ≤ t, g (X s ω) ≤ C) :
    pathIntegral (fun s ω => g (X s ω)) t ω ≤ C * t := by
  unfold pathIntegral
  have hc : Continuous fun r : ℝ => g (X (Real.toNNReal r) ω) :=
    hg.comp (hXc.comp continuous_real_toNNReal)
  calc ∫ s in (0 : ℝ)..(t : ℝ), g (X (Real.toNNReal s) ω)
      ≤ ∫ _ in (0 : ℝ)..(t : ℝ), C :=
        intervalIntegral.integral_mono_on t.2 (hc.intervalIntegrable _ _) intervalIntegrable_const
          fun s hs => hξ _ (Real.toNNReal_le_iff_le_coe.2 hs.2)
    _ = C * t := by simp [mul_comm]

/-! ### The time `t ∧ R` -/

/-- `((t ∧ r).untopA : WithTop ℝ≥0) = t ∧ r`. -/
theorem coe_untopA_min (t : ℝ≥0) (r : WithTop ℝ≥0) :
    (((min (t : WithTop ℝ≥0) r).untopA : ℝ≥0) : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) r := by
  have hne : min (t : WithTop ℝ≥0) r ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop]

theorem untopA_min_le (t : ℝ≥0) (r : WithTop ℝ≥0) : (min (t : WithTop ℝ≥0) r).untopA ≤ t :=
  WithTop.untopA_le (min_le_left _ _)

theorem coe_untopA_min_le_right (t : ℝ≥0) (r : WithTop ℝ≥0) :
    (((min (t : WithTop ℝ≥0) r).untopA : ℝ≥0) : WithTop ℝ≥0) ≤ r := by
  rw [coe_untopA_min]; exact min_le_right _ _

theorem untopA_min_eq_of_lt {t : ℝ≥0} {r : WithTop ℝ≥0} (h : (t : WithTop ℝ≥0) < r) :
    (min (t : WithTop ℝ≥0) r).untopA = t := by
  rw [min_eq_left h.le]; rfl

theorem untopA_min_eq_of_le {t : ℝ≥0} {r : WithTop ℝ≥0} (h : r ≤ t) :
    (min (t : WithTop ℝ≥0) r).untopA = r.untopA := by
  rw [min_eq_right h]

/-! ### Itô's formula at the stopped time -/

section Stopped

variable (hX : IsDiffusionSolution ℱ α β X P) (hXc : ∀ ω, Continuous fun t => X t ω)

include hX hXc

omit [IsProbabilityMeasure P] in
/-- The exit time of `(l, u)` is a stopping time. -/
theorem isStoppingTime_exit_of_diffusion (l u : ℝ) :
    IsStoppingTime ℱ (hittingAfter X (Ioo l u)ᶜ 0) :=
  isStoppingTime_exit hX.1.stronglyAdapted hXc l u

omit [IsProbabilityMeasure P] in
/-- `ω ↦ (t ∧ R ω).untopA` is measurable. -/
theorem measurable_untopA_min_exit (l u : ℝ) (t : ℝ≥0) :
    Measurable fun ω => (min (t : WithTop ℝ≥0) (hittingAfter X (Ioo l u)ᶜ 0 ω)).untopA :=
  (measurable_const.min (isStoppingTime_exit_of_diffusion hX hXc l u).measurable').untopA

omit [IsProbabilityMeasure P] in
/-- `ω ↦ X_{t∧R} ω` is measurable. -/
theorem measurable_stoppedProcess_exit (l u : ℝ) (t : ℝ≥0) :
    Measurable fun ω => X (min (t : WithTop ℝ≥0) (hittingAfter X (Ioo l u)ᶜ 0 ω)).untopA ω :=
  ((hX.1.stronglyAdapted_stoppedProcess (isStoppingTime_exit_of_diffusion hX hXc l u) t).mono
    (ℱ.le t)).measurable

omit [IsProbabilityMeasure P] in
/-- The stopped value `X_R` is measurable. -/
theorem measurable_stoppedValue_exit (l u : ℝ) :
    Measurable (stoppedValue X (hittingAfter X (Ioo l u)ᶜ 0)) :=
  (measurable_stoppedValue hX.1 (isStoppingTime_exit_of_diffusion hX hXc l u)).mono
    (isStoppingTime_exit_of_diffusion hX hXc l u).measurableSpace_le le_rfl

/-- **Itô's formula at the stopped time `t ∧ R`** (`R` the exit time of `(l, u)`, start in
`[l, u]`): `E[f(X_{t∧R}) - f(X₀) - ∫₀^{t∧R} Lf(X_s) ds] = 0` for `f ∈ C²`. The stopped local
martingale is bounded on `[0, t]` because the path stays in `[l, u]` up to `R`. -/
theorem integral_stopped_generator_eq_zero (hα : Continuous α) (hβ : Continuous β)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (h0 : ∀ᵐ ω ∂P, X 0 ω ∈ Icc l u) (t : ℝ≥0) :
    ∫ ω, (f (X (min (t : WithTop ℝ≥0) (hittingAfter X (Ioo l u)ᶜ 0 ω)).untopA ω) - f (X 0 ω) -
      pathIntegral (fun s ω => generator α β f (X s ω))
        (min (t : WithTop ℝ≥0) (hittingAfter X (Ioo l u)ᶜ 0 ω)).untopA ω) ∂P = 0 := by
  set R := hittingAfter X (Ioo l u)ᶜ 0 with hR
  set L := generator α β f with hL
  set N : ℝ≥0 → Ω → ℝ := fun t ω =>
    f (X t ω) - f (X 0 ω) - pathIntegral (fun s ω => L (X s ω)) t ω with hN
  have hNlm : IsContLocalMartingale ℱ N P :=
    Internal.IsDiffusionSolution.isContLocalMartingale_generator hX hXc hα hβ hf
  have hLc : Continuous L := continuous_generator hα hβ hf
  have hNc : ∀ ω, Continuous fun t => N t ω := fun ω =>
    ((hf.continuous.comp (hXc ω)).sub continuous_const).sub
      (continuous_pathIntegral_comp hLc (hXc ω))
  have hRst : IsStoppingTime ℱ R := isStoppingTime_exit_of_diffusion hX hXc l u
  have hstop : IsContLocalMartingale ℱ (stoppedProcess N R) P :=
    hNlm.stoppedProcess_of_continuous hNc hRst
  obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf.continuous.continuousOn (s := Icc l u))
  obtain ⟨CL, hCL⟩ := isCompact_Icc.exists_bound_of_continuousOn (hLc.continuousOn (s := Icc l u))
  have hzero := Infrastructure.IsContLocalMartingale.integral_eq_zero hstop (fun ω => ?_) (t := t)
    (C := 2 * Cf + max CL 0 * t) ?_
  · have : (fun ω => stoppedProcess N R t ω) = fun ω =>
        f (X (min (t : WithTop ℝ≥0) (R ω)).untopA ω) - f (X 0 ω) -
          pathIntegral (fun s ω => L (X s ω)) (min (t : WithTop ℝ≥0) (R ω)).untopA ω := by
      funext ω; rfl
    rw [← this]
    exact hzero
  · -- `N^R_0 = 0`
    rw [stoppedProcess_eq_of_le (by simp)]
    simp [hN, pathIntegral]
  · -- the bound on `[0, t]`
    filter_upwards [h0] with ω hω s hs
    set ρ := (min (s : WithTop ℝ≥0) (R ω)).untopA with hρ
    have hρs : ρ ≤ s := untopA_min_le s (R ω)
    have hρR : (ρ : WithTop ℝ≥0) ≤ R ω := coe_untopA_min_le_right s (R ω)
    have hmem : ∀ r ≤ ρ, X r ω ∈ Icc l u := fun r hr =>
      mem_Icc_of_le_exit (hXc ω) hω ((WithTop.coe_le_coe.2 hr).trans hρR)
    have hI : |pathIntegral (fun s ω => L (X s ω)) ρ ω| ≤ max CL 0 * ρ :=
      abs_pathIntegral_le_of_le fun r hr =>
        (le_trans (by simpa [Real.norm_eq_abs] using hCL _ (hmem r hr)) (le_max_left _ _))
    have h1 : |f (X ρ ω)| ≤ Cf := by simpa [Real.norm_eq_abs] using hCf _ (hmem ρ le_rfl)
    have h2 : |f (X 0 ω)| ≤ Cf := by simpa [Real.norm_eq_abs] using hCf _ hω
    have h3 : max CL 0 * (ρ : ℝ) ≤ max CL 0 * s :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hρs) (le_max_right _ _)
    have h4 : max CL 0 * (s : ℝ) ≤ max CL 0 * t :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hs) (le_max_right _ _)
    change |N ρ ω| ≤ 2 * Cf + max CL 0 * t
    calc |f (X ρ ω) - f (X 0 ω) - pathIntegral (fun s ω => L (X s ω)) ρ ω|
        ≤ |f (X ρ ω) - f (X 0 ω)| + |pathIntegral (fun s ω => L (X s ω)) ρ ω| := abs_sub _ _
      _ ≤ (|f (X ρ ω)| + |f (X 0 ω)|) + max CL 0 * ρ := add_le_add (abs_sub _ _) hI
      _ ≤ 2 * Cf + max CL 0 * t := by linarith

/-- Integrability of `f(X_{t∧R}) - f(X₀)` for continuous `f` (bounded on `[l, u]`). -/
theorem integrable_comp_stopped_sub {f : ℝ → ℝ} (hf : Continuous f)
    (h0 : ∀ᵐ ω ∂P, X 0 ω ∈ Icc l u) (t : ℝ≥0) :
    Integrable (fun ω =>
      f (X (min (t : WithTop ℝ≥0) (hittingAfter X (Ioo l u)ᶜ 0 ω)).untopA ω) - f (X 0 ω)) P := by
  obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn (hf.continuousOn (s := Icc l u))
  refine (integrable_const (2 * Cf)).mono' ?_ ?_
  · exact ((hf.measurable.comp (measurable_stoppedProcess_exit hX hXc l u t)).sub
      (hf.measurable.comp (Internal.IsDiffusionSolution.measurable hX 0))).aestronglyMeasurable
  · filter_upwards [h0] with ω hω
    have hmem : X (min (t : WithTop ℝ≥0) (hittingAfter X (Ioo l u)ᶜ 0 ω)).untopA ω ∈ Icc l u :=
      mem_Icc_of_le_exit (hXc ω) hω (coe_untopA_min_le_right _ _)
    have h1 := hCf _ hmem
    have h2 := hCf _ hω
    rw [Real.norm_eq_abs] at h1 h2 ⊢
    calc |f _ - f (X 0 ω)| ≤ |f _| + |f (X 0 ω)| := abs_sub _ _
      _ ≤ 2 * Cf := by linarith

/-- **Supermartingale bound.** If `Lf ≤ 0` on `[l, u]` then `E f(X_{t∧R}) ≤ E f(X₀)`. -/
theorem integral_comp_stopped_le (hα : Continuous α) (hβ : Continuous β)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hLf : ∀ v ∈ Icc l u, generator α β f v ≤ 0) (h0 : ∀ᵐ ω ∂P, X 0 ω ∈ Icc l u) (t : ℝ≥0) :
    ∫ ω, f (X (min (t : WithTop ℝ≥0) (hittingAfter X (Ioo l u)ᶜ 0 ω)).untopA ω) ∂P ≤
      ∫ ω, f (X 0 ω) ∂P := by
  have hzero := integral_stopped_generator_eq_zero hX hXc hα hβ hf h0 t
  have hint1 := integrable_comp_stopped_sub hX hXc hf.continuous h0 t
  have hLc : Continuous (generator α β f) := continuous_generator hα hβ hf
  set R := hittingAfter X (Ioo l u)ᶜ 0 with hR
  -- the full Itô expression is integrable: it is the stopped local martingale
  have hint2 : Integrable (fun ω =>
      f (X (min (t : WithTop ℝ≥0) (R ω)).untopA ω) - f (X 0 ω) -
        pathIntegral (fun s ω => generator α β f (X s ω)) (min (t : WithTop ℝ≥0) (R ω)).untopA ω)
      P := by
    obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hf.continuous.continuousOn (s := Icc l u))
    obtain ⟨CL, hCL⟩ := isCompact_Icc.exists_bound_of_continuousOn (hLc.continuousOn (s := Icc l u))
    refine (integrable_const (2 * Cf + max CL 0 * t)).mono' ?_ ?_
    · set N : ℝ≥0 → Ω → ℝ := fun t ω => f (X t ω) - f (X 0 ω) -
        pathIntegral (fun s ω => generator α β f (X s ω)) t ω with hN
      have hNlm : IsContLocalMartingale ℱ N P :=
    Internal.IsDiffusionSolution.isContLocalMartingale_generator hX hXc hα hβ hf
      have hRst : IsStoppingTime ℱ R := isStoppingTime_exit_of_diffusion hX hXc l u
      exact ((hNlm.1.stronglyAdapted_stoppedProcess hRst t).mono (ℱ.le t)).aestronglyMeasurable
    · filter_upwards [h0] with ω hω
      set ρ := (min (t : WithTop ℝ≥0) (R ω)).untopA with hρ
      have hρt : ρ ≤ t := untopA_min_le t (R ω)
      have hρR : (ρ : WithTop ℝ≥0) ≤ R ω := coe_untopA_min_le_right t (R ω)
      have hmem : ∀ r ≤ ρ, X r ω ∈ Icc l u := fun r hr =>
        mem_Icc_of_le_exit (hXc ω) hω ((WithTop.coe_le_coe.2 hr).trans hρR)
      have hI : |pathIntegral (fun s ω => generator α β f (X s ω)) ρ ω| ≤ max CL 0 * ρ :=
        abs_pathIntegral_le_of_le fun r hr =>
          (le_trans (by simpa [Real.norm_eq_abs] using hCL _ (hmem r hr)) (le_max_left _ _))
      have h1 : |f (X ρ ω)| ≤ Cf := by simpa [Real.norm_eq_abs] using hCf _ (hmem ρ le_rfl)
      have h2 : |f (X 0 ω)| ≤ Cf := by simpa [Real.norm_eq_abs] using hCf _ hω
      have h3 : max CL 0 * (ρ : ℝ) ≤ max CL 0 * t :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hρt) (le_max_right _ _)
      rw [Real.norm_eq_abs]
      calc |f (X ρ ω) - f (X 0 ω) - pathIntegral (fun s ω => generator α β f (X s ω)) ρ ω|
          ≤ |f (X ρ ω) - f (X 0 ω)| +
            |pathIntegral (fun s ω => generator α β f (X s ω)) ρ ω| := abs_sub _ _
        _ ≤ (|f (X ρ ω)| + |f (X 0 ω)|) + max CL 0 * ρ := add_le_add (abs_sub _ _) hI
        _ ≤ 2 * Cf + max CL 0 * t := by linarith
  -- pointwise: the path integral is `≤ 0`
  have hmono : ∫ ω, (f (X (min (t : WithTop ℝ≥0) (R ω)).untopA ω) - f (X 0 ω)) ∂P ≤
      ∫ ω, (f (X (min (t : WithTop ℝ≥0) (R ω)).untopA ω) - f (X 0 ω) -
        pathIntegral (fun s ω => generator α β f (X s ω))
          (min (t : WithTop ℝ≥0) (R ω)).untopA ω) ∂P := by
    refine integral_mono_ae hint1 hint2 ?_
    filter_upwards [h0] with ω hω
    set ρ := (min (t : WithTop ℝ≥0) (R ω)).untopA with hρ
    have hρR : (ρ : WithTop ℝ≥0) ≤ R ω := coe_untopA_min_le_right t (R ω)
    have hI : pathIntegral (fun s ω => generator α β f (X s ω)) ρ ω ≤ 0 * ρ :=
      pathIntegral_comp_le_of_le hLc (hXc ω) fun r hr =>
        hLf _ (mem_Icc_of_le_exit (hXc ω) hω ((WithTop.coe_le_coe.2 hr).trans hρR))
    simp only [zero_mul] at hI
    linarith
  rw [hzero] at hmono
  have hint0 : Integrable (fun ω => f (X 0 ω)) P := by
    obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hf.continuous.continuousOn (s := Icc l u))
    refine (integrable_const Cf).mono' (hf.continuous.measurable.comp
      (Internal.IsDiffusionSolution.measurable hX 0)).aestronglyMeasurable ?_
    filter_upwards [h0] with ω hω using hCf _ hω
  have hintρ : Integrable (fun ω => f (X (min (t : WithTop ℝ≥0) (R ω)).untopA ω)) P := by
    have := hint1.add hint0
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp
  rw [integral_sub hintρ hint0] at hmono
  linarith

/-- **Lyapunov bound.** If `Lf ≤ -1` and `|f| ≤ C` on `[l, u]`, then `E[t ∧ R] ≤ 2C`. -/
theorem integral_min_exit_le (hα : Continuous α) (hβ : Continuous β)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hLf : ∀ v ∈ Icc l u, generator α β f v ≤ -1) {C : ℝ} (hfb : ∀ v ∈ Icc l u, |f v| ≤ C)
    (h0 : ∀ᵐ ω ∂P, X 0 ω ∈ Icc l u) (t : ℝ≥0) :
    ∫ ω, (((min (t : WithTop ℝ≥0) (hittingAfter X (Ioo l u)ᶜ 0 ω)).untopA : ℝ≥0) : ℝ) ∂P ≤
      2 * C := by
  have hzero := integral_stopped_generator_eq_zero hX hXc hα hβ hf h0 t
  have hLc : Continuous (generator α β f) := continuous_generator hα hβ hf
  have hint1 := integrable_comp_stopped_sub hX hXc hf.continuous h0 t
  set R := hittingAfter X (Ioo l u)ᶜ 0 with hR
  have hintρ : Integrable (fun ω =>
      (((min (t : WithTop ℝ≥0) (R ω)).untopA : ℝ≥0) : ℝ)) P := by
    refine (integrable_const (t : ℝ)).mono' (measurable_coe_nnreal_real.comp
      (measurable_untopA_min_exit hX hXc l u t)).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
    exact_mod_cast untopA_min_le t (R ω)
  -- the Itô expression is integrable (it has zero integral and dominates the sum below)
  have hint2 : Integrable (fun ω =>
      f (X (min (t : WithTop ℝ≥0) (R ω)).untopA ω) - f (X 0 ω) -
        pathIntegral (fun s ω => generator α β f (X s ω)) (min (t : WithTop ℝ≥0) (R ω)).untopA ω)
      P := by
    obtain ⟨CL, hCL⟩ := isCompact_Icc.exists_bound_of_continuousOn (hLc.continuousOn (s := Icc l u))
    refine (integrable_const (2 * C + max CL 0 * t)).mono' ?_ ?_
    · set N : ℝ≥0 → Ω → ℝ := fun t ω => f (X t ω) - f (X 0 ω) -
        pathIntegral (fun s ω => generator α β f (X s ω)) t ω with hN
      have hNlm : IsContLocalMartingale ℱ N P :=
    Internal.IsDiffusionSolution.isContLocalMartingale_generator hX hXc hα hβ hf
      have hRst : IsStoppingTime ℱ R := isStoppingTime_exit_of_diffusion hX hXc l u
      exact ((hNlm.1.stronglyAdapted_stoppedProcess hRst t).mono (ℱ.le t)).aestronglyMeasurable
    · filter_upwards [h0] with ω hω
      set ρ := (min (t : WithTop ℝ≥0) (R ω)).untopA with hρ
      have hρt : ρ ≤ t := untopA_min_le t (R ω)
      have hρR : (ρ : WithTop ℝ≥0) ≤ R ω := coe_untopA_min_le_right t (R ω)
      have hmem : ∀ r ≤ ρ, X r ω ∈ Icc l u := fun r hr =>
        mem_Icc_of_le_exit (hXc ω) hω ((WithTop.coe_le_coe.2 hr).trans hρR)
      have hI : |pathIntegral (fun s ω => generator α β f (X s ω)) ρ ω| ≤ max CL 0 * ρ :=
        abs_pathIntegral_le_of_le fun r hr =>
          (le_trans (by simpa [Real.norm_eq_abs] using hCL _ (hmem r hr)) (le_max_left _ _))
      have h1 : |f (X ρ ω)| ≤ C := hfb _ (hmem ρ le_rfl)
      have h2 : |f (X 0 ω)| ≤ C := hfb _ hω
      have h3 : max CL 0 * (ρ : ℝ) ≤ max CL 0 * t :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hρt) (le_max_right _ _)
      rw [Real.norm_eq_abs]
      calc |f (X ρ ω) - f (X 0 ω) - pathIntegral (fun s ω => generator α β f (X s ω)) ρ ω|
          ≤ |f (X ρ ω) - f (X 0 ω)| +
            |pathIntegral (fun s ω => generator α β f (X s ω)) ρ ω| := abs_sub _ _
        _ ≤ (|f (X ρ ω)| + |f (X 0 ω)|) + max CL 0 * ρ := add_le_add (abs_sub _ _) hI
        _ ≤ 2 * C + max CL 0 * t := by linarith
  -- pointwise: `∫₀^ρ Lf(X) ≤ -ρ`, so `f(X_ρ) - f(X_0) + ρ ≤` the Itô expression
  have hmono : ∫ ω, ((f (X (min (t : WithTop ℝ≥0) (R ω)).untopA ω) - f (X 0 ω)) +
      (((min (t : WithTop ℝ≥0) (R ω)).untopA : ℝ≥0) : ℝ)) ∂P ≤
      ∫ ω, (f (X (min (t : WithTop ℝ≥0) (R ω)).untopA ω) - f (X 0 ω) -
        pathIntegral (fun s ω => generator α β f (X s ω))
          (min (t : WithTop ℝ≥0) (R ω)).untopA ω) ∂P := by
    refine integral_mono_ae (hint1.add hintρ) hint2 ?_
    filter_upwards [h0] with ω hω
    set ρ := (min (t : WithTop ℝ≥0) (R ω)).untopA with hρ
    have hρR : (ρ : WithTop ℝ≥0) ≤ R ω := coe_untopA_min_le_right t (R ω)
    have hI : pathIntegral (fun s ω => generator α β f (X s ω)) ρ ω ≤ -1 * ρ :=
      pathIntegral_comp_le_of_le hLc (hXc ω) fun r hr =>
        hLf _ (mem_Icc_of_le_exit (hXc ω) hω ((WithTop.coe_le_coe.2 hr).trans hρR))
    linarith
  rw [hzero, integral_add hint1 hintρ] at hmono
  -- `E[f(X_0) - f(X_ρ)] ≤ 2C`
  have hb : ∫ ω, (f (X (min (t : WithTop ℝ≥0) (R ω)).untopA ω) - f (X 0 ω)) ∂P ≥ -(2 * C) := by
    have := integral_mono_ae (integrable_const (-(2 * C))) hint1 ?_
    · simpa using this
    filter_upwards [h0] with ω hω
    have h1 : |f (X (min (t : WithTop ℝ≥0) (R ω)).untopA ω)| ≤ C :=
      hfb _ (mem_Icc_of_le_exit (hXc ω) hω (coe_untopA_min_le_right t (R ω)))
    have h2 : |f (X 0 ω)| ≤ C := hfb _ hω
    have := abs_le.1 h1
    have := abs_le.1 h2
    linarith
  linarith

/-- **Tail bound for the exit time**: `P(R > T) ≤ 2C/T` under the Lyapunov hypotheses. -/
theorem measureReal_lt_exit_le (hα : Continuous α) (hβ : Continuous β)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hLf : ∀ v ∈ Icc l u, generator α β f v ≤ -1) {C : ℝ} (hfb : ∀ v ∈ Icc l u, |f v| ≤ C)
    (h0 : ∀ᵐ ω ∂P, X 0 ω ∈ Icc l u) {T : ℝ≥0} (hT : 0 < T) :
    P.real {ω | (T : WithTop ℝ≥0) < hittingAfter X (Ioo l u)ᶜ 0 ω} ≤ 2 * C / T := by
  set R := hittingAfter X (Ioo l u)ᶜ 0 with hR
  have hE := integral_min_exit_le hX hXc hα hβ hf hLf hfb h0 T
  have hRst : IsStoppingTime ℱ R := isStoppingTime_exit_of_diffusion hX hXc l u
  have hmeas : MeasurableSet {ω | (T : WithTop ℝ≥0) < R ω} :=
    ℱ.le T _ (hRst.measurableSet_gt T)
  have hintρ : Integrable (fun ω => (((min (T : WithTop ℝ≥0) (R ω)).untopA : ℝ≥0) : ℝ)) P := by
    refine (integrable_const (T : ℝ)).mono' (measurable_coe_nnreal_real.comp
      (measurable_untopA_min_exit hX hXc l u T)).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
    exact_mod_cast untopA_min_le T (R ω)
  have hind : ∫ ω, {ω | (T : WithTop ℝ≥0) < R ω}.indicator (fun _ => (T : ℝ)) ω ∂P ≤
      ∫ ω, (((min (T : WithTop ℝ≥0) (R ω)).untopA : ℝ≥0) : ℝ) ∂P := by
    refine integral_mono_ae ((integrable_const _).indicator hmeas) hintρ
      (Eventually.of_forall fun ω => ?_)
    by_cases hω : (T : WithTop ℝ≥0) < R ω
    · simp only [indicator_of_mem (show ω ∈ {ω | (T : WithTop ℝ≥0) < R ω} from hω)]
      rw [untopA_min_eq_of_lt hω]
    · simp only [indicator_of_notMem (show ω ∉ {ω | (T : WithTop ℝ≥0) < R ω} from hω)]
      exact NNReal.coe_nonneg _
  rw [integral_indicator_const _ hmeas, smul_eq_mul] at hind
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  rw [le_div_iff₀ hTpos]
  linarith

/-- **Upper bound on exiting at the right endpoint.** If `Lf ≤ 0` and `f ≥ 0` on `[l, u]` then
`f(u) · P(R ≤ T, X_R = u) ≤ E f(X₀)`. -/
theorem measureReal_exit_eq_right_le (hα : Continuous α) (hβ : Continuous β)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hLf : ∀ v ∈ Icc l u, generator α β f v ≤ 0) (hf0 : ∀ v ∈ Icc l u, 0 ≤ f v)
    (h0 : ∀ᵐ ω ∂P, X 0 ω ∈ Icc l u) (T : ℝ≥0) :
    f u * P.real {ω | hittingAfter X (Ioo l u)ᶜ 0 ω ≤ T ∧
      stoppedValue X (hittingAfter X (Ioo l u)ᶜ 0) ω = u} ≤ ∫ ω, f (X 0 ω) ∂P := by
  set R := hittingAfter X (Ioo l u)ᶜ 0 with hR
  have hle := integral_comp_stopped_le hX hXc hα hβ hf hLf h0 T
  have hRst : IsStoppingTime ℱ R := isStoppingTime_exit_of_diffusion hX hXc l u
  set E := {ω | R ω ≤ T ∧ stoppedValue X R ω = u} with hE
  have hmeas : MeasurableSet E :=
    (ℱ.le T _ (hRst.measurableSet_le T)).inter
      ((measurable_stoppedValue_exit hX hXc l u) (measurableSet_singleton u))
  have hintρ : Integrable (fun ω => f (X (min (T : WithTop ℝ≥0) (R ω)).untopA ω)) P := by
    obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hf.continuous.continuousOn (s := Icc l u))
    refine (integrable_const Cf).mono' (hf.continuous.measurable.comp
      (measurable_stoppedProcess_exit hX hXc l u T)).aestronglyMeasurable ?_
    filter_upwards [h0] with ω hω
    exact hCf _ (mem_Icc_of_le_exit (hXc ω) hω (coe_untopA_min_le_right T (R ω)))
  have hind : ∫ ω, E.indicator (fun _ => f u) ω ∂P ≤
      ∫ ω, f (X (min (T : WithTop ℝ≥0) (R ω)).untopA ω) ∂P := by
    refine integral_mono_ae ((integrable_const _).indicator hmeas) hintρ ?_
    filter_upwards [h0] with ω hω
    by_cases hωE : ω ∈ E
    · rw [indicator_of_mem hωE]
      obtain ⟨h1, h2⟩ := hωE
      rw [untopA_min_eq_of_le h1]
      exact (congrArg f h2).symm.le
    · rw [indicator_of_notMem hωE]
      exact hf0 _ (mem_Icc_of_le_exit (hXc ω) hω (coe_untopA_min_le_right T (R ω)))
  rw [integral_indicator_const _ hmeas, smul_eq_mul, mul_comm] at hind
  exact hind.trans hle

/-- **Lower bound on exiting at the left endpoint by time `T`.** With a Lyapunov function `g`
(`Lg ≤ -1`, `|g| ≤ C` on `[l, u]`) and a supermartingale function `f` (`Lf ≤ 0`, `f ≥ 0` on
`[l, u]`, `f(u) > 0`),
`P(R ≤ T, X_R = l) ≥ 1 - 2C/T - E f(X₀) / f(u)`. -/
theorem measureReal_exit_eq_left_ge (hα : Continuous α) (hβ : Continuous β) (hlu : l < u)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hLg : ∀ v ∈ Icc l u, generator α β g v ≤ -1) {C : ℝ} (hgb : ∀ v ∈ Icc l u, |g v| ≤ C)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hLf : ∀ v ∈ Icc l u, generator α β f v ≤ 0)
    (hf0 : ∀ v ∈ Icc l u, 0 ≤ f v) (hfu : 0 < f u)
    (h0 : ∀ᵐ ω ∂P, X 0 ω ∈ Icc l u) {T : ℝ≥0} (hT : 0 < T) :
    1 - 2 * C / T - (∫ ω, f (X 0 ω) ∂P) / f u ≤
      P.real {ω | hittingAfter X (Ioo l u)ᶜ 0 ω ≤ T ∧
        stoppedValue X (hittingAfter X (Ioo l u)ᶜ 0) ω = l} := by
  have htail := measureReal_lt_exit_le hX hXc hα hβ hg hLg hgb h0 hT
  have hright := measureReal_exit_eq_right_le hX hXc hα hβ hf hLf hf0 h0 T
  set R := hittingAfter X (Ioo l u)ᶜ 0 with hR
  have hRst : IsStoppingTime ℱ R := isStoppingTime_exit_of_diffusion hX hXc l u
  have hmeasV : Measurable (stoppedValue X R) := measurable_stoppedValue_exit hX hXc l u
  have hmeasT : MeasurableSet {ω | R ω ≤ T} := ℱ.le T _ (hRst.measurableSet_le T)
  set El := {ω | R ω ≤ T ∧ stoppedValue X R ω = l} with hEl
  set Eu := {ω | R ω ≤ T ∧ stoppedValue X R ω = u} with hEu
  have hmeasl : MeasurableSet El := hmeasT.inter (hmeasV (measurableSet_singleton l))
  have hmeasu : MeasurableSet Eu := hmeasT.inter (hmeasV (measurableSet_singleton u))
  -- `{R ≤ T} ⊆ El ∪ Eu` a.e.
  have hsub : {ω | R ω ≤ T} ≤ᵐ[P] El ∪ Eu := by
    filter_upwards [h0] with ω hω hωT
    have hne : R ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hωT
    rcases stoppedValue_exit_mem (hXc ω) hω hne with h | h
    · exact Or.inl ⟨hωT, h⟩
    · exact Or.inr ⟨hωT, h⟩
  have hdisj : Disjoint El Eu := by
    rw [Set.disjoint_left]
    rintro ω ⟨-, h1⟩ ⟨-, h2⟩
    exact hlu.ne (h1.symm.trans h2)
  have h1 : P.real {ω | R ω ≤ T} ≤ P.real El + P.real Eu := by
    rw [← measureReal_union hdisj hmeasu]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  have h2 : P.real {ω | R ω ≤ T} = 1 - P.real {ω | (T : WithTop ℝ≥0) < R ω} := by
    have hc : {ω | (T : WithTop ℝ≥0) < R ω} = {ω | R ω ≤ T}ᶜ := by
      ext ω; simp only [mem_ofPred_eq, mem_compl_iff, not_le]
    rw [hc, measureReal_compl hmeasT, probReal_univ]; ring
  have h3 : P.real Eu ≤ (∫ ω, f (X 0 ω) ∂P) / f u := by
    rw [le_div_iff₀ hfu, mul_comm]; exact hright
  linarith

end Stopped

end ComplexSLE.Recurrence

end
