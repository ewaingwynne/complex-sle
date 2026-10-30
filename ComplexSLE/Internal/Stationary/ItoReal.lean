/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.External.ItoFormula
public import ComplexSLE.Infrastructure.Stochastic.Stationary_LocalMartingale
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Itô's formula for a real diffusion, in expectation

The scalar case of the EXTERNAL `ito_formula` (`step:kol-ito-expectation`, paper.tex:L2365-2375):
for `X` an `IsDiffusionSolution ℱ α β X P` with everywhere-continuous paths and `f` of class `C²`,

* `IsDiffusionSolution.isContLocalMartingale_generator`:
  `f(X_t) - f(X_0) - ∫₀ᵗ (Lf)(X_s) ds` is a continuous local martingale, where
  `Lf = f'α + ½f''β²` is `generator α β f`;
* `IsDiffusionSolution.integral_sub_integral_eq`: if `f` and `Lf` are bounded then
  `E f(X_t) - E f(X_0) = E ∫₀ᵗ (Lf)(X_s) ds`;
* `IsDiffusionSolution.hasDerivWithinAt_integral_comp`: the right derivative at `t = 0` of
  `t ↦ E f(X_t)` is `E (Lf)(X_0)` (the differentiation step of `step:kol-derivative-at-zero`,
  by dominated convergence along the path continuity instead of Fubini);
* `IsDiffusionSolution.lipschitzWith_integral_comp`: `t ↦ E f(X_t)` is Lipschitz.

Everything consumes `ito_formula`, so is `PROVED_REL{ito_formula}`.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Internal

/-- The generator `Lf = f'α + ½f''β²` of the diffusion `dX = α(X) dt + β(X) dB`. -/
@[expose] noncomputable def generator (α β f : ℝ → ℝ) (u : ℝ) : ℝ :=
  deriv f u * α u + (1 / 2) * deriv (deriv f) u * β u ^ 2

theorem continuous_generator {α β f : ℝ → ℝ} (hα : Continuous α) (hβ : Continuous β)
    (hf : ContDiff ℝ 2 f) : Continuous (generator α β f) := by
  have h1 : Continuous (deriv f) := hf.continuous_deriv one_le_two
  have h2 : Continuous (deriv (deriv f)) := hf.deriv'.continuous_deriv_one
  unfold generator; fun_prop

/-! ### Derivatives of `f ∘ (x ↦ x 0)` on `Fin 1 → ℝ` -/

/-- The coordinate projection `(Fin 1 → ℝ) →L[ℝ] ℝ`. -/
noncomputable abbrev proj₀ : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) 0

theorem fderiv_comp_proj₀ {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : Fin 1 → ℝ) :
    fderiv ℝ (f ∘ proj₀) x (Pi.single 0 1) = deriv f (x 0) := by
  rw [fderiv_comp x (hf.differentiable two_ne_zero _) proj₀.differentiableAt,
    proj₀.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, Pi.single_eq_same]
  rfl

theorem iteratedFDeriv_two_comp_proj₀ {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : Fin 1 → ℝ) :
    iteratedFDeriv ℝ 2 (f ∘ proj₀) x ![Pi.single 0 1, Pi.single 0 1] =
      deriv (deriv f) (x 0) := by
  rw [proj₀.iteratedFDeriv_comp_right hf x le_rfl,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have : (fun i : Fin 2 => proj₀ (![Pi.single (0 : Fin 1) (1 : ℝ), Pi.single 0 1] i)) =
      fun _ => (1 : ℝ) := by
    funext i; fin_cases i <;> simp
  rw [this, ← iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_succ, iteratedDeriv_one]
  rfl

/-! ### Itô's formula for `f(X_t)` -/

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ≥0 mΩ} {α β : ℝ → ℝ} {X : ℝ≥0 → Ω → ℝ}

/-- Itô's formula in the scalar case: `f(X_t) - f(X_0) - ∫₀ᵗ (Lf)(X_s) ds` is a continuous local
martingale for `f ∈ C²` (paper.tex:L2365-2369). Consumes `ito_formula`. -/
theorem IsDiffusionSolution.isContLocalMartingale_generator
    (hX : IsDiffusionSolution ℱ α β X P) (hXc : ∀ ω, Continuous fun t => X t ω)
    (hα : Continuous α) (hβ : Continuous β) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    IsContLocalMartingale ℱ (fun t ω => f (X t ω) - f (X 0 ω) -
      pathIntegral (fun s ω => generator α β f (X s ω)) t ω) P := by
  obtain ⟨hprog, -, hM, hMM⟩ := hX
  -- the one-dimensional process, its drift and its diffusion matrix
  set X' : ℝ≥0 → Ω → (Fin 1 → ℝ) := fun t ω _ => X t ω with hX'
  set A : ℝ≥0 → Ω → (Fin 1 → ℝ) := fun t ω _ => α (X t ω) with hA
  set Q : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ := fun t ω _ _ => β (X t ω) ^ 2 with hQ
  have hX'prog : IsStronglyProgressive ℱ X' := fun i =>
    (continuous_pi fun _ => continuous_id).comp_stronglyMeasurable (hprog i)
  have hAprog : IsStronglyProgressive ℱ A := fun i =>
    (continuous_pi fun _ => hα).comp_stronglyMeasurable (hprog i)
  have hQprog : IsStronglyProgressive ℱ Q := fun i =>
    (continuous_pi fun _ => continuous_pi fun _ => hβ.pow 2).comp_stronglyMeasurable (hprog i)
  have hXc' : ∀ ω, Continuous fun t => X' t ω := fun ω => continuous_pi fun _ => hXc ω
  have hAint : ∀ᵐ ω ∂P, ∀ (i : Fin 1) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => A (Real.toNNReal s) ω i) volume 0 t :=
    Eventually.of_forall fun ω _ t =>
      (hα.comp ((hXc ω).comp continuous_real_toNNReal)).intervalIntegrable _ _
  have hQint : ∀ᵐ ω ∂P, ∀ (i j : Fin 1) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => Q (Real.toNNReal s) ω i j) volume 0 t :=
    Eventually.of_forall fun ω _ _ t =>
      ((hβ.pow 2).comp ((hXc ω).comp continuous_real_toNNReal)).intervalIntegrable _ _
  have hM' : ∀ i, IsContLocalMartingale ℱ
      (fun t ω => X' t ω i - X' 0 ω i - pathIntegral (fun s ω => A s ω i) t ω) P :=
    fun _ => hM
  have hMM' : ∀ i j, IsContLocalMartingale ℱ (fun t ω =>
      (X' t ω i - X' 0 ω i - pathIntegral (fun s ω => A s ω i) t ω) *
        (X' t ω j - X' 0 ω j - pathIntegral (fun s ω => A s ω j) t ω) -
        pathIntegral (fun s ω => Q s ω i j) t ω) P := by
    intro i j
    convert hMM using 1
    funext t ω
    simp only [hX', hA, hQ]
    ring
  have hF : ContDiffOn ℝ 2 (f ∘ proj₀) univ := (hf.comp proj₀.contDiff).contDiffOn
  have hFm : Measurable (f ∘ proj₀) := hf.continuous.measurable.comp proj₀.continuous.measurable
  have hito := External.ito_formula ℱ X' A Q hX'prog hXc' hAprog hAint hQprog hQint hM' hMM'
    univ isOpen_univ (f ∘ proj₀) hFm hF (Eventually.of_forall fun _ _ => mem_univ _)
  convert hito using 1
  funext t ω
  simp only [Function.comp, hX']
  congr 1
  unfold pathIntegral
  congr 1
  funext s
  simp only [Fin.sum_univ_one, hA, hQ, generator]
  rw [fderiv_comp_proj₀ hf, iteratedFDeriv_two_comp_proj₀ hf]
  ring

/-- The bound `|∫₀ᵗ ξ_s ds| ≤ C t` for a path bounded by `C`. -/
theorem abs_pathIntegral_le {ξ : ℝ≥0 → Ω → ℝ} {C : ℝ} {ω : Ω} (hξ : ∀ s, |ξ s ω| ≤ C)
    (t : ℝ≥0) : |pathIntegral ξ t ω| ≤ C * t := by
  unfold pathIntegral
  have := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun s : ℝ => ξ (Real.toNNReal s) ω) (a := 0) (b := t) (C := C)
    fun s _ => by simpa [Real.norm_eq_abs] using hξ (Real.toNNReal s)
  simpa [Real.norm_eq_abs, abs_of_nonneg t.2] using this

omit [IsProbabilityMeasure P] in
/-- `X t` is measurable. -/
theorem IsDiffusionSolution.measurable (hX : IsDiffusionSolution ℱ α β X P) (t : ℝ≥0) :
    Measurable (X t) :=
  ((hX.1.stronglyAdapted t).mono (ℱ.le t)).measurable

/-- The path integral `∫₀ᵗ (Lf)(X_s) ds` is a.e. strongly measurable (as the difference of the
Itô local martingale and `f(X_t) - f(X_0)`). -/
theorem IsDiffusionSolution.aestronglyMeasurable_pathIntegral_generator
    (hX : IsDiffusionSolution ℱ α β X P) (hXc : ∀ ω, Continuous fun t => X t ω)
    (hα : Continuous α) (hβ : Continuous β) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ≥0) :
    AEStronglyMeasurable (fun ω => pathIntegral (fun s ω => generator α β f (X s ω)) t ω) P := by
  have hM := IsDiffusionSolution.isContLocalMartingale_generator hX hXc hα hβ hf
  have h1 : AEStronglyMeasurable (fun ω => f (X t ω) - f (X 0 ω) -
      pathIntegral (fun s ω => generator α β f (X s ω)) t ω) P :=
    ((hM.1.stronglyAdapted t).mono (ℱ.le t)).aestronglyMeasurable
  have h2 : AEStronglyMeasurable (fun ω => f (X t ω) - f (X 0 ω)) P :=
    ((hf.continuous.measurable.comp (IsDiffusionSolution.measurable hX t)).sub
      (hf.continuous.measurable.comp (IsDiffusionSolution.measurable hX 0))).aestronglyMeasurable
  refine (h2.sub h1).congr (Eventually.of_forall fun ω => ?_)
  simp only [Pi.sub_apply]
  ring

/-- Integrability of `∫₀ᵗ (Lf)(X_s) ds` when `Lf` is bounded. -/
theorem IsDiffusionSolution.integrable_pathIntegral_generator
    (hX : IsDiffusionSolution ℱ α β X P) (hXc : ∀ ω, Continuous fun t => X t ω)
    (hα : Continuous α) (hβ : Continuous β) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {CL : ℝ} (hLb : ∀ u, |generator α β f u| ≤ CL) (t : ℝ≥0) :
    Integrable (fun ω => pathIntegral (fun s ω => generator α β f (X s ω)) t ω) P :=
  (integrable_const (CL * (t : ℝ))).mono'
    (IsDiffusionSolution.aestronglyMeasurable_pathIntegral_generator hX hXc hα hβ hf t)
    (Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using
        abs_pathIntegral_le (ξ := fun s ω => generator α β f (X s ω)) (fun s => hLb (X s ω)) t)

/-- Integrability of `f(X_t)` for bounded continuous `f`. -/
theorem IsDiffusionSolution.integrable_comp (hX : IsDiffusionSolution ℱ α β X P)
    {f : ℝ → ℝ} (hf : Continuous f) {Cf : ℝ} (hfb : ∀ u, |f u| ≤ Cf) (t : ℝ≥0) :
    Integrable (fun ω => f (X t ω)) P :=
  (integrable_const Cf).mono'
    (hf.measurable.comp (IsDiffusionSolution.measurable hX t)).aestronglyMeasurable
    (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hfb (X t ω))

/-- Itô's formula in expectation: `E f(X_t) - E f(X_0) = E ∫₀ᵗ (Lf)(X_s) ds` for bounded `f`
with bounded generator (paper.tex:L2370-2374; the local martingale is bounded on `[0, t]`, hence
a true martingale). -/
theorem IsDiffusionSolution.integral_sub_integral_eq
    (hX : IsDiffusionSolution ℱ α β X P) (hXc : ∀ ω, Continuous fun t => X t ω)
    (hα : Continuous α) (hβ : Continuous β) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {Cf CL : ℝ} (hfb : ∀ u, |f u| ≤ Cf) (hLb : ∀ u, |generator α β f u| ≤ CL) (t : ℝ≥0) :
    (∫ ω, f (X t ω) ∂P) - ∫ ω, f (X 0 ω) ∂P =
      ∫ ω, pathIntegral (fun s ω => generator α β f (X s ω)) t ω ∂P := by
  have hM := IsDiffusionSolution.isContLocalMartingale_generator hX hXc hα hβ hf
  have hCL : 0 ≤ CL := le_trans (abs_nonneg _) (hLb 0)
  have hzero := Infrastructure.IsContLocalMartingale.integral_eq_zero hM
    (fun ω => by simp [pathIntegral]) (t := t) (C := 2 * Cf + CL * t)
    (Eventually.of_forall fun ω s hs => by
      have h1 := hfb (X s ω)
      have h2 := hfb (X 0 ω)
      have h3 := abs_pathIntegral_le (ξ := fun s ω => generator α β f (X s ω))
        (fun s => hLb (X s ω)) s
      have h4 : CL * (s : ℝ) ≤ CL * t :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hs) hCL
      calc |f (X s ω) - f (X 0 ω) - pathIntegral (fun s ω => generator α β f (X s ω)) s ω|
          ≤ |f (X s ω) - f (X 0 ω)| + |pathIntegral (fun s ω => generator α β f (X s ω)) s ω| :=
            abs_sub _ _
        _ ≤ (|f (X s ω)| + |f (X 0 ω)|) + CL * s := add_le_add (abs_sub _ _) h3
        _ ≤ 2 * Cf + CL * t := by linarith)
  have hint1 := IsDiffusionSolution.integrable_comp hX hf.continuous hfb t
  have hint0 := IsDiffusionSolution.integrable_comp hX hf.continuous hfb 0
  have hintI := IsDiffusionSolution.integrable_pathIntegral_generator hX hXc hα hβ hf hLb t
  have hint10 : Integrable (fun ω => f (X t ω) - f (X 0 ω)) P := hint1.sub hint0
  rw [integral_sub hint10 hintI, integral_sub hint1 hint0] at hzero
  linarith

/-- `t ↦ E f(X_t)` is Lipschitz with constant `CL`. -/
theorem IsDiffusionSolution.abs_integral_sub_integral_le
    (hX : IsDiffusionSolution ℱ α β X P) (hXc : ∀ ω, Continuous fun t => X t ω)
    (hα : Continuous α) (hβ : Continuous β) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {Cf CL : ℝ} (hfb : ∀ u, |f u| ≤ Cf) (hLb : ∀ u, |generator α β f u| ≤ CL) (s t : ℝ≥0) :
    |(∫ ω, f (X t ω) ∂P) - ∫ ω, f (X s ω) ∂P| ≤ CL * |(t : ℝ) - s| := by
  have hs := IsDiffusionSolution.integral_sub_integral_eq hX hXc hα hβ hf hfb hLb s
  have ht := IsDiffusionSolution.integral_sub_integral_eq hX hXc hα hβ hf hfb hLb t
  have hsub : (∫ ω, f (X t ω) ∂P) - ∫ ω, f (X s ω) ∂P =
      ∫ ω, (pathIntegral (fun s ω => generator α β f (X s ω)) t ω -
        pathIntegral (fun s ω => generator α β f (X s ω)) s ω) ∂P := by
    rw [integral_sub (IsDiffusionSolution.integrable_pathIntegral_generator hX hXc hα hβ hf hLb t)
      (IsDiffusionSolution.integrable_pathIntegral_generator hX hXc hα hβ hf hLb s), ← ht, ← hs]
    ring
  rw [hsub]
  have hcont : ∀ ω, Continuous fun r : ℝ => generator α β f (X (Real.toNNReal r) ω) := fun ω =>
    (continuous_generator hα hβ hf).comp ((hXc ω).comp continuous_real_toNNReal)
  have hbound : ∀ ω, |pathIntegral (fun s ω => generator α β f (X s ω)) t ω -
      pathIntegral (fun s ω => generator α β f (X s ω)) s ω| ≤ CL * |(t : ℝ) - s| := by
    intro ω
    unfold pathIntegral
    rw [intervalIntegral.integral_interval_sub_left ((hcont ω).intervalIntegrable _ _)
      ((hcont ω).intervalIntegrable _ _)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun r : ℝ => generator α β f (X (Real.toNNReal r) ω)) (a := s) (b := t) (C := CL)
      fun r _ => by simpa [Real.norm_eq_abs] using hLb (X (Real.toNNReal r) ω)
    simpa [Real.norm_eq_abs] using this
  have := norm_integral_le_of_norm_le_const (μ := P)
    (f := fun ω => pathIntegral (fun s ω => generator α β f (X s ω)) t ω -
      pathIntegral (fun s ω => generator α β f (X s ω)) s ω) (C := CL * |(t : ℝ) - s|)
    (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hbound ω)
  simpa [Real.norm_eq_abs] using this

/-- The right derivative at `0` of `t ↦ E f(X_t)` is `E (Lf)(X_0)` (paper.tex:L2376-2380,
(A.3): differentiate the Itô identity at `t = 0`; here by dominated convergence of the time
averages `t⁻¹ ∫₀ᵗ (Lf)(X_s) ds → (Lf)(X_0)` along the continuous paths). -/
theorem IsDiffusionSolution.hasDerivWithinAt_integral_comp
    (hX : IsDiffusionSolution ℱ α β X P) (hXc : ∀ ω, Continuous fun t => X t ω)
    (hα : Continuous α) (hβ : Continuous β) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {Cf CL : ℝ} (hfb : ∀ u, |f u| ≤ Cf) (hLb : ∀ u, |generator α β f u| ≤ CL) :
    HasDerivWithinAt (fun t : ℝ => ∫ ω, f (X (Real.toNNReal t) ω) ∂P)
      (∫ ω, generator α β f (X 0 ω) ∂P) (Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hIoi : Ici (0 : ℝ) \ {0} = Ioi 0 := by
    ext u; simp [lt_iff_le_and_ne, eq_comm]
  rw [hIoi]
  set L := generator α β f with hL
  -- the slope is the expectation of the time average
  have hslope : ∀ t : ℝ, 0 < t →
      slope (fun t : ℝ => ∫ ω, f (X (Real.toNNReal t) ω) ∂P) 0 t =
        ∫ ω, t⁻¹ * pathIntegral (fun s ω => L (X s ω)) (Real.toNNReal t) ω ∂P := by
    intro t ht
    rw [slope_def_field, sub_zero, Real.toNNReal_zero, div_eq_inv_mul, integral_const_mul,
      IsDiffusionSolution.integral_sub_integral_eq hX hXc hα hβ hf hfb hLb (Real.toNNReal t)]
  have hcongr : (fun t : ℝ =>
      ∫ ω, t⁻¹ * pathIntegral (fun s ω => L (X s ω)) (Real.toNNReal t) ω ∂P)
      =ᶠ[𝓝[Ioi 0] 0] slope (fun t : ℝ => ∫ ω, f (X (Real.toNNReal t) ω) ∂P) 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hslope t ht).symm
  refine Tendsto.congr' hcongr ?_
  -- dominated convergence
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => CL) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (IsDiffusionSolution.aestronglyMeasurable_pathIntegral_generator hX hXc hα hβ hf
      (Real.toNNReal t)).const_mul _
  · filter_upwards [self_mem_nhdsWithin] with t ht
    refine Eventually.of_forall fun ω => ?_
    have h := abs_pathIntegral_le (ξ := fun s ω => L (X s ω)) (fun s => hLb (X s ω))
      (Real.toNNReal t)
    rw [Real.coe_toNNReal _ (le_of_lt ht)] at h
    rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos ht]
    calc t⁻¹ * |pathIntegral (fun s ω => L (X s ω)) (Real.toNNReal t) ω| ≤ t⁻¹ * (CL * t) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (le_of_lt ht))
      _ = CL := by
          have : t ≠ 0 := (mem_Ioi.mp ht).ne'
          field_simp
  · exact integrable_const _
  · refine Eventually.of_forall fun ω => ?_
    -- `t⁻¹ ∫₀ᵗ L(X_s) ds → L(X_0)` by continuity of the path
    have hcont : Continuous fun r : ℝ => L (X (Real.toNNReal r) ω) :=
      (continuous_generator hα hβ hf).comp ((hXc ω).comp continuous_real_toNNReal)
    have hderiv : HasDerivWithinAt (fun u : ℝ => ∫ r in (0 : ℝ)..u, L (X (Real.toNNReal r) ω))
        (L (X (Real.toNNReal 0) ω)) (Ici 0) 0 :=
      intervalIntegral.integral_hasDerivWithinAt_right (hcont.intervalIntegrable _ _)
        (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousWithinAt
    rw [hasDerivWithinAt_iff_tendsto_slope, hIoi, Real.toNNReal_zero] at hderiv
    refine hderiv.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [slope_def_field, sub_zero, intervalIntegral.integral_same, sub_zero, div_eq_inv_mul]
    unfold pathIntegral
    rw [Real.coe_toNNReal _ (le_of_lt (mem_Ioi.mp ht))]

end ComplexSLE.Internal

end
