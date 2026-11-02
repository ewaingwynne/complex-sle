/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.ItoReal
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The occupation measure of a diffusion, and Dynkin's formula against it (M10-R5a)

For a process `X` with everywhere-continuous paths, `occupation X P T` is the *occupation measure*
on `ℝ`: the image of `P ⊗ Leb|_{(0,T]}` under `(ω, s) ↦ X_s(ω)`. So
`∫ φ d(occupation X P T) = E ∫₀ᵀ φ(X_s) ds` and `occupation X P T {N} = E Leb{s ≤ T : X_s ∈ N}`.

Itô's formula in expectation (`IsDiffusionSolution.integral_sub_integral_eq`) then reads, for `g`
of class `C²` with `g` and the generator `L g` bounded,

  `|∫ L g d(occupation X P T)| ≤ 2 ‖g‖_∞`           (`abs_integral_generator_occupation_le`).

All the occupation estimates (`OccupationBound`, `OccupationCritical`) are consequences of this
single inequality applied to suitable periodic `g`. The only classical input is
`External.ito_formula` (through `ItoReal.lean`).
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Internal

section Occupation

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

/-- The path map `(ω, s) ↦ X_s(ω)` on `Ω × ℝ` (`s < 0` is read as time `0`). -/
@[expose] noncomputable def pathMap (X : ℝ≥0 → Ω → ℝ) (p : Ω × ℝ) : ℝ := X p.2.toNNReal p.1

/-- The occupation measure of `X` on `(0, T]`: the image of `P ⊗ Leb|_{(0,T]}` under the path
map. -/
@[expose] noncomputable def occupation (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (T : ℝ≥0) : Measure ℝ :=
  (P.prod (volume.restrict (Ioc (0 : ℝ) T))).map (pathMap X)

theorem measurable_pathMap (hXc : ∀ ω, Continuous fun t => X t ω) (hXm : ∀ t, Measurable (X t)) :
    Measurable (pathMap X) := by
  have hjoint : Measurable (Function.uncurry X) :=
    measurable_uncurry_of_continuous_of_measurable hXc hXm
  exact hjoint.comp ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)

instance [IsFiniteMeasure P] (T : ℝ≥0) : IsFiniteMeasure (occupation X P T) := by
  unfold occupation
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) T)) := inferInstance
  infer_instance

variable [IsProbabilityMeasure P]

theorem occupation_univ (hXc : ∀ ω, Continuous fun t => X t ω) (hXm : ∀ t, Measurable (X t))
    (T : ℝ≥0) : occupation X P T univ = ENNReal.ofReal T := by
  unfold occupation
  rw [Measure.map_apply (measurable_pathMap hXc hXm) MeasurableSet.univ, preimage_univ,
    ← univ_prod_univ, Measure.prod_prod, measure_univ, one_mul, Measure.restrict_apply_univ,
    Real.volume_Ioc]
  simp

theorem real_occupation_univ (hXc : ∀ ω, Continuous fun t => X t ω) (hXm : ∀ t, Measurable (X t))
    (T : ℝ≥0) : (occupation X P T).real univ = T := by
  rw [Measure.real, occupation_univ hXc hXm, ENNReal.toReal_ofReal (NNReal.coe_nonneg T)]

/-- `∫ φ d(occupation) = E ∫₀ᵀ φ(X_s) ds` for bounded continuous `φ`. -/
theorem integral_occupation (hXc : ∀ ω, Continuous fun t => X t ω) (hXm : ∀ t, Measurable (X t))
    {φ : ℝ → ℝ} (hφ : Continuous φ) {C : ℝ} (hC : ∀ x, |φ x| ≤ C) (T : ℝ≥0) :
    ∫ x, φ x ∂(occupation X P T) =
      ∫ ω, ∫ s in Ioc (0 : ℝ) T, φ (X s.toNNReal ω) ∂volume ∂P := by
  have hm := measurable_pathMap hXc hXm
  unfold occupation
  rw [integral_map hm.aemeasurable hφ.aestronglyMeasurable]
  have hint : Integrable (fun p : Ω × ℝ => φ (pathMap X p))
      (P.prod (volume.restrict (Ioc (0 : ℝ) T))) :=
    (integrable_const C).mono' (hφ.measurable.comp hm).aestronglyMeasurable
      (Eventually.of_forall fun p => by simpa [Real.norm_eq_abs] using hC _)
  rw [integral_prod _ hint]
  rfl

variable {ℱ : Filtration ℝ≥0 mΩ} {α β : ℝ → ℝ}

/-- **Dynkin's formula against the occupation measure.** For `g ∈ C²` bounded by `Cg` with bounded
generator, `|∫ L g d(occupation X P T)| ≤ 2 Cg`, since
`∫ L g d(occupation) = E g(X_T) - E g(X_0)`. -/
theorem abs_integral_generator_occupation_le (hX : IsDiffusionSolution ℱ α β X P)
    (hXc : ∀ ω, Continuous fun t => X t ω) (hα : Continuous α) (hβ : Continuous β) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) {Cg CL : ℝ} (hgb : ∀ u, |g u| ≤ Cg)
    (hLb : ∀ u, |generator α β g u| ≤ CL) (T : ℝ≥0) :
    |∫ x, generator α β g x ∂(occupation X P T)| ≤ 2 * Cg := by
  have hXm : ∀ t, Measurable (X t) := IsDiffusionSolution.measurable hX
  rw [integral_occupation hXc hXm (continuous_generator hα hβ hg) hLb T]
  have e : ∀ ω, ∫ s in Ioc (0 : ℝ) T, generator α β g (X s.toNNReal ω) ∂volume =
      pathIntegral (fun s ω => generator α β g (X s ω)) T ω := fun ω => by
    unfold pathIntegral
    rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg T)]
  simp only [e]
  rw [← IsDiffusionSolution.integral_sub_integral_eq hX hXc hα hβ hg hgb hLb T]
  have b1 : |∫ ω, g (X T ω) ∂P| ≤ Cg := by
    have := norm_integral_le_of_norm_le_const (μ := P) (f := fun ω => g (X T ω)) (C := Cg)
      (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hgb _)
    simpa [Real.norm_eq_abs, abs_of_nonneg (le_trans (abs_nonneg _) (hgb 0))] using this
  have b2 : |∫ ω, g (X 0 ω) ∂P| ≤ Cg := by
    have := norm_integral_le_of_norm_le_const (μ := P) (f := fun ω => g (X 0 ω)) (C := Cg)
      (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hgb _)
    simpa [Real.norm_eq_abs, abs_of_nonneg (le_trans (abs_nonneg _) (hgb 0))] using this
  calc |(∫ ω, g (X T ω) ∂P) - ∫ ω, g (X 0 ω) ∂P|
      ≤ |∫ ω, g (X T ω) ∂P| + |∫ ω, g (X 0 ω) ∂P| := abs_sub _ _
    _ ≤ 2 * Cg := by linarith

end Occupation

end ComplexSLE.Internal

end
