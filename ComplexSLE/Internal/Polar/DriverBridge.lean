/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsSLEDriverAdapted
public import ComplexSLE.Frozen.Defs.IsContLocalMartingale
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Distributions.Gaussian.Fernique
import ComplexSLE.Internal.Driver.GaussianMap
import ComplexSLE.Internal.Driver.Process

/-!
# The driver bridge: `Re U`, `Im U` and their brackets are martingales

For an `SLE_Σ` driver `U` that is a Brownian motion with respect to `ℱ` (`IsSLEDriverAdapted`),
with `Σ = covMatrix a b c` positive semidefinite (`0 < a`, `c² ≤ ab`), the processes

* `Re U_t`, `Im U_t`,
* `(Re U_t)² - a t`, `(Im U_t)² - b t`, `(Re U_t)(Im U_t) - c t`

are `ℱ`-martingales (`step:driver-representation` in martingale form: `⟨Re U⟩ = a t`,
`⟨Im U⟩ = b t`, `⟨Re U, Im U⟩ = c t`), hence continuous local martingales in the sense of
`ComplexSLE.IsContLocalMartingale`. These are the characteristics of the state `(Re f, Im f)` fed to
Itô's formula (E1) in the proof of Lemma 2.11.

The proof uses only the Gaussian second moments of an increment and its independence of the past:
`𝔼[D | ℱ_s] = 𝔼[D]` for `D` independent of `ℱ_s` (`condExp_indep_eq`).
-/

public section

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE

/-! ### Second moments of `complexGaussian` -/

section Gaussian

variable {S : Matrix (Fin 2) (Fin 2) ℝ}

/-- The embedding `ℝ² → ℂ` used in `complexGaussian`. -/
private theorem complexGaussian_eq_map (S : Matrix (Fin 2) (Fin 2) ℝ) :
    complexGaussian S = (multivariateGaussian 0 S).map
      fun x : EuclideanSpace ℝ (Fin 2) => (x 0 : ℂ) + (x 1 : ℂ) * Complex.I := rfl

private theorem measurable_embed :
    Measurable fun x : EuclideanSpace ℝ (Fin 2) => (x 0 : ℂ) + (x 1 : ℂ) * Complex.I := by
  fun_prop

private theorem re_embed (x : EuclideanSpace ℝ (Fin 2)) :
    ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I).re = x 0 := by simp

private theorem im_embed (x : EuclideanSpace ℝ (Fin 2)) :
    ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I).im = x 1 := by simp

private theorem memLp_eval_multivariateGaussian (i : Fin 2) :
    MemLp (fun x : EuclideanSpace ℝ (Fin 2) => x i) 2 (multivariateGaussian 0 S) := by
  have := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) i).comp_memLp'
    (IsGaussian.memLp_two_id (μ := multivariateGaussian 0 S))
  simpa [Function.comp_def] using this

private theorem integral_eval_multivariateGaussian (i : Fin 2) :
    ∫ x : EuclideanSpace ℝ (Fin 2), x i ∂(multivariateGaussian 0 S) = 0 := by
  have h := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) i).integral_comp_comm
    (IsGaussian.integrable_id (μ := multivariateGaussian 0 S))
  simpa [Function.comp_def, integral_id_multivariateGaussian] using h

private theorem integral_eval_mul_eval_multivariateGaussian (hS : S.PosSemidef) (i j : Fin 2) :
    ∫ x : EuclideanSpace ℝ (Fin 2), x i * x j ∂(multivariateGaussian 0 S) = S i j := by
  have hcov := covariance_eval_multivariateGaussian (μ := 0) hS i j
  rw [covariance_eq_sub (memLp_eval_multivariateGaussian i) (memLp_eval_multivariateGaussian j),
    integral_eval_multivariateGaussian, integral_eval_multivariateGaussian, mul_zero, sub_zero]
    at hcov
  exact hcov

theorem memLp_re_complexGaussian (S : Matrix (Fin 2) (Fin 2) ℝ) :
    MemLp (fun w : ℂ => w.re) 2 (complexGaussian S) := by
  rw [complexGaussian_eq_map]
  refine (memLp_map_measure_iff Complex.continuous_re.aestronglyMeasurable
    measurable_embed.aemeasurable).2 ?_
  simpa [Function.comp_def, re_embed] using memLp_eval_multivariateGaussian (S := S) 0

theorem memLp_im_complexGaussian (S : Matrix (Fin 2) (Fin 2) ℝ) :
    MemLp (fun w : ℂ => w.im) 2 (complexGaussian S) := by
  rw [complexGaussian_eq_map]
  refine (memLp_map_measure_iff Complex.continuous_im.aestronglyMeasurable
    measurable_embed.aemeasurable).2 ?_
  simpa [Function.comp_def, im_embed] using memLp_eval_multivariateGaussian (S := S) 1

theorem integral_re_complexGaussian (S : Matrix (Fin 2) (Fin 2) ℝ) :
    ∫ w, w.re ∂(complexGaussian S) = 0 := by
  rw [complexGaussian_eq_map, integral_map (f := fun w : ℂ => w.re)
    measurable_embed.aemeasurable Complex.continuous_re.aestronglyMeasurable]
  simpa [re_embed] using integral_eval_multivariateGaussian (S := S) 0

theorem integral_im_complexGaussian (S : Matrix (Fin 2) (Fin 2) ℝ) :
    ∫ w, w.im ∂(complexGaussian S) = 0 := by
  rw [complexGaussian_eq_map, integral_map (f := fun w : ℂ => w.im)
    measurable_embed.aemeasurable Complex.continuous_im.aestronglyMeasurable]
  simpa [im_embed] using integral_eval_multivariateGaussian (S := S) 1

theorem integral_re_mul_re_complexGaussian (hS : S.PosSemidef) :
    ∫ w, w.re * w.re ∂(complexGaussian S) = S 0 0 := by
  rw [complexGaussian_eq_map, integral_map (f := fun w : ℂ => w.re * w.re)
    measurable_embed.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
  simpa [re_embed] using integral_eval_mul_eval_multivariateGaussian hS 0 0

theorem integral_im_mul_im_complexGaussian (hS : S.PosSemidef) :
    ∫ w, w.im * w.im ∂(complexGaussian S) = S 1 1 := by
  rw [complexGaussian_eq_map, integral_map (f := fun w : ℂ => w.im * w.im)
    measurable_embed.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
  simpa [im_embed] using integral_eval_mul_eval_multivariateGaussian hS 1 1

theorem integral_re_mul_im_complexGaussian (hS : S.PosSemidef) :
    ∫ w, w.re * w.im ∂(complexGaussian S) = S 0 1 := by
  rw [complexGaussian_eq_map, integral_map (f := fun w : ℂ => w.re * w.im)
    measurable_embed.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
  simpa [re_embed, im_embed] using integral_eval_mul_eval_multivariateGaussian hS 0 1

end Gaussian

/-- `Σ = covMatrix a b c` is positive semidefinite for `a > 0`, `c² ≤ ab`. -/
theorem covMatrix_posSemidef {a b c : ℝ} (ha : 0 < a) (hc : c ^ 2 ≤ a * b) :
    (covMatrix a b c).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose (Internal.driverMatrix a b c)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial,
    Internal.driverMatrix_mul_transpose a b c ha hc] at h
  exact h

/-! ### A conditional-expectation lemma for independent increments -/

section CondExp

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Quadratic bracket lemma.** If `R`, `J` are `𝒜`-measurable and square integrable, and
`D₁`, `D₂` are square integrable, measurable with respect to a σ-algebra `m₁` independent of `𝒜`,
centered, with `𝔼[D₁ D₂] = κ`, then `𝔼[(R + D₁)(J + D₂) - κ | 𝒜] = R J`. -/
theorem condExp_add_mul_add_sub_of_indep {𝒜 m₁ : MeasurableSpace Ω} (h𝒜 : 𝒜 ≤ m) (hm₁ : m₁ ≤ m)
    (hind : Indep m₁ 𝒜 P) {R J D₁ D₂ : Ω → ℝ} (hR : StronglyMeasurable[𝒜] R)
    (hJ : StronglyMeasurable[𝒜] J) (hR2 : MemLp R 2 P) (hJ2 : MemLp J 2 P)
    (hD₁ : StronglyMeasurable[m₁] D₁) (hD₂ : StronglyMeasurable[m₁] D₂) (hD₁2 : MemLp D₁ 2 P)
    (hD₂2 : MemLp D₂ 2 P) (hD₁0 : P[D₁] = 0) (hD₂0 : P[D₂] = 0) {κ : ℝ}
    (hκ : P[fun ω => D₁ ω * D₂ ω] = κ) :
    P[fun ω => (R ω + D₁ ω) * (J ω + D₂ ω) - κ | 𝒜] =ᵐ[P] fun ω => R ω * J ω := by
  have : SigmaFinite (P.trim h𝒜) := inferInstance
  -- the four pieces
  have hRJ : Integrable (fun ω => R ω * J ω) P := hR2.integrable_mul hJ2
  have hRD : Integrable (fun ω => R ω * D₂ ω) P := hR2.integrable_mul hD₂2
  have hJD : Integrable (fun ω => J ω * D₁ ω) P := hJ2.integrable_mul hD₁2
  have hDD : Integrable (fun ω => D₁ ω * D₂ ω) P := hD₁2.integrable_mul hD₂2
  have hDDκ : Integrable (fun ω => D₁ ω * D₂ ω - κ) P := hDD.sub (integrable_const κ)
  have hdecomp : (fun ω => (R ω + D₁ ω) * (J ω + D₂ ω) - κ) =
      (fun ω => R ω * J ω) + (fun ω => R ω * D₂ ω) + (fun ω => J ω * D₁ ω) +
        fun ω => D₁ ω * D₂ ω - κ := by
    ext ω; simp only [Pi.add_apply]; ring
  rw [hdecomp]
  -- `𝔼[R J | 𝒜] = R J`
  have e1 : P[fun ω => R ω * J ω | 𝒜] = fun ω => R ω * J ω :=
    condExp_of_stronglyMeasurable h𝒜 (hR.mul hJ) hRJ
  -- `𝔼[D₂ | 𝒜] = 0`, `𝔼[D₁ | 𝒜] = 0`
  have hD₂c : P[D₂ | 𝒜] =ᵐ[P] fun _ => 0 := by
    refine (condExp_indep_eq hm₁ h𝒜 hD₂ hind).trans ?_
    rw [hD₂0]
  have hD₁c : P[D₁ | 𝒜] =ᵐ[P] fun _ => 0 := by
    refine (condExp_indep_eq hm₁ h𝒜 hD₁ hind).trans ?_
    rw [hD₁0]
  have e2 : P[fun ω => R ω * D₂ ω | 𝒜] =ᵐ[P] fun _ => 0 := by
    have := condExp_mul_of_stronglyMeasurable_left (μ := P) hR hRD (hD₂2.integrable one_le_two)
    refine this.trans ?_
    filter_upwards [hD₂c] with ω hω
    simp [hω]
  have e3 : P[fun ω => J ω * D₁ ω | 𝒜] =ᵐ[P] fun _ => 0 := by
    have := condExp_mul_of_stronglyMeasurable_left (μ := P) hJ hJD (hD₁2.integrable one_le_two)
    refine this.trans ?_
    filter_upwards [hD₁c] with ω hω
    simp [hω]
  -- `𝔼[D₁ D₂ - κ | 𝒜] = 𝔼[D₁ D₂] - κ = 0`
  have e4 : P[fun ω => D₁ ω * D₂ ω - κ | 𝒜] =ᵐ[P] fun _ => 0 := by
    have hsm : StronglyMeasurable[m₁] fun ω => D₁ ω * D₂ ω - κ :=
      (hD₁.mul hD₂).sub stronglyMeasurable_const
    refine (condExp_indep_eq hm₁ h𝒜 hsm hind).trans ?_
    rw [integral_sub hDD (integrable_const κ), hκ]
    simp
  refine (condExp_add ((hRJ.add hRD).add hJD) hDDκ 𝒜).trans ?_
  refine ((condExp_add (hRJ.add hRD) hJD 𝒜).add EventuallyEq.rfl).trans ?_
  refine (((condExp_add hRJ hRD 𝒜).add EventuallyEq.rfl).add EventuallyEq.rfl).trans ?_
  filter_upwards [e2, e3, e4] with ω h2 h3 h4
  simp only [Pi.add_apply, e1, h2, h3, h4, add_zero]

end CondExp

/-! ### Martingales attached to an adapted `SLE_Σ` driver -/

namespace IsSLEDriverAdapted

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 m} {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- Each `U t` is measurable. -/
theorem measurable (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) : Measurable (U t) :=
  hU.adapted.measurable

/-- Increments have the Gaussian law of Definition 1.4. -/
theorem hasLaw_increment (hU : IsSLEDriverAdapted a b c U P ℱ) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω => U t ω - U s ω) (complexGaussian (((t : ℝ) - s) • covMatrix a b c)) P :=
  hU.toIsSLEDriver.law_increment s t hst

/-- The σ-algebra of the increment `U t - U s` is a sub-σ-algebra of `m`. -/
theorem comap_increment_le (hU : IsSLEDriverAdapted a b c U P ℱ) (s t : ℝ≥0) :
    MeasurableSpace.comap (fun ω => U t ω - U s ω) inferInstance ≤ m :=
  measurable_iff_comap_le.1 ((hU.measurable t).sub (hU.measurable s))

theorem stronglyMeasurable_re_increment_comap (U : ℝ≥0 → Ω → ℂ) (s t : ℝ≥0) :
    StronglyMeasurable[MeasurableSpace.comap (fun ω => U t ω - U s ω) inferInstance]
      fun ω => (U t ω - U s ω).re :=
  (Complex.measurable_re.comp (comap_measurable _)).stronglyMeasurable

theorem stronglyMeasurable_im_increment_comap (U : ℝ≥0 → Ω → ℂ) (s t : ℝ≥0) :
    StronglyMeasurable[MeasurableSpace.comap (fun ω => U t ω - U s ω) inferInstance]
      fun ω => (U t ω - U s ω).im :=
  (Complex.measurable_im.comp (comap_measurable _)).stronglyMeasurable

theorem stronglyMeasurable_re (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) :
    StronglyMeasurable[ℱ t] fun ω => (U t ω).re :=
  (Complex.measurable_re.comp (hU.adapted t)).stronglyMeasurable

theorem stronglyMeasurable_im (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) :
    StronglyMeasurable[ℱ t] fun ω => (U t ω).im :=
  (Complex.measurable_im.comp (hU.adapted t)).stronglyMeasurable

theorem memLp_re_increment (hU : IsSLEDriverAdapted a b c U P ℱ) {s t : ℝ≥0} (hst : s ≤ t) :
    MemLp (fun ω => (U t ω - U s ω).re) 2 P :=
  (hU.hasLaw_increment hst).memLp_comp (memLp_re_complexGaussian _)

theorem memLp_im_increment (hU : IsSLEDriverAdapted a b c U P ℱ) {s t : ℝ≥0} (hst : s ≤ t) :
    MemLp (fun ω => (U t ω - U s ω).im) 2 P :=
  (hU.hasLaw_increment hst).memLp_comp (memLp_im_complexGaussian _)

theorem memLp_re (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) :
    MemLp (fun ω => (U t ω).re) 2 P := by
  refine (hU.memLp_re_increment (bot_le : (0 : ℝ≥0) ≤ t)).ae_eq ?_
  filter_upwards [hU.toIsSLEDriver.zero] with ω hω
  simp [hω]

theorem memLp_im (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) :
    MemLp (fun ω => (U t ω).im) 2 P := by
  refine (hU.memLp_im_increment (bot_le : (0 : ℝ≥0) ≤ t)).ae_eq ?_
  filter_upwards [hU.toIsSLEDriver.zero] with ω hω
  simp [hω]

theorem integral_re_increment (hU : IsSLEDriverAdapted a b c U P ℱ) {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω => (U t ω - U s ω).re] = 0 := by
  have := (hU.hasLaw_increment hst).integral_comp (f := fun w : ℂ => w.re)
    Complex.continuous_re.aestronglyMeasurable
  rw [Function.comp_def] at this
  rw [this, integral_re_complexGaussian]

theorem integral_im_increment (hU : IsSLEDriverAdapted a b c U P ℱ) {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω => (U t ω - U s ω).im] = 0 := by
  have := (hU.hasLaw_increment hst).integral_comp (f := fun w : ℂ => w.im)
    Complex.continuous_im.aestronglyMeasurable
  rw [Function.comp_def] at this
  rw [this, integral_im_complexGaussian]

theorem integral_re_mul_re_increment (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a)
    (hc : c ^ 2 ≤ a * b) {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω => (U t ω - U s ω).re * (U t ω - U s ω).re] = ((t : ℝ) - s) * a := by
  have hS : (((t : ℝ) - s) • covMatrix a b c).PosSemidef :=
    (covMatrix_posSemidef ha hc).smul (by simp [hst])
  have := (hU.hasLaw_increment hst).integral_comp (f := fun w : ℂ => w.re * w.re)
    (Complex.continuous_re.mul Complex.continuous_re).aestronglyMeasurable
  rw [Function.comp_def] at this
  rw [this, integral_re_mul_re_complexGaussian hS]
  simp [covMatrix]

theorem integral_im_mul_im_increment (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a)
    (hc : c ^ 2 ≤ a * b) {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω => (U t ω - U s ω).im * (U t ω - U s ω).im] = ((t : ℝ) - s) * b := by
  have hS : (((t : ℝ) - s) • covMatrix a b c).PosSemidef :=
    (covMatrix_posSemidef ha hc).smul (by simp [hst])
  have := (hU.hasLaw_increment hst).integral_comp (f := fun w : ℂ => w.im * w.im)
    (Complex.continuous_im.mul Complex.continuous_im).aestronglyMeasurable
  rw [Function.comp_def] at this
  rw [this, integral_im_mul_im_complexGaussian hS]
  simp [covMatrix]

theorem integral_re_mul_im_increment (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a)
    (hc : c ^ 2 ≤ a * b) {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω => (U t ω - U s ω).re * (U t ω - U s ω).im] = ((t : ℝ) - s) * c := by
  have hS : (((t : ℝ) - s) • covMatrix a b c).PosSemidef :=
    (covMatrix_posSemidef ha hc).smul (by simp [hst])
  have := (hU.hasLaw_increment hst).integral_comp (f := fun w : ℂ => w.re * w.im)
    (Complex.continuous_re.mul Complex.continuous_im).aestronglyMeasurable
  rw [Function.comp_def] at this
  rw [this, integral_re_mul_im_complexGaussian hS]
  simp [covMatrix]

variable [IsProbabilityMeasure P]

/-- `Re U` is an `ℱ`-martingale. -/
theorem martingale_re (hU : IsSLEDriverAdapted a b c U P ℱ) :
    Martingale (fun t ω => (U t ω).re) ℱ P := by
  refine ⟨fun t => hU.stronglyMeasurable_re t, fun s t hst => ?_⟩
  beta_reduce
  have : SigmaFinite (P.trim (ℱ.le s)) := inferInstance
  have hdecomp : (fun ω => (U t ω).re) =
      (fun ω => (U t ω - U s ω).re) + fun ω => (U s ω).re := by
    ext ω; simp
  have hint1 : Integrable (fun ω => (U t ω - U s ω).re) P :=
    (hU.memLp_re_increment hst).integrable one_le_two
  have hint2 : Integrable (fun ω => (U s ω).re) P := (hU.memLp_re s).integrable one_le_two
  rw [hdecomp]
  refine (condExp_add hint1 hint2 (ℱ s)).trans ?_
  have h1 : P[fun ω => (U t ω - U s ω).re | ℱ s] =ᵐ[P] fun _ => 0 := by
    refine (condExp_indep_eq (hU.comap_increment_le s t) (ℱ.le s)
      (stronglyMeasurable_re_increment_comap U s t) (hU.indep_increment s t hst)).trans ?_
    rw [hU.integral_re_increment hst]
  have h2 : P[fun ω => (U s ω).re | ℱ s] = fun ω => (U s ω).re :=
    condExp_of_stronglyMeasurable (ℱ.le s) (hU.stronglyMeasurable_re s) hint2
  filter_upwards [h1] with ω h1
  simp only [Pi.add_apply, h1, h2, zero_add]

/-- `Im U` is an `ℱ`-martingale. -/
theorem martingale_im (hU : IsSLEDriverAdapted a b c U P ℱ) :
    Martingale (fun t ω => (U t ω).im) ℱ P := by
  refine ⟨fun t => hU.stronglyMeasurable_im t, fun s t hst => ?_⟩
  beta_reduce
  have : SigmaFinite (P.trim (ℱ.le s)) := inferInstance
  have hdecomp : (fun ω => (U t ω).im) =
      (fun ω => (U t ω - U s ω).im) + fun ω => (U s ω).im := by
    ext ω; simp
  have hint1 : Integrable (fun ω => (U t ω - U s ω).im) P :=
    (hU.memLp_im_increment hst).integrable one_le_two
  have hint2 : Integrable (fun ω => (U s ω).im) P := (hU.memLp_im s).integrable one_le_two
  rw [hdecomp]
  refine (condExp_add hint1 hint2 (ℱ s)).trans ?_
  have h1 : P[fun ω => (U t ω - U s ω).im | ℱ s] =ᵐ[P] fun _ => 0 := by
    refine (condExp_indep_eq (hU.comap_increment_le s t) (ℱ.le s)
      (stronglyMeasurable_im_increment_comap U s t) (hU.indep_increment s t hst)).trans ?_
    rw [hU.integral_im_increment hst]
  have h2 : P[fun ω => (U s ω).im | ℱ s] = fun ω => (U s ω).im :=
    condExp_of_stronglyMeasurable (ℱ.le s) (hU.stronglyMeasurable_im s) hint2
  filter_upwards [h1] with ω h1
  simp only [Pi.add_apply, h1, h2, zero_add]

/-- The common pattern for the three bracket martingales: `X_t Y_t - κ t` where
`X_t = X_s + D₁`, `Y_t = Y_s + D₂` with `𝔼[D₁ D₂] = κ (t - s)`. -/
private theorem martingale_mul_sub_of_increments (hU : IsSLEDriverAdapted a b c U P ℱ)
    {X Y : ℝ≥0 → Ω → ℝ} {κ : ℝ} (hX : ∀ t, StronglyMeasurable[ℱ t] (X t))
    (hY : ∀ t, StronglyMeasurable[ℱ t] (Y t)) (hX2 : ∀ t, MemLp (X t) 2 P)
    (hY2 : ∀ t, MemLp (Y t) 2 P)
    (hXinc : ∀ s t : ℝ≥0, s ≤ t → StronglyMeasurable[MeasurableSpace.comap
      (fun ω => U t ω - U s ω) inferInstance] fun ω => X t ω - X s ω)
    (hYinc : ∀ s t : ℝ≥0, s ≤ t → StronglyMeasurable[MeasurableSpace.comap
      (fun ω => U t ω - U s ω) inferInstance] fun ω => Y t ω - Y s ω)
    (hX0 : ∀ s t : ℝ≥0, s ≤ t → P[fun ω => X t ω - X s ω] = 0)
    (hY0 : ∀ s t : ℝ≥0, s ≤ t → P[fun ω => Y t ω - Y s ω] = 0)
    (hκ : ∀ s t : ℝ≥0, s ≤ t →
      P[fun ω => (X t ω - X s ω) * (Y t ω - Y s ω)] = ((t : ℝ) - s) * κ) :
    Martingale (fun t ω => X t ω * Y t ω - κ * (t : ℝ)) ℱ P := by
  refine ⟨fun t => ((hX t).mul (hY t)).sub stronglyMeasurable_const, fun s t hst => ?_⟩
  beta_reduce
  have : SigmaFinite (P.trim (ℱ.le s)) := inferInstance
  have hXinc2 : MemLp (fun ω => X t ω - X s ω) 2 P := (hX2 t).sub (hX2 s)
  have hYinc2 : MemLp (fun ω => Y t ω - Y s ω) 2 P := (hY2 t).sub (hY2 s)
  have hcore := condExp_add_mul_add_sub_of_indep (ℱ.le s) (hU.comap_increment_le s t)
    (hU.indep_increment s t hst) (hX s) (hY s) (hX2 s) (hY2 s) (hXinc s t hst) (hYinc s t hst)
    hXinc2 hYinc2 (hX0 s t hst) (hY0 s t hst) (hκ s t hst)
  have hdecomp : (fun ω => X t ω * Y t ω - κ * (t : ℝ)) =
      (fun ω => (X s ω + (X t ω - X s ω)) * (Y s ω + (Y t ω - Y s ω)) - ((t : ℝ) - s) * κ) +
        fun _ => -(κ * (s : ℝ)) := by
    ext ω; simp only [Pi.add_apply]; ring
  have hint : Integrable (fun ω => (X s ω + (X t ω - X s ω)) * (Y s ω + (Y t ω - Y s ω)) -
      ((t : ℝ) - s) * κ) P := by
    have h1 : MemLp (fun ω => X s ω + (X t ω - X s ω)) 2 P := (hX2 s).add hXinc2
    have h2 : MemLp (fun ω => Y s ω + (Y t ω - Y s ω)) 2 P := (hY2 s).add hYinc2
    exact (h1.integrable_mul h2).sub (integrable_const _)
  rw [hdecomp]
  refine (condExp_add hint (integrable_const _) (ℱ s)).trans ?_
  have hconst : P[(fun _ => -(κ * (s : ℝ)) : Ω → ℝ) | ℱ s] = fun _ => -(κ * (s : ℝ)) :=
    condExp_const (ℱ.le s) _
  filter_upwards [hcore] with ω h1
  simp only [Pi.add_apply, h1, hconst]
  ring

/-- `(Re U_t)² - a t` is an `ℱ`-martingale (`⟨Re U⟩_t = a t`). -/
theorem martingale_re_sq (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a)
    (hc : c ^ 2 ≤ a * b) :
    Martingale (fun t ω => (U t ω).re ^ 2 - a * (t : ℝ)) ℱ P := by
  have h := hU.martingale_mul_sub_of_increments (X := fun t ω => (U t ω).re)
    (Y := fun t ω => (U t ω).re) (κ := a) hU.stronglyMeasurable_re hU.stronglyMeasurable_re
    hU.memLp_re hU.memLp_re
    (fun s t hst => by simpa [Complex.sub_re] using stronglyMeasurable_re_increment_comap U s t)
    (fun s t hst => by simpa [Complex.sub_re] using stronglyMeasurable_re_increment_comap U s t)
    (fun s t hst => by simpa [Complex.sub_re] using hU.integral_re_increment hst)
    (fun s t hst => by simpa [Complex.sub_re] using hU.integral_re_increment hst)
    (fun s t hst => by simpa [Complex.sub_re] using hU.integral_re_mul_re_increment ha hc hst)
  have : (fun t ω => (U t ω).re ^ 2 - a * (t : ℝ)) =
      fun t ω => (U t ω).re * (U t ω).re - a * (t : ℝ) := by
    funext t ω; ring
  rw [this]; exact h

/-- `(Im U_t)² - b t` is an `ℱ`-martingale (`⟨Im U⟩_t = b t`). -/
theorem martingale_im_sq (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a)
    (hc : c ^ 2 ≤ a * b) :
    Martingale (fun t ω => (U t ω).im ^ 2 - b * (t : ℝ)) ℱ P := by
  have h := hU.martingale_mul_sub_of_increments (X := fun t ω => (U t ω).im)
    (Y := fun t ω => (U t ω).im) (κ := b) hU.stronglyMeasurable_im hU.stronglyMeasurable_im
    hU.memLp_im hU.memLp_im
    (fun s t hst => by simpa [Complex.sub_im] using stronglyMeasurable_im_increment_comap U s t)
    (fun s t hst => by simpa [Complex.sub_im] using stronglyMeasurable_im_increment_comap U s t)
    (fun s t hst => by simpa [Complex.sub_im] using hU.integral_im_increment hst)
    (fun s t hst => by simpa [Complex.sub_im] using hU.integral_im_increment hst)
    (fun s t hst => by simpa [Complex.sub_im] using hU.integral_im_mul_im_increment ha hc hst)
  have : (fun t ω => (U t ω).im ^ 2 - b * (t : ℝ)) =
      fun t ω => (U t ω).im * (U t ω).im - b * (t : ℝ) := by
    funext t ω; ring
  rw [this]; exact h

/-- `(Re U_t)(Im U_t) - c t` is an `ℱ`-martingale (`⟨Re U, Im U⟩_t = c t`). -/
theorem martingale_re_mul_im (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a)
    (hc : c ^ 2 ≤ a * b) :
    Martingale (fun t ω => (U t ω).re * (U t ω).im - c * (t : ℝ)) ℱ P :=
  hU.martingale_mul_sub_of_increments (X := fun t ω => (U t ω).re)
    (Y := fun t ω => (U t ω).im) (κ := c) hU.stronglyMeasurable_re hU.stronglyMeasurable_im
    hU.memLp_re hU.memLp_im
    (fun s t hst => by simpa [Complex.sub_re] using stronglyMeasurable_re_increment_comap U s t)
    (fun s t hst => by simpa [Complex.sub_im] using stronglyMeasurable_im_increment_comap U s t)
    (fun s t hst => by simpa [Complex.sub_re] using hU.integral_re_increment hst)
    (fun s t hst => by simpa [Complex.sub_im] using hU.integral_im_increment hst)
    (fun s t hst => by
      simpa [Complex.sub_re, Complex.sub_im] using hU.integral_re_mul_im_increment ha hc hst)

end IsSLEDriverAdapted

/-! ### From martingales with continuous paths to `IsContLocalMartingale` -/

section ToLocal

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}

/-- A martingale with everywhere-continuous paths is a continuous local martingale (localizing
sequence `τ n = ∞`). -/
theorem _root_.MeasureTheory.Martingale.isContLocalMartingale {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ P)
    (hc : ∀ ω, Continuous fun t => M t ω) : IsContLocalMartingale ℱ M P := by
  refine ⟨hM.stronglyAdapted.isStronglyProgressive_of_continuous hc,
    Eventually.of_forall hc, fun _ _ => ⊤, fun n => ?_, ?_, fun n => ?_⟩
  · intro i
    have : {ω : Ω | (⊤ : WithTop ℝ≥0) ≤ (i : WithTop ℝ≥0)} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, top_le_iff]
      exact WithTop.coe_ne_top
    rw [this]
    exact @MeasurableSet.empty _ (ℱ i)
  · exact Eventually.of_forall fun ω t => Eventually.of_forall fun n => le_top
  · have : stoppedProcess M (fun _ => (⊤ : WithTop ℝ≥0)) = M := by
      ext t ω
      exact stoppedProcess_eq_of_le le_top
    rw [this]
    exact hM

end ToLocal

namespace IsSLEDriverAdapted

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ≥0 m} {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

theorem isContLocalMartingale_re (hU : IsSLEDriverAdapted a b c U P ℱ) :
    IsContLocalMartingale ℱ (fun t ω => (U t ω).re) P :=
  hU.martingale_re.isContLocalMartingale fun ω => Complex.continuous_re.comp (hU.cont ω)

theorem isContLocalMartingale_im (hU : IsSLEDriverAdapted a b c U P ℱ) :
    IsContLocalMartingale ℱ (fun t ω => (U t ω).im) P :=
  hU.martingale_im.isContLocalMartingale fun ω => Complex.continuous_im.comp (hU.cont ω)

theorem isContLocalMartingale_re_sq (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a)
    (hc : c ^ 2 ≤ a * b) :
    IsContLocalMartingale ℱ (fun t ω => (U t ω).re ^ 2 - a * (t : ℝ)) P :=
  (hU.martingale_re_sq ha hc).isContLocalMartingale fun ω => by
    have := Complex.continuous_re.comp (hU.cont ω)
    fun_prop

theorem isContLocalMartingale_im_sq (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a)
    (hc : c ^ 2 ≤ a * b) :
    IsContLocalMartingale ℱ (fun t ω => (U t ω).im ^ 2 - b * (t : ℝ)) P :=
  (hU.martingale_im_sq ha hc).isContLocalMartingale fun ω => by
    have := Complex.continuous_im.comp (hU.cont ω)
    fun_prop

theorem isContLocalMartingale_re_mul_im (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a)
    (hc : c ^ 2 ≤ a * b) :
    IsContLocalMartingale ℱ (fun t ω => (U t ω).re * (U t ω).im - c * (t : ℝ)) P :=
  (hU.martingale_re_mul_im ha hc).isContLocalMartingale fun ω => by
    have h1 := Complex.continuous_re.comp (hU.cont ω)
    have h2 := Complex.continuous_im.comp (hU.cont ω)
    fun_prop

end IsSLEDriverAdapted

end ComplexSLE

end
