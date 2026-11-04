/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.CovMatrix
public import ComplexSLE.Frozen.Defs.ComplexGaussian
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.Complex.Basic
import ComplexSLE.Infrastructure.Gaussian.MapMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Mass of balls for the planar centered Gaussian

Source-independent Gaussian facts used in the support theorem for the driver of `SLE_Σ`.

For a positive semidefinite real `2 × 2` matrix `S`, `covRange S ⊆ ℂ` is the real subspace
`{(S v)₀ + i (S v)₁}` (the range of `S` in the coordinates `(re, im)`).

* `complexGaussian_compl_covRange`: `complexGaussian (t • S)` is carried by `covRange S`;
* `exists_complexGaussian_ball_lower_bound`: there is `q₀ > 0` with
  `complexGaussian (t • S) (ball y √t) ≥ q₀` for all `t > 0` and `y ∈ covRange S` with
  `‖y‖ ≤ 2 √t` (scale-invariant lower bound).

Route. A factorization `S = M Mᵀ` gives `complexGaussian (t • S) = (√t M)_* stdGaussian`; the
range of `M` and of `S = M Mᵀ` agree (`Matrix.rank_self_mul_conjTranspose`). The scaled problem is
a lower bound for `stdGaussian {x | ‖M x - z‖ < 1}` uniformly over the compact set
`covRange S ∩ closedBall 0 2`, obtained from a finite cover by balls of radius `1/2`, since the
standard Gaussian is positive on open sets.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal ENNReal MatrixOrder

namespace ComplexSLE.Infrastructure.SupportGaussian

/-- The identification `ℝ² → ℂ`, `w ↦ w 0 + i w 1`, as an `ℝ`-linear map. -/
noncomputable def ell : (Fin 2 → ℝ) →ₗ[ℝ] ℂ where
  toFun w := ⟨w 0, w 1⟩
  map_add' _ _ := by apply Complex.ext <;> simp
  map_smul' _ _ := by apply Complex.ext <;> simp

@[simp] theorem ell_re (w : Fin 2 → ℝ) : (ell w).re = w 0 := rfl
@[simp] theorem ell_im (w : Fin 2 → ℝ) : (ell w).im = w 1 := rfl

/-- The range of the covariance matrix, as a real subspace of `ℂ`. -/
noncomputable def covRange (S : Matrix (Fin 2) (Fin 2) ℝ) : Submodule ℝ ℂ :=
  Submodule.map ell (LinearMap.range S.mulVecLin)

theorem mem_covRange_iff (S : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ) :
    z ∈ covRange S ↔ ∃ v : Fin 2 → ℝ, S.mulVec v 0 = z.re ∧ S.mulVec v 1 = z.im := by
  unfold covRange
  simp only [Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨v, rfl, rfl⟩
  · rintro ⟨v, h0, h1⟩
    exact ⟨_, ⟨v, rfl⟩, Complex.ext (by simpa using h0) (by simpa using h1)⟩

theorem covRange_eq_of_mul_transpose {S M : Matrix (Fin 2) (Fin 2) ℝ} (h : M * Mᵀ = S) :
    covRange S = Submodule.map ell (LinearMap.range M.mulVecLin) := by
  unfold covRange
  congr 1
  have hle : LinearMap.range S.mulVecLin ≤ LinearMap.range M.mulVecLin := by
    rw [← h, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have := Matrix.rank_self_mul_conjTranspose M
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, h] at this
  exact this

instance : (gaussianReal 0 1).IsOpenPosMeasure :=
  (gaussianReal_absolutelyContinuous' 0 (one_ne_zero)).isOpenPosMeasure

instance : (stdGaussian (EuclideanSpace ℝ (Fin 2))).IsOpenPosMeasure := by
  rw [← map_pi_eq_stdGaussian]
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).isOpenPosMeasure_map
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.surjective

/-- The planar linear map `x ↦ M x`, valued in `ℂ`. -/
noncomputable def cmap (M : Matrix (Fin 2) (Fin 2) ℝ) (x : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  ell (M.mulVec x.ofLp)

theorem continuous_cmap (M : Matrix (Fin 2) (Fin 2) ℝ) : Continuous (cmap M) := by
  have h : cmap M = fun x => (((M.mulVec x.ofLp) 0 : ℝ) : ℂ) +
      (((M.mulVec x.ofLp) 1 : ℝ) : ℂ) * Complex.I := by
    funext x
    apply Complex.ext <;> simp [cmap]
  rw [h]
  have hv : Continuous fun x : EuclideanSpace ℝ (Fin 2) => M.mulVec x.ofLp :=
    Continuous.matrix_mulVec continuous_const (PiLp.continuous_ofLp 2 _)
  have h0 : Continuous fun x : EuclideanSpace ℝ (Fin 2) => (M.mulVec x.ofLp) 0 :=
    (continuous_apply 0).comp hv
  have h1 : Continuous fun x : EuclideanSpace ℝ (Fin 2) => (M.mulVec x.ofLp) 1 :=
    (continuous_apply 1).comp hv
  fun_prop

theorem cmap_mem_covRange {S M : Matrix (Fin 2) (Fin 2) ℝ} (h : M * Mᵀ = S)
    (x : EuclideanSpace ℝ (Fin 2)) : cmap M x ∈ covRange S := by
  rw [covRange_eq_of_mul_transpose h]
  exact ⟨_, ⟨x.ofLp, rfl⟩, rfl⟩

theorem exists_cmap_eq {S M : Matrix (Fin 2) (Fin 2) ℝ} (h : M * Mᵀ = S) {z : ℂ}
    (hz : z ∈ covRange S) : ∃ x : EuclideanSpace ℝ (Fin 2), cmap M x = z := by
  rw [covRange_eq_of_mul_transpose h] at hz
  obtain ⟨_, ⟨v, rfl⟩, rfl⟩ := hz
  exact ⟨WithLp.toLp 2 v, rfl⟩

theorem complexGaussian_smul_eq_map {S M : Matrix (Fin 2) (Fin 2) ℝ} (h : M * Mᵀ = S) {t : ℝ}
    (ht : 0 ≤ t) :
    complexGaussian (t • S) = (stdGaussian (EuclideanSpace ℝ (Fin 2))).map
      (fun x => ((Real.sqrt t : ℝ) : ℂ) * cmap M x) := by
  have h1 : (Real.sqrt t • M) * 1 * (Real.sqrt t • M)ᵀ = t • S := by
    rw [← h]
    simp [Matrix.transpose_smul, smul_smul,
      Real.mul_self_sqrt ht]
  have h2 := map_matrixApply_multivariateGaussian (Real.sqrt t • M) (S := 1) Matrix.PosSemidef.one
  rw [multivariateGaussian_zero_one, h1] at h2
  unfold complexGaussian
  rw [← h2, Measure.map_map (by fun_prop) (Infrastructure.measurable_matrixApply _)]
  congr 1
  funext x
  apply Complex.ext <;> simp [cmap, Function.comp, Infrastructure.matrixApply_apply_zero,
    Infrastructure.matrixApply_apply_one, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem isClosed_covRange (S : Matrix (Fin 2) (Fin 2) ℝ) : IsClosed (covRange S : Set ℂ) :=
  Submodule.closed_of_finiteDimensional _

theorem exists_stdGaussian_lower_bound {S M : Matrix (Fin 2) (Fin 2) ℝ} (h : M * Mᵀ = S) :
    ∃ q₀ : ℝ≥0∞, 0 < q₀ ∧ ∀ z ∈ covRange S, ‖z‖ ≤ 2 →
      q₀ ≤ stdGaussian (EuclideanSpace ℝ (Fin 2)) {x | ‖cmap M x - z‖ < 1} := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin 2)) with hγ
  have hK : IsCompact ((covRange S : Set ℂ) ∩ Metric.closedBall 0 2) :=
    (isCompact_closedBall (0 : ℂ) 2).inter_left (isClosed_covRange S)
  have hc := continuous_cmap M
  let V : ℂ → Set (EuclideanSpace ℝ (Fin 2)) := fun z => {x | ‖cmap M x - z‖ < 1 / 2}
  have hVpos : ∀ z ∈ covRange S, 0 < γ (V z) := by
    intro z hz
    obtain ⟨x₀, hx₀⟩ := exists_cmap_eq h hz
    refine IsOpen.measure_pos γ (isOpen_lt (continuous_norm.comp (hc.sub continuous_const))
      continuous_const) ⟨x₀, ?_⟩
    simp [V, hx₀]
  obtain ⟨t, htK, htcov⟩ := hK.elim_nhds_subcover (fun z => Metric.ball z (1 / 2))
    (fun z _ => Metric.ball_mem_nhds z (by norm_num))
  refine ⟨t.inf fun z => γ (V z),
    (Finset.lt_inf_iff ENNReal.zero_lt_top).2 fun z hz => hVpos z (htK z hz).1, ?_⟩
  intro z hz hz2
  have hzK : z ∈ (covRange S : Set ℂ) ∩ Metric.closedBall 0 2 := ⟨hz, by simpa using hz2⟩
  have := htcov hzK
  simp only [Set.mem_iUnion, exists_prop] at this
  obtain ⟨z₀, hz₀, hzz₀⟩ := this
  refine (Finset.inf_le hz₀).trans (measure_mono ?_)
  intro x hx
  change ‖cmap M x - z₀‖ < 1 / 2 at hx
  change ‖cmap M x - z‖ < 1
  rw [Metric.mem_ball, dist_eq_norm] at hzz₀
  calc ‖cmap M x - z‖ = ‖(cmap M x - z₀) + (z₀ - z)‖ := by ring_nf
    _ ≤ ‖cmap M x - z₀‖ + ‖z₀ - z‖ := norm_add_le _ _
    _ < 1 := by rw [norm_sub_rev z₀ z] at *; linarith

theorem quadForm_nonneg {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c ^ 2 ≤ a * b)
    (x₀ x₁ : ℝ) : 0 ≤ x₀ * (a * x₀ + c * x₁) + x₁ * (c * x₀ + b * x₁) := by
  rcases ha.eq_or_lt with h0 | hpos
  · subst h0
    have : c = 0 := by nlinarith [sq_nonneg c]
    subst this
    nlinarith [mul_nonneg hb (sq_nonneg x₁)]
  · have h1 : 0 ≤ a * (x₀ * (a * x₀ + c * x₁) + x₁ * (c * x₀ + b * x₁)) := by
      nlinarith [sq_nonneg (a * x₀ + c * x₁), mul_nonneg (sub_nonneg.2 hc) (sq_nonneg x₁)]
    exact nonneg_of_mul_nonneg_right h1 hpos

/-- `Σ = covMatrix a b c` is positive semidefinite for `a, b ≥ 0`, `c² ≤ a b`. -/
theorem covMatrix_posSemidef' {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c ^ 2 ≤ a * b) :
    (ComplexSLE.covMatrix a b c).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [ComplexSLE.covMatrix]
  · intro x
    simpa [dotProduct, Matrix.mulVec, ComplexSLE.covMatrix, Fin.sum_univ_two] using
      quadForm_nonneg ha hb hc (x 0) (x 1)

theorem exists_mul_transpose {S : Matrix (Fin 2) (Fin 2) ℝ} (hS : S.PosSemidef) :
    ∃ M : Matrix (Fin 2) (Fin 2) ℝ, M * Mᵀ = S := by
  refine ⟨CFC.sqrt S, ?_⟩
  have h1 : (CFC.sqrt S).PosSemidef := by
    rw [← nonneg_iff_posSemidef]; exact CFC.sqrt_nonneg S
  have h2 := h1.isHermitian
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial, h2.eq]
  exact CFC.sqrt_mul_sqrt_self S hS.nonneg

/-- **Scaled ball lower bound.** For a positive semidefinite `S`, there is `q₀ > 0` such that
for every `t > 0` and every `y` in the range of `S` with `‖y‖ ≤ 2 √t`, the centered Gaussian
`complexGaussian (t • S)` gives mass at least `q₀` to the ball of radius `√t` around `y`. -/
theorem exists_complexGaussian_ball_lower_bound {S : Matrix (Fin 2) (Fin 2) ℝ}
    (hS : S.PosSemidef) :
    ∃ q₀ : ℝ≥0∞, 0 < q₀ ∧ ∀ t : ℝ, 0 < t → ∀ y ∈ covRange S, ‖y‖ ≤ 2 * Real.sqrt t →
      q₀ ≤ complexGaussian (t • S) (Metric.ball y (Real.sqrt t)) := by
  obtain ⟨M, hM⟩ := exists_mul_transpose hS
  obtain ⟨q₀, hq₀, hq⟩ := exists_stdGaussian_lower_bound hM
  refine ⟨q₀, hq₀, fun t ht y hy hy2 => ?_⟩
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  rw [complexGaussian_smul_eq_map hM ht.le, Measure.map_apply (by
    have := continuous_cmap M
    fun_prop) Metric.isOpen_ball.measurableSet]
  have hyR : (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * y ∈ covRange S := by
    have := (covRange S).smul_mem (Real.sqrt t)⁻¹ hy
    simpa [Complex.real_smul] using this
  have hnorm : ‖(((Real.sqrt t)⁻¹ : ℝ) : ℂ) * y‖ ≤ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)]
    rw [inv_mul_le_iff₀ hs]
    linarith
  refine (hq _ hyR hnorm).trans (measure_mono ?_)
  intro x hx
  change ‖cmap M x - (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * y‖ < 1 at hx
  change (((Real.sqrt t : ℝ) : ℂ) * cmap M x) ∈ Metric.ball y (Real.sqrt t)
  rw [Metric.mem_ball, dist_eq_norm]
  have : ((Real.sqrt t : ℝ) : ℂ) * cmap M x - y =
      ((Real.sqrt t : ℝ) : ℂ) * (cmap M x - (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * y) := by
    have : ((Real.sqrt t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    push_cast
    field_simp
  rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  calc Real.sqrt t * ‖cmap M x - (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * y‖ < Real.sqrt t * 1 := by
        gcongr
    _ = Real.sqrt t := mul_one _

/-- A centered Gaussian `complexGaussian (t • S)` is carried by the range of `S`. -/
theorem complexGaussian_compl_covRange {S : Matrix (Fin 2) (Fin 2) ℝ} (hS : S.PosSemidef)
    {t : ℝ} (ht : 0 ≤ t) : complexGaussian (t • S) ((covRange S : Set ℂ)ᶜ) = 0 := by
  obtain ⟨M, hM⟩ := exists_mul_transpose hS
  rw [complexGaussian_smul_eq_map hM ht, Measure.map_apply (by
    have := continuous_cmap M
    fun_prop) (isClosed_covRange S).isOpen_compl.measurableSet]
  convert measure_empty (μ := stdGaussian (EuclideanSpace ℝ (Fin 2)))
  ext x
  simp only [Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe, Set.mem_empty_iff_false,
    iff_false, not_not]
  have := (covRange S).smul_mem (Real.sqrt t) (cmap_mem_covRange hM x)
  simpa [Complex.real_smul] using this

end ComplexSLE.Infrastructure.SupportGaussian

end
