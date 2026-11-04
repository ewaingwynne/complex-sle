/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsSLEDriver
import ComplexSLE.Internal.Driver.GaussianMap

/-!
# Scaling and symmetries of the driver of `SLE_Σ`

Internal lemmas about the sealed predicate `IsSLEDriver`.

* `IsSLEDriver.scale` (Brownian scaling, paper.tex:L774-780): if `U` is an `SLE_Σ` driver and
  `r > 0`, then `s ↦ r U(s / r²)` is again an `SLE_Σ` driver with the same `(a, b, c)`.
* `IsSLEDriver.neg` (`-U =_d U`, paper.tex:L984): `-U` is an `SLE_Σ` driver with the same
  `(a, b, c)`.
* `IsSLEDriver.conjugate` (reflection, (2.2)): `conj U` is an `SLE_{Σ'}` driver with `c' = -c`.
* `IsSLEDriver.mul_I` (multiplication by `i`, used for duality): `i U` is an `SLE_{Σ'}` driver
  with `(a', b', c') = (b, a, -c)`, since `i (x + i y) = -y + i x`.

All four are instances of one lemma, `IsSLEDriver.map_linear`: a real-linear image
`L (U (s / κ))` of the driver with invertible matrix `M` is again a driver, provided
`M Σ Mᵀ = κ Σ'`. No positivity of `Σ` is assumed anywhere: for non-positive-semidefinite `Σ` the
law `complexGaussian` degenerates to the Dirac mass at `0` and the statements remain true.
-/

public section

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal ComplexConjugate

namespace ComplexSLE

/-- Precomposing a process with independent increments with a monotone time change keeps the
independence of increments. -/
theorem _root_.ProbabilityTheory.HasIndepIncrements.comp_monotone {T T' Ω E : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [Preorder T] [Preorder T'] [Sub E]
    [MeasurableSpace E] {X : T' → Ω → E} (h : HasIndepIncrements X P) {φ : T → T'}
    (hφ : Monotone φ) : HasIndepIncrements (fun s => X (φ s)) P :=
  fun n t ht => h n (φ ∘ t) (hφ.comp ht)

namespace IsSLEDriver

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- An `SLE_Σ` driver lives on a probability space. -/
theorem isProbabilityMeasure (hU : IsSLEDriver a b c U P) : IsProbabilityMeasure P :=
  (hU.law_increment 0 0 le_rfl).isProbabilityMeasure

/-- A real-linear image `s ↦ L (U (s / κ))` of an `SLE_Σ` driver, with `L` additive and continuous
with invertible `(re, im)`-matrix `M`, is an `SLE_{Σ'}` driver whenever `M Σ Mᵀ = κ Σ'`. -/
theorem map_linear (hU : IsSLEDriver a b c U P) {a' b' c' : ℝ} (κ : ℝ≥0) (hκ : 0 < κ)
    (L : ℂ →+ ℂ) (hL : Continuous L) (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : IsUnit M.det)
    (hLM : ∀ x y : ℝ, L (x + y * Complex.I) =
      ((M 0 0 * x + M 0 1 * y : ℝ) : ℂ) + ((M 1 0 * x + M 1 1 * y : ℝ) : ℂ) * Complex.I)
    (hcov : M * covMatrix a b c * Mᵀ = (κ : ℝ) • covMatrix a' b' c') :
    IsSLEDriver a' b' c' (fun s ω => L (U (s / κ) ω)) P := by
  have hκ0 : (κ : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hκ.ne'
  have hdiv : Continuous fun s : ℝ≥0 => s / κ := continuous_id.div_const κ
  have hmono : Monotone fun s : ℝ≥0 => s / κ := fun s t hst => by change s / κ ≤ t / κ; gcongr
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hU.cont] with ω hω
    exact hL.comp (hω.comp hdiv)
  · filter_upwards [hU.zero] with ω hω
    simp [hω]
  · exact (hU.indepIncrements.comp_monotone hmono).map' (f := L) hL.measurable
  · intro s t hst
    have hlaw := (hU.law_increment (s / κ) (t / κ) (hmono hst)).map_complexGaussian M hM L
      hL.measurable hLM
    have hfun : (fun ω => L (U (t / κ) ω - U (s / κ) ω)) =
        fun ω => L (U (t / κ) ω) - L (U (s / κ) ω) := by
      funext ω
      exact map_sub L _ _
    rw [hfun] at hlaw
    convert hlaw using 2
    rw [Matrix.mul_smul, Matrix.smul_mul, hcov, smul_smul]
    congr 1
    rw [NNReal.coe_div, NNReal.coe_div]
    field_simp

/-- **Brownian scaling** (paper.tex:L774-780). If `U` is an `SLE_Σ` driver and `r > 0`, then
`s ↦ r U(s / r²)` is an `SLE_Σ` driver with the same `(a, b, c)`. -/
theorem scale (hU : IsSLEDriver a b c U P) (r : ℝ≥0) (hr : 0 < r) :
    IsSLEDriver a b c (fun s ω => (r : ℂ) * U (s / r ^ 2) ω) P := by
  have hr' : (r : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hr.ne'
  have := hU.map_linear (a' := a) (b' := b) (c' := c) (r ^ 2) (by positivity)
    (AddMonoidHom.mulLeft (r : ℂ)) (continuous_const.mul continuous_id)
    !![(r : ℝ), 0; 0, (r : ℝ)] (by simpa [Matrix.det_fin_two_of] using hr')
    (by intro x y; simp [Complex.ofReal_mul]; ring)
    (by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [covMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring)
  simpa using this

/-- **Negation symmetry** (`-U =_d U`, paper.tex:L984). If `U` is an `SLE_Σ` driver, so is `-U`,
with the same `(a, b, c)`. -/
theorem neg (hU : IsSLEDriver a b c U P) : IsSLEDriver a b c (fun s ω => - U s ω) P := by
  have := hU.map_linear (a' := a) (b' := b) (c' := c) 1 one_pos
    (-AddMonoidHom.id ℂ) continuous_neg
    !![(-1 : ℝ), 0; 0, -1] (by simp [Matrix.det_fin_two_of])
    (by intro x y; simp; ring)
    (by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [covMatrix, Matrix.mul_apply, Fin.sum_univ_two])
  simpa using this

/-- **Reflection** (paper (2.2)). If `U` is an `SLE_Σ` driver with `Σ = [[a, c], [c, b]]`, then
`conj U` is an `SLE_{Σ'}` driver with `Σ' = [[a, -c], [-c, b]]`. -/
theorem conjugate (hU : IsSLEDriver a b c U P) :
    IsSLEDriver a b (-c) (fun s ω => conj (U s ω)) P := by
  have := hU.map_linear (a' := a) (b' := b) (c' := -c) 1 one_pos
    (starRingEnd ℂ).toAddMonoidHom (Complex.continuous_conj)
    !![(1 : ℝ), 0; 0, -1] (by simp [Matrix.det_fin_two_of])
    (by intro x y; simp [Complex.conj_ofReal])
    (by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [covMatrix, Matrix.mul_apply, Fin.sum_univ_two])
  simpa using this

/-- **Multiplication by `i`** (used for duality, Prop 1.5). If `U` is an `SLE_Σ` driver with
`Σ = [[a, c], [c, b]]`, then `i U` is an `SLE_{Σ'}` driver with `Σ' = [[b, -c], [-c, a]]`:
indeed `i (x + i y) = -y + i x`. -/
theorem mul_I (hU : IsSLEDriver a b c U P) :
    IsSLEDriver b a (-c) (fun s ω => Complex.I * U s ω) P := by
  have := hU.map_linear (a' := b) (b' := a) (c' := -c) 1 one_pos
    (AddMonoidHom.mulLeft Complex.I) (continuous_const.mul continuous_id)
    !![(0 : ℝ), -1; 1, 0] (by simp [Matrix.det_fin_two_of])
    (by intro x y; simp; ring_nf; simp [Complex.I_sq]; ring)
    (by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [covMatrix, Matrix.mul_apply, Fin.sum_univ_two])
  simpa using this

end IsSLEDriver

end ComplexSLE

end
