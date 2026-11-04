/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Calculus for the Itô step of the polar decomposition (M6/S8)

The deterministic derivative computations behind `step:polar-ito-log` and the bracket of
`log|f|`. On `ℝ³ = Fin 3 → ℝ` (coordinates `x, y, d`: the real and imaginary parts of `f` and the
accumulated drift) we consider

* `logNorm₃ w = ½ log (x² + y²)`, with gradient `(x/q, y/q, 0)` and Hessian
  `[[1/q - 2x²/q², -2xy/q², 0], [-2xy/q², 1/q - 2y²/q², 0], [0, 0, 0]]`, `q = x² + y²`;
* `sqDev w = (logNorm₃ w - d)²`, whose first and second derivatives are computed from those of
  `logNorm₃`.

The general lemma `iteratedFDeriv_two_single` expresses `iteratedFDeriv ℝ 2 F v ![eᵢ, eⱼ]` as the
derivative in direction `eᵢ` of the `j`-th partial derivative `w ↦ fderiv ℝ F w eⱼ`, which is how
the second derivatives in `External.ito_formula` are evaluated. All derivatives are stated
existentially with an explicit evaluation formula, which is all the Itô integrand needs.
-/

public section

open Set Filter Topology

namespace ComplexSLE.Internal.Polar

/-! ### Second derivatives in coordinate directions -/

/-- `iteratedFDeriv ℝ 2 F v ![eᵢ, eⱼ]` is the derivative in direction `eᵢ` of the `j`-th partial
derivative, for `F` of class `C²` on an open set `D ∋ v`. -/
theorem iteratedFDeriv_two_single {n : ℕ} {F : (Fin n → ℝ) → ℝ} {D : Set (Fin n → ℝ)}
    (hD : IsOpen D) (hF : ContDiffOn ℝ 2 F D) {v : Fin n → ℝ} (hv : v ∈ D) {i j : Fin n}
    {g : (Fin n → ℝ) → ℝ} (hg : ∀ w ∈ D, fderiv ℝ F w (Pi.single j 1) = g w)
    {L : (Fin n → ℝ) →L[ℝ] ℝ} (hL : HasFDerivAt g L v) :
    iteratedFDeriv ℝ 2 F v ![Pi.single i 1, Pi.single j 1] = L (Pi.single i 1) := by
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hdiff : DifferentiableAt ℝ (fun w => fderiv ℝ F w) v :=
    ((hF.fderiv_of_isOpen hD (m := 1) (by norm_num)).differentiableOn
      (by norm_num)).differentiableAt (hD.mem_nhds hv)
  have h1 : fderiv ℝ (fun w => fderiv ℝ F w (Pi.single j 1)) v =
      (fderiv ℝ (fun w => fderiv ℝ F w) v).flip (Pi.single j 1) := by
    rw [fderiv_clm_apply hdiff (differentiableAt_const _)]
    simp
  have h2 : fderiv ℝ (fun w => fderiv ℝ F w (Pi.single j 1)) v = L := by
    rw [← hL.fderiv]
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [hD.mem_nhds hv] with w hw
    exact hg w hw
  have := congrArg (fun T : (Fin n → ℝ) →L[ℝ] ℝ => T (Pi.single i 1)) (h1.symm.trans h2)
  simpa using this

/-! ### `q(w) = x² + y²` and `½ log q` on `ℝ³` -/

/-- `q(w) = w₀² + w₁²`. -/
@[expose] def sqNorm₃ (w : Fin 3 → ℝ) : ℝ := w 0 ^ 2 + w 1 ^ 2

/-- `½ log (w₀² + w₁²)`. -/
@[expose] noncomputable def logNorm₃ (w : Fin 3 → ℝ) : ℝ := (1 / 2) * Real.log (sqNorm₃ w)

/-- `(½ log (w₀² + w₁²) - w₂)²`. -/
@[expose] noncomputable def sqDev (w : Fin 3 → ℝ) : ℝ := (logNorm₃ w - w 2) ^ 2

/-- The open set `{w | w₀² + w₁² > 0}` on which both functions are smooth. -/
@[expose] def posSet₃ : Set (Fin 3 → ℝ) := {w | 0 < sqNorm₃ w}

theorem continuous_sqNorm₃ : Continuous sqNorm₃ := by
  unfold sqNorm₃; fun_prop

theorem isOpen_posSet₃ : IsOpen posSet₃ := isOpen_lt continuous_const continuous_sqNorm₃

theorem contDiff_sqNorm₃ : ContDiff ℝ 2 sqNorm₃ := by
  unfold sqNorm₃; fun_prop

theorem contDiffOn_logNorm₃ : ContDiffOn ℝ 2 logNorm₃ posSet₃ := by
  unfold logNorm₃
  exact contDiffOn_const.mul (contDiff_sqNorm₃.contDiffOn.log fun v hv => ne_of_gt hv)

theorem contDiffOn_sqDev : ContDiffOn ℝ 2 sqDev posSet₃ := by
  unfold sqDev
  have h2 : ContDiffOn ℝ 2 (fun w : Fin 3 → ℝ => w 2) posSet₃ := by fun_prop
  exact (contDiffOn_logNorm₃.sub h2).pow 2

theorem measurable_logNorm₃ : Measurable logNorm₃ := by
  unfold logNorm₃ sqNorm₃; fun_prop

theorem measurable_sqDev : Measurable sqDev := by
  unfold sqDev
  exact (measurable_logNorm₃.sub (measurable_pi_apply 2)).pow_const 2

/-- First derivative of `q`. -/
theorem hasFDerivAt_sqNorm₃ (v : Fin 3 → ℝ) :
    ∃ L : (Fin 3 → ℝ) →L[ℝ] ℝ, HasFDerivAt sqNorm₃ L v ∧
      ∀ u, L u = 2 * v 0 * u 0 + 2 * v 1 * u 1 := by
  refine ⟨_, ((hasFDerivAt_apply (𝕜 := ℝ) 0 v).pow 2).add ((hasFDerivAt_apply (𝕜 := ℝ) 1 v).pow 2),
    fun u => ?_⟩
  simp

/-- First derivative of `½ log q`. -/
theorem hasFDerivAt_logNorm₃ {v : Fin 3 → ℝ} (hv : v ∈ posSet₃) :
    ∃ L : (Fin 3 → ℝ) →L[ℝ] ℝ, HasFDerivAt logNorm₃ L v ∧
      ∀ u, L u = (sqNorm₃ v)⁻¹ * (v 0 * u 0 + v 1 * u 1) := by
  obtain ⟨Lq, hLq, hLq'⟩ := hasFDerivAt_sqNorm₃ v
  refine ⟨_, (hLq.log (ne_of_gt hv)).const_mul (1 / 2), fun u => ?_⟩
  simp [hLq']
  ring

/-- The gradient of `½ log q`: `(x/q, y/q, 0)`. -/
@[expose] noncomputable def gradLog₃ (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![v 0 * (sqNorm₃ v)⁻¹, v 1 * (sqNorm₃ v)⁻¹, 0]

theorem fderiv_logNorm₃_single {v : Fin 3 → ℝ} (hv : v ∈ posSet₃) (i : Fin 3) :
    fderiv ℝ logNorm₃ v (Pi.single i 1) = gradLog₃ v i := by
  obtain ⟨L, hL, hL'⟩ := hasFDerivAt_logNorm₃ hv
  rw [hL.fderiv, hL']
  fin_cases i <;> simp [gradLog₃] <;> ring

/-- Derivative of `(q w)⁻¹`. -/
theorem hasFDerivAt_inv_sqNorm₃ {v : Fin 3 → ℝ} (hv : v ∈ posSet₃) :
    ∃ L : (Fin 3 → ℝ) →L[ℝ] ℝ, HasFDerivAt (fun w => (sqNorm₃ w)⁻¹) L v ∧
      ∀ u, L u = -(sqNorm₃ v ^ 2)⁻¹ * (2 * v 0 * u 0 + 2 * v 1 * u 1) := by
  obtain ⟨Lq, hLq, hLq'⟩ := hasFDerivAt_sqNorm₃ v
  refine ⟨_, (hasDerivAt_inv (ne_of_gt hv)).comp_hasFDerivAt v hLq, fun u => ?_⟩
  simp [hLq']

/-- Derivative of the `j`-th component of the gradient of `½ log q`. -/
theorem hasFDerivAt_gradLog₃ {v : Fin 3 → ℝ} (hv : v ∈ posSet₃) (j : Fin 3) :
    ∃ L : (Fin 3 → ℝ) →L[ℝ] ℝ, HasFDerivAt (fun w => gradLog₃ w j) L v ∧
      ∀ u, L u = gradLog₃ v j * (-(sqNorm₃ v)⁻¹ * (2 * v 0 * u 0 + 2 * v 1 * u 1)) +
        (sqNorm₃ v)⁻¹ * (![u 0, u 1, 0] j) := by
  obtain ⟨Li, hLi, hLi'⟩ := hasFDerivAt_inv_sqNorm₃ hv
  have hq : sqNorm₃ v ≠ 0 := ne_of_gt hv
  fin_cases j
  · refine ⟨_, (hasFDerivAt_apply (𝕜 := ℝ) 0 v).mul hLi, fun u => ?_⟩
    simp [hLi', gradLog₃]
    ring
  · refine ⟨_, (hasFDerivAt_apply (𝕜 := ℝ) 1 v).mul hLi, fun u => ?_⟩
    simp [hLi', gradLog₃]
    ring
  · refine ⟨0, ?_, fun u => ?_⟩
    · simpa [gradLog₃] using hasFDerivAt_const (0 : ℝ) v
    · simp [gradLog₃]

/-- The Hessian of `½ log q`. -/
@[expose] noncomputable def hessLog₃ (v : Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  gradLog₃ v j * (-(sqNorm₃ v)⁻¹ * (2 * v 0 * (Pi.single i 1 : Fin 3 → ℝ) 0 +
    2 * v 1 * (Pi.single i 1 : Fin 3 → ℝ) 1)) +
    (sqNorm₃ v)⁻¹ * (![(Pi.single i 1 : Fin 3 → ℝ) 0, (Pi.single i 1 : Fin 3 → ℝ) 1, 0] j)

theorem iteratedFDeriv_logNorm₃ {v : Fin 3 → ℝ} (hv : v ∈ posSet₃) (i j : Fin 3) :
    iteratedFDeriv ℝ 2 logNorm₃ v ![Pi.single i 1, Pi.single j 1] = hessLog₃ v i j := by
  obtain ⟨L, hL, hL'⟩ := hasFDerivAt_gradLog₃ hv j
  rw [iteratedFDeriv_two_single isOpen_posSet₃ contDiffOn_logNorm₃ hv
    (fun w hw => fderiv_logNorm₃_single hw j) hL, hL']
  rfl

/-! ### `(½ log q - d)²` -/

/-- The deviation `½ log q - d`. -/
@[expose] noncomputable def logDev (w : Fin 3 → ℝ) : ℝ := logNorm₃ w - w 2

/-- The gradient of the deviation: `(x/q, y/q, -1)`. -/
@[expose] noncomputable def gradDev (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![v 0 * (sqNorm₃ v)⁻¹, v 1 * (sqNorm₃ v)⁻¹, -1]

theorem hasFDerivAt_logDev {v : Fin 3 → ℝ} (hv : v ∈ posSet₃) :
    ∃ L : (Fin 3 → ℝ) →L[ℝ] ℝ, HasFDerivAt logDev L v ∧
      ∀ u, L u = (sqNorm₃ v)⁻¹ * (v 0 * u 0 + v 1 * u 1) - u 2 := by
  obtain ⟨L, hL, hL'⟩ := hasFDerivAt_logNorm₃ hv
  exact ⟨_, hL.sub (hasFDerivAt_apply (𝕜 := ℝ) 2 v), fun u => by simp [hL']⟩

theorem hasFDerivAt_sqDev {v : Fin 3 → ℝ} (hv : v ∈ posSet₃) :
    ∃ L : (Fin 3 → ℝ) →L[ℝ] ℝ, HasFDerivAt sqDev L v ∧
      ∀ u, L u = 2 * logDev v * ((sqNorm₃ v)⁻¹ * (v 0 * u 0 + v 1 * u 1) - u 2) := by
  obtain ⟨L, hL, hL'⟩ := hasFDerivAt_logDev hv
  refine ⟨_, hL.pow 2, fun u => ?_⟩
  simp [hL', logDev]

theorem fderiv_sqDev_single {v : Fin 3 → ℝ} (hv : v ∈ posSet₃) (i : Fin 3) :
    fderiv ℝ sqDev v (Pi.single i 1) = 2 * logDev v * gradDev v i := by
  obtain ⟨L, hL, hL'⟩ := hasFDerivAt_sqDev hv
  rw [hL.fderiv, hL']
  congr 1
  fin_cases i <;> simp [gradDev] <;> ring

/-- Derivative of the `j`-th component of the gradient of the deviation. -/
theorem hasFDerivAt_gradDev {v : Fin 3 → ℝ} (hv : v ∈ posSet₃) (j : Fin 3) :
    ∃ L : (Fin 3 → ℝ) →L[ℝ] ℝ, HasFDerivAt (fun w => gradDev w j) L v ∧
      ∀ u, L u = gradLog₃ v j * (-(sqNorm₃ v)⁻¹ * (2 * v 0 * u 0 + 2 * v 1 * u 1)) +
        (sqNorm₃ v)⁻¹ * (![u 0, u 1, 0] j) := by
  obtain ⟨L, hL, hL'⟩ := hasFDerivAt_gradLog₃ hv j
  refine ⟨L, ?_, hL'⟩
  refine (hL.sub_const (![0, 0, 1] j)).congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
  fin_cases j <;> simp [gradDev, gradLog₃]

/-- Second derivatives of `(½ log q - d)²`:
`∂ᵢⱼ = 2 ∂ᵢⱼ(½ log q) (½ log q - d) + 2 ∂ᵢ(½ log q - d) ∂ⱼ(½ log q - d)`. -/
theorem iteratedFDeriv_sqDev {v : Fin 3 → ℝ} (hv : v ∈ posSet₃) (i j : Fin 3) :
    iteratedFDeriv ℝ 2 sqDev v ![Pi.single i 1, Pi.single j 1] =
      2 * logDev v * hessLog₃ v i j + 2 * gradDev v i * gradDev v j := by
  obtain ⟨LE, hLE, hLE'⟩ := hasFDerivAt_logDev hv
  obtain ⟨Lg, hLg, hLg'⟩ := hasFDerivAt_gradDev hv j
  have hg : HasFDerivAt (fun w => 2 * logDev w * gradDev w j)
      ((2 * logDev v) • Lg + gradDev v j • ((2 : ℝ) • LE)) v :=
    (hLE.const_mul 2).mul hLg
  rw [iteratedFDeriv_two_single isOpen_posSet₃ contDiffOn_sqDev hv
    (fun w hw => fderiv_sqDev_single hw j) hg]
  simp only [add_apply, smul_apply, smul_eq_mul, hLg', hLE']
  unfold hessLog₃
  have : (sqNorm₃ v)⁻¹ *
      (v 0 * (Pi.single i 1 : Fin 3 → ℝ) 0 + v 1 * (Pi.single i 1 : Fin 3 → ℝ) 1) -
      (Pi.single i 1 : Fin 3 → ℝ) 2 = gradDev v i := by
    fin_cases i <;> simp [gradDev] <;> ring
  rw [this]
  ring

end ComplexSLE.Internal.Polar

end
