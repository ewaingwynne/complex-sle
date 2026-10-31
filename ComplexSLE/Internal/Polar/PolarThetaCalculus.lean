/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.PolarItoCalculus
public import ComplexSLE.Internal.Polar.Riemann
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Calculus for the Itô step of the argument `θ` (M6/S11)

The deterministic derivative computations behind the imaginary part of `step:polar-real-imag`.
On `ℝ⁴ = Fin 4 → ℝ` (coordinates `w = (u₀, u₁)`, `v = (u₂, u₃)`, the real and imaginary parts of
`f` stopped at two successive sector times) we consider

  `argProd u = Arg (w v̄) = Arg ((u₀ + i u₁)(u₂ - i u₃))`,

which is `C^∞` on the open set `argDomain = {u | w v̄ ∈ slitPlane}` (as `Im ∘ log ∘ prodConj`),
with gradient `(-u₁/|w|², u₀/|w|², u₃/|v|², -u₂/|v|²)` (`gradArg`) and block-diagonal Hessian
(`hessArg`). In polar coordinates, `prodConj ![r₁ cos α, r₁ sin α, r₂ cos β, r₂ sin β] =
r₁ r₂ e^{i(α - β)}`, so `argProd = α - β` as soon as `|α - β| < π`, and the point lies in
`argDomain` as soon as `|α - β| ≤ π/2`.
-/

public section

open Set Filter Topology Complex

namespace ComplexSLE.Internal.Polar

/-! ### `w v̄` and its argument -/

/-- `prodConj u = (u₀ + i u₁)(u₂ - i u₃) = w v̄`. -/
@[expose] noncomputable def prodConj (u : Fin 4 → ℝ) : ℂ :=
  ((u 0 : ℂ) + (u 1 : ℂ) * I) * ((u 2 : ℂ) - (u 3 : ℂ) * I)

/-- `argProd u = Arg (w v̄)`. -/
@[expose] noncomputable def argProd (u : Fin 4 → ℝ) : ℝ := arg (prodConj u)

/-- The open set `{u | w v̄ ∈ slitPlane}` on which `argProd` is smooth. -/
@[expose] def argDomain : Set (Fin 4 → ℝ) := {u | prodConj u ∈ slitPlane}

theorem continuous_prodConj : Continuous prodConj := by
  unfold prodConj; fun_prop

theorem isOpen_argDomain : IsOpen argDomain := isOpen_slitPlane.preimage continuous_prodConj

theorem measurable_argProd : Measurable argProd :=
  measurable_arg.comp continuous_prodConj.measurable

theorem argProd_eq_log_im (u : Fin 4 → ℝ) : argProd u = (log (prodConj u)).im :=
  (log_im _).symm

theorem contDiff_prodConj : ContDiff ℝ 2 prodConj := by
  have hc : ∀ i : Fin 4, ContDiff ℝ 2 fun u : Fin 4 → ℝ => (u i : ℂ) := fun i =>
    ofRealCLM.contDiff.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i).contDiff
  unfold prodConj
  exact ((hc 0).add ((hc 1).mul contDiff_const)).mul ((hc 2).sub ((hc 3).mul contDiff_const))

theorem contDiffOn_argProd : ContDiffOn ℝ 2 argProd argDomain := by
  have h : argProd = fun u => imCLM (log (prodConj u)) := funext fun u => argProd_eq_log_im u
  rw [h]
  intro u hu
  have hlog : ContDiffAt ℝ 2 (fun u => log (prodConj u)) u :=
    ((contDiffAt_log hu).restrict_scalars ℝ).comp u contDiff_prodConj.contDiffAt
  exact (imCLM.contDiff.contDiffAt.comp u hlog).contDiffWithinAt

/-! ### Nonvanishing of the factors -/

theorem normSq_add_mul_I (x y : ℝ) : normSq ((x : ℂ) + (y : ℂ) * I) = x ^ 2 + y ^ 2 := by
  rw [normSq_apply]; simp; ring

theorem normSq_sub_mul_I (x y : ℝ) : normSq ((x : ℂ) - (y : ℂ) * I) = x ^ 2 + y ^ 2 := by
  rw [normSq_apply]; simp; ring

theorem left_ne_zero_of_mem_argDomain {u : Fin 4 → ℝ} (hu : u ∈ argDomain) :
    (u 0 : ℂ) + (u 1 : ℂ) * I ≠ 0 :=
  left_ne_zero_of_mul (slitPlane_ne_zero hu)

theorem right_ne_zero_of_mem_argDomain {u : Fin 4 → ℝ} (hu : u ∈ argDomain) :
    (u 2 : ℂ) - (u 3 : ℂ) * I ≠ 0 :=
  right_ne_zero_of_mul (slitPlane_ne_zero hu)

theorem sq_add_sq_left_ne_zero {u : Fin 4 → ℝ} (hu : u ∈ argDomain) :
    u 0 ^ 2 + u 1 ^ 2 ≠ 0 := by
  rw [← normSq_add_mul_I]
  exact normSq_pos.2 (left_ne_zero_of_mem_argDomain hu) |>.ne'

theorem sq_add_sq_right_ne_zero {u : Fin 4 → ℝ} (hu : u ∈ argDomain) :
    u 2 ^ 2 + u 3 ^ 2 ≠ 0 := by
  rw [← normSq_sub_mul_I]
  exact normSq_pos.2 (right_ne_zero_of_mem_argDomain hu) |>.ne'

/-! ### First derivatives -/

/-- Derivative of the polynomial map `prodConj`. -/
theorem hasFDerivAt_prodConj (u : Fin 4 → ℝ) :
    ∃ L : (Fin 4 → ℝ) →L[ℝ] ℂ, HasFDerivAt prodConj L u ∧
      ∀ e, L e = ((e 0 : ℂ) + (e 1 : ℂ) * I) * ((u 2 : ℂ) - (u 3 : ℂ) * I) +
        ((u 0 : ℂ) + (u 1 : ℂ) * I) * ((e 2 : ℂ) - (e 3 : ℂ) * I) := by
  have hc : ∀ i : Fin 4, HasFDerivAt (fun u : Fin 4 → ℝ => (u i : ℂ))
      (ofRealCLM.comp (ContinuousLinearMap.proj i)) u := fun i =>
    ofRealCLM.hasFDerivAt.comp u (hasFDerivAt_apply (𝕜 := ℝ) i u)
  refine ⟨_, ((hc 0).add ((hc 1).mul_const I)).mul ((hc 2).sub ((hc 3).mul_const I)),
    fun e => ?_⟩
  simp only [add_apply, smul_apply, sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, ofRealCLM_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply]
  ring

/-- Derivative of `argProd = Im ∘ log ∘ prodConj` on `argDomain`. -/
theorem hasFDerivAt_argProd {u : Fin 4 → ℝ} (hu : u ∈ argDomain) :
    ∃ L : (Fin 4 → ℝ) →L[ℝ] ℝ, HasFDerivAt argProd L u ∧
      ∀ e, L e = ((prodConj u)⁻¹ * (((e 0 : ℂ) + (e 1 : ℂ) * I) * ((u 2 : ℂ) - (u 3 : ℂ) * I) +
        ((u 0 : ℂ) + (u 1 : ℂ) * I) * ((e 2 : ℂ) - (e 3 : ℂ) * I))).im := by
  obtain ⟨Lp, hLp, hLp'⟩ := hasFDerivAt_prodConj u
  have hlog := (hasStrictFDerivAt_log_real hu).hasFDerivAt.comp u hLp
  have him := imCLM.hasFDerivAt.comp u hlog
  have h : argProd = fun u => imCLM (log (prodConj u)) := funext fun u => argProd_eq_log_im u
  refine ⟨_, by rw [h]; exact him, fun e => ?_⟩
  simp [hLp']

/-- The gradient of `argProd`: `(-u₁/|w|², u₀/|w|², u₃/|v|², -u₂/|v|²)`. -/
@[expose] noncomputable def gradArg (u : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![-u 1 * (u 0 ^ 2 + u 1 ^ 2)⁻¹, u 0 * (u 0 ^ 2 + u 1 ^ 2)⁻¹,
    u 3 * (u 2 ^ 2 + u 3 ^ 2)⁻¹, -u 2 * (u 2 ^ 2 + u 3 ^ 2)⁻¹]

theorem fderiv_argProd_single {u : Fin 4 → ℝ} (hu : u ∈ argDomain) (i : Fin 4) :
    fderiv ℝ argProd u (Pi.single i 1) = gradArg u i := by
  obtain ⟨L, hL, hL'⟩ := hasFDerivAt_argProd hu
  rw [hL.fderiv, hL']
  have hw := left_ne_zero_of_mem_argDomain hu
  have hv := right_ne_zero_of_mem_argDomain hu
  have hq0 := sq_add_sq_left_ne_zero hu
  have hq1 := sq_add_sq_right_ne_zero hu
  set w : ℂ := (u 0 : ℂ) + (u 1 : ℂ) * I with hwdef
  set v : ℂ := (u 2 : ℂ) - (u 3 : ℂ) * I with hvdef
  have hp : prodConj u = w * v := rfl
  have hwim : w⁻¹.im = -u 1 * (u 0 ^ 2 + u 1 ^ 2)⁻¹ := by
    rw [inv_im, hwdef, normSq_add_mul_I]; simp [div_eq_mul_inv]
  have hwre : w⁻¹.re = u 0 * (u 0 ^ 2 + u 1 ^ 2)⁻¹ := by
    rw [inv_re, hwdef, normSq_add_mul_I]; simp [div_eq_mul_inv]
  have hvim : v⁻¹.im = u 3 * (u 2 ^ 2 + u 3 ^ 2)⁻¹ := by
    rw [inv_im, hvdef, normSq_sub_mul_I]; simp [div_eq_mul_inv]
  have hvre : v⁻¹.re = u 2 * (u 2 ^ 2 + u 3 ^ 2)⁻¹ := by
    rw [inv_re, hvdef, normSq_sub_mul_I]; simp [div_eq_mul_inv]
  fin_cases i
  · have : (prodConj u)⁻¹ * ((((Pi.single (0 : Fin 4) (1 : ℝ) : Fin 4 → ℝ) 0 : ℝ) +
        ((Pi.single (0 : Fin 4) (1 : ℝ) : Fin 4 → ℝ) 1 : ℝ) * I) * v +
        w * (((Pi.single (0 : Fin 4) (1 : ℝ) : Fin 4 → ℝ) 2 : ℝ) -
          ((Pi.single (0 : Fin 4) (1 : ℝ) : Fin 4 → ℝ) 3 : ℝ) * I)) = w⁻¹ := by
      rw [hp]; simp; field_simp
    simp only [Fin.zero_eta, Fin.isValue] at this ⊢
    rw [this, hwim]
    simp [gradArg] <;> ring
  · have : (prodConj u)⁻¹ * ((((Pi.single (1 : Fin 4) (1 : ℝ) : Fin 4 → ℝ) 0 : ℝ) +
        ((Pi.single (1 : Fin 4) (1 : ℝ) : Fin 4 → ℝ) 1 : ℝ) * I) * v +
        w * (((Pi.single (1 : Fin 4) (1 : ℝ) : Fin 4 → ℝ) 2 : ℝ) -
          ((Pi.single (1 : Fin 4) (1 : ℝ) : Fin 4 → ℝ) 3 : ℝ) * I)) = I * w⁻¹ := by
      rw [hp]; simp; field_simp
    simp only [Fin.mk_one, Fin.isValue] at this ⊢
    rw [this, I_mul_im, hwre]
    simp [gradArg] <;> ring
  · have : (prodConj u)⁻¹ * ((((Pi.single (2 : Fin 4) (1 : ℝ) : Fin 4 → ℝ) 0 : ℝ) +
        ((Pi.single (2 : Fin 4) (1 : ℝ) : Fin 4 → ℝ) 1 : ℝ) * I) * v +
        w * (((Pi.single (2 : Fin 4) (1 : ℝ) : Fin 4 → ℝ) 2 : ℝ) -
          ((Pi.single (2 : Fin 4) (1 : ℝ) : Fin 4 → ℝ) 3 : ℝ) * I)) = v⁻¹ := by
      rw [hp]; simp; field_simp
    simp only [Fin.reduceFinMk, Fin.isValue] at this ⊢
    rw [this, hvim]
    simp [gradArg] <;> ring
  · have : (prodConj u)⁻¹ * ((((Pi.single (3 : Fin 4) (1 : ℝ) : Fin 4 → ℝ) 0 : ℝ) +
        ((Pi.single (3 : Fin 4) (1 : ℝ) : Fin 4 → ℝ) 1 : ℝ) * I) * v +
        w * (((Pi.single (3 : Fin 4) (1 : ℝ) : Fin 4 → ℝ) 2 : ℝ) -
          ((Pi.single (3 : Fin 4) (1 : ℝ) : Fin 4 → ℝ) 3 : ℝ) * I)) = -(I * v⁻¹) := by
      rw [hp]; simp; field_simp
    simp only [Fin.reduceFinMk, Fin.isValue] at this ⊢
    rw [this, neg_im, I_mul_im, hvre]
    simp [gradArg] <;> ring

/-! ### Second derivatives -/

/-- Derivative of `u ↦ u a ^ 2 + u b ^ 2`. -/
theorem hasFDerivAt_sq_add_sq (a b : Fin 4) (u : Fin 4 → ℝ) :
    ∃ L : (Fin 4 → ℝ) →L[ℝ] ℝ, HasFDerivAt (fun u : Fin 4 → ℝ => u a ^ 2 + u b ^ 2) L u ∧
      ∀ e, L e = 2 * u a * e a + 2 * u b * e b := by
  refine ⟨_, ((hasFDerivAt_apply (𝕜 := ℝ) a u).pow 2).add ((hasFDerivAt_apply (𝕜 := ℝ) b u).pow 2),
    fun e => ?_⟩
  simp

/-- Derivative of `u ↦ (u a ^ 2 + u b ^ 2)⁻¹` where the sum is nonzero. -/
theorem hasFDerivAt_inv_sq_add_sq (a b : Fin 4) {u : Fin 4 → ℝ} (hu : u a ^ 2 + u b ^ 2 ≠ 0) :
    ∃ L : (Fin 4 → ℝ) →L[ℝ] ℝ, HasFDerivAt (fun u : Fin 4 → ℝ => (u a ^ 2 + u b ^ 2)⁻¹) L u ∧
      ∀ e, L e = -((u a ^ 2 + u b ^ 2) ^ 2)⁻¹ * (2 * u a * e a + 2 * u b * e b) := by
  obtain ⟨Lq, hLq, hLq'⟩ := hasFDerivAt_sq_add_sq a b u
  refine ⟨_, (hasDerivAt_inv hu).comp_hasFDerivAt u hLq, fun e => ?_⟩
  simp [hLq']

/-- The Hessian of `argProd` (block diagonal: the Hessian of `Arg w` and minus that of `Arg v`),
written as the derivative of the `j`-th component of the gradient in direction `eᵢ`. -/
@[expose] noncomputable def hessArg (u : Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
  ![-(Pi.single i 1 : Fin 4 → ℝ) 1 * (u 0 ^ 2 + u 1 ^ 2)⁻¹ + -u 1 * (-((u 0 ^ 2 + u 1 ^ 2) ^ 2)⁻¹ *
      (2 * u 0 * (Pi.single i 1 : Fin 4 → ℝ) 0 + 2 * u 1 * (Pi.single i 1 : Fin 4 → ℝ) 1)),
    (Pi.single i 1 : Fin 4 → ℝ) 0 * (u 0 ^ 2 + u 1 ^ 2)⁻¹ + u 0 * (-((u 0 ^ 2 + u 1 ^ 2) ^ 2)⁻¹ *
      (2 * u 0 * (Pi.single i 1 : Fin 4 → ℝ) 0 + 2 * u 1 * (Pi.single i 1 : Fin 4 → ℝ) 1)),
    (Pi.single i 1 : Fin 4 → ℝ) 3 * (u 2 ^ 2 + u 3 ^ 2)⁻¹ + u 3 * (-((u 2 ^ 2 + u 3 ^ 2) ^ 2)⁻¹ *
      (2 * u 2 * (Pi.single i 1 : Fin 4 → ℝ) 2 + 2 * u 3 * (Pi.single i 1 : Fin 4 → ℝ) 3)),
    -(Pi.single i 1 : Fin 4 → ℝ) 2 * (u 2 ^ 2 + u 3 ^ 2)⁻¹ + -u 2 * (-((u 2 ^ 2 + u 3 ^ 2) ^ 2)⁻¹ *
      (2 * u 2 * (Pi.single i 1 : Fin 4 → ℝ) 2 + 2 * u 3 * (Pi.single i 1 : Fin 4 → ℝ) 3))] j

/-- Derivative of the `j`-th component of the gradient of `argProd`. -/
theorem hasFDerivAt_gradArg {u : Fin 4 → ℝ} (hu : u ∈ argDomain) (j : Fin 4) :
    ∃ L : (Fin 4 → ℝ) →L[ℝ] ℝ, HasFDerivAt (fun w => gradArg w j) L u ∧
      ∀ i : Fin 4, L (Pi.single i 1) = hessArg u i j := by
  have hq0 := sq_add_sq_left_ne_zero hu
  have hq1 := sq_add_sq_right_ne_zero hu
  obtain ⟨L0, hL0, hL0'⟩ := hasFDerivAt_inv_sq_add_sq 0 1 hq0
  obtain ⟨L1, hL1, hL1'⟩ := hasFDerivAt_inv_sq_add_sq 2 3 hq1
  fin_cases j
  · refine ⟨_, ((hasFDerivAt_apply (𝕜 := ℝ) 1 u).neg).mul hL0, fun i => ?_⟩
    simp [hL0', gradArg, hessArg] <;> ring
  · refine ⟨_, (hasFDerivAt_apply (𝕜 := ℝ) 0 u).mul hL0, fun i => ?_⟩
    simp [hL0', gradArg, hessArg] <;> ring
  · refine ⟨_, (hasFDerivAt_apply (𝕜 := ℝ) 3 u).mul hL1, fun i => ?_⟩
    simp [hL1', gradArg, hessArg] <;> ring
  · refine ⟨_, ((hasFDerivAt_apply (𝕜 := ℝ) 2 u).neg).mul hL1, fun i => ?_⟩
    simp [hL1', gradArg, hessArg] <;> ring

theorem iteratedFDeriv_argProd {u : Fin 4 → ℝ} (hu : u ∈ argDomain) (i j : Fin 4) :
    iteratedFDeriv ℝ 2 argProd u ![Pi.single i 1, Pi.single j 1] = hessArg u i j := by
  obtain ⟨L, hL, hL'⟩ := hasFDerivAt_gradArg hu j
  rw [iteratedFDeriv_two_single isOpen_argDomain contDiffOn_argProd hu
    (fun w hw => fderiv_argProd_single hw j) hL, hL']

/-! ### Polar form -/

/-- `prodConj ![r₁ cos α, r₁ sin α, r₂ cos β, r₂ sin β] = r₁ r₂ e^{i(α - β)}`. -/
theorem prodConj_polar (r₁ r₂ α β : ℝ) :
    prodConj ![r₁ * Real.cos α, r₁ * Real.sin α, r₂ * Real.cos β, r₂ * Real.sin β] =
      ((r₁ * r₂ : ℝ) : ℂ) * exp (((α - β : ℝ) : ℂ) * I) := by
  show (((r₁ * Real.cos α : ℝ) : ℂ) + ((r₁ * Real.sin α : ℝ) : ℂ) * I) *
      (((r₂ * Real.cos β : ℝ) : ℂ) - ((r₂ * Real.sin β : ℝ) : ℂ) * I) = _
  rw [exp_mul_I]
  push_cast
  rw [Complex.cos_sub, Complex.sin_sub]
  linear_combination (-((r₁ : ℂ) * r₂ * sin (α : ℂ) * sin (β : ℂ))) * I_sq

/-- `r e^{iφ} ∈ slitPlane` for `r > 0` and `|φ| ≤ π/2`. -/
theorem real_mul_exp_mem_slitPlane {r φ : ℝ} (hr : 0 < r) (hφ : |φ| ≤ Real.pi / 2) :
    (r : ℂ) * exp ((φ : ℂ) * I) ∈ slitPlane := by
  rw [mem_slitPlane_iff, re_ofReal_mul, im_ofReal_mul, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
  have hφ' := abs_le.1 hφ
  have hcos : 0 ≤ Real.cos φ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le hφ'.1 hφ'.2
  rcases hcos.lt_or_eq with h | h
  · exact Or.inl (mul_pos hr h)
  · right
    have hsin : Real.sin φ ≠ 0 := by
      intro hs
      have := Real.sin_sq_add_cos_sq φ
      rw [hs, ← h] at this
      norm_num at this
    exact mul_ne_zero hr.ne' hsin

/-- `Arg (r e^{iφ}) = φ` for `r > 0` and `|φ| < π`. -/
theorem arg_real_mul_exp {r φ : ℝ} (hr : 0 < r) (hφ : |φ| < Real.pi) :
    arg ((r : ℂ) * exp ((φ : ℂ) * I)) = φ := by
  rw [arg_real_mul _ hr]
  exact arg_exp_mul_I_of_abs_lt hφ

end ComplexSLE.Internal.Polar

end
