/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.PeriodicGlue
public import ComplexSLE.Infrastructure.PeriodicODE.DoubleZeroTaylor
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Removing the second-order jet of the right-hand side at a double zero

For the equation `D h' + α h = r` with `D` having a nondegenerate double zero at `0` and
`α 0 ≠ 0`, a smooth `T`-periodic trigonometric polynomial `φ` with prescribed `2`-jet at `0`
makes the residual `r̃ = r - (D φ' + α φ)` vanish to second order at `0`. Then
`ρ = r̃ / D` (extended by `0` on the lattice `Tℤ`) is continuous and `T`-periodic with
`ρ 0 = 0`, and `D ρ = r̃`.
-/

public section

open Set Filter Topology Real Function

namespace ComplexSLE.Infrastructure

/-- The trigonometric polynomial `c₀ + c₁ sin(ωu)/ω + c₂ (1 - cos(ωu))/ω²`. -/
noncomputable def trigPoly0 (ω c0 c1 c2 u : ℝ) : ℝ :=
  c0 + c1 * (Real.sin (ω * u) / ω) + c2 * ((1 - Real.cos (ω * u)) / ω ^ 2)

/-- First derivative of `trigPoly0`. -/
noncomputable def trigPoly1 (ω c1 c2 u : ℝ) : ℝ :=
  c1 * Real.cos (ω * u) + c2 * (Real.sin (ω * u) / ω)

/-- Second derivative of `trigPoly0`. -/
noncomputable def trigPoly2 (ω c1 c2 u : ℝ) : ℝ :=
  -(c1 * ω * Real.sin (ω * u)) + c2 * Real.cos (ω * u)

/-- Third derivative of `trigPoly0`. -/
noncomputable def trigPoly3 (ω c1 c2 u : ℝ) : ℝ :=
  -(c1 * ω ^ 2 * Real.cos (ω * u)) - c2 * ω * Real.sin (ω * u)

section trig

variable (ω c0 c1 c2 : ℝ)

private theorem hasDerivAt_sin_mul (u : ℝ) :
    HasDerivAt (fun u => Real.sin (ω * u)) (Real.cos (ω * u) * (ω * 1)) u :=
  ((hasDerivAt_id u).const_mul ω).sin

private theorem hasDerivAt_cos_mul (u : ℝ) :
    HasDerivAt (fun u => Real.cos (ω * u)) (-Real.sin (ω * u) * (ω * 1)) u :=
  ((hasDerivAt_id u).const_mul ω).cos

theorem hasDerivAt_trigPoly0 (hω : ω ≠ 0) (u : ℝ) :
    HasDerivAt (trigPoly0 ω c0 c1 c2) (trigPoly1 ω c1 c2 u) u := by
  have h1 := ((((hasDerivAt_sin_mul ω u).div_const ω).const_mul c1).const_add c0).add
    ((((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_cos_mul ω u)).div_const (ω ^ 2)).const_mul c2)
  convert h1 using 1 <;> first | rfl | (unfold trigPoly1; field_simp; try ring)

theorem hasDerivAt_trigPoly1 (hω : ω ≠ 0) (u : ℝ) :
    HasDerivAt (trigPoly1 ω c1 c2) (trigPoly2 ω c1 c2 u) u := by
  have h1 := ((hasDerivAt_cos_mul ω u).const_mul c1).add
    (((hasDerivAt_sin_mul ω u).div_const ω).const_mul c2)
  convert h1 using 1 <;> first | rfl | (unfold trigPoly2; field_simp)

theorem hasDerivAt_trigPoly2 (u : ℝ) :
    HasDerivAt (trigPoly2 ω c1 c2) (trigPoly3 ω c1 c2 u) u := by
  have h1 := (((hasDerivAt_sin_mul ω u).const_mul (c1 * ω)).neg).add
    ((hasDerivAt_cos_mul ω u).const_mul c2)
  convert h1 using 1 <;> first | rfl | (unfold trigPoly3; ring)

end trig

theorem periodic_trigPoly0 {ω T : ℝ} (h : ω * T = 2 * π) (c0 c1 c2 : ℝ) :
    Periodic (trigPoly0 ω c0 c1 c2) T := fun u => by
  unfold trigPoly0
  rw [mul_add, h, Real.sin_add_two_pi, Real.cos_add_two_pi]

theorem periodic_trigPoly1 {ω T : ℝ} (h : ω * T = 2 * π) (c1 c2 : ℝ) :
    Periodic (trigPoly1 ω c1 c2) T := fun u => by
  unfold trigPoly1
  rw [mul_add, h, Real.sin_add_two_pi, Real.cos_add_two_pi]

theorem contDiff_trigPoly0 (ω c0 c1 c2 : ℝ) : ContDiff ℝ 2 (trigPoly0 ω c0 c1 c2) := by
  unfold trigPoly0; fun_prop

theorem contDiff_trigPoly1 (ω c1 c2 : ℝ) : ContDiff ℝ 2 (trigPoly1 ω c1 c2) := by
  unfold trigPoly1; fun_prop

section resid

variable {α D r φ0 φ1 φ2 φ3 : ℝ → ℝ}

private theorem hasDerivAt_of_contDiff_two {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (u : ℝ) :
    HasDerivAt f (deriv f u) u :=
  ((contDiff_two_deriv_facts hf).1 u).hasDerivAt

private theorem hasDerivAt_deriv_of_contDiff_two {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (u : ℝ) :
    HasDerivAt (deriv f) (deriv (deriv f) u) u :=
  ((contDiff_two_deriv_facts hf).2.1 u).hasDerivAt

/-- First derivative of the residual `r - (D φ₁ + α φ₀)`. -/
theorem residual_hasDerivAt (hα : ContDiff ℝ 2 α) (hD : ContDiff ℝ 2 D) (hr : ContDiff ℝ 2 r)
    (h0 : ∀ u, HasDerivAt φ0 (φ1 u) u) (h1 : ∀ u, HasDerivAt φ1 (φ2 u) u) (u : ℝ) :
    HasDerivAt (fun u => r u - (D u * φ1 u + α u * φ0 u))
      (deriv r u - (deriv D u * φ1 u + D u * φ2 u + (deriv α u * φ0 u + α u * φ1 u))) u :=
  (hasDerivAt_of_contDiff_two hr u).sub
    (((hasDerivAt_of_contDiff_two hD u).mul (h1 u)).add
      ((hasDerivAt_of_contDiff_two hα u).mul (h0 u)))

/-- Second derivative of the residual `r - (D φ₁ + α φ₀)`. -/
theorem residual_hasDerivAt_deriv (hα : ContDiff ℝ 2 α) (hD : ContDiff ℝ 2 D)
    (hr : ContDiff ℝ 2 r) (h0 : ∀ u, HasDerivAt φ0 (φ1 u) u) (h1 : ∀ u, HasDerivAt φ1 (φ2 u) u)
    (h2 : ∀ u, HasDerivAt φ2 (φ3 u) u) (u : ℝ) :
    HasDerivAt (fun u => deriv r u -
        (deriv D u * φ1 u + D u * φ2 u + (deriv α u * φ0 u + α u * φ1 u)))
      (deriv (deriv r) u - (deriv (deriv D) u * φ1 u + deriv D u * φ2 u +
        (deriv D u * φ2 u + D u * φ3 u) + (deriv (deriv α) u * φ0 u + deriv α u * φ1 u +
        (deriv α u * φ1 u + α u * φ2 u)))) u :=
  (hasDerivAt_deriv_of_contDiff_two hr u).sub
    ((((hasDerivAt_deriv_of_contDiff_two hD u).mul (h1 u)).add
      ((hasDerivAt_of_contDiff_two hD u).mul (h2 u))).add
      (((hasDerivAt_deriv_of_contDiff_two hα u).mul (h0 u)).add
        ((hasDerivAt_of_contDiff_two hα u).mul (h1 u))))

end resid

/-- A point of `(0, T)` is not in the lattice `Tℤ`. -/
theorem not_lattice_of_mem_Ioo {T v : ℝ} (hT : 0 < T) (hv : v ∈ Ioo 0 T) :
    ¬ ∃ n : ℤ, v = n * T := by
  rintro ⟨n, rfl⟩
  have h1 : (0 : ℝ) < n := by
    by_contra h
    nlinarith [hv.1, not_lt.1 h]
  have h2 : (n : ℝ) < 1 := by
    by_contra h
    nlinarith [hv.2, not_lt.1 h]
  have h1' : 0 < n := by exact_mod_cast h1
  have h2' : n < 1 := by exact_mod_cast h2
  omega

/-- **Residual density.** For `D` with a nondegenerate double zero at the lattice `Tℤ` and
`α 0 ≠ 0`, there is a smooth periodic `φ` and a continuous periodic `ρ` with `ρ 0 = 0` and
`D ρ = r - (D φ' + α φ)`. -/
theorem exists_residual_density {α D r : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hα : ContDiff ℝ 2 α) (hD : ContDiff ℝ 2 D) (hr : ContDiff ℝ 2 r)
    (hαper : Periodic α T) (hDper : Periodic D T) (hrper : Periodic r T)
    (hD0 : ∀ u, 0 ≤ D u) (hDzero : ∀ u, D u = 0 ↔ ∃ n : ℤ, u = n * T)
    (hD2 : 0 < deriv (deriv D) 0) (hα0 : α 0 ≠ 0) :
    ∃ φ ρ : ℝ → ℝ, ContDiff ℝ 1 φ ∧ Periodic φ T ∧ Continuous ρ ∧ Periodic ρ T ∧ ρ 0 = 0 ∧
      ∀ u, D u * ρ u = r u - (D u * deriv φ u + α u * φ u) := by
  have hDz : D 0 = 0 := (hDzero 0).2 ⟨0, by simp⟩
  have hD1 : deriv D 0 = 0 := by
    have hmin : IsLocalMin D 0 := Filter.Eventually.of_forall fun x => by rw [hDz]; exact hD0 x
    exact hmin.deriv_eq_zero
  obtain ⟨δ₁, hδ₁, c, C, hc, hC, hDb⟩ := exists_sq_bounds hD hDz hD1 hD2
  set ω : ℝ := 2 * π / T with hωdef
  have hω : ω ≠ 0 := by positivity
  have hωT : ω * T = 2 * π := by rw [hωdef]; field_simp
  -- coefficients of the trigonometric polynomial
  set c0 : ℝ := r 0 / α 0 with hc0
  set c1 : ℝ := (deriv r 0 - deriv α 0 * c0) / α 0 with hc1
  set c2 : ℝ := (deriv (deriv r) 0 - deriv (deriv D) 0 * c1 - deriv (deriv α) 0 * c0
    - 2 * deriv α 0 * c1) / α 0 with hc2
  set φ0 := trigPoly0 ω c0 c1 c2 with hφ0
  set φ1 := trigPoly1 ω c1 c2 with hφ1
  set φ2 := trigPoly2 ω c1 c2 with hφ2
  set φ3 := trigPoly3 ω c1 c2 with hφ3
  have d0 : ∀ u, HasDerivAt φ0 (φ1 u) u := hasDerivAt_trigPoly0 ω c0 c1 c2 hω
  have d1 : ∀ u, HasDerivAt φ1 (φ2 u) u := hasDerivAt_trigPoly1 ω c1 c2 hω
  have d2 : ∀ u, HasDerivAt φ2 (φ3 u) u := hasDerivAt_trigPoly2 ω c1 c2
  have hφ0v : φ0 0 = c0 := by simp [hφ0, trigPoly0]
  have hφ1v : φ1 0 = c1 := by simp [hφ1, trigPoly1]
  have hφ2v : φ2 0 = c2 := by simp [hφ2, trigPoly2]
  have hφ0per : Periodic φ0 T := periodic_trigPoly0 hωT c0 c1 c2
  have hφ1per : Periodic φ1 T := periodic_trigPoly1 hωT c1 c2
  have hφ0c : ContDiff ℝ 2 φ0 := contDiff_trigPoly0 ω c0 c1 c2
  have hφ1c : ContDiff ℝ 2 φ1 := contDiff_trigPoly1 ω c1 c2
  -- the residual
  set rt : ℝ → ℝ := fun u => r u - (D u * φ1 u + α u * φ0 u) with hrt
  set R1 : ℝ → ℝ := fun u => deriv r u -
      (deriv D u * φ1 u + D u * φ2 u + (deriv α u * φ0 u + α u * φ1 u)) with hR1
  set R2 : ℝ → ℝ := fun u => deriv (deriv r) u - (deriv (deriv D) u * φ1 u + deriv D u * φ2 u +
        (deriv D u * φ2 u + D u * φ3 u) + (deriv (deriv α) u * φ0 u + deriv α u * φ1 u +
        (deriv α u * φ1 u + α u * φ2 u))) with hR2
  have hrtc : ContDiff ℝ 2 rt := hr.sub ((hD.mul hφ1c).add (hα.mul hφ0c))
  have e1 : deriv rt = R1 := funext fun u => (residual_hasDerivAt hα hD hr d0 d1 u).deriv
  have e2 : deriv R1 = R2 :=
    funext fun u => (residual_hasDerivAt_deriv hα hD hr d0 d1 d2 u).deriv
  have rt0 : rt 0 = 0 := by
    simp only [hrt, hDz, hφ0v, zero_mul, zero_add, hc0]
    field_simp
    ring
  have rt1 : deriv rt 0 = 0 := by
    rw [e1]
    simp only [hR1, hD1, hDz, hφ0v, hφ1v, zero_mul, zero_add, hc1]
    field_simp
    ring
  have rt2 : deriv (deriv rt) 0 = 0 := by
    rw [e1, e2]
    simp only [hR2, hD1, hDz, hφ0v, hφ1v, hφ2v, zero_mul, zero_add, hc2]
    field_simp
    ring
  have hrtper : Periodic rt T := fun u => by
    simp only [hrt, hrper u, hDper u, hαper u, hφ0per u, hφ1per u]
  -- the density `ρ`
  set ρ : ℝ → ℝ := fun u => if D u = 0 then 0 else rt u / D u with hρ
  have hρper : Periodic ρ T := fun u => by simp only [hρ, hDper u, hrtper u]
  have hρ0 : ρ 0 = 0 := by simp [hρ, hDz]
  have hDρ : ∀ u, D u * ρ u = rt u := fun u => by
    by_cases hu : D u = 0
    · obtain ⟨n, hn⟩ := (hDzero u).1 hu
      have : rt u = 0 := by
        rw [hn, show (n : ℝ) * T = 0 + n * T by ring, (hrtper.int_mul n) 0, rt0]
      simp [hρ, hu, this]
    · simp only [hρ, hu, ite_false]
      field_simp
  have hρcont0 : ContinuousAt ρ 0 := by
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δ₂, hδ₂, hrb⟩ := abs_le_sq_of_second_order_zero hrtc rt0 rt1 rt2
      (ε := ε * c / 2) (by positivity)
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun y hy => ?_⟩
    rw [Real.dist_eq, sub_zero] at hy
    rw [Real.dist_eq, hρ0, sub_zero]
    have hy' : |y| < min δ₁ δ₂ := hy
    have hyI₁ : y ∈ Icc (-δ₁) δ₁ := by
      have := (abs_lt.1 (hy'.trans_le (min_le_left _ _)))
      exact ⟨this.1.le, this.2.le⟩
    have hyI₂ : y ∈ Icc (-δ₂) δ₂ := by
      have := (abs_lt.1 (hy'.trans_le (min_le_right _ _)))
      exact ⟨this.1.le, this.2.le⟩
    by_cases hy0 : y = 0
    · simp [hy0, hρ0, hε]
    · have hypos : 0 < y ^ 2 := by positivity
      have hDy : c * y ^ 2 ≤ D y := (hDb y hyI₁).1
      have hDpos : 0 < D y := lt_of_lt_of_le (by positivity) hDy
      simp only [hρ, hDpos.ne', ite_false]
      rw [abs_div, abs_of_pos hDpos, div_lt_iff₀ hDpos]
      have := hrb y hyI₂
      nlinarith [hypos, mul_pos hc hypos]
  have hρcont : Continuous ρ := by
    refine Periodic.continuous_of_continuousAt_Ico (x := 0) hT hρper fun v hv => ?_
    rcases eq_or_lt_of_le hv.1 with h0v | h0v
    · rw [← h0v]; exact hρcont0
    · have hvI : v ∈ Ioo 0 T := ⟨h0v, by linarith [hv.2]⟩
      have hDv : D v ≠ 0 := fun h => not_lattice_of_mem_Ioo hT hvI ((hDzero v).1 h)
      have hev : ∀ᶠ u in 𝓝 v, D u ≠ 0 := hD.continuous.continuousAt.eventually_ne hDv
      have hq : ContinuousAt (fun u => rt u / D u) v :=
        hrtc.continuous.continuousAt.div hD.continuous.continuousAt hDv
      refine hq.congr ?_
      filter_upwards [hev] with u hu
      simp [hρ, hu]
  refine ⟨φ0, ρ, hφ0c.of_le (by norm_num), hφ0per, hρcont, hρper, hρ0, fun u => ?_⟩
  rw [hDρ u, (d0 u).deriv]

end ComplexSLE.Infrastructure

end
