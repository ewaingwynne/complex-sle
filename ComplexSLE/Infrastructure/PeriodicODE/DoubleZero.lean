/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.PeriodicODE.DoubleZeroCore

/-!
# Periodic solutions of `D h' + α h = r` with a double zero of `D`

Let `D ≥ 0` be `C²` and `T`-periodic with zero set exactly `x₀ + Tℤ` and `D'' x₀ > 0`, and let
`α`, `r` be `C²` and `T`-periodic with `α x₀ ≠ 0`. Then the first-order equation
`D h' + α h = r` has a `C¹` `T`-periodic solution `h`.

Proof outline: translate to `x₀ = 0` and, if `α 0 < 0`, reflect `u ↦ -u` so that `α 0 > 0`.
A trigonometric polynomial `φ` removes the `2`-jet of the right-hand side at `0`
(`DoubleZeroResidual`), leaving `D ρ` with `ρ` continuous and `ρ 0 = 0`; then
`exists_periodic_solution_core` solves `D K' + α K = D ρ`, and `h = φ + K`.
-/

public section

open Set Filter Topology Function

namespace ComplexSLE.Infrastructure

/-- The case `x₀ = 0` and `α 0 > 0`. -/
theorem exists_periodic_solution_zero_pos {α D r : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hα : ContDiff ℝ 2 α) (hD : ContDiff ℝ 2 D) (hr : ContDiff ℝ 2 r)
    (hαper : Periodic α T) (hDper : Periodic D T) (hrper : Periodic r T)
    (hD0 : ∀ u, 0 ≤ D u) (hDzero : ∀ u, D u = 0 ↔ ∃ n : ℤ, u = n * T)
    (hD2 : 0 < deriv (deriv D) 0) (hα0 : 0 < α 0) :
    ∃ h : ℝ → ℝ, ContDiff ℝ 1 h ∧ Periodic h T ∧ ∀ u, D u * deriv h u + α u * h u = r u := by
  obtain ⟨φ, ρ, hφc, hφper, hρc, hρper, hρ0, hφρ⟩ :=
    exists_residual_density hT hα hD hr hαper hDper hrper hD0 hDzero hD2 hα0.ne'
  obtain ⟨K, hKc, hKper, hKeq⟩ := exists_periodic_solution_core hT (hα.of_le (by norm_num)) hD
    hαper hDper hρc hρper hρ0 hD0 hDzero hD2 hα0
  refine ⟨fun u => φ u + K u, hφc.add hKc, fun u => by simp only [hφper u, hKper u], fun u => ?_⟩
  have hφd : HasDerivAt φ (deriv φ u) u :=
    ((hφc.differentiable one_ne_zero) u).hasDerivAt
  have hKd : HasDerivAt K (deriv K u) u :=
    ((hKc.differentiable one_ne_zero) u).hasDerivAt
  have h3 : HasDerivAt (fun u => φ u + K u) (deriv φ u + deriv K u) u := hφd.add hKd
  rw [h3.deriv]
  have h1 := hKeq u
  have h2 := hφρ u
  linear_combination h1 + h2

/-- The case `x₀ = 0`. -/
theorem exists_periodic_solution_zero {α D r : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hα : ContDiff ℝ 2 α) (hD : ContDiff ℝ 2 D) (hr : ContDiff ℝ 2 r)
    (hαper : Periodic α T) (hDper : Periodic D T) (hrper : Periodic r T)
    (hD0 : ∀ u, 0 ≤ D u) (hDzero : ∀ u, D u = 0 ↔ ∃ n : ℤ, u = n * T)
    (hD2 : 0 < deriv (deriv D) 0) (hα0 : α 0 ≠ 0) :
    ∃ h : ℝ → ℝ, ContDiff ℝ 1 h ∧ Periodic h T ∧ ∀ u, D u * deriv h u + α u * h u = r u := by
  rcases lt_or_gt_of_ne hα0 with hneg | hpos
  · -- reflect `u ↦ -u`
    have hneg_cd : ContDiff ℝ 2 (fun u : ℝ => -u) := contDiff_neg
    obtain ⟨h, hc, hper, heq⟩ := exists_periodic_solution_zero_pos (T := T)
      (α := fun u => -α (-u)) (D := fun u => D (-u)) (r := fun u => -r (-u)) hT
      (hα.comp hneg_cd |>.neg) (hD.comp hneg_cd) (hr.comp hneg_cd |>.neg)
      (fun u => by simp only [neg_add, ← sub_eq_add_neg, hαper.sub_eq])
      (fun u => by simp only [neg_add, ← sub_eq_add_neg, hDper.sub_eq])
      (fun u => by simp only [neg_add, ← sub_eq_add_neg, hrper.sub_eq])
      (fun u => hD0 _)
      (fun u => by
        rw [hDzero]
        constructor
        · rintro ⟨n, hn⟩; exact ⟨-n, by push_cast; linarith⟩
        · rintro ⟨n, hn⟩; exact ⟨-n, by push_cast; linarith⟩)
      (by
        have e1 : deriv (fun u : ℝ => D (-u)) = fun u => -deriv D (-u) :=
          funext fun u => deriv_comp_neg D u
        have e2 : deriv (deriv fun u : ℝ => D (-u)) = fun u => deriv (deriv D) (-u) := by
          rw [e1]; funext u
          have : deriv (fun u : ℝ => -deriv D (-u)) u = -deriv (fun u : ℝ => deriv D (-u)) u :=
            deriv.neg
          rw [this, deriv_comp_neg (deriv D) u]; ring
        rw [e2]; simpa using hD2)
      (by simpa using hneg)
    refine ⟨fun u => h (-u), hc.comp contDiff_neg, fun u => ?_, fun u => ?_⟩
    · simp only [neg_add, ← sub_eq_add_neg, hper.sub_eq]
    · have e : deriv (fun u => h (-u)) u = -deriv h (-u) := deriv_comp_neg h u
      have := heq (-u)
      simp only [neg_neg] at this
      rw [e]
      linear_combination -this
  · exact exists_periodic_solution_zero_pos hT hα hD hr hαper hDper hrper hD0 hDzero hD2 hpos

/-- **Periodic solution with a double zero of the leading coefficient.** Let `D ≥ 0` be `C²` and
`T`-periodic whose zero set is exactly `x₀ + Tℤ` with `D'' x₀ > 0`, and let `α`, `r` be `C²`
and `T`-periodic with `α x₀ ≠ 0`. Then `D h' + α h = r` has a `C¹` `T`-periodic solution. -/
theorem exists_periodic_solution_of_doubleZero {α D r : ℝ → ℝ} {T x₀ : ℝ} (hT : 0 < T)
    (hα : ContDiff ℝ 2 α) (hD : ContDiff ℝ 2 D) (hr : ContDiff ℝ 2 r)
    (hαper : Function.Periodic α T) (hDper : Function.Periodic D T)
    (hrper : Function.Periodic r T)
    (hD0 : ∀ u, 0 ≤ D u) (hDzero : ∀ u, D u = 0 ↔ ∃ n : ℤ, u = x₀ + n * T)
    (hD2 : 0 < deriv (deriv D) x₀) (hαx₀ : α x₀ ≠ 0) :
    ∃ h : ℝ → ℝ, ContDiff ℝ 1 h ∧ Function.Periodic h T ∧
      ∀ u, D u * deriv h u + α u * h u = r u := by
  have hsh : ContDiff ℝ 2 (fun u : ℝ => u + x₀) := contDiff_id.add contDiff_const
  have hper : ∀ {f : ℝ → ℝ}, Periodic f T → Periodic (fun u => f (u + x₀)) T :=
    fun {f} hf u => by
      simp only [add_right_comm u T x₀]
      exact hf (u + x₀)
  obtain ⟨h, hc, hhper, heq⟩ := exists_periodic_solution_zero (T := T)
    (α := fun u => α (u + x₀)) (D := fun u => D (u + x₀)) (r := fun u => r (u + x₀)) hT
    (hα.comp hsh) (hD.comp hsh) (hr.comp hsh) (hper hαper) (hper hDper) (hper hrper)
    (fun u => hD0 _)
    (fun u => by
      rw [hDzero]
      constructor
      · rintro ⟨n, hn⟩; exact ⟨n, by linarith⟩
      · rintro ⟨n, hn⟩; exact ⟨n, by linarith⟩)
    (by
      have e1 : deriv (fun u : ℝ => D (u + x₀)) = fun u => deriv D (u + x₀) :=
        funext fun u => deriv_comp_add_const D x₀ u
      rw [e1, deriv_comp_add_const (deriv D) x₀ 0, zero_add]
      exact hD2)
    (by simpa using hαx₀)
  refine ⟨fun u => h (u - x₀), hc.comp (contDiff_id.sub contDiff_const), fun u => ?_, fun u => ?_⟩
  · simp only [add_sub_right_comm u T x₀]
    exact hhper (u - x₀)
  · have e : deriv (fun u => h (u - x₀)) u = deriv h (u - x₀) := deriv_comp_sub_const h x₀ u
    have := heq (u - x₀)
    simp only [sub_add_cancel] at this
    rw [e]
    exact this

end ComplexSLE.Infrastructure

end
