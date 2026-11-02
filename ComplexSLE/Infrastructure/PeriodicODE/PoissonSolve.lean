/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Primitive
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The integrating-factor solution of `h' + a h = ρ`

For continuous `a` and `ρ`, with `A x = ∫₀ˣ a`, the general solution of `h' + a h = ρ` is
`h = e^{-A} (K + ∫₀ˣ e^{A} ρ)` (`linSol a ρ K`). If `a` and `ρ` are `T`-periodic then
`A (x + T) = A x + A T`, so `linSol a ρ K` is `T`-periodic as soon as
`e^{-A T} (K + ∫₀ᵀ e^{A} ρ) = K`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory intervalIntegral Function
open scoped ContDiff

namespace ComplexSLE.Infrastructure

/-- The primitive `A x = ∫₀ˣ a`. -/
noncomputable def primA (a : ℝ → ℝ) (x : ℝ) : ℝ := ∫ u in (0)..x, a u

/-- The solution `e^{-A x} (K + ∫₀ˣ e^{A} ρ)` of `h' + a h = ρ` with `h 0 = K`. -/
noncomputable def linSol (a ρ : ℝ → ℝ) (K x : ℝ) : ℝ :=
  Real.exp (-primA a x) * (K + ∫ u in (0)..x, Real.exp (primA a u) * ρ u)

variable {a ρ : ℝ → ℝ} {T : ℝ}

theorem hasDerivAt_primA (ha : Continuous a) (x : ℝ) : HasDerivAt (primA a) (a x) x :=
  hasDerivAt_integral_of_continuous ha 0 x

theorem continuous_primA (ha : Continuous a) : Continuous (primA a) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_primA ha x).continuousAt

theorem primA_add_period (ha : Continuous a) (haper : Periodic a T) (x : ℝ) :
    primA a (x + T) = primA a x + primA a T := by
  have := haper.intervalIntegral_add_eq_add 0 x (fun _ _ => ha.intervalIntegrable _ _)
  simpa only [primA, zero_add] using this

theorem hasDerivAt_linSol (ha : Continuous a) (hρ : Continuous ρ) (K x : ℝ) :
    HasDerivAt (linSol a ρ K) (ρ x - a x * linSol a ρ K x) x := by
  have hA := hasDerivAt_primA ha x
  have hE : HasDerivAt (fun y => Real.exp (-primA a y)) (Real.exp (-primA a x) * (-a x)) x :=
    hA.neg.exp
  have hcont : Continuous fun u => Real.exp (primA a u) * ρ u :=
    (continuous_primA ha).rexp.mul hρ
  have hW : HasDerivAt (fun y => K + ∫ u in (0)..y, Real.exp (primA a u) * ρ u)
      (Real.exp (primA a x) * ρ x) x :=
    (hasDerivAt_integral_of_continuous hcont 0 x).const_add K
  have h := hE.mul hW
  have hee : Real.exp (-primA a x) * Real.exp (primA a x) = 1 := by
    rw [← Real.exp_add]; simp
  refine (show HasDerivAt (linSol a ρ K) _ x from h).congr_deriv ?_
  unfold linSol
  linear_combination (ρ x) * hee

theorem continuous_linSol (ha : Continuous a) (hρ : Continuous ρ) (K : ℝ) :
    Continuous (linSol a ρ K) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_linSol ha hρ K x).continuousAt

theorem deriv_linSol (ha : Continuous a) (hρ : Continuous ρ) (K x : ℝ) :
    deriv (linSol a ρ K) x = ρ x - a x * linSol a ρ K x :=
  (hasDerivAt_linSol ha hρ K x).deriv

theorem contDiff_one_linSol (ha : Continuous a) (hρ : Continuous ρ) (K : ℝ) :
    ContDiff ℝ 1 (linSol a ρ K) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (hasDerivAt_linSol ha hρ K x).differentiableAt, ?_⟩
  have : deriv (linSol a ρ K) = fun x => ρ x - a x * linSol a ρ K x :=
    funext (deriv_linSol ha hρ K)
  rw [this]
  exact hρ.sub (ha.mul (continuous_linSol ha hρ K))

/-- Shifting the argument of `linSol` by a period. -/
theorem linSol_add_period (ha : Continuous a) (hρ : Continuous ρ) (haper : Periodic a T)
    (hρper : Periodic ρ T) (K x : ℝ) :
    linSol a ρ K (x + T) = Real.exp (-primA a x) *
      (Real.exp (-primA a T) * (K + ∫ u in (0)..T, Real.exp (primA a u) * ρ u) +
        ∫ u in (0)..x, Real.exp (primA a u) * ρ u) := by
  set w : ℝ → ℝ := fun u => Real.exp (primA a u) * ρ u with hw
  have hwc : Continuous w := (continuous_primA ha).rexp.mul hρ
  have hshift : ∀ u, w (u + T) = Real.exp (primA a T) * w u := by
    intro u
    simp only [hw, primA_add_period ha haper, hρper u, Real.exp_add]
    ring
  have h1 : ∫ u in (0)..(x + T), w u = (∫ u in (0)..T, w u) + ∫ u in T..(x + T), w u :=
    (integral_add_adjacent_intervals (hwc.intervalIntegrable _ _)
      (hwc.intervalIntegrable _ _)).symm
  have h2 : ∫ u in T..(x + T), w u = Real.exp (primA a T) * ∫ u in (0)..x, w u := by
    have := intervalIntegral.integral_comp_add_right (a := 0) (b := x) w T
    rw [zero_add] at this
    rw [← this]
    simp only [hshift]
    exact intervalIntegral.integral_const_mul _ _
  have hee : Real.exp (-primA a T) * Real.exp (primA a T) = 1 := by
    rw [← Real.exp_add]; simp
  unfold linSol
  rw [primA_add_period ha haper, h1, h2, neg_add, Real.exp_add]
  linear_combination (Real.exp (-primA a x) * ∫ u in (0)..x, w u) * hee

/-- `linSol a ρ K` is `T`-periodic if `e^{-A T} (K + ∫₀ᵀ e^{A} ρ) = K`. -/
theorem periodic_linSol (ha : Continuous a) (hρ : Continuous ρ) (haper : Periodic a T)
    (hρper : Periodic ρ T) {K : ℝ}
    (hK : Real.exp (-primA a T) * (K + ∫ u in (0)..T, Real.exp (primA a u) * ρ u) = K) :
    Periodic (linSol a ρ K) T := by
  intro x
  rw [linSol_add_period ha hρ haper hρper, hK]
  rfl

/-- If `A T ≠ 0`, some `linSol a ρ K` is `T`-periodic. -/
theorem exists_periodic_linSol_of_ne (ha : Continuous a) (hρ : Continuous ρ)
    (haper : Periodic a T) (hρper : Periodic ρ T) (hAT : primA a T ≠ 0) :
    ∃ K : ℝ, Periodic (linSol a ρ K) T := by
  set I : ℝ := ∫ u in (0)..T, Real.exp (primA a u) * ρ u with hI
  have he : Real.exp (primA a T) - 1 ≠ 0 := by
    intro h
    exact hAT (Real.exp_eq_one_iff _ |>.1 (by linarith))
  refine ⟨I / (Real.exp (primA a T) - 1), periodic_linSol ha hρ haper hρper ?_⟩
  have hpos : Real.exp (primA a T) ≠ 0 := (Real.exp_pos _).ne'
  rw [Real.exp_neg]
  field_simp
  ring

end ComplexSLE.Infrastructure

end
