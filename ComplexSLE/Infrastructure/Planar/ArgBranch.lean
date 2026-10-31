/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Algebra.Order.Group
public import ComplexSLE.Infrastructure.Planar.ChainArg

/-!
# Comparing continuous branches of the argument

Two continuous functions on a preconnected set whose exponentials `exp (i f)` and `exp (i g)`
agree differ by a constant in `2πℤ`. We also record elementary facts about when a quotient lies
in the slit plane.
-/

public section

open Complex Set

namespace ComplexSLE.Planar

/-- If `exp (t i) = 1` then `t = 2πm` for an integer `m`. -/
lemma exists_int_of_exp_mul_I_eq_one {t : ℝ} (h : Complex.exp (t * Complex.I) = 1) :
    ∃ m : ℤ, t = 2 * Real.pi * m := by
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 h
  refine ⟨m, ?_⟩
  have h2 : (t : ℂ) * Complex.I = ((2 * Real.pi * m : ℝ) : ℂ) * Complex.I := by
    rw [hm]; push_cast; ring
  exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero h2

/-- A continuous function `h` on a preconnected set, with `exp (h i) = 1` everywhere on the set,
is constant on it. -/
theorem eq_of_exp_mul_I_eq_one {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsPreconnected S) {h : X → ℝ} (hc : ContinuousOn h S)
    (hexp : ∀ x ∈ S, Complex.exp (h x * Complex.I) = 1) {a b : X} (ha : a ∈ S) (hb : b ∈ S) :
    h a = h b := by
  have key : ∀ a ∈ S, ∀ b ∈ S, h a < h b → False := by
    intro a ha b hb hab
    obtain ⟨m, hm⟩ := exists_int_of_exp_mul_I_eq_one (hexp a ha)
    obtain ⟨k, hk⟩ := exists_int_of_exp_mul_I_eq_one (hexp b hb)
    have hmk : m < k := by
      have : (m : ℝ) < k := by
        have hpi := Real.pi_pos
        rw [hm, hk] at hab
        nlinarith
      exact_mod_cast this
    have hmk' : ((m : ℝ) + 1) ≤ k := by exact_mod_cast hmk
    have hmem : h a + Real.pi ∈ Icc (h a) (h b) := by
      refine ⟨by linarith [Real.pi_pos], ?_⟩
      have hpi := Real.pi_pos
      rw [hm, hk]
      nlinarith
    obtain ⟨x, hxS, hx⟩ := hS.intermediate_value ha hb hc hmem
    have h1 := hexp x hxS
    rw [hx] at h1
    have h2 : Complex.exp (((h a + Real.pi : ℝ) : ℂ) * Complex.I) = -1 := by
      push_cast
      rw [add_mul, Complex.exp_add, hexp a ha, Complex.exp_pi_mul_I, one_mul]
    rw [h2] at h1
    norm_num at h1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact key a ha b hb hlt
  · exact key b hb a ha hgt

/-- If `exp (f i) = exp (g i)` on a preconnected set where `f` and `g` are continuous, then
`f = g + c` for a constant `c` with `exp (c i) = 1`. -/
theorem exists_const_of_exp_mul_I_eq {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsPreconnected S) {f g : X → ℝ} (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hexp : ∀ x ∈ S, Complex.exp (f x * Complex.I) = Complex.exp (g x * Complex.I)) {a : X}
    (ha : a ∈ S) :
    ∃ c : ℝ, Complex.exp (c * Complex.I) = 1 ∧ ∀ x ∈ S, f x = g x + c := by
  have hone : ∀ x ∈ S, Complex.exp (((f x - g x : ℝ) : ℂ) * Complex.I) = 1 := by
    intro x hx
    push_cast
    rw [sub_mul, Complex.exp_sub, hexp x hx, div_self (Complex.exp_ne_zero _)]
  refine ⟨f a - g a, hone a ha, fun x hx => ?_⟩
  have := eq_of_exp_mul_I_eq_one hS (h := fun x => f x - g x) (hf.sub hg) hone hx ha
  beta_reduce at this
  linarith

/-- A quotient `u / v` outside the slit plane is a nonpositive real multiple of... i.e.
`u = -t v` with `t ≥ 0`. -/
lemma exists_nonneg_of_div_not_mem_slitPlane {u v : ℂ} (hv : v ≠ 0) (h : u / v ∉ slitPlane) :
    ∃ t : ℝ, 0 ≤ t ∧ u = -(t : ℂ) * v := by
  rw [mem_slitPlane_iff] at h
  push Not at h
  obtain ⟨hre, him⟩ := h
  refine ⟨-(u / v).re, by linarith, ?_⟩
  have h1 : u / v = (((u / v).re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using him)
  have h2 : u = (u / v) * v := by field_simp
  calc u = (u / v) * v := h2
    _ = (((u / v).re : ℝ) : ℂ) * v := congrArg (fun x => x * v) h1
    _ = -((-(u / v).re : ℝ) : ℂ) * v := by push_cast; ring

/-- If `u` and `v` both lie in the open upper half plane, then `u / v` is in the slit plane. -/
lemma div_mem_slitPlane_of_im_pos {u v : ℂ} (hu : 0 < u.im) (hv : 0 < v.im) :
    u / v ∈ slitPlane := by
  have hv0 : v ≠ 0 := fun h => by simp [h] at hv
  by_contra h
  obtain ⟨t, ht, heq⟩ := exists_nonneg_of_div_not_mem_slitPlane hv0 h
  have : u.im = -t * v.im := by rw [heq]; simp
  nlinarith

/-- If `u` and `v` both lie in the open lower half plane, then `u / v` is in the slit plane. -/
lemma div_mem_slitPlane_of_im_neg {u v : ℂ} (hu : u.im < 0) (hv : v.im < 0) :
    u / v ∈ slitPlane := by
  have hv0 : v ≠ 0 := fun h => by simp [h] at hv
  by_contra h
  obtain ⟨t, ht, heq⟩ := exists_nonneg_of_div_not_mem_slitPlane hv0 h
  have : u.im = -t * v.im := by rw [heq]; simp
  nlinarith

/-- If `r ≠ 0` and `exp (t i) = r / ‖r‖` with `exp (t i) = 1`, then `r = ‖r‖`. -/
lemma eq_ofReal_norm_of_div_eq_one {r : ℂ} (hr : r ≠ 0) (h : r / ((‖r‖ : ℝ) : ℂ) = 1) :
    r = ((‖r‖ : ℝ) : ℂ) := by
  have hn : ((‖r‖ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.2 hr
  rwa [div_eq_one_iff_eq hn] at h

end ComplexSLE.Planar

end
