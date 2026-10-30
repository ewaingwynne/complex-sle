/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsAdmissibleDensity
public import ComplexSLE.Infrastructure.PeriodicGlue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Admissible densities: common infrastructure

Elementary facts about the drift `µ` and the diffusion coefficient `D` of (1.10)
(smoothness, `π`-periodicity, positivity, the `c ↦ -c` symmetry), the notion of a
*pre-density* (everything an admissible density needs except the normalisation `∫₀^{2π} p = 1`,
with the first-order equation `-µp + (Dp)' = K` in place of the second-order one), the
normalisation step, and the transport of admissible densities under `u ↦ -u`
(paper.tex:L1002-1010, graph node `step:p-wlog-c-nonneg`).
-/

public section

open Set Filter Topology MeasureTheory intervalIntegral Function Real
open scoped ContDiff

namespace ComplexSLE.Internal

variable {a b c : ℝ}

/-! ### The coefficients `µ` and `D` -/

theorem contDiff_mu (a b c : ℝ) : ContDiff ℝ ∞ (mu a b c) := by
  unfold mu; fun_prop

theorem contDiff_diffusionD (a b c : ℝ) : ContDiff ℝ ∞ (diffusionD a b c) := by
  unfold diffusionD; fun_prop

theorem continuous_mu (a b c : ℝ) : Continuous (mu a b c) := (contDiff_mu a b c).continuous

theorem continuous_diffusionD (a b c : ℝ) : Continuous (diffusionD a b c) :=
  (contDiff_diffusionD a b c).continuous

theorem mu_periodic (a b c : ℝ) : Periodic (mu a b c) π := by
  intro u
  simp only [mu]
  rw [show 2 * (u + π) = 2 * u + 2 * π by ring, sin_add_two_pi, cos_add_two_pi]

theorem diffusionD_periodic (a b c : ℝ) : Periodic (diffusionD a b c) π := by
  intro u
  simp only [diffusionD, sin_add_pi, cos_add_pi]
  ring

theorem mu_neg_c (a b c u : ℝ) : mu a b (-c) u = -mu a b c (-u) := by
  simp only [mu]
  rw [show 2 * -u = -(2 * u) by ring, sin_neg, cos_neg]
  ring

theorem diffusionD_neg_c (a b c u : ℝ) : diffusionD a b (-c) u = diffusionD a b c (-u) := by
  simp only [diffusionD, sin_neg, cos_neg]
  ring

/-- `2(a+b) D = (a sin u - c cos u)² + (b cos u - c sin u)² + (ab - c²)`. -/
theorem two_mul_add_mul_diffusionD (a b c u : ℝ) :
    2 * (a + b) * diffusionD a b c u =
      (a * sin u - c * cos u) ^ 2 + (b * cos u - c * sin u) ^ 2 + (a * b - c ^ 2) := by
  have h := sin_sq_add_cos_sq u
  simp only [diffusionD]
  linear_combination (a * b - c ^ 2) * h

theorem diffusionD_pos (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 < a * b) (u : ℝ) :
    0 < diffusionD a b c u := by
  have h := two_mul_add_mul_diffusionD a b c u
  have h2 : 0 < 2 * (a + b) * diffusionD a b c u := by
    rw [h]; nlinarith [sq_nonneg (a * sin u - c * cos u), sq_nonneg (b * cos u - c * sin u)]
  nlinarith

theorem diffusionD_nonneg (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b) (u : ℝ) :
    0 ≤ diffusionD a b c u := by
  have h := two_mul_add_mul_diffusionD a b c u
  have h2 : 0 ≤ 2 * (a + b) * diffusionD a b c u := by
    rw [h]; nlinarith [sq_nonneg (a * sin u - c * cos u), sq_nonneg (b * cos u - c * sin u)]
  nlinarith

/-! ### Pre-densities and normalisation -/

/-- A *pre-density*: everything `IsAdmissibleDensity` asks for except the normalisation, with
the first-order equation `(Dp)' = K + µ p` everywhere in place of the second-order one. -/
structure IsPreDensity (a b c : ℝ) (p : ℝ → ℝ) (x K : ℝ) : Prop where
  continuous : Continuous p
  nonneg : ∀ u, 0 ≤ p u
  periodic : Periodic p π
  integral_pos : 0 < ∫ u in (0)..(2 * π), p u
  contDiffOn : ContDiffOn ℝ 2 p {u | ∀ n : ℤ, u ≠ x + n * π}
  hasDerivAt : ∀ u, HasDerivAt (fun v => diffusionD a b c v * p v) (K + mu a b c u * p u) u

/-- Normalising a pre-density gives an admissible density. -/
theorem IsPreDensity.exists_isAdmissibleDensity {p : ℝ → ℝ} {x K : ℝ}
    (h : IsPreDensity a b c p x K) : ∃ q, IsAdmissibleDensity a b c q := by
  set I := ∫ u in (0)..(2 * π), p u with hIdef
  have hI : 0 < I := h.integral_pos
  have hd : ∀ v, HasDerivAt (fun w => diffusionD a b c w * (I⁻¹ * p w))
      (I⁻¹ * K + mu a b c v * (I⁻¹ * p v)) v := by
    intro v
    have := (h.hasDerivAt v).const_mul I⁻¹
    convert this using 1
    · funext w; ring
    · ring
  have hderiv : deriv (fun w => diffusionD a b c w * (I⁻¹ * p w)) =
      fun v => I⁻¹ * K + mu a b c v * (I⁻¹ * p v) := funext fun v => (hd v).deriv
  refine ⟨fun u => I⁻¹ * p u, continuous_const.mul h.continuous,
    fun u => mul_nonneg (inv_nonneg.2 hI.le) (h.nonneg u), fun u => by simp only [h.periodic u],
    ?_, x, contDiffOn_const.mul h.contDiffOn, ?_, ?_⟩
  · rw [intervalIntegral.integral_const_mul]; exact inv_mul_cancel₀ hI.ne'
  · intro u _
    rw [hderiv, deriv_const_add]
    ring
  · rw [contDiff_one_iff_deriv]
    refine ⟨fun v => (hd v).differentiableAt, ?_⟩
    rw [hderiv]
    exact continuous_const.add ((continuous_mu a b c).mul (continuous_const.mul h.continuous))

/-! ### The symmetry `c ↦ -c` -/

/-- Transport of an admissible density under `u ↦ -u` (paper.tex:L1002-1010): if `p` is
admissible for `(a, b, c)` then `u ↦ p (-u)` is admissible for `(a, b, -c)`. -/
theorem IsAdmissibleDensity.neg_c {p : ℝ → ℝ} (h : IsAdmissibleDensity a b c p) :
    IsAdmissibleDensity a b (-c) (fun u => p (-u)) := by
  obtain ⟨hcont, hnn, hper, hint, x, hC2, hode, hC1⟩ := h
  have hneg : Continuous fun u : ℝ => -u := continuous_neg
  refine ⟨hcont.comp hneg, fun u => hnn _, fun u => ?_, ?_, -x, ?_, ?_, ?_⟩
  · change p (-(u + π)) = p (-u)
    rw [show -(u + π) = -u - π by ring, hper.sub_eq]
  · have h2 : Periodic p (2 * π) := by simpa using hper.nsmul 2
    rw [integral_comp_neg, neg_zero]
    have := h2.intervalIntegral_add_eq (-(2 * π)) 0
    rw [neg_add_cancel, zero_add] at this
    rw [this]; exact hint
  · have hmaps : MapsTo (fun u : ℝ => -u) {u | ∀ n : ℤ, u ≠ -x + n * π}
        {u | ∀ n : ℤ, u ≠ x + n * π} := by
      intro u hu n hn
      apply hu (-n)
      push_cast
      linarith
    exact hC2.comp contDiff_neg.contDiffOn hmaps
  · intro u hu
    have hu' : ∀ n : ℤ, -u ≠ x + n * π := by
      intro n hn
      apply hu (-n)
      push_cast
      linarith
    have e1 : (fun v => mu a b (-c) v * p (-v)) =
        fun v => -((fun w => mu a b c w * p w) (-v)) := by
      funext v; simp only [mu_neg_c]; ring
    have e2 : (fun v => diffusionD a b (-c) v * p (-v)) =
        fun v => (fun w => diffusionD a b c w * p w) (-v) := by
      funext v; simp only [diffusionD_neg_c]
    rw [e1, e2]
    have e3 : deriv (fun v => (fun w => diffusionD a b c w * p w) (-v)) =
        fun v => -deriv (fun w => diffusionD a b c w * p w) (-v) :=
      funext fun v => deriv_comp_neg (fun w => diffusionD a b c w * p w) v
    rw [e3]
    have e4 : deriv (fun v => -((fun w => mu a b c w * p w) (-v))) u =
        deriv (fun w => mu a b c w * p w) (-u) := by
      rw [show (fun v => -((fun w => mu a b c w * p w) (-v))) =
          -(fun v => (fun w => mu a b c w * p w) (-v)) from rfl, deriv.neg,
        deriv_comp_neg (fun w => mu a b c w * p w) u]
      ring
    have e5 : deriv (fun v => -deriv (fun w => diffusionD a b c w * p w) (-v)) u =
        deriv (deriv fun w => diffusionD a b c w * p w) (-u) := by
      rw [show (fun v => -deriv (fun w => diffusionD a b c w * p w) (-v)) =
          -(fun v => deriv (fun w => diffusionD a b c w * p w) (-v)) from rfl, deriv.neg,
        deriv_comp_neg (deriv fun w => diffusionD a b c w * p w) u]
      ring
    rw [e4, e5]
    exact hode (-u) hu'
  · have e2 : (fun u => diffusionD a b (-c) u * p (-u)) =
        (fun w => diffusionD a b c w * p w) ∘ fun u => -u := by
      funext v; simp only [Function.comp, diffusionD_neg_c]
    rw [e2]
    exact hC1.comp contDiff_neg

end ComplexSLE.Internal

end
