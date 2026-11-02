/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Periodic primitives (M10-R5a)

Elementary calculus for `π`-periodic functions, used to build the test functions `g` of the
occupation estimates (`Occupation*.lean`) from Dynkin's formula:

* `exists_periodic_primitive_sub_mean`: for `φ` continuous and `π`-periodic, with mean
  `φ̄ = (1/π) ∫₀^π φ`, the primitive `g(x) = ∫₀ˣ (φ - φ̄)` is `π`-periodic with
  `|g| ≤ ∫₀^π |φ - φ̄|`;
* `exists_periodic_contDiff_two_second_deriv`: for `ψ ≥ 0` continuous and `π`-periodic with
  `M = ∫₀^π ψ`, there is a `C²` `π`-periodic `g` with `g'' = ψ - M/π`, `|g'| ≤ 4M`, `|g| ≤ 4πM`;
* `exists_periodic_contDiff_two_first_deriv`: for `φ ≥ 0` of class `C¹` and `π`-periodic, a `C²`
  `π`-periodic `g` with `g' = φ - M/π` and `|g| ≤ 2M`.
-/

public section

open Real Set MeasureTheory Function
open scoped Topology

namespace ComplexSLE.Internal

section Primitive

variable {f φ : ℝ → ℝ}

theorem hasDerivAt_integral_zero (hf : Continuous f) (x : ℝ) :
    HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, f t) (f x) x :=
  (hf.integral_hasStrictDerivAt 0 x).hasDerivAt

/-- A primitive of a `π`-periodic function with zero mean over a period is `π`-periodic. -/
theorem periodic_integral_zero (hf : Continuous f) (hper : Periodic f π)
    (h0 : ∫ t in (0 : ℝ)..π, f t = 0) : Periodic (fun u => ∫ t in (0 : ℝ)..u, f t) π := by
  intro x
  have h1 : ∫ t in (0 : ℝ)..x + π, f t =
      (∫ t in (0 : ℝ)..π, f t) + ∫ t in π..x + π, f t :=
    (intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _)).symm
  have h2 : ∫ t in π..x + π, f t = ∫ t in (0 : ℝ)..x, f t := by
    have := intervalIntegral.integral_comp_add_right (a := 0) (b := x) f π
    rw [zero_add] at this
    rw [← this]
    exact intervalIntegral.integral_congr fun t _ => (hper t).symm ▸ rfl
  simp only
  rw [h1, h0, zero_add, h2]

theorem integral_sub_mean_eq_zero (hφ : Continuous φ) :
    ∫ t in (0 : ℝ)..π, (φ t - (∫ s in (0 : ℝ)..π, φ s) / π) = 0 := by
  rw [intervalIntegral.integral_sub (hφ.intervalIntegrable _ _) intervalIntegrable_const]
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  field_simp
  ring

/-- `|∫₀ˣ f| ≤ ∫₀^π |f|` for `f` continuous, `π`-periodic with zero mean over a period. -/
theorem abs_integral_zero_le (hf : Continuous f) (hper : Periodic f π)
    (h0 : ∫ t in (0 : ℝ)..π, f t = 0) (x : ℝ) :
    |∫ t in (0 : ℝ)..x, f t| ≤ ∫ t in (0 : ℝ)..π, |f t| := by
  obtain ⟨y, hy, hxy⟩ := (periodic_integral_zero hf hper h0).exists_mem_Ico₀ pi_pos x
  have hxy' : ∫ t in (0 : ℝ)..x, f t = ∫ t in (0 : ℝ)..y, f t := hxy
  rw [hxy']
  refine (intervalIntegral.abs_integral_le_integral_abs (μ := volume) hy.1).trans ?_
  have hnn : 0 ≤ ∫ t in y..π, |f t| :=
    intervalIntegral.integral_nonneg hy.2.le fun t _ => abs_nonneg _
  have := intervalIntegral.integral_add_adjacent_intervals (f := fun t => |f t|) (a := 0) (b := y)
    (c := π) (μ := volume) (hf.abs.intervalIntegrable _ _) (hf.abs.intervalIntegrable _ _)
  linarith

/-- **The periodic primitive of `φ - φ̄`.** -/
theorem exists_periodic_primitive_sub_mean (hφ : Continuous φ) (hper : Periodic φ π) :
    ∃ g : ℝ → ℝ, (∀ x, HasDerivAt g (φ x - (∫ s in (0 : ℝ)..π, φ s) / π) x) ∧ Periodic g π ∧
      ∀ x, |g x| ≤ ∫ t in (0 : ℝ)..π, |φ t - (∫ s in (0 : ℝ)..π, φ s) / π| := by
  have hc : Continuous fun t => φ t - (∫ s in (0 : ℝ)..π, φ s) / π := hφ.sub continuous_const
  have hp : Periodic (fun t => φ t - (∫ s in (0 : ℝ)..π, φ s) / π) π := fun t => by
    simp only [hper t]
  have h0 := integral_sub_mean_eq_zero hφ
  exact ⟨fun u => ∫ t in (0 : ℝ)..u, (φ t - (∫ s in (0 : ℝ)..π, φ s) / π),
    fun x => hasDerivAt_integral_zero hc x, periodic_integral_zero hc hp h0,
    abs_integral_zero_le hc hp h0⟩

theorem contDiff_two_of_hasDerivAt {g g₁ g₂ : ℝ → ℝ} (h₁ : ∀ x, HasDerivAt g (g₁ x) x)
    (h₂ : ∀ x, HasDerivAt g₁ (g₂ x) x) (hc : Continuous g₂) : ContDiff ℝ 2 g := by
  have e1 : deriv g = g₁ := funext fun x => (h₁ x).deriv
  have e2 : deriv g₁ = g₂ := funext fun x => (h₂ x).deriv
  have h2 : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
  rw [h2, contDiff_succ_iff_deriv]
  refine ⟨fun x => (h₁ x).differentiableAt, by simp, ?_⟩
  rw [e1, contDiff_one_iff_deriv]
  exact ⟨fun x => (h₂ x).differentiableAt, by rw [e2]; exact hc⟩

theorem deriv_deriv_eq {g g₁ g₂ : ℝ → ℝ} (h₁ : ∀ x, HasDerivAt g (g₁ x) x)
    (h₂ : ∀ x, HasDerivAt g₁ (g₂ x) x) (x : ℝ) : deriv (deriv g) x = g₂ x := by
  have e1 : deriv g = g₁ := funext fun x => (h₁ x).deriv
  rw [e1]
  exact (h₂ x).deriv

theorem abs_sub_mean_le {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hnn : ∀ x, 0 ≤ ψ x) :
    ∫ t in (0 : ℝ)..π, |ψ t - (∫ s in (0 : ℝ)..π, ψ s) / π| ≤ 2 * ∫ s in (0 : ℝ)..π, ψ s := by
  set M := ∫ s in (0 : ℝ)..π, ψ s with hM
  have hM0 : 0 ≤ M := intervalIntegral.integral_nonneg pi_pos.le fun t _ => hnn t
  have hmono : ∫ t in (0 : ℝ)..π, |ψ t - M / π| ≤ ∫ t in (0 : ℝ)..π, (ψ t + M / π) :=
    intervalIntegral.integral_mono_on pi_pos.le
      ((hψ.sub continuous_const).abs.intervalIntegrable _ _)
      ((hψ.add continuous_const).intervalIntegrable _ _) fun t _ => by
        have := hnn t
        have : 0 ≤ M / π := div_nonneg hM0 pi_pos.le
        rw [abs_le]; constructor <;> linarith
  refine hmono.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_add (hψ.intervalIntegrable _ _) intervalIntegrable_const]
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  rw [← hM]
  field_simp
  ring

/-- **A `C²` periodic function with prescribed second derivative.** For `ψ ≥ 0` continuous and
`π`-periodic with `M = ∫₀^π ψ`, there is a `C²` `π`-periodic `g` with `g'' = ψ - M/π`,
`|g'| ≤ 4M` and `|g| ≤ 4πM`. -/
theorem exists_periodic_contDiff_two_second_deriv {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hper : Periodic ψ π) (hnn : ∀ x, 0 ≤ ψ x) :
    ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ Periodic g π ∧
      (∀ x, deriv (deriv g) x = ψ x - (∫ s in (0 : ℝ)..π, ψ s) / π) ∧
      (∀ x, |deriv g x| ≤ 4 * ∫ s in (0 : ℝ)..π, ψ s) ∧
      (∀ x, |g x| ≤ 4 * π * ∫ s in (0 : ℝ)..π, ψ s) := by
  set M := ∫ s in (0 : ℝ)..π, ψ s with hM
  have hM0 : 0 ≤ M := intervalIntegral.integral_nonneg pi_pos.le fun t _ => hnn t
  -- the first primitive `h`, with `h' = ψ - M/π`
  obtain ⟨h, hh, hhper, hhb⟩ := exists_periodic_primitive_sub_mean hψ hper
  have hh2 : ∀ x, |h x| ≤ 2 * M := fun x => (hhb x).trans (abs_sub_mean_le hψ hnn)
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun x => (hh x).continuousAt
  -- the second primitive `g`, with `g' = h - h̄`
  obtain ⟨g, hg, hgper, hgb⟩ := exists_periodic_primitive_sub_mean hhc hhper
  set m₁ := (∫ s in (0 : ℝ)..π, h s) / π with hm₁
  have hm₁b : |m₁| ≤ 2 * M := by
    have : |∫ s in (0 : ℝ)..π, h s| ≤ 2 * M * π := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := π) (f := h)
        (C := 2 * M) fun x _ => by simpa [Real.norm_eq_abs] using hh2 x
      simpa [Real.norm_eq_abs, abs_of_pos pi_pos] using this
    rw [hm₁, abs_div, abs_of_pos pi_pos, div_le_iff₀ pi_pos]
    exact this
  have hg'b : ∀ x, |h x - m₁| ≤ 4 * M := fun x => by
    have := hh2 x
    have h2 := hm₁b
    calc |h x - m₁| ≤ |h x| + |m₁| := abs_sub _ _
      _ ≤ 4 * M := by linarith
  have hgbd : ∀ x, |g x| ≤ 4 * π * M := fun x => by
    refine (hgb x).trans ?_
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := π)
      (f := fun t => |h t - m₁|) (C := 4 * M) fun t _ => by
        simpa [Real.norm_eq_abs, abs_abs] using hg'b t
    simp only [Real.norm_eq_abs, abs_of_pos pi_pos, sub_zero] at this
    have h0 : 0 ≤ ∫ t in (0 : ℝ)..π, |h t - m₁| :=
      intervalIntegral.integral_nonneg pi_pos.le fun t _ => abs_nonneg _
    rw [abs_of_nonneg h0] at this
    linarith
  have hh' : ∀ x, HasDerivAt (fun x => h x - m₁) (ψ x - M / π) x := fun x => (hh x).sub_const m₁
  refine ⟨g, contDiff_two_of_hasDerivAt hg hh' (hψ.sub continuous_const), hgper,
    fun x => deriv_deriv_eq hg hh' x, fun x => ?_, hgbd⟩
  rw [(hg x).deriv]
  exact hg'b x

/-- **A `C²` periodic function with prescribed first derivative.** For `φ ≥ 0` of class `C¹`
and `π`-periodic with `M = ∫₀^π φ`, there is a `C²` `π`-periodic `g` with `g' = φ - M/π`,
`g'' = φ'` and `|g| ≤ 2M`. -/
theorem exists_periodic_contDiff_two_first_deriv {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hper : Periodic φ π) (hnn : ∀ x, 0 ≤ φ x) :
    ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ Periodic g π ∧
      (∀ x, deriv g x = φ x - (∫ s in (0 : ℝ)..π, φ s) / π) ∧
      (∀ x, deriv (deriv g) x = deriv φ x) ∧
      ∀ x, |g x| ≤ 2 * ∫ s in (0 : ℝ)..π, φ s := by
  obtain ⟨g, hg, hgper, hgb⟩ := exists_periodic_primitive_sub_mean hφ.continuous hper
  have hφd : ∀ x, HasDerivAt φ (deriv φ x) x := fun x =>
    (hφ.differentiable one_ne_zero x).hasDerivAt
  have hφ' : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hd : ∀ x, HasDerivAt (fun x => φ x - (∫ s in (0 : ℝ)..π, φ s) / π) (deriv φ x) x :=
    fun x => (hφd x).sub_const _
  refine ⟨g, contDiff_two_of_hasDerivAt hg hd hφ', hgper, fun x => (hg x).deriv,
    fun x => deriv_deriv_eq hg hd x, fun x => (hgb x).trans (abs_sub_mean_le hφ.continuous hnn)⟩

end Primitive

end ComplexSLE.Internal

end
