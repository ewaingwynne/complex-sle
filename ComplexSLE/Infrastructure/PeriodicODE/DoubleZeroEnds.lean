/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.LHopitalAtTop
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Behaviour of the integrating-factor solution at the two ends of a period

Let `a > 0` near an end of `(0, T)` with `A' = a`, `G' = e^A ρ`, and `b = 1/a` with `b' ≥ -1/2`.
The solution `H = e^{-A} G` of `H' = ρ - a H` satisfies `H → 0` and `a H → 0` at the end
whenever `ρ → 0` there and either

* (left end) `A → -∞`, `G → 0`, `b → 0`, or
* (right end) `A → +∞`, `b → 0`.

Both are proved by L'Hôpital's rule (`0/0` at the left end, `∞/∞` at the right end), applied
to `G / e^A` and to `G / (e^A b)`; the key identity is `(e^A b)' = e^A (1 + b') ≥ e^A / 2`.
-/

public section

open Set Filter Topology Real

namespace ComplexSLE.Infrastructure

/-- The derivative of `e^A b` along `A' = a`, `a b = 1`. -/
private theorem hasDerivAt_exp_mul {a b b' A : ℝ → ℝ} {x : ℝ} (hA : HasDerivAt A (a x) x)
    (hb : HasDerivAt b (b' x) x) (hab : a x * b x = 1) :
    HasDerivAt (fun x => Real.exp (A x) * b x) (Real.exp (A x) * (1 + b' x)) x := by
  convert hA.exp.mul hb using 1
  linear_combination (-(Real.exp (A x))) * hab

theorem tendsto_left_end {a b b' ρ A G : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hA : ∀ x ∈ Ioo 0 δ, HasDerivAt A (a x) x)
    (hG : ∀ x ∈ Ioo 0 δ, HasDerivAt G (Real.exp (A x) * ρ x) x)
    (hb : ∀ x ∈ Ioo 0 δ, HasDerivAt b (b' x) x) (hb' : ∀ x ∈ Ioo 0 δ, -(1 / 2) ≤ b' x)
    (hab : ∀ x ∈ Ioo 0 δ, a x * b x = 1)
    (hA0 : Tendsto A (𝓝[>] 0) atBot) (hG0 : Tendsto G (𝓝[>] 0) (𝓝 0))
    (hb0 : Tendsto b (𝓝[>] 0) (𝓝 0)) (hρ0 : Tendsto ρ (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun x => Real.exp (-A x) * G x) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun x => a x * (Real.exp (-A x) * G x)) (𝓝[>] 0) (𝓝 0) := by
  have hexp : Tendsto (fun x => Real.exp (A x)) (𝓝[>] 0) (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hA0
  have hbne : ∀ x ∈ Ioo 0 δ, b x ≠ 0 := fun x hx h => by
    have := hab x hx; rw [h, mul_zero] at this; exact zero_ne_one this
  have hane : ∀ x ∈ Ioo 0 δ, a x ≠ 0 := fun x hx h => by
    have := hab x hx; rw [h, zero_mul] at this; exact zero_ne_one this
  constructor
  · -- `G / e^A`
    have key := HasDerivAt.lhopital_zero_right_on_Ioo (f := G) (g := fun x => Real.exp (A x))
      (f' := fun x => Real.exp (A x) * ρ x) (g' := fun x => Real.exp (A x) * a x) (l := 𝓝 0) hδ hG
      (fun x hx => (hA x hx).exp) (fun x hx => mul_ne_zero (Real.exp_pos _).ne' (hane x hx))
      hG0 hexp ?_
    · refine key.congr' ?_
      filter_upwards with x
      rw [Real.exp_neg, div_eq_inv_mul]
    · have : Tendsto (fun x => ρ x * b x) (𝓝[>] 0) (𝓝 0) := by simpa using hρ0.mul hb0
      refine this.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hδ] with x hx
      have ha := hane x hx
      have hx' := hab x hx
      rw [mul_div_mul_left _ _ (Real.exp_pos (A x)).ne', eq_div_iff ha]
      linear_combination (ρ x) * hx'
  · -- `G / (e^A b)`
    have hexpb : Tendsto (fun x => Real.exp (A x) * b x) (𝓝[>] 0) (𝓝 0) := by
      simpa using hexp.mul hb0
    have key := HasDerivAt.lhopital_zero_right_on_Ioo (f := G) (g := fun x => Real.exp (A x) * b x)
      (f' := fun x => Real.exp (A x) * ρ x) (g' := fun x => Real.exp (A x) * (1 + b' x)) (l := 𝓝 0)
      hδ hG (fun x hx => hasDerivAt_exp_mul (hA x hx) (hb x hx) (hab x hx))
      (fun x hx => mul_ne_zero (Real.exp_pos _).ne' (by linarith [hb' x hx])) hG0 hexpb ?_
    · refine key.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hδ] with x hx
      have hbx := hbne x hx
      have hax : a x = (b x)⁻¹ := eq_inv_of_mul_eq_one_left (hab x hx)
      rw [hax, Real.exp_neg]
      field_simp
    · have h2 : Tendsto (fun x => 2 * |ρ x|) (𝓝[>] 0) (𝓝 0) := by
        simpa using hρ0.abs.const_mul (2 : ℝ)
      refine squeeze_zero_norm' ?_ h2
      filter_upwards [Ioo_mem_nhdsGT hδ] with x hx
      have hb'x := hb' x hx
      have hp : 0 < 1 + b' x := by linarith
      have hE := Real.exp_pos (A x)
      rw [Real.norm_eq_abs, mul_div_mul_left _ _ hE.ne', abs_div, abs_of_pos hp,
        div_le_iff₀ hp]
      nlinarith [abs_nonneg (ρ x)]

theorem tendsto_right_end {a b b' ρ A G : ℝ → ℝ} {T δ : ℝ} (hδ : 0 < δ)
    (hA : ∀ x ∈ Ioo (T - δ) T, HasDerivAt A (a x) x)
    (hG : ∀ x ∈ Ioo (T - δ) T, HasDerivAt G (Real.exp (A x) * ρ x) x)
    (hb : ∀ x ∈ Ioo (T - δ) T, HasDerivAt b (b' x) x)
    (hb' : ∀ x ∈ Ioo (T - δ) T, -(1 / 2) ≤ b' x)
    (hab : ∀ x ∈ Ioo (T - δ) T, a x * b x = 1) (hapos : ∀ x ∈ Ioo (T - δ) T, 0 < a x)
    (hAT : Tendsto A (𝓝[<] T) atTop) (hb0 : Tendsto b (𝓝[<] T) (𝓝 0))
    (hρT : Tendsto ρ (𝓝[<] T) (𝓝 0)) :
    Tendsto (fun x => Real.exp (-A x) * G x) (𝓝[<] T) (𝓝 0) ∧
      Tendsto (fun x => a x * (Real.exp (-A x) * G x)) (𝓝[<] T) (𝓝 0) := by
  have hTδ : T - δ < T := by linarith
  have hexp : Tendsto (fun x => Real.exp (A x)) (𝓝[<] T) atTop :=
    Real.tendsto_exp_atTop.comp hAT
  have hbpos : ∀ x ∈ Ioo (T - δ) T, 0 < b x := fun x hx => by
    have := hab x hx
    have ha := hapos x hx
    by_contra h
    nlinarith [not_lt.1 h]
  have hmem : ∀ᶠ x in 𝓝[<] T, x ∈ Ioo (T - δ) T := Ioo_mem_nhdsLT hTδ
  constructor
  · have key := lhopital_atTop_left_on_Ioo (f := G) (g := fun x => Real.exp (A x))
      (f' := fun x => Real.exp (A x) * ρ x) (g' := fun x => Real.exp (A x) * a x) (l := 0) hTδ hG
      (fun x hx => (hA x hx).exp)
      (fun x hx => mul_ne_zero (Real.exp_pos _).ne' (hapos x hx).ne') hexp ?_
    · refine key.congr' ?_
      filter_upwards with x
      rw [Real.exp_neg, div_eq_inv_mul]
    · have : Tendsto (fun x => ρ x * b x) (𝓝[<] T) (𝓝 0) := by simpa using hρT.mul hb0
      refine this.congr' ?_
      filter_upwards [hmem] with x hx
      have ha := (hapos x hx).ne'
      have hx' := hab x hx
      rw [mul_div_mul_left _ _ (Real.exp_pos (A x)).ne', eq_div_iff ha]
      linear_combination (ρ x) * hx'
  · -- the monotone quantity `e^{A/2} b`
    set x₁ : ℝ := T - δ / 2 with hx₁
    have hx₁I : x₁ ∈ Ioo (T - δ) T := ⟨by rw [hx₁]; linarith, by rw [hx₁]; linarith⟩
    have hF : ∀ x ∈ Ioo (T - δ) T, HasDerivAt (fun x => Real.exp (A x / 2) * b x)
        (Real.exp (A x / 2) * (1 / 2 + b' x)) x := fun x hx => by
      convert ((hA x hx).div_const 2).exp.mul (hb x hx) using 1
      have := hab x hx
      linear_combination (-(Real.exp (A x / 2)) / 2) * this
    have hmono : MonotoneOn (fun x => Real.exp (A x / 2) * b x) (Ico x₁ T) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ico _ _) ?_ ?_ ?_
      · intro x hx
        exact (hF x ⟨by linarith [hx.1, hx₁I.1], hx.2⟩).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Ico] at hx
        exact (hF x ⟨by linarith [hx.1, hx₁I.1], hx.2⟩).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Ico] at hx
        have hxI : x ∈ Ioo (T - δ) T := ⟨by linarith [hx.1, hx₁I.1], hx.2⟩
        rw [(hF x hxI).deriv]
        have := hb' x hxI
        exact mul_nonneg (Real.exp_pos _).le (by linarith)
    set κ : ℝ := Real.exp (A x₁ / 2) * b x₁ with hκ
    have hκpos : 0 < κ := mul_pos (Real.exp_pos _) (hbpos x₁ hx₁I)
    have hlow : ∀ x ∈ Ico x₁ T, κ * Real.exp (A x / 2) ≤ Real.exp (A x) * b x := fun x hx => by
      have h1 := hmono (left_mem_Ico.2 (by linarith [hx₁I.2] : x₁ < T)) hx hx.1
      have h2 : Real.exp (A x) = Real.exp (A x / 2) * Real.exp (A x / 2) := by
        rw [← Real.exp_add]; congr 1; ring
      calc κ * Real.exp (A x / 2) = Real.exp (A x / 2) * κ := mul_comm _ _
        _ ≤ Real.exp (A x / 2) * (Real.exp (A x / 2) * b x) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = Real.exp (A x) * b x := by rw [h2]; ring
    have hlim : Tendsto (fun x => κ * Real.exp (A x / 2)) (𝓝[<] T) atTop :=
      Tendsto.const_mul_atTop hκpos
        (Real.tendsto_exp_atTop.comp (hAT.atTop_div_const (by norm_num : (0 : ℝ) < 2)))
    have hgb : Tendsto (fun x => Real.exp (A x) * b x) (𝓝[<] T) atTop := by
      refine tendsto_atTop_mono' _ ?_ hlim
      filter_upwards [Ico_mem_nhdsLT hx₁I.2] with x hx using hlow x hx
    have key := lhopital_atTop_left_on_Ioo (f := G) (g := fun x => Real.exp (A x) * b x)
      (f' := fun x => Real.exp (A x) * ρ x) (g' := fun x => Real.exp (A x) * (1 + b' x)) (l := 0)
      hTδ hG (fun x hx => hasDerivAt_exp_mul (hA x hx) (hb x hx) (hab x hx))
      (fun x hx => mul_ne_zero (Real.exp_pos _).ne' (by linarith [hb' x hx])) hgb ?_
    · refine key.congr' ?_
      filter_upwards [hmem] with x hx
      have hbx := (hbpos x hx).ne'
      have hax : a x = (b x)⁻¹ := eq_inv_of_mul_eq_one_left (hab x hx)
      rw [hax, Real.exp_neg]
      field_simp
    · have h2 : Tendsto (fun x => 2 * |ρ x|) (𝓝[<] T) (𝓝 0) := by
        simpa using hρT.abs.const_mul (2 : ℝ)
      refine squeeze_zero_norm' ?_ h2
      filter_upwards [hmem] with x hx
      have hb'x := hb' x hx
      have hp : 0 < 1 + b' x := by linarith
      have hE := Real.exp_pos (A x)
      rw [Real.norm_eq_abs, mul_div_mul_left _ _ hE.ne', abs_div, abs_of_pos hp,
        div_le_iff₀ hp]
      nlinarith [abs_nonneg (ρ x)]

end ComplexSLE.Infrastructure

end
