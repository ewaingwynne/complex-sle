/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The chain argument

For a chain `β₀, …, βₙ` of points of `ℂ`, `chainArg β w = ∑ₖ Arg ((w - βₖ) / (w - βₖ₊₁))` is a
continuous branch of the argument of `(w - β₀) / (w - βₙ)` on the set of points that stay at
distance `> ρ` from every `βₖ`, when consecutive distances are `< ρ`. It satisfies
`exp (i · chainArg β w) = r / ‖r‖` for `r = (w - β₀) / (w - βₙ)`, and tends to `0` at infinity.
-/

@[expose] public section

open Complex Filter Topology Set

namespace ComplexSLE.Planar

/-- The chain argument `∑ₖ Arg ((w - βₖ) / (w - βₖ₊₁))` of a chain `β : Fin (n + 1) → ℂ`. -/
noncomputable def chainArg {n : ℕ} (β : Fin (n + 1) → ℂ) (w : ℂ) : ℝ :=
  ∑ k : Fin n, Complex.arg ((w - β k.castSucc) / (w - β k.succ))

/-- The set of points at distance `> ρ` from every vertex of the chain. -/
def chainAvoid {n : ℕ} (β : Fin (n + 1) → ℂ) (ρ : ℝ) : Set ℂ :=
  {w | ∀ k, ρ < ‖w - β k‖}

lemma ratio_mem_slitPlane {a b w : ℂ} {ρ : ℝ} (hab : ‖b - a‖ < ρ) (hw : ρ < ‖w - b‖) :
    (w - a) / (w - b) ∈ slitPlane := by
  have hwb : w - b ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    linarith [norm_nonneg (b - a)]
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg _) hab
  have hEq : (w - a) / (w - b) = 1 + (b - a) / (w - b) := by
    field_simp
    ring
  have hlt : ‖(b - a) / (w - b)‖ < 1 := by
    rw [norm_div, div_lt_one (lt_trans hρ hw)]
    exact lt_trans hab hw
  rw [hEq]
  refine mem_slitPlane_iff.2 (Or.inl ?_)
  have := abs_le.1 (Complex.abs_re_le_norm ((b - a) / (w - b)))
  simp only [Complex.add_re, Complex.one_re]
  linarith [this.1, norm_nonneg ((b - a) / (w - b)), neg_le_of_abs_le (abs_le.2 this)]

/-- If `0 < z.im` then `0 < arg z`. -/
lemma arg_pos_of_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < Complex.arg z := by
  have h1 : 0 ≤ Complex.arg z := Complex.arg_nonneg_iff.2 hz.le
  rcases h1.eq_or_lt with h | h
  · exact absurd (Complex.arg_eq_zero_iff.1 h.symm).2 hz.ne'
  · exact h

/-- Each ratio is nonzero off the chain. -/
lemma chain_ratio_ne_zero {a b w : ℂ} (ha : w ≠ a) (hb : w ≠ b) : (w - a) / (w - b) ≠ 0 :=
  div_ne_zero (sub_ne_zero.2 ha) (sub_ne_zero.2 hb)

variable {n : ℕ} {β : Fin (n + 1) → ℂ} {ρ : ℝ}

/-- The chain argument is continuous on the set of points at distance `> ρ` from the chain. -/
theorem continuousOn_chainArg (hβ : ∀ k : Fin n, dist (β k.castSucc) (β k.succ) < ρ) :
    ContinuousOn (chainArg β) (chainAvoid β ρ) := by
  unfold chainArg
  refine continuousOn_finsetSum _ fun k _ => ?_
  intro w hw
  have h1 : ρ < ‖w - β k.succ‖ := hw k.succ
  have h2 : ρ < ‖w - β k.castSucc‖ := hw k.castSucc
  have hab : ‖β k.succ - β k.castSucc‖ < ρ := by rw [← dist_eq_norm, dist_comm]; exact hβ k
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg _) hab
  have hne : w - β k.succ ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; linarith
  refine ContinuousAt.continuousWithinAt ?_
  have hc : ContinuousAt (fun w => (w - β k.castSucc) / (w - β k.succ)) w :=
    (continuousAt_id.sub continuousAt_const).div (continuousAt_id.sub continuousAt_const) hne
  exact ContinuousAt.comp (g := Complex.arg) (Complex.continuousAt_arg (ratio_mem_slitPlane hab h1))
    hc

/-- Telescoping of a product of ratios. -/
lemma prod_div_telescope : ∀ {n : ℕ} (a : Fin (n + 1) → ℂ), (∀ k, a k ≠ 0) →
    ∏ k : Fin n, a k.castSucc / a k.succ = a 0 / a (Fin.last n)
  | 0, a, ha => by simp [div_self (ha 0)]
  | n + 1, a, ha => by
    rw [Fin.prod_univ_castSucc]
    have ih := prod_div_telescope (fun i : Fin (n + 1) => a i.castSucc) (fun k => ha _)
    simp only [Fin.succ_castSucc] at ih ⊢
    rw [ih]
    have := ha (Fin.last n).castSucc
    have h2 := ha (Fin.last (n + 1))
    simp only [Fin.succ_last, Fin.castSucc_zero] at *
    field_simp

/-- The chain argument is a branch of the argument of `(w - β₀) / (w - βₙ)`: its exponential
is the unit vector in the direction of `r = (w - β₀) / (w - βₙ)`. -/
theorem exp_chainArg_mul_I {w : ℂ} (hw : ∀ k, w ≠ β k) :
    Complex.exp (chainArg β w * Complex.I) =
      ((w - β 0) / (w - β (Fin.last n))) / ((‖(w - β 0) / (w - β (Fin.last n))‖ : ℝ) : ℂ) := by
  have hz : ∀ k : Fin n, (w - β k.castSucc) / (w - β k.succ) ≠ 0 :=
    fun k => chain_ratio_ne_zero (hw _) (hw _)
  have hprod := prod_div_telescope (fun k => w - β k) (fun k => sub_ne_zero.2 (hw k))
  beta_reduce at hprod
  unfold chainArg
  rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  have hk : ∀ k : Fin n, Complex.exp ((Complex.arg ((w - β k.castSucc) / (w - β k.succ)) : ℂ) *
      Complex.I) = ((w - β k.castSucc) / (w - β k.succ)) /
        ((‖(w - β k.castSucc) / (w - β k.succ)‖ : ℝ) : ℂ) := by
    intro k
    have h := Complex.norm_mul_exp_arg_mul_I ((w - β k.castSucc) / (w - β k.succ))
    have hn : ((‖(w - β k.castSucc) / (w - β k.succ)‖ : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.2 (hz k)
    rw [eq_div_iff hn, mul_comm]
    exact h
  rw [Finset.prod_congr rfl fun k _ => hk k, Finset.prod_div_distrib, hprod]
  congr 1
  rw [← Complex.ofReal_prod, ← norm_prod, hprod]

/-- The chain argument and `arg ((w - β₀) / (w - βₙ))` have the same exponential. -/
theorem exp_chainArg_mul_I_eq_exp_arg {w : ℂ} (hw : ∀ k, w ≠ β k) :
    Complex.exp (chainArg β w * Complex.I) =
      Complex.exp (Complex.arg ((w - β 0) / (w - β (Fin.last n))) * Complex.I) := by
  rw [exp_chainArg_mul_I hw]
  have hr : (w - β 0) / (w - β (Fin.last n)) ≠ 0 := chain_ratio_ne_zero (hw _) (hw _)
  have h := Complex.norm_mul_exp_arg_mul_I ((w - β 0) / (w - β (Fin.last n)))
  have hn : ((‖(w - β 0) / (w - β (Fin.last n))‖ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.2 hr
  rw [div_eq_iff hn, mul_comm]
  exact h.symm

/-- `‖w - b‖ → ∞` along the cocompact filter. -/
lemma tendsto_norm_sub_cocompact (b : ℂ) :
    Tendsto (fun w : ℂ => ‖w - b‖) (cocompact ℂ) atTop := by
  refine tendsto_atTop_mono (fun w => ?_) (tendsto_atTop_add_const_right _ (-‖b‖)
    (tendsto_norm_cocompact_atTop (E := ℂ)))
  have := norm_sub_norm_le w b
  linarith

/-- A single ratio `(w - a) / (w - b)` tends to `1`, hence its argument to `0`. -/
lemma tendsto_arg_ratio (a b : ℂ) :
    Tendsto (fun w : ℂ => Complex.arg ((w - a) / (w - b))) (cocompact ℂ) (𝓝 0) := by
  have h0 : Tendsto (fun w : ℂ => (b - a) / (w - b)) (cocompact ℂ) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_div]
    exact tendsto_const_nhds.div_atTop (tendsto_norm_sub_cocompact b)
  have h1 : Tendsto (fun w : ℂ => 1 + (b - a) / (w - b)) (cocompact ℂ) (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℂ))).add h0
  have h2 : Tendsto (fun w : ℂ => (w - a) / (w - b)) (cocompact ℂ) (𝓝 1) := by
    refine h1.congr' ?_
    filter_upwards [(isCompact_singleton (x := b)).compl_mem_cocompact] with w hw
    have : w - b ≠ 0 := sub_ne_zero.2 hw
    field_simp
    ring
  have h3 := (Complex.continuousAt_arg (x := 1) (by simp)).tendsto.comp h2
  simpa [Function.comp_def] using h3

/-- The chain argument tends to `0` at infinity. -/
theorem tendsto_chainArg (β : Fin (n + 1) → ℂ) :
    Tendsto (chainArg β) (cocompact ℂ) (𝓝 0) := by
  unfold chainArg
  have h : Tendsto (fun w : ℂ => ∑ k : Fin n, Complex.arg ((w - β k.castSucc) / (w - β k.succ)))
      (cocompact ℂ) (𝓝 (∑ _k : Fin n, (0 : ℝ))) :=
    tendsto_finsetSum _ fun k _ => tendsto_arg_ratio _ _
  rwa [Finset.sum_const_zero] at h

end ComplexSLE.Planar

end
