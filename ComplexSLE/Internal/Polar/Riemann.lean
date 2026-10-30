/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Riemann sums and discrete winding of a continuously lifted argument

Two elementary deterministic facts used to express the clock `∫₀ᵗ |f_s|⁻² ds` and the argument
`θ_t` of the Loewner path through *finitely many* values `f_{kt/N}`, `k ≤ N`:

* `tendsto_riemannSum`: left Riemann sums of a function continuous on `[0, t]` converge to the
  integral;
* `eventually_sum_arg_eq`: if `θ` is a continuous lift of the argument of a nonvanishing `f` on
  `[0, t]`, then for all large `N` the principal arguments of the successive ratios
  `f((k+1)t/N) / f(kt/N)` add up to `θ t - θ 0`.
-/

public section

open scoped NNReal Real Topology
open Set Filter MeasureTheory Complex

namespace ComplexSLE.Internal.Polar

/-! ### Riemann sums -/

/-- Left Riemann sums `∑_{k<N} (t/N) φ(k t/N)` of a function continuous on `[0, t]` converge to
`∫₀ᵗ φ`. -/
theorem tendsto_riemannSum {φ : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) (hφ : ContinuousOn φ (Icc 0 t)) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, (t / N) * φ (k * t / N)) atTop
      (𝓝 (∫ s in (0 : ℝ)..t, φ s)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε' : 0 < ε / (t + 1) := by positivity
  obtain ⟨δ, hδ, hδφ⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hφ) (ε / (t + 1)) hε'
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (t / δ)
  refine ⟨N₀ + 1, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by
    have : (N₀ : ℝ) + 1 ≤ N := by exact_mod_cast hN
    have h0 : (0 : ℝ) ≤ N₀ := N₀.cast_nonneg
    linarith
  set h : ℝ := t / N with hh
  have hh0 : 0 ≤ h := by positivity
  have hhδ : h < δ := by
    have : t / δ < N := by
      have : (N₀ : ℝ) + 1 ≤ N := by exact_mod_cast hN
      linarith
    rw [hh, div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hδ] at this
    linarith
  -- the grid
  set a : ℕ → ℝ := fun k => k * t / N with ha
  have ha0 : a 0 = 0 := by simp [ha]
  have haN : a N = t := by simp [ha]; field_simp
  have hamem : ∀ k, k ≤ N → a k ∈ Icc 0 t := by
    intro k hk
    have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
    refine ⟨by positivity, ?_⟩
    rw [ha]; dsimp only
    rw [div_le_iff₀ hNpos]
    nlinarith
  have hastep : ∀ k, a (k + 1) = a k + h := by
    intro k; simp only [ha, hh]; push_cast; ring
  have hint : ∀ k < N, IntervalIntegrable φ volume (a k) (a (k + 1)) := by
    intro k hk
    refine ContinuousOn.intervalIntegrable ?_
    have hsub : uIcc (a k) (a (k + 1)) ⊆ Icc 0 t := by
      rw [uIcc_of_le (by rw [hastep]; linarith)]
      exact Icc_subset_Icc (hamem k hk.le).1 (hamem (k + 1) hk).2
    exact hφ.mono hsub
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := φ) (a := a)
    (n := N) hint
  rw [ha0, haN] at hsum
  rw [Real.dist_eq, ← hsum, ← Finset.sum_sub_distrib]
  -- each term is small
  have hterm : ∀ k ∈ Finset.range N,
      |(t / N) * φ (k * t / N) - ∫ s in a k..a (k + 1), φ s| ≤ ε / (t + 1) * h := by
    intro k hk
    have hk' : k < N := Finset.mem_range.1 hk
    have hconst : (t / N) * φ (a k) = ∫ s in a k..a (k + 1), φ (a k) := by
      rw [intervalIntegral.integral_const, hastep, smul_eq_mul]
      simp [hh]
    have : (t / N) * φ (k * t / N) - ∫ s in a k..a (k + 1), φ s =
        ∫ s in a k..a (k + 1), (φ (a k) - φ s) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hint k hk')]
      rw [← hconst]
    rw [this]
    have hbd := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a k) (b := a (k + 1)) (f := fun s => φ (a k) - φ s) (C := ε / (t + 1)) ?_
    · rw [Real.norm_eq_abs] at hbd
      refine hbd.trans ?_
      rw [hastep, add_sub_cancel_left, abs_of_nonneg hh0, mul_comm]
    · intro s hs
      rw [uIoc_of_le (by rw [hastep]; linarith)] at hs
      have hsI : s ∈ Icc 0 t := ⟨(hamem k hk'.le).1.trans hs.1.le,
        hs.2.trans (hamem (k + 1) hk').2⟩
      have hd : dist (a k) s < δ := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hs.1])]
        rw [hastep] at hs
        linarith [hs.2]
      have := hδφ (a k) (hamem k hk'.le) s hsI hd
      rw [Real.dist_eq] at this
      rw [Real.norm_eq_abs]
      exact this.le
  calc |∑ k ∈ Finset.range N, ((t / N) * φ (k * t / N) - ∫ s in a k..a (k + 1), φ s)|
      ≤ ∑ k ∈ Finset.range N, |(t / N) * φ (k * t / N) - ∫ s in a k..a (k + 1), φ s| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range N, ε / (t + 1) * h := Finset.sum_le_sum hterm
    _ = ε * (t / (t + 1)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hh]
        field_simp
    _ < ε := by
        have : t / (t + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
        nlinarith

/-! ### Discrete winding -/

theorem arg_exp_mul_I_of_abs_lt {θ : ℝ} (h : |θ| < π) : arg (exp (θ * I)) = θ := by
  rw [arg_exp_mul_I, toIocMod_eq_self]
  have := abs_lt.1 h
  constructor <;> linarith [this.1, this.2]

/-- The principal argument of a ratio of two points whose arguments differ by less than `π` is the
difference of the (lifted) arguments. -/
theorem arg_div_eq_sub {N₁ N₂ α β : ℝ} (h₁ : 0 < N₁) (h₂ : 0 < N₂) (hαβ : |α - β| < π) :
    arg ((N₁ : ℂ) * exp (α * I) / ((N₂ : ℂ) * exp (β * I))) = α - β := by
  have h : (N₁ : ℂ) * exp (α * I) / ((N₂ : ℂ) * exp (β * I)) =
      ((N₁ / N₂ : ℝ) : ℂ) * exp (((α - β : ℝ) : ℂ) * I) := by
    have hN₂ : (N₂ : ℂ) ≠ 0 := by exact_mod_cast h₂.ne'
    rw [ofReal_sub, sub_mul, exp_sub]
    push_cast
    field_simp
  rw [h, arg_real_mul _ (div_pos h₁ h₂), arg_exp_mul_I_of_abs_lt hαβ]

/-- **Discrete winding.** If `θ` is a continuous lift of the argument of a nonvanishing function
`f` on `[0, t]`, then for all large `N` the principal arguments of the successive ratios
`f((k+1)t/N) / f(kt/N)`, `k < N`, add up to `θ t - θ 0`. -/
theorem eventually_sum_arg_eq {f : ℝ → ℂ} {θ : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hθ : ContinuousOn θ (Icc 0 t)) (hf : ∀ r ∈ Icc (0 : ℝ) t, f r = ‖f r‖ * exp (θ r * I))
    (hf0 : ∀ r ∈ Icc (0 : ℝ) t, f r ≠ 0) :
    ∀ᶠ N : ℕ in atTop,
      ∑ k ∈ Finset.range N, arg (f (((k + 1 : ℕ) : ℝ) * t / N) / f (k * t / N)) = θ t - θ 0 := by
  obtain ⟨δ, hδ, hδθ⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hθ) π Real.pi_pos
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (t / δ)
  filter_upwards [eventually_gt_atTop N₀] with N hN
  have hNpos : (0 : ℝ) < N := by
    have : (N₀ : ℝ) < N := by exact_mod_cast hN
    have h0 : (0 : ℝ) ≤ N₀ := N₀.cast_nonneg
    linarith
  have hamem : ∀ k, k ≤ N → (k : ℝ) * t / N ∈ Icc (0 : ℝ) t := by
    intro k hk
    have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hNpos]
    nlinarith
  have hstep : ∀ k, (((k + 1 : ℕ) : ℝ) * t / N) - (k * t / N) = t / N := by
    intro k; push_cast; ring
  have htδ : t / N < δ := by
    have : t / δ < N := by
      have : (N₀ : ℝ) < N := by exact_mod_cast hN
      linarith
    rw [div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hδ] at this
    linarith
  have hterm : ∀ k ∈ Finset.range N,
      arg (f (((k + 1 : ℕ) : ℝ) * t / N) / f (k * t / N)) =
        θ (((k + 1 : ℕ) : ℝ) * t / N) - θ (k * t / N) := by
    intro k hk
    have hk' : k < N := Finset.mem_range.1 hk
    have hm1 := hamem (k + 1) hk'
    have hm0 := hamem k hk'.le
    have hd : dist (θ (((k + 1 : ℕ) : ℝ) * t / N)) (θ (k * t / N)) < π := by
      refine hδθ _ hm1 _ hm0 ?_
      rw [Real.dist_eq, hstep, abs_of_nonneg (by positivity)]
      exact htδ
    rw [Real.dist_eq] at hd
    have e1 := hf _ hm1
    have e0 := hf _ hm0
    have n1 : 0 < ‖f (((k + 1 : ℕ) : ℝ) * t / N)‖ := norm_pos_iff.2 (hf0 _ hm1)
    have n0 : 0 < ‖f ((k : ℝ) * t / N)‖ := norm_pos_iff.2 (hf0 _ hm0)
    rw [e1, e0]
    exact arg_div_eq_sub n1 n0 hd
  rw [Finset.sum_congr rfl hterm]
  have := Finset.sum_range_sub (fun k : ℕ => θ ((k : ℝ) * t / N)) N
  rw [this]
  have hN' : (N : ℝ) * t / N = t := by field_simp
  rw [hN']
  simp

end ComplexSLE.Internal.Polar

end
