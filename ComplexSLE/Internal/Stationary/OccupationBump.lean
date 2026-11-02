/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.CriticalCoefficients
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# A shrinking periodic bump at the zero lattice of `D` (M10-R5a)

For the critical case `c² = ab` (`D(u) = (R²/2) sin²(u - x₀)`), the occupation of the zero lattice
`x₀ + πℤ` is controlled by Dynkin's formula with the test functions

  `ψ_N(x) = φ(N² sin²(x - x₀))`,   `φ(s) = 1 - smoothTransition(2s)`:

`ψ_N` is smooth, `π`-periodic, `0 ≤ ψ_N ≤ 1`, `ψ_N = 1` on the lattice and `ψ_N = 0` where
`N |sin(x - x₀)| ≥ 1`. The key estimate is
`|½ ψ_N'(x) · R² sin²(x - x₀)| ≤ K_φ R² / N` (`abs_half_deriv_critBump_mul_le`): this is `½ ψ_N' β²`
with `β² = 2D = R² sin²`, and it comes from `|ψ_N'| ≲ N² |sin|`, `N |sin| < 1` on the support.
-/

public section

open Real Set Function Filter
open scoped Topology

namespace ComplexSLE.Internal

/-! ### The profile -/

/-- The profile `φ(s) = 1 - smoothTransition(2s)`: smooth, `φ(0) = 1`, `0 ≤ φ ≤ 1`, `φ = 0` on
`[1/2, ∞)`. -/
@[expose] noncomputable def bumpProfile (s : ℝ) : ℝ := 1 - Real.smoothTransition (2 * s)

theorem contDiff_bumpProfile : ContDiff ℝ 1 bumpProfile :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id))

theorem bumpProfile_zero : bumpProfile 0 = 1 := by simp [bumpProfile, Real.smoothTransition.zero]

theorem bumpProfile_nonneg (s : ℝ) : 0 ≤ bumpProfile s := by
  unfold bumpProfile; linarith [Real.smoothTransition.le_one (2 * s)]

theorem bumpProfile_le_one (s : ℝ) : bumpProfile s ≤ 1 := by
  unfold bumpProfile; linarith [Real.smoothTransition.nonneg (2 * s)]

theorem bumpProfile_eq_zero_of_half_le {s : ℝ} (h : 1 / 2 ≤ s) : bumpProfile s = 0 := by
  unfold bumpProfile
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  norm_num

theorem deriv_bumpProfile_eq_zero_of_one_le {s : ℝ} (h : 1 ≤ s) : deriv bumpProfile s = 0 := by
  have : bumpProfile =ᶠ[𝓝 s] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds (show 1 / 2 < s by linarith)] with t ht
    exact bumpProfile_eq_zero_of_half_le (le_of_lt ht)
  rw [this.deriv_eq, deriv_const]

theorem exists_abs_deriv_bumpProfile_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s, 0 ≤ s → |deriv bumpProfile s| ≤ K := by
  have hc : Continuous (deriv bumpProfile) := contDiff_bumpProfile.continuous_deriv le_rfl
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (f := deriv bumpProfile) hc.continuousOn
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨K, hK0, fun s hs => ?_⟩
  by_cases h1 : s ≤ 1
  · simpa [Real.norm_eq_abs] using hK s ⟨hs, h1⟩
  · rw [deriv_bumpProfile_eq_zero_of_one_le (by linarith)]
    simpa using hK0

/-! ### The family `ψ_N` -/

/-- `ψ_N(x) = φ(N² sin²(x - x₀))`. -/
@[expose] noncomputable def critBump (x₀ N x : ℝ) : ℝ := bumpProfile (N ^ 2 * sin (x - x₀) ^ 2)

variable {x₀ N : ℝ}

theorem contDiff_critBump (x₀ N : ℝ) : ContDiff ℝ 1 (critBump x₀ N) :=
  contDiff_bumpProfile.comp (by fun_prop)

theorem periodic_critBump (x₀ N : ℝ) : Periodic (critBump x₀ N) π := fun x => by
  have : x + π - x₀ = (x - x₀) + π := by ring
  simp [critBump, this, sin_add_pi]

theorem critBump_nonneg (x₀ N x : ℝ) : 0 ≤ critBump x₀ N x := bumpProfile_nonneg _

theorem critBump_le_one (x₀ N x : ℝ) : critBump x₀ N x ≤ 1 := bumpProfile_le_one _

theorem critBump_of_sin_eq_zero {x : ℝ} (h : sin (x - x₀) = 0) : critBump x₀ N x = 1 := by
  simp [critBump, h, bumpProfile_zero]

theorem critBump_eq_zero_of_one_le {x : ℝ} (h : 1 ≤ N ^ 2 * sin (x - x₀) ^ 2) :
    critBump x₀ N x = 0 :=
  bumpProfile_eq_zero_of_half_le (by linarith)

theorem deriv_critBump (x₀ N x : ℝ) : deriv (critBump x₀ N) x =
    deriv bumpProfile (N ^ 2 * sin (x - x₀) ^ 2) * (N ^ 2 * (2 * sin (x - x₀) * cos (x - x₀))) := by
  have h1 := (contDiff_bumpProfile.differentiable one_ne_zero (N ^ 2 * sin (x - x₀) ^ 2)).hasDerivAt
  have h2 := hasDerivAt_mul_sin_sq_sub (N ^ 2) x₀ x
  exact (h1.comp x h2).deriv

/-- **The key estimate**: `|½ ψ_N' · R² sin²(x - x₀)| ≤ K_φ R² / N`. -/
theorem abs_half_deriv_critBump_mul_le {R Kφ : ℝ} (hN : 0 < N) (hK0 : 0 ≤ Kφ)
    (hK : ∀ s, 0 ≤ s → |deriv bumpProfile s| ≤ Kφ) (x : ℝ) :
    |1 / 2 * deriv (critBump x₀ N) x * (R ^ 2 * sin (x - x₀) ^ 2)| ≤ Kφ * R ^ 2 / N := by
  rw [deriv_critBump]
  set t := sin (x - x₀) with ht
  set cc := cos (x - x₀) with hcc
  have hb0 : 0 ≤ Kφ * R ^ 2 / N := by positivity
  by_cases h : 1 ≤ N ^ 2 * t ^ 2
  · rw [deriv_bumpProfile_eq_zero_of_one_le h]
    simpa using hb0
  · rw [not_le] at h
    have h1 : |t| * N < 1 := by
      have h2 : (t * N) ^ 2 < 1 ^ 2 := by nlinarith
      have := abs_lt_of_sq_lt_sq h2 zero_le_one
      rwa [abs_mul, abs_of_pos hN] at this
    have h3 : N ^ 2 * |t| ^ 3 ≤ 1 / N := by
      rw [le_div_iff₀ hN]
      have := pow_le_one₀ (mul_nonneg (abs_nonneg t) hN.le) h1.le (n := 3)
      nlinarith
    have hφ := hK (N ^ 2 * t ^ 2) (by positivity)
    have hc1 : |cc| ≤ 1 := abs_cos_le_one _
    set φ' := deriv bumpProfile (N ^ 2 * t ^ 2) with hφ'
    have e : 1 / 2 * (φ' * (N ^ 2 * (2 * t * cc))) * (R ^ 2 * t ^ 2) =
        φ' * (N ^ 2 * R ^ 2) * (t ^ 3 * cc) := by ring
    rw [e]
    simp only [abs_mul, abs_pow, sq_abs]
    calc |φ'| * (N ^ 2 * R ^ 2) * (|t| ^ 3 * |cc|)
        ≤ Kφ * (N ^ 2 * R ^ 2) * (|t| ^ 3 * 1) := by gcongr
      _ = Kφ * R ^ 2 * (N ^ 2 * |t| ^ 3) := by ring
      _ ≤ Kφ * R ^ 2 * (1 / N) := by gcongr
      _ = Kφ * R ^ 2 / N := by ring

end ComplexSLE.Internal

end
