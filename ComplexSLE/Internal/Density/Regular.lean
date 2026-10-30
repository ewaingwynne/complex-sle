/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Density.Basic
public import ComplexSLE.Infrastructure.Primitive

/-!
# Admissible densities, Case 1: `c² < ab`

When `c² < ab` the diffusion coefficient `D` is positive everywhere. Instead of the source's
`p₀ + r_* p₁` (paper.tex:L1012-1080, which needs a closed-form antiderivative of `µ/D`) we use
the route authorised by the orchestrator: with `Φ(u) = ∫₀ᵘ µ/D` and `λ = Φ(π)`, the function
`q(u) = exp(Φ(u)) ∫_u^{u+π} exp(-Φ(s)) ds` is positive, `π`-periodic and satisfies
`q' = (µ/D) q + (e^{-λ} - 1)`, so `p = q / D` solves `-µp + (Dp)' = e^{-λ} - 1` on all of `ℝ`
and hence the stationary equation `-(µp)' + (Dp)'' = 0`. This replaces the graph nodes
`step:p-case1-*`.
-/

public section

open Set Filter Topology MeasureTheory intervalIntegral Function Real
open scoped ContDiff

namespace ComplexSLE.Internal

variable {a b c : ℝ}

/-- **Lemma 2.13, Case 1** (`c² < ab`): an admissible density exists. -/
theorem exists_admissibleDensity_of_sq_lt (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 < a * b) :
    ∃ p, IsAdmissibleDensity a b c p := by
  have hD : ∀ u, 0 < diffusionD a b c u := diffusionD_pos ha hb hc
  have hDne : ∀ u, diffusionD a b c u ≠ 0 := fun u => (hD u).ne'
  -- the ratio `g = µ / D`
  set g : ℝ → ℝ := fun u => mu a b c u / diffusionD a b c u with hg
  have hg_smooth : ContDiff ℝ ∞ g := (contDiff_mu a b c).div (contDiff_diffusionD a b c) hDne
  have hg_cont : Continuous g := hg_smooth.continuous
  have hg_per : Periodic g π := (mu_periodic a b c).div (diffusionD_periodic a b c)
  -- `Φ = ∫₀ᵘ g`
  set Φ : ℝ → ℝ := fun u => ∫ s in (0)..u, g s with hΦ
  have hΦ_deriv : ∀ u, HasDerivAt Φ (g u) u :=
    Infrastructure.hasDerivAt_integral_of_continuous hg_cont 0
  have hΦ_smooth : ContDiff ℝ ∞ Φ := Infrastructure.contDiff_integral_of_contDiff hg_smooth 0
  set lam : ℝ := Φ π with hlam
  have hΦ_add : ∀ u, Φ (u + π) = Φ u + lam := by
    intro u
    simp only [hΦ, hlam]
    rw [← integral_add_adjacent_intervals (hg_cont.intervalIntegrable 0 u)
      (hg_cont.intervalIntegrable u (u + π))]
    congr 1
    rw [hg_per.intervalIntegral_add_eq u 0, zero_add]
  -- `E = exp (-Φ)` and its primitive `F`
  set E : ℝ → ℝ := fun u => exp (-Φ u) with hE
  have hE_smooth : ContDiff ℝ ∞ E := hΦ_smooth.neg.exp
  have hE_cont : Continuous E := hE_smooth.continuous
  have hE_pos : ∀ u, 0 < E u := fun u => exp_pos _
  set F : ℝ → ℝ := fun u => ∫ s in (0)..u, E s with hF
  have hF_deriv : ∀ u, HasDerivAt F (E u) u :=
    Infrastructure.hasDerivAt_integral_of_continuous hE_cont 0
  have hF_smooth : ContDiff ℝ ∞ F := Infrastructure.contDiff_integral_of_contDiff hE_smooth 0
  have hF_sub : ∀ u, F (u + π) - F u = ∫ s in u..(u + π), E s := by
    intro u
    simp only [hF]
    exact integral_interval_sub_left (hE_cont.intervalIntegrable _ _)
      (hE_cont.intervalIntegrable _ _)
  have hF_pos : ∀ u, 0 < F (u + π) - F u := by
    intro u
    rw [hF_sub]
    exact intervalIntegral_pos_of_pos (hE_cont.intervalIntegrable _ _) hE_pos
      (by linarith [pi_pos])
  have hF_shift : ∀ u, F (u + π + π) - F (u + π) = exp (-lam) * (F (u + π) - F u) := by
    intro u
    rw [hF_sub, hF_sub, ← intervalIntegral.integral_const_mul,
      ← integral_comp_add_right (fun s => E s) π]
    congr 1
    funext s
    simp only [hE, hΦ_add]
    rw [neg_add, exp_add]
    ring
  -- `q = exp Φ · (F (· + π) - F)`
  set q : ℝ → ℝ := fun u => exp (Φ u) * (F (u + π) - F u) with hq
  have hq_pos : ∀ u, 0 < q u := fun u => mul_pos (exp_pos _) (hF_pos u)
  have hq_per : Periodic q π := by
    intro u
    simp only [hq]
    rw [hF_shift, hΦ_add]
    have : exp (Φ u + lam) * exp (-lam) = exp (Φ u) := by
      rw [← exp_add]; ring_nf
    rw [← mul_assoc, this]
  set K : ℝ := exp (-lam) - 1 with hK
  have hq_deriv : ∀ u, HasDerivAt q (g u * q u + K) u := by
    intro u
    have h1 := ((hΦ_deriv u).exp).mul
      (((hF_deriv (u + π)).comp_add_const u π).sub (hF_deriv u))
    convert h1 using 1
    have e1 : exp (Φ u) * exp (-Φ u) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
    simp only [hq, hE, hK, hΦ_add, Pi.sub_apply]
    rw [neg_add, exp_add]
    linear_combination (1 - exp (-lam)) * e1
  have hq_smooth : ContDiff ℝ ∞ q :=
    hΦ_smooth.exp.mul ((hF_smooth.comp (contDiff_id.add contDiff_const)).sub hF_smooth)
  -- `p₀ = q / D`
  set p₀ : ℝ → ℝ := fun u => q u / diffusionD a b c u with hp₀
  have hp₀_smooth : ContDiff ℝ ∞ p₀ := hq_smooth.div (contDiff_diffusionD a b c) hDne
  have hp₀_pos : ∀ u, 0 < p₀ u := fun u => div_pos (hq_pos u) (hD u)
  have hp₀_per : Periodic p₀ π := hq_per.div (diffusionD_periodic a b c)
  have hDp : (fun v => diffusionD a b c v * p₀ v) = q := by
    funext v
    simp only [hp₀]
    exact mul_div_cancel₀ _ (hDne v)
  have pre : IsPreDensity a b c p₀ 0 K :=
    { continuous := hp₀_smooth.continuous
      nonneg := fun u => (hp₀_pos u).le
      periodic := hp₀_per
      integral_pos := Infrastructure.Periodic.integral_two_mul_pos (x := 0) pi_pos hp₀_per
        hp₀_smooth.continuous (fun u _ => hp₀_pos u)
      contDiffOn := (hp₀_smooth.of_le (by simp)).contDiffOn
      hasDerivAt := by
        intro u
        rw [hDp]
        convert hq_deriv u using 1
        simp only [hp₀, hg]
        field_simp
        ring }
  exact pre.exists_isAdmissibleDensity

end ComplexSLE.Internal

end
