/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.KernelBasic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Lemma A.1 in kernel form: invariance of `p₀(u) du` under the semigroup

Let `p₀` be a Kolmogorov density for `(α, β)` (`IsKolmogorovDensity`) and `p` a diffusion kernel
(`IsDiffusionKernel α β p`, `KernelBasic.lean`). For every `C²` `π`-periodic test function `f` and
every `t`,
`∫₀^π (T_t f)(u) p₀(u) du = ∫₀^π f(u) p₀(u) du`,
with `T_t f(u) = ∫ f(v) p t u v dv` for `t > 0` (and `T_0 = id`); see
`IsDiffusionKernel.integral_kernelOp_mul_eq` (and `integral_transition_mul_eq` for `t > 0` in the
literal form).

Route (the analytic part of paper.tex:L2376-2402, here for the kernel instead of a single process):

* `hasDerivWithinAt_integral_kernelOp`: for `g ∈ C²` periodic, the right derivative at `0` of
  `h ↦ ∫₀^π T_h g · p₀` is `∫₀^π Lg · p₀ = 0`. For each `u` the slope converges to `Lg(u)`
  (Itô in expectation along a solution from `u`, `hasDerivWithinAt_kernelOp`), and it is bounded
  by `C_L` (`abs_kernelOp_sub_le`); dominated convergence in `u`, then
  `IsKolmogorovDensity.integral_generator_eq_zero`.
* `contDiff_kernelOp` and `periodic_kernelOp`: `T_s f` is again `C²` and periodic, so the semigroup
  identity `T_{s+h} = T_h ∘ T_s` (`kernelOp_add`) reduces the right derivative of
  `Ψ(s) = ∫₀^π T_s f · p₀` at every `s ≥ 0` to the one at `0`;
* `Ψ` is Lipschitz (`abs_kernelOp_sub_le` and `∫₀^π p₀ = 1`), hence constant
  (`constant_of_has_deriv_right_zero`).

Everything consumes `ito_formula` (through `ItoReal.lean`), so is `PROVED_REL{ito_formula}`.
The Markov property and the properties of the kernel are explicit hypotheses
(`IsDiffusionKernel`), not assumed from any external.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set Function Real intervalIntegral
open scoped Interval

namespace ComplexSLE.Internal

variable {α β : ℝ → ℝ} {p : ℝ≥0 → ℝ → ℝ → ℝ} {p₀ : ℝ → ℝ}

/-- The generator of a `π`-periodic `g` is `π`-periodic when `α` and `β²` are. -/
theorem periodic_generator (hαper : Periodic α π) (hβper : Periodic (fun u => β u ^ 2) π)
    {g : ℝ → ℝ} (hgper : Periodic g π) : Periodic (generator α β g) π := fun u => by
  simp only [generator, hgper.deriv_periodic u, hgper.deriv_periodic.deriv_periodic u, hαper u]
  have := hβper u
  simp only at this
  rw [this]

namespace IsDiffusionKernel

/-- `T_s f` is `C²` for a `C²` periodic `f` and every `s ≥ 0`. -/
theorem contDiff_kernelOp (K : IsDiffusionKernel α β p) (s : ℝ≥0) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfper : Periodic f π) : ContDiff ℝ 2 (kernelOp p s f) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simpa using hf
  rw [kernelOp_of_pos (pos_iff_ne_zero.mpr hs)]
  exact K.smooth s (pos_iff_ne_zero.mpr hs) f hf.continuous.measurable
    (hfper.exists_bound pi_ne_zero hf.continuous)

/-- `T_s f` is `π`-periodic for a `π`-periodic `f` (equivariance of the kernel). -/
theorem periodic_kernelOp (K : IsDiffusionKernel α β p) (s : ℝ≥0) {f : ℝ → ℝ}
    (hfper : Periodic f π) : Periodic (kernelOp p s f) π := by
  rcases eq_or_ne s 0 with rfl | hs
  · simpa using hfper
  rw [kernelOp_of_pos (pos_iff_ne_zero.mpr hs)]
  exact periodic_integral_mul_transition (K.equivariant s (pos_iff_ne_zero.mpr hs)) hfper

/-- **The infinitesimal step.** For `g ∈ C²` periodic and a Kolmogorov density `p₀`, the right
derivative at `0` of `h ↦ ∫₀^π (T_h g) p₀` vanishes (it is `∫₀^π (Lg) p₀ = 0`). -/
theorem hasDerivWithinAt_integral_kernelOp (K : IsDiffusionKernel α β p) (hα : ContDiff ℝ 1 α)
    (hβ : ContDiff ℝ 2 β) (hαper : Periodic α π) (hβper : Periodic (fun u => β u ^ 2) π)
    (hp₀ : IsKolmogorovDensity α β p₀) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgper : Periodic g π) :
    HasDerivWithinAt (fun h : ℝ => ∫ u in (0)..π, kernelOp p (Real.toNNReal h) g u * p₀ u) 0
      (Ici 0) 0 := by
  have hαc := hα.continuous
  have hβc := hβ.continuous
  obtain ⟨Cg, hCg⟩ := hgper.exists_bound pi_ne_zero hg.continuous
  have hLcont := continuous_generator hαc hβc hg
  obtain ⟨CL, hCL⟩ := (periodic_generator hαper hβper hgper).exists_bound pi_ne_zero hLcont
  have hint0 : ∫ u in (0)..π, generator α β g u * p₀ u = 0 :=
    hp₀.integral_generator_eq_zero hα hβ hαper hβper hg hgper
  have hp₀c := hp₀.continuous
  have hgc := hg.continuous
  -- continuity of `T_h g` for `h > 0`
  have hTc : ∀ h : ℝ, 0 < h → Continuous (kernelOp p (Real.toNNReal h) g) := fun h hh =>
    (K.contDiff_kernelOp _ hg hgper).continuous
  have hIoi : Ici (0 : ℝ) \ {0} = Ioi 0 := by
    ext u; simp [lt_iff_le_and_ne, eq_comm]
  rw [hasDerivWithinAt_iff_tendsto_slope, hIoi]
  set F : ℝ → ℝ := fun h => ∫ u in (0)..π, kernelOp p (Real.toNNReal h) g u * p₀ u with hF
  -- the slope is the integral of the difference quotient
  have hslope : ∀ h : ℝ, 0 < h → slope F 0 h =
      ∫ u in (0)..π, h⁻¹ * (kernelOp p (Real.toNNReal h) g u - g u) * p₀ u := by
    intro h hh
    have hc1 : Continuous fun u => kernelOp p (Real.toNNReal h) g u * p₀ u := (hTc h hh).mul hp₀c
    have hc2 : Continuous fun u => g u * p₀ u := hgc.mul hp₀c
    have e : ∀ u, h⁻¹ * (kernelOp p (Real.toNNReal h) g u - g u) * p₀ u =
        h⁻¹ * (kernelOp p (Real.toNNReal h) g u * p₀ u - g u * p₀ u) := fun u => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
    simp only [slope_def_field, hF, Real.toNNReal_zero, kernelOp_zero, sub_zero, div_eq_inv_mul]
  have hcongr : (fun h : ℝ => ∫ u in (0)..π, h⁻¹ * (kernelOp p (Real.toNNReal h) g u - g u) * p₀ u)
      =ᶠ[𝓝[>] 0] slope F 0 := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (hslope h hh).symm
  have hlim : Tendsto (fun h : ℝ =>
      ∫ u in (0)..π, h⁻¹ * (kernelOp p (Real.toNNReal h) g u - g u) * p₀ u) (𝓝[>] 0)
      (𝓝 (∫ u in (0)..π, generator α β g u * p₀ u)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun u => CL * p₀ u) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact (((continuous_const.mul ((hTc h hh).sub hgc)).mul hp₀c)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with h hh
      refine Eventually.of_forall fun u _ => ?_
      have hh' : (0 : ℝ) < h := hh
      have hb := K.abs_kernelOp_sub_le hαc hβc hg hCg hCL u 0 (Real.toNNReal h)
      rw [kernelOp_zero, Real.coe_toNNReal _ hh'.le, NNReal.coe_zero, sub_zero,
        abs_of_pos hh'] at hb
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_inv, abs_of_pos hh', abs_of_nonneg (hp₀.nonneg u)]
      refine mul_le_mul_of_nonneg_right ?_ (hp₀.nonneg u)
      calc h⁻¹ * |kernelOp p (Real.toNNReal h) g u - g u| ≤ h⁻¹ * (CL * h) :=
            mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hh'.le)
        _ = CL := by field_simp
    · exact (continuous_const.mul hp₀c).intervalIntegrable _ _
    · refine Eventually.of_forall fun u _ => ?_
      have hd := K.hasDerivWithinAt_kernelOp hαc hβc hg hCg hCL u
      rw [hasDerivWithinAt_iff_tendsto_slope, hIoi] at hd
      refine (hd.mul_const (p₀ u)).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [slope_def_field, Real.toNNReal_zero, kernelOp_zero, sub_zero, div_eq_inv_mul]
  rw [hint0] at hlim
  exact hlim.congr' hcongr

/-- **Lemma A.1 in kernel form, `C²` periodic test functions.**
`∫₀^π (T_t f) p₀ = ∫₀^π f p₀` for every `t ≥ 0` (`T_0 = id`), for `f ∈ C²` periodic and `p₀` a
Kolmogorov density. -/
theorem integral_kernelOp_mul_eq (K : IsDiffusionKernel α β p) (hα : ContDiff ℝ 1 α)
    (hβ : ContDiff ℝ 2 β) (hαper : Periodic α π) (hβper : Periodic (fun u => β u ^ 2) π)
    (hp₀ : IsKolmogorovDensity α β p₀) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfper : Periodic f π)
    (t : ℝ≥0) :
    ∫ u in (0)..π, kernelOp p t f u * p₀ u = ∫ u in (0)..π, f u * p₀ u := by
  have hαc := hα.continuous
  have hβc := hβ.continuous
  have hp₀c := hp₀.continuous
  obtain ⟨Cf, hCf⟩ := hfper.exists_bound pi_ne_zero hf.continuous
  obtain ⟨CL, hCL⟩ := (periodic_generator hαper hβper hfper).exists_bound pi_ne_zero
    (continuous_generator hαc hβc hf)
  have hfb : ∃ C : ℝ, ∀ v, |f v| ≤ C := ⟨Cf, hCf⟩
  set Ψ : ℝ → ℝ := fun x => ∫ u in (0)..π, kernelOp p (Real.toNNReal x) f u * p₀ u with hΨ
  -- `Ψ` is Lipschitz
  have hΨlip : LipschitzWith (Real.toNNReal CL) Ψ := by
    refine LipschitzWith.of_dist_le' fun x y => ?_
    simp only [hΨ, Real.dist_eq]
    have hcont : ∀ s : ℝ≥0, Continuous fun u => kernelOp p s f u * p₀ u := fun s =>
      ((K.contDiff_kernelOp s hf hfper).continuous).mul hp₀c
    rw [← intervalIntegral.integral_sub ((hcont _).intervalIntegrable _ _)
      ((hcont _).intervalIntegrable _ _)]
    have hCL0 : 0 ≤ CL := le_trans (abs_nonneg _) (hCL 0)
    have hb : ∀ u ∈ Ioc (0 : ℝ) π, ‖kernelOp p (Real.toNNReal x) f u * p₀ u -
        kernelOp p (Real.toNNReal y) f u * p₀ u‖ ≤ (CL * |x - y|) * p₀ u := by
      intro u _
      rw [← sub_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp₀.nonneg u)]
      refine mul_le_mul_of_nonneg_right ?_ (hp₀.nonneg u)
      calc |kernelOp p (Real.toNNReal x) f u - kernelOp p (Real.toNNReal y) f u|
          ≤ CL * |((Real.toNNReal x : ℝ≥0) : ℝ) - ((Real.toNNReal y : ℝ≥0) : ℝ)| :=
            K.abs_kernelOp_sub_le hαc hβc hf hCf hCL u _ _
        _ ≤ CL * |x - y| := by
            apply mul_le_mul_of_nonneg_left _ hCL0
            rw [Real.coe_toNNReal', Real.coe_toNNReal']
            exact abs_max_sub_max_le_abs x y 0
    have := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := 0) (b := π) pi_pos.le
      (f := fun u => kernelOp p (Real.toNNReal x) f u * p₀ u -
        kernelOp p (Real.toNNReal y) f u * p₀ u) (g := fun u => (CL * |x - y|) * p₀ u)
      (Eventually.of_forall hb) ((continuous_const.mul hp₀c).intervalIntegrable _ _)
    rw [intervalIntegral.integral_const_mul, hp₀.integral_eq_one, mul_one] at this
    simpa [Real.norm_eq_abs] using this
  -- the right derivative of `Ψ` vanishes at every `s ≥ 0`
  have hΨderiv : ∀ s : ℝ, 0 ≤ s → HasDerivWithinAt Ψ 0 (Ici s) s := by
    intro s hs
    set s' : ℝ≥0 := Real.toNNReal s with hs'
    set g : ℝ → ℝ := kernelOp p s' f with hg
    have hgC2 : ContDiff ℝ 2 g := K.contDiff_kernelOp s' hf hfper
    have hgper : Periodic g π := K.periodic_kernelOp s' hfper
    have h1 := K.hasDerivWithinAt_integral_kernelOp hα hβ hαper hβper hp₀ hgC2 hgper
    -- `Ψ (t + s) = ∫₀^π T_t g p₀` for `t ≥ 0`
    have hshift : ∀ t : ℝ, 0 ≤ t →
        ∫ u in (0)..π, kernelOp p (Real.toNNReal t) g u * p₀ u = Ψ (t + s) := by
      intro t ht
      simp only [hΨ]
      rw [Real.toNNReal_add ht hs, K.kernelOp_add _ _ hf.continuous.measurable hfb]
    have h1' : HasDerivWithinAt (fun t : ℝ => Ψ (t + s)) 0 (Ici 0) (s - s) := by
      rw [sub_self]
      refine h1.congr (fun t ht => (hshift t ht).symm) ?_
      exact (hshift 0 le_rfl).symm
    have h2 : HasDerivWithinAt (fun u : ℝ => u - s) 1 (Ici s) s :=
      (hasDerivWithinAt_sub_const_iff s).mpr (hasDerivWithinAt_id s (Ici s))
    have hmaps : MapsTo (fun u : ℝ => u - s) (Ici s) (Ici 0) := fun u hu => by
      simpa [mem_Ici, sub_nonneg] using hu
    have h3 := HasDerivWithinAt.comp (h := fun u : ℝ => u - s) s h1' h2 hmaps
    simp only [zero_mul] at h3
    refine h3.congr (fun u _ => ?_) ?_ <;> simp [Function.comp]
  have hconst := constant_of_has_deriv_right_zero (a := 0) (b := (t : ℝ))
    hΨlip.continuous.continuousOn (fun x hx => hΨderiv x hx.1) t ⟨t.2, le_rfl⟩
  simpa [hΨ, Real.toNNReal_coe, Real.toNNReal_zero] using hconst

/-- **Lemma A.1 in kernel form, `C²` periodic test functions, literal form.**
`∫₀^π (∫ f(v) p t u v dv) p₀(u) du = ∫₀^π f(u) p₀(u) du` for every `t > 0`. -/
theorem integral_transition_mul_eq (K : IsDiffusionKernel α β p) (hα : ContDiff ℝ 1 α)
    (hβ : ContDiff ℝ 2 β) (hαper : Periodic α π) (hβper : Periodic (fun u => β u ^ 2) π)
    (hp₀ : IsKolmogorovDensity α β p₀) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfper : Periodic f π)
    {t : ℝ≥0} (ht : 0 < t) :
    ∫ u in (0)..π, (∫ v, f v * p t u v) * p₀ u = ∫ u in (0)..π, f u * p₀ u := by
  have := K.integral_kernelOp_mul_eq hα hβ hαper hβper hp₀ hf hfper t
  rwa [kernelOp_of_pos ht] at this

end IsDiffusionKernel

end ComplexSLE.Internal

end
