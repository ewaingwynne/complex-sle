/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.KolmogorovDensity
public import ComplexSLE.Internal.Stationary.ItoReal
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Lemma A.1: invariance of `E f(X_t)` for periodic test functions

The probabilistic assembly of Lemma A.1 (paper.tex:L2360-2402), modulo the Markov property of
the diffusion, which is an EXTERNAL input not yet in the manifest (see the handoff report and the
docstring of `integral_comp_eq_of_markov`). Given

* a Kolmogorov density `p₀` for `(α, β)` (`IsKolmogorovDensity`),
* a solution `X` of `dX = α(X) dt + β(X) dB` in martingale form with everywhere-continuous paths
  and `X₀ ~ p₀(u) 1_{[0,π]}(u) du` (stated through integrals of bounded measurable functions),
* a transition density `p` with smooth, `π`-equivariant semigroup `T_s f(u) = ∫ f(v) p s u v dv`
  and the Markov property `E f(X_{t+s}) = E (T_s f)(X_t)`,

we prove `E f(X_t) = E f(X_0)` for every `C²` `π`-periodic `f`
(`step:kol-derivative-vanishes-all-times`): `t ↦ E f(X_t)` is Lipschitz, and its right derivative
at every `s` vanishes, because by the Markov property it is `t ↦ E (T_s f)(X_t)` near `s`, whose
derivative at `0` is `∫₀^π L(T_s f) p₀ = 0` by `IsKolmogorovDensity.integral_generator_eq_zero`.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set Function Real

namespace ComplexSLE.Internal

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ≥0 mΩ} {α β : ℝ → ℝ} {X : ℝ≥0 → Ω → ℝ}

omit [IsProbabilityMeasure P] in
/-- `E (Lf)(X_0) = 0` for a `C²` `π`-periodic `f` when `X_0 ~ p₀ 1_{[0,π]} du`
(`step:kol-derivative-at-zero` and `step:kol-integration-by-parts`). -/
theorem integral_generator_comp_zero_eq_zero (hα : ContDiff ℝ 1 α) (hβ : ContDiff ℝ 2 β)
    (hαper : Periodic α π) (hβper : Periodic (fun u => β u ^ 2) π)
    {p₀ : ℝ → ℝ} (hp₀ : IsKolmogorovDensity α β p₀)
    (h0 : ∀ g : ℝ → ℝ, Measurable g → (∃ C : ℝ, ∀ v, |g v| ≤ C) →
      ∫ ω, g (X 0 ω) ∂P = ∫ u in (0)..π, g u * p₀ u)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfper : Periodic f π) :
    ∫ ω, generator α β f (X 0 ω) ∂P = 0 := by
  have hLcont : Continuous (generator α β f) := continuous_generator hα.continuous hβ.continuous hf
  have hLper : Periodic (generator α β f) π := fun u => by
    simp only [generator, hfper.deriv_periodic u, hfper.deriv_periodic.deriv_periodic u, hαper u]
    have := hβper u
    simp only at this
    rw [this]
  rw [h0 _ hLcont.measurable (hLper.exists_bound pi_ne_zero hLcont)]
  exact hp₀.integral_generator_eq_zero hα hβ hαper hβper hf hfper

/-- The semigroup `T_s f(u) = ∫ f(v) p s u v dv` of a `π`-equivariant transition density maps
`π`-periodic functions to `π`-periodic functions (`step:kol-semigroup-smooth`). -/
theorem periodic_integral_mul_transition {p : ℝ≥0 → ℝ → ℝ → ℝ} {s : ℝ≥0}
    (hp_per : ∀ u v, p s (u + π) (v + π) = p s u v) {f : ℝ → ℝ} (hfper : Periodic f π) :
    Periodic (fun u => ∫ v, f v * p s u v) π := by
  intro u
  simp only
  rw [← integral_add_right_eq_self (fun v => f v * p s (u + π) v) π]
  congr 1
  funext v
  rw [hfper v, hp_per u v]

/-- **Lemma A.1, modulo the Markov property** (`step:kol-derivative-vanishes-all-times`,
paper.tex:L2395-2401). Let `p₀` be a Kolmogorov density for `(α, β)` and `X` a solution of
`dX = α(X) dt + β(X) dB` (martingale form, everywhere-continuous paths) with
`X₀ ~ p₀(u) 1_{[0,π]}(u) du`. Let `p` be a transition density whose semigroup
`T_s f(u) = ∫ f(v) p s u v dv` is `C²` for bounded measurable `f` and `s > 0`
(`hormander_oneDim`), which is `π`-equivariant, and for which `X` has the Markov property
`E f(X_{t+s}) = E (T_s f)(X_t)` (`step:kol-markov-semigroup`; the last two are the content of the
EXTERNAL input `markov_oneDim` proposed in the handoff report). Then `E f(X_t) = E f(X_0)` for
every `C²` `π`-periodic `f`. -/
theorem integral_comp_eq_of_markov (hα : ContDiff ℝ 1 α) (hβ : ContDiff ℝ 2 β)
    (hαper : Periodic α π) (hβper : Periodic (fun u => β u ^ 2) π)
    {p₀ : ℝ → ℝ} (hp₀ : IsKolmogorovDensity α β p₀)
    (hX : IsDiffusionSolution ℱ α β X P) (hXc : ∀ ω, Continuous fun t => X t ω)
    (h0 : ∀ g : ℝ → ℝ, Measurable g → (∃ C : ℝ, ∀ v, |g v| ≤ C) →
      ∫ ω, g (X 0 ω) ∂P = ∫ u in (0)..π, g u * p₀ u)
    (p : ℝ≥0 → ℝ → ℝ → ℝ)
    (hp_smooth : ∀ s : ℝ≥0, 0 < s → ∀ f : ℝ → ℝ, Measurable f → (∃ C : ℝ, ∀ v, |f v| ≤ C) →
      ContDiff ℝ 2 fun u => ∫ v, f v * p s u v)
    (hp_per : ∀ s : ℝ≥0, 0 < s → ∀ u v, p s (u + π) (v + π) = p s u v)
    (hMarkov : ∀ t s : ℝ≥0, 0 < s → ∀ f : ℝ → ℝ, Measurable f → (∃ C : ℝ, ∀ v, |f v| ≤ C) →
      ∫ ω, f (X (t + s) ω) ∂P = ∫ ω, (∫ v, f v * p s (X t ω) v) ∂P)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfper : Periodic f π) (t : ℝ≥0) :
    ∫ ω, f (X t ω) ∂P = ∫ ω, f (X 0 ω) ∂P := by
  have hαc := hα.continuous
  have hβc := hβ.continuous
  -- bounds for a `C²` periodic test function and its generator
  have bounds : ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → Periodic g π →
      (∃ C : ℝ, ∀ u, |g u| ≤ C) ∧ ∃ C : ℝ, ∀ u, |generator α β g u| ≤ C := by
    intro g hg hgper
    refine ⟨hgper.exists_bound pi_ne_zero hg.continuous, ?_⟩
    have hLper : Periodic (generator α β g) π := fun u => by
      simp only [generator, hgper.deriv_periodic u, hgper.deriv_periodic.deriv_periodic u,
        hαper u]
      have := hβper u
      simp only at this
      rw [this]
    exact hLper.exists_bound pi_ne_zero (continuous_generator hαc hβc hg)
  -- the right derivative of `t ↦ E g(X_t)` at `0` vanishes for every `C²` periodic `g`
  have hderiv0 : ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → Periodic g π →
      HasDerivWithinAt (fun t : ℝ => ∫ ω, g (X (Real.toNNReal t) ω) ∂P) 0 (Ici 0) 0 := by
    intro g hg hgper
    obtain ⟨⟨Cg, hCg⟩, ⟨CL, hCL⟩⟩ := bounds g hg hgper
    have := IsDiffusionSolution.hasDerivWithinAt_integral_comp hX hXc hαc hβc hg hCg hCL
    rwa [integral_generator_comp_zero_eq_zero hα hβ hαper hβper hp₀ h0 hg hgper] at this
  obtain ⟨⟨Cf, hCf⟩, ⟨CL, hCL⟩⟩ := bounds f hf hfper
  set φ : ℝ → ℝ := fun t => ∫ ω, f (X (Real.toNNReal t) ω) ∂P with hφ
  -- `φ` is Lipschitz
  have hφlip : LipschitzWith (Real.toNNReal CL) φ := by
    refine LipschitzWith.of_dist_le' fun x y => ?_
    simp only [hφ, Real.dist_eq]
    calc |(∫ ω, f (X (Real.toNNReal x) ω) ∂P) - ∫ ω, f (X (Real.toNNReal y) ω) ∂P|
        ≤ CL * |((Real.toNNReal x : ℝ≥0) : ℝ) - ((Real.toNNReal y : ℝ≥0) : ℝ)| :=
          IsDiffusionSolution.abs_integral_sub_integral_le hX hXc hαc hβc hf hCf hCL _ _
      _ ≤ CL * |x - y| := by
          apply mul_le_mul_of_nonneg_left _ (le_trans (abs_nonneg _) (hCL 0))
          rw [Real.coe_toNNReal', Real.coe_toNNReal']
          exact abs_max_sub_max_le_abs x y 0
  -- the right derivative of `φ` vanishes at every `s ≥ 0`
  have hφderiv : ∀ s : ℝ, 0 ≤ s → HasDerivWithinAt φ 0 (Ici s) s := by
    intro s hs
    rcases hs.eq_or_lt with rfl | hspos
    · exact hderiv0 f hf hfper
    · -- the test function `g = T_s f`
      set s' : ℝ≥0 := Real.toNNReal s with hs'
      have hs'pos : 0 < s' := Real.toNNReal_pos.mpr hspos
      set g : ℝ → ℝ := fun u => ∫ v, f v * p s' u v with hg
      have hgC2 : ContDiff ℝ 2 g := hp_smooth s' hs'pos f hf.continuous.measurable ⟨Cf, hCf⟩
      have hgper : Periodic g π := periodic_integral_mul_transition (hp_per s' hs'pos) hfper
      -- `E g(X_t) = φ (t + s)` for `t ≥ 0`
      have hshift : ∀ t : ℝ, 0 ≤ t →
          ∫ ω, g (X (Real.toNNReal t) ω) ∂P = φ (t + s) := by
        intro t ht
        simp only [hφ, hg]
        rw [Real.toNNReal_add ht hspos.le, hMarkov _ _ hs'pos f hf.continuous.measurable ⟨Cf, hCf⟩]
      have h1 : HasDerivWithinAt (fun t : ℝ => φ (t + s)) 0 (Ici 0) (s - s) := by
        rw [sub_self]
        exact (hderiv0 g hgC2 hgper).congr (fun t ht => (hshift t ht).symm) (hshift 0 le_rfl).symm
      -- transport along `u ↦ u - s`
      have h2 : HasDerivWithinAt (fun u : ℝ => u - s) 1 (Ici s) s :=
        (hasDerivWithinAt_sub_const_iff s).mpr (hasDerivWithinAt_id s (Ici s))
      have hmaps : MapsTo (fun u : ℝ => u - s) (Ici s) (Ici 0) := fun u hu => by
        simpa [mem_Ici, sub_nonneg] using hu
      have h3 := HasDerivWithinAt.comp (h := fun u : ℝ => u - s) s h1 h2 hmaps
      simp only [zero_mul] at h3
      refine h3.congr (fun u _ => ?_) ?_ <;> simp [Function.comp]
  -- hence `φ` is constant on `[0, t]`
  have hconst := constant_of_has_deriv_right_zero (a := 0) (b := (t : ℝ))
    hφlip.continuous.continuousOn (fun x hx => hφderiv x hx.1) t ⟨t.2, le_rfl⟩
  simpa [hφ, Real.toNNReal_coe, Real.toNNReal_zero] using hconst

end ComplexSLE.Internal

end
