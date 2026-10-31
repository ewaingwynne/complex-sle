/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.KernelInvariance
public import ComplexSLE.Internal.Stationary.Law
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Lemma A.1 in kernel form: the law form

Under the hypotheses of `KernelInvariance.lean`, for `t > 0`:

* `IsDiffusionKernel.integral_transition_mul_eq_of_periodic`: the invariance
  `∫₀^π (T_t f) p₀ = ∫₀^π f p₀` holds for every bounded measurable `π`-periodic `f` (extension of
  the `C²` periodic case by the density of trigonometric polynomials, through the law
  `μ₀ ⊗ κ_t` on `ℝ × ℝ` of a pair `(U, V)` with `U ~ p₀(u) 1_{[0,π]} du` and
  `V | U = u ~ p t u v dv`, and `map_addCircle_eq_of_forall_integral_eq`);
* `IsDiffusionKernel.map_addCircle_transition_eq`: the law form. The pushforward of
  `p₀(u) 1_{[0,π]}(u) du` under the transition kernel `κ_t(u) = p t u v dv`, taken modulo `π` (as a
  measure on `AddCircle π`), equals the pushforward of `p₀(u) 1_{[0,π]}(u) du` modulo `π`;
* `IsDiffusionKernel.map_exp_transition_eq`: the same for `e^{2iu}` as a measure on `ℂ`.

`kolmogorovMeasure p₀` is the measure `p₀(u) 1_{[0,π]}(u) du` (the form in which
`Law.lean` states the initial law); `IsDiffusionKernel.transitionKernel` is the Markov kernel
`u ↦ p t u v dv`.

Everything consumes `ito_formula` (through `ItoReal.lean`), so is `PROVED_REL{ito_formula}`.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set Function Real intervalIntegral

namespace ComplexSLE.Internal

variable {α β : ℝ → ℝ} {p : ℝ≥0 → ℝ → ℝ → ℝ} {p₀ : ℝ → ℝ}

/-! ### The measure `p₀(u) 1_{[0,π]}(u) du` -/

/-- The measure `p₀(u) 1_{[0,π]}(u) du`. -/
@[expose] noncomputable def kolmogorovMeasure (p₀ : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Icc 0 π)).withDensity fun u => ENNReal.ofReal (p₀ u)

theorem integral_kolmogorovMeasure (hp₀ : IsKolmogorovDensity α β p₀) {G : ℝ → ℝ} :
    ∫ u, G u ∂(kolmogorovMeasure p₀) = ∫ u in (0)..π, G u * p₀ u := by
  rw [kolmogorovMeasure, integral_withDensity_eq_integral_toReal_smul (f := fun v =>
      ENNReal.ofReal (p₀ v)) (ENNReal.measurable_ofReal.comp hp₀.continuous.measurable)
      (Eventually.of_forall fun v => ENNReal.ofReal_lt_top),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le pi_pos.le]
  congr 1
  funext v
  rw [ENNReal.toReal_ofReal (hp₀.nonneg v), smul_eq_mul, mul_comm]

theorem isProbabilityMeasure_kolmogorovMeasure (hp₀ : IsKolmogorovDensity α β p₀) :
    IsProbabilityMeasure (kolmogorovMeasure p₀) := by
  refine ⟨?_⟩
  rw [kolmogorovMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hp₀.continuous.integrableOn_Icc
      (Eventually.of_forall hp₀.nonneg), integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le pi_pos.le, hp₀.integral_eq_one, ENNReal.ofReal_one]

/-! ### The transition kernel `u ↦ p t u v dv` -/

theorem integral_withDensity_transition {t : ℝ≥0} {u : ℝ} (hnn : ∀ v, 0 ≤ p t u v)
    (hm : Measurable (p t u)) {g : ℝ → ℝ} :
    ∫ v, g v ∂(volume.withDensity fun v => ENNReal.ofReal (p t u v)) = ∫ v, g v * p t u v := by
  rw [integral_withDensity_eq_integral_toReal_smul (f := fun v => ENNReal.ofReal (p t u v))
    (ENNReal.measurable_ofReal.comp hm) (Eventually.of_forall fun v => ENNReal.ofReal_lt_top)]
  congr 1
  funext v
  rw [ENNReal.toReal_ofReal (hnn v), smul_eq_mul, mul_comm]

namespace IsDiffusionKernel

/-- `p t u` is integrable (it is a probability density, being the law of a solution). -/
theorem integrable_transition (K : IsDiffusionKernel α β p) {t : ℝ≥0} (ht : 0 < t) (u : ℝ) :
    Integrable (p t u) := by
  have h := (K.isProbabilityMeasure_withDensity ht u).measure_univ
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  have hm : Measurable (p t u) := (K.continuous t ht u).measurable
  have := integrable_toReal_of_lintegral_ne_top (μ := volume)
    (f := fun v => ENNReal.ofReal (p t u v)) (ENNReal.measurable_ofReal.comp hm).aemeasurable
    (by rw [h]; exact ENNReal.one_ne_top)
  refine this.congr (Eventually.of_forall fun v => ?_)
  simp [ENNReal.toReal_ofReal (K.nonneg t u v)]

/-- `u ↦ p t u v dv` is a measurable family of measures. -/
theorem measurable_withDensity_transition (K : IsDiffusionKernel α β p) {t : ℝ≥0} (ht : 0 < t) :
    Measurable fun u : ℝ => (volume.withDensity fun v => ENNReal.ofReal (p t u v)) := by
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  have e : ∀ u, (volume.withDensity fun v => ENNReal.ofReal (p t u v)) A =
      ENNReal.ofReal (∫ v, A.indicator (fun _ => (1 : ℝ)) v * p t u v) := by
    intro u
    rw [withDensity_apply _ hA]
    have : ∫ v, A.indicator (fun _ => (1 : ℝ)) v * p t u v = ∫ v in A, p t u v := by
      rw [← MeasureTheory.integral_indicator hA]
      congr 1
      funext v
      by_cases hv : v ∈ A <;> simp [hv]
    rw [this, ofReal_integral_eq_lintegral_ofReal (K.integrable_transition ht u).restrict
      (Eventually.of_forall fun v => K.nonneg t u v)]
  simp_rw [e]
  refine ENNReal.measurable_ofReal.comp ?_
  exact (K.smooth t ht _ (measurable_const.indicator hA)
    ⟨1, fun v => by by_cases hv : v ∈ A <;> simp [hv]⟩).continuous.measurable

/-- The Markov kernel `u ↦ p t u v dv`, `t > 0`. -/
@[expose] noncomputable def transitionKernel (K : IsDiffusionKernel α β p) {t : ℝ≥0}
    (ht : 0 < t) : Kernel ℝ ℝ where
  toFun u := volume.withDensity fun v => ENNReal.ofReal (p t u v)
  measurable' := K.measurable_withDensity_transition ht

theorem transitionKernel_apply (K : IsDiffusionKernel α β p) {t : ℝ≥0} (ht : 0 < t) (u : ℝ) :
    K.transitionKernel ht u = volume.withDensity fun v => ENNReal.ofReal (p t u v) := rfl

instance (K : IsDiffusionKernel α β p) {t : ℝ≥0} (ht : 0 < t) :
    IsMarkovKernel (K.transitionKernel ht) :=
  ⟨fun u => by rw [transitionKernel_apply]; exact K.isProbabilityMeasure_withDensity ht u⟩

theorem integral_transitionKernel (K : IsDiffusionKernel α β p) {t : ℝ≥0} (ht : 0 < t) (u : ℝ)
    (g : ℝ → ℝ) : ∫ v, g v ∂(K.transitionKernel ht u) = ∫ v, g v * p t u v := by
  rw [transitionKernel_apply]
  exact integral_withDensity_transition (K.nonneg t u) (K.continuous t ht u).measurable

/-! ### The pair `(U, V)`: `U ~ p₀ 1_{[0,π]} du`, `V | U = u ~ p t u v dv` -/

section Pair

variable (K : IsDiffusionKernel α β p) {t : ℝ≥0} (ht : 0 < t)

include K ht in
theorem integral_snd_compProd (hp₀ : IsKolmogorovDensity α β p₀) {g : ℝ → ℝ} (hg : Measurable g)
    {C : ℝ} (hC : ∀ v, |g v| ≤ C) :
    ∫ z, g z.2 ∂((kolmogorovMeasure p₀) ⊗ₘ (K.transitionKernel ht)) =
      ∫ u in (0)..π, (∫ v, g v * p t u v) * p₀ u := by
  have := isProbabilityMeasure_kolmogorovMeasure hp₀
  have hint : Integrable (fun z : ℝ × ℝ => g z.2)
      ((kolmogorovMeasure p₀) ⊗ₘ (K.transitionKernel ht)) :=
    (integrable_const C).mono' (hg.comp measurable_snd).aestronglyMeasurable
      (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hC z.2)
  rw [Measure.integral_compProd hint]
  simp_rw [K.integral_transitionKernel ht]
  rw [integral_kolmogorovMeasure hp₀ (G := fun u => ∫ v, g v * p t u v)]

include K ht in
theorem integral_fst_compProd (hp₀ : IsKolmogorovDensity α β p₀) {g : ℝ → ℝ}
    (hg : Measurable g) :
    ∫ z, g z.1 ∂((kolmogorovMeasure p₀) ⊗ₘ (K.transitionKernel ht)) =
      ∫ u in (0)..π, g u * p₀ u := by
  have := isProbabilityMeasure_kolmogorovMeasure hp₀
  have h1 : ((kolmogorovMeasure p₀) ⊗ₘ (K.transitionKernel ht)).map Prod.fst =
      kolmogorovMeasure p₀ := Measure.fst_compProd _ _
  calc ∫ z, g z.1 ∂((kolmogorovMeasure p₀) ⊗ₘ (K.transitionKernel ht))
      = ∫ x, g x ∂(((kolmogorovMeasure p₀) ⊗ₘ (K.transitionKernel ht)).map Prod.fst) :=
        (integral_map measurable_fst.aemeasurable hg.aestronglyMeasurable).symm
    _ = ∫ x, g x ∂(kolmogorovMeasure p₀) := by rw [h1]
    _ = ∫ u in (0)..π, g u * p₀ u := integral_kolmogorovMeasure hp₀

/-- **The law form, core.** The two coordinates of `μ₀ ⊗ κ_t` have the same law modulo `π`. -/
theorem map_addCircle_compProd_eq (hα : ContDiff ℝ 1 α) (hβ : ContDiff ℝ 2 β)
    (hαper : Periodic α π) (hβper : Periodic (fun u => β u ^ 2) π)
    (hp₀ : IsKolmogorovDensity α β p₀) :
    ((kolmogorovMeasure p₀) ⊗ₘ (K.transitionKernel ht)).map
        (fun z : ℝ × ℝ => ((Prod.snd z : ℝ) : AddCircle π)) =
      ((kolmogorovMeasure p₀) ⊗ₘ (K.transitionKernel ht)).map
        (fun z : ℝ × ℝ => ((Prod.fst z : ℝ) : AddCircle π)) := by
  have := isProbabilityMeasure_kolmogorovMeasure hp₀
  refine map_addCircle_eq_of_forall_integral_eq (Y := Prod.snd) (Z := Prod.fst)
    measurable_snd measurable_fst fun f hf hfper => ?_
  obtain ⟨C, hC⟩ := hfper.exists_bound pi_ne_zero hf.continuous
  rw [K.integral_snd_compProd ht hp₀ hf.continuous.measurable hC,
    K.integral_fst_compProd ht hp₀ hf.continuous.measurable]
  exact K.integral_transition_mul_eq hα hβ hαper hβper hp₀ hf hfper ht

include K ht in
/-- **Lemma A.1 in kernel form, bounded measurable periodic test functions.**
`∫₀^π (∫ f(v) p t u v dv) p₀(u) du = ∫₀^π f p₀` for every bounded measurable `π`-periodic `f`
and `t > 0`. -/
theorem integral_transition_mul_eq_of_periodic (hα : ContDiff ℝ 1 α) (hβ : ContDiff ℝ 2 β)
    (hαper : Periodic α π) (hβper : Periodic (fun u => β u ^ 2) π)
    (hp₀ : IsKolmogorovDensity α β p₀) {f : ℝ → ℝ} (hf : Measurable f)
    (hfb : ∃ C : ℝ, ∀ v, |f v| ≤ C) (hfper : Periodic f π) :
    ∫ u in (0)..π, (∫ v, f v * p t u v) * p₀ u = ∫ u in (0)..π, f u * p₀ u := by
  have := isProbabilityMeasure_kolmogorovMeasure hp₀
  obtain ⟨C, hC⟩ := hfb
  -- `f` as a function on the circle
  have key : ∀ u : ℝ, f ((AddCircle.equivIoc π 0 (u : AddCircle π) : ℝ)) = f u := by
    intro u
    have h1 : (((AddCircle.equivIoc π 0 (u : AddCircle π)) : ℝ) : AddCircle π) =
        (u : AddCircle π) := (AddCircle.equivIoc π 0).symm_apply_apply (u : AddCircle π)
    rw [← hfper.lift_coe (AddCircle.equivIoc π 0 (u : AddCircle π) : ℝ), h1, hfper.lift_coe]
  have hfm : Measurable (hfper.lift : AddCircle π → ℝ) := by
    have : (hfper.lift : AddCircle π → ℝ) =
        fun x => f ((AddCircle.measurableEquivIoc π 0 x : Set.Ioc 0 (0 + π)) : ℝ) := by
      funext x
      obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
      rw [hfper.lift_coe]
      exact (key u).symm
    rw [this]
    exact hf.comp (measurable_subtype_coe.comp (AddCircle.measurableEquivIoc π 0).measurable)
  have hmap := K.map_addCircle_compProd_eq ht hα hβ hαper hβper hp₀
  have hlift : ∀ (Y : ℝ × ℝ → ℝ), Measurable Y →
      ∫ z, f (Y z) ∂((kolmogorovMeasure p₀) ⊗ₘ (K.transitionKernel ht)) =
        ∫ x, hfper.lift x ∂(((kolmogorovMeasure p₀) ⊗ₘ (K.transitionKernel ht)).map
          (fun z : ℝ × ℝ => ((Y z : ℝ) : AddCircle π))) := by
    intro Y hY
    rw [integral_map (φ := fun z : ℝ × ℝ => ((Y z : ℝ) : AddCircle π))
      (measurable_coe_addCircle.comp hY).aemeasurable hfm.aestronglyMeasurable]
    rfl
  rw [← K.integral_snd_compProd ht hp₀ hf hC, ← K.integral_fst_compProd ht hp₀ hf]
  rw [show (fun z : ℝ × ℝ => f z.2) = fun z => f (Prod.snd z) from rfl,
    show (fun z : ℝ × ℝ => f z.1) = fun z => f (Prod.fst z) from rfl,
    hlift Prod.snd measurable_snd, hlift Prod.fst measurable_fst, hmap]

end Pair

/-! ### The law form -/

/-- **Lemma A.1 in kernel form, law form.** The pushforward of `p₀(u) 1_{[0,π]}(u) du` under the
transition kernel `κ_t(u) = p t u v dv`, modulo `π`, equals the pushforward of
`p₀(u) 1_{[0,π]}(u) du` modulo `π` (as measures on `AddCircle π`), for every `t > 0`. -/
theorem map_addCircle_transition_eq (K : IsDiffusionKernel α β p) {t : ℝ≥0} (ht : 0 < t)
    (hα : ContDiff ℝ 1 α) (hβ : ContDiff ℝ 2 β) (hαper : Periodic α π)
    (hβper : Periodic (fun u => β u ^ 2) π) (hp₀ : IsKolmogorovDensity α β p₀) :
    ((K.transitionKernel ht) ∘ₘ kolmogorovMeasure p₀).map ((↑) : ℝ → AddCircle π) =
      (kolmogorovMeasure p₀).map ((↑) : ℝ → AddCircle π) := by
  have := isProbabilityMeasure_kolmogorovMeasure hp₀
  have h := K.map_addCircle_compProd_eq ht hα hβ hαper hβper hp₀
  have e2 : ((kolmogorovMeasure p₀) ⊗ₘ (K.transitionKernel ht)).map
      (fun z : ℝ × ℝ => ((Prod.snd z : ℝ) : AddCircle π)) =
      ((K.transitionKernel ht) ∘ₘ kolmogorovMeasure p₀).map ((↑) : ℝ → AddCircle π) := by
    rw [show (fun z : ℝ × ℝ => ((Prod.snd z : ℝ) : AddCircle π)) =
        ((↑) : ℝ → AddCircle π) ∘ Prod.snd from rfl,
      ← Measure.map_map measurable_coe_addCircle measurable_snd]
    congr 1
    exact Measure.snd_compProd _ _
  have e1 : ((kolmogorovMeasure p₀) ⊗ₘ (K.transitionKernel ht)).map
      (fun z : ℝ × ℝ => ((Prod.fst z : ℝ) : AddCircle π)) =
      (kolmogorovMeasure p₀).map ((↑) : ℝ → AddCircle π) := by
    rw [show (fun z : ℝ × ℝ => ((Prod.fst z : ℝ) : AddCircle π)) =
        ((↑) : ℝ → AddCircle π) ∘ Prod.fst from rfl,
      ← Measure.map_map measurable_coe_addCircle measurable_fst]
    congr 1
    exact Measure.fst_compProd _ _
  rw [← e2, ← e1, h]

/-- **Lemma A.1 in kernel form, law of `e^{2iu}`.** The pushforward of
`p₀(u) 1_{[0,π]}(u) du` under the transition kernel, then under `u ↦ e^{2iu}`, equals the
pushforward of `p₀(u) 1_{[0,π]}(u) du` under `u ↦ e^{2iu}` (as measures on `ℂ`). -/
theorem map_exp_transition_eq (K : IsDiffusionKernel α β p) {t : ℝ≥0} (ht : 0 < t)
    (hα : ContDiff ℝ 1 α) (hβ : ContDiff ℝ 2 β) (hαper : Periodic α π)
    (hβper : Periodic (fun u => β u ^ 2) π) (hp₀ : IsKolmogorovDensity α β p₀) :
    ((K.transitionKernel ht) ∘ₘ kolmogorovMeasure p₀).map
        (fun u : ℝ => Complex.exp (2 * Complex.I * u)) =
      (kolmogorovMeasure p₀).map (fun u : ℝ => Complex.exp (2 * Complex.I * u)) := by
  have := isProbabilityMeasure_kolmogorovMeasure hp₀
  have hm : Measurable fun u : ℝ => Complex.exp (2 * Complex.I * u) := by fun_prop
  have h := map_exp_eq_of_forall_integral_eq
    (P := (kolmogorovMeasure p₀) ⊗ₘ (K.transitionKernel ht)) (Y := Prod.snd)
    (Z := Prod.fst) measurable_snd measurable_fst fun f hf hfper => by
    obtain ⟨C, hC⟩ := hfper.exists_bound pi_ne_zero hf.continuous
    rw [K.integral_snd_compProd ht hp₀ hf.continuous.measurable hC,
      K.integral_fst_compProd ht hp₀ hf.continuous.measurable]
    exact K.integral_transition_mul_eq hα hβ hαper hβper hp₀ hf hfper ht
  have e2 : ((kolmogorovMeasure p₀) ⊗ₘ (K.transitionKernel ht)).map
      (fun z : ℝ × ℝ => Complex.exp (2 * Complex.I * (Prod.snd z : ℝ))) =
      ((K.transitionKernel ht) ∘ₘ kolmogorovMeasure p₀).map
        (fun u : ℝ => Complex.exp (2 * Complex.I * u)) := by
    rw [show (fun z : ℝ × ℝ => Complex.exp (2 * Complex.I * (Prod.snd z : ℝ))) =
        (fun u : ℝ => Complex.exp (2 * Complex.I * u)) ∘ Prod.snd from rfl,
      ← Measure.map_map hm measurable_snd]
    congr 1
    exact Measure.snd_compProd _ _
  have e1 : ((kolmogorovMeasure p₀) ⊗ₘ (K.transitionKernel ht)).map
      (fun z : ℝ × ℝ => Complex.exp (2 * Complex.I * (Prod.fst z : ℝ))) =
      (kolmogorovMeasure p₀).map (fun u : ℝ => Complex.exp (2 * Complex.I * u)) := by
    rw [show (fun z : ℝ × ℝ => Complex.exp (2 * Complex.I * (Prod.fst z : ℝ))) =
        (fun u : ℝ => Complex.exp (2 * Complex.I * u)) ∘ Prod.fst from rfl,
      ← Measure.map_map hm measurable_fst]
    congr 1
    exact Measure.fst_compProd _ _
  rw [← e2, ← e1, h]

/-- The invariance for all `t ≥ 0` (`T_0 = id`), bounded measurable `π`-periodic `f`, in terms of
`kernelOp`. -/
theorem integral_kernelOp_mul_eq_of_periodic (K : IsDiffusionKernel α β p) (t : ℝ≥0)
    (hα : ContDiff ℝ 1 α) (hβ : ContDiff ℝ 2 β) (hαper : Periodic α π)
    (hβper : Periodic (fun u => β u ^ 2) π) (hp₀ : IsKolmogorovDensity α β p₀) {f : ℝ → ℝ}
    (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ v, |f v| ≤ C) (hfper : Periodic f π) :
    ∫ u in (0)..π, kernelOp p t f u * p₀ u = ∫ u in (0)..π, f u * p₀ u := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  have ht' := pos_iff_ne_zero.mpr ht
  rw [kernelOp_of_pos ht']
  exact K.integral_transition_mul_eq_of_periodic ht' hα hβ hαper hβper hp₀ hf hfb hfper

end IsDiffusionKernel

end ComplexSLE.Internal

end
