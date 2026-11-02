/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.PathStatRestart
public import ComplexSLE.Internal.Phases.AllZLebesgue
public import ComplexSLE.Internal.Stationary.ThetaHatSolution

/-!
# The driver law and the restart kernel `H_F` (M7/A4c)

* `driverLaw hU`: the law `Λ` of the driver on `CPath`;
* `obsKernel Λ F β = H_F(β) = ∫ F(obsC (w, β)) dΛ(w)`, the expectation of the observable of the
  chain started at `e^{iβ}`;
* `obsKernel_add_pi`, `obsKernel_periodic`: `H_F` is `π`-periodic (reflection
  `obsC (-w, β) = obsC (w, β + π)` and `-U =_d U`);
* `periodic_eq_comp_exp`: a `π`-periodic function of `β` is a function of `e^{2iβ}`.

Split out of `PathStat.lean` (M10) so that it imports no one-time stationarity result.
-/

@[expose] public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter Complex

namespace ComplexSLE.Internal

open Polar

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-- The law of the driver `U` on `CPath`. -/
noncomputable def driverLaw (hU : IsSLEDriverAdapted a b c U P ℱ) : Measure CPath :=
  P.map (CPath.ofDriver U hU.cont)

theorem isProbabilityMeasure_driverLaw
    (hU : IsSLEDriverAdapted a b c U P ℱ) : IsProbabilityMeasure (driverLaw hU) :=
  (Measure.isProbabilityMeasure_map_iff
    (CPath.measurable_ofDriver hU.cont fun _ => hU.adapted.measurable).aemeasurable).mpr
      (hU.toIsSLEDriver.isProbabilityMeasure)

/-- `H_F(β) = ∫ F(obsC (w, β)) dΛ(w)`: the expectation of the observable of the chain started at
`e^{iβ}`, for the driver law `Λ`. -/
noncomputable def obsKernel (Λ : Measure CPath)
    (F : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞) (β : ℝ) : ℝ≥0∞ :=
  ∫⁻ w, F (obsC (w, β)) ∂Λ

theorem measurable_obsKernel (hU : IsSLEDriverAdapted a b c U P ℱ) (Λ : Measure CPath)
    [SFinite Λ] {F : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    Measurable (obsKernel Λ F) :=
  Measurable.lintegral_prod_left' (f := fun p : CPath × ℝ => F (obsC p))
    (hF.comp (measurable_obsC hU))

/-- **`π`-periodicity of `H_F`** (reflection `obsC (-w, β) = obsC (w, β + π)` and `-U =_d U`). -/
theorem obsKernel_add_pi [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ)
    (ha : 0 < a) (hc : c ^ 2 ≤ a * b) {F : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hF : Measurable F) (β : ℝ) :
    obsKernel (driverLaw hU) F (β + π) = obsKernel (driverLaw hU) F β := by
  have hUm : ∀ t, Measurable (U t) := fun t => hU.adapted.measurable
  have hι := CPath.measurable_ofDriver hU.cont hUm
  obtain ⟨ℱc, hUc⟩ := exists_isSLEDriverAdapted_eval hU.toIsSLEDriver hU.cont hUm
  have : IsProbabilityMeasure (driverLaw hU) := isProbabilityMeasure_driverLaw hU
  have hgood := ae_sigmaDom_eq_Ici hUc (unitPt (β + π)) ha hc (unitPt_ne_zero _)
  have hFβ : Measurable fun w : CPath => F (obsC (w, β)) :=
    hF.comp ((measurable_obsC hU).comp (measurable_id.prodMk measurable_const))
  unfold obsKernel
  calc ∫⁻ w, F (obsC (w, β + π)) ∂(driverLaw hU)
      = ∫⁻ w, F (obsC (CPath.neg w, β)) ∂(driverLaw hU) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hgood] with w hw
        rw [obsC_neg w β hw]
    _ = ∫⁻ w, F (obsC (w, β)) ∂((driverLaw hU).map CPath.neg) :=
        (lintegral_map hFβ CPath.measurable_neg).symm
    _ = ∫⁻ w, F (obsC (w, β)) ∂(driverLaw hU) := by
        rw [driverLaw, map_neg_eq hU.toIsSLEDriver hU.cont hUm]

theorem obsKernel_periodic [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ)
    (ha : 0 < a) (hc : c ^ 2 ≤ a * b) {F : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hF : Measurable F) : Function.Periodic (obsKernel (driverLaw hU) F) π :=
  fun β => obsKernel_add_pi hU ha hc hF β

/-- A `π`-periodic function of `β` is a function of `e^{2iβ}`. -/
theorem periodic_eq_comp_exp {G : ℝ → ℝ≥0∞} (hG : Function.Periodic G π) (β : ℝ) :
    G β = G (Complex.arg (Complex.exp (2 * Complex.I * (β : ℂ))) / 2) := by
  have h : 2 * Complex.I * (β : ℂ) = ((2 * β : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.arg_exp_mul_I, ← self_sub_toIocDiv_zsmul]
  have h2 : (2 * β - toIocDiv Real.two_pi_pos (-π) (2 * β) • (2 * π)) / 2 =
      β - (toIocDiv Real.two_pi_pos (-π) (2 * β) : ℝ) * π := by
    rw [zsmul_eq_mul]; ring
  rw [h2, hG.sub_int_mul_eq]

end ComplexSLE.Internal

end
