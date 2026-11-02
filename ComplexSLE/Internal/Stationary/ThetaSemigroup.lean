/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.PathStatKernel
public import ComplexSLE.Internal.Stationary.PathStatRestart
public import ComplexSLE.Internal.Stationary.ThetaHatSolution

/-!
# The semigroup of `θ̂` (M10-R3): measurability, periodicity, Chapman–Kolmogorov

`thetaSemigroup hU t f u = Q_t f(u) = E f(θ̂_t(e^{iu}))` is the Markov semigroup of the concrete
process `θ̂`, built from the in-project strong Markov restart (`lintegral_pathObsAt`), with no
transition kernel.

* `measurable_thetaSemigroup`, `abs_thetaSemigroup_le`: `Q_t f` is measurable and bounded by `C`
  when `f` is measurable and bounded by `C`;
* `obsKernel_thetaObs`: for `f` measurable, `π`-periodic, `|f| ≤ C`, the restart kernel `H_F` of
  the observable `F(ξ, inc, _) = f(arg ξ / 2 + inc t) + C` is `Q_t f + C`;
* `thetaSemigroup_periodic`: `Q_t f` is `π`-periodic (from `obsKernel_add_pi`);
* `thetaSemigroup_add`: Chapman–Kolmogorov `Q_{s+t} f = Q_s (Q_t f)`.

The strong Markov step is `lintegral_pathObsAt` (`PathStatRestart.lean`).
-/

public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter Function

namespace ComplexSLE.Internal

open Polar

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-- `Q_t f(u) = E f(θ̂_t(e^{iu}))`. -/
@[expose] noncomputable def thetaSemigroup (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) (f : ℝ → ℝ)
    (u : ℝ) : ℝ :=
  ∫ ω, f (thetaHat hU (unitPt u) t ω) ∂P

/-! ### Measurability and the sup-norm bound -/

section Basic

variable [IsProbabilityMeasure P]

/-- `Q_t f` is measurable for measurable `f` (joint measurability of `(ω, u) ↦ θ̂_t(e^{iu})(ω)`). -/
theorem measurable_thetaSemigroup (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) {f : ℝ → ℝ}
    (hf : Measurable f) : Measurable (thetaSemigroup hU t f) := by
  have h : Measurable fun p : Ω × ℝ => f (thetaHat hU (unitPt p.2) t p.1) :=
    hf.comp (measurable_thetaHat_unit hU t)
  exact h.stronglyMeasurable.integral_prod_left'.measurable

/-- `|Q_t f| ≤ C` when `|f| ≤ C`. -/
theorem abs_thetaSemigroup_le (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) {f : ℝ → ℝ} {C : ℝ}
    (hC : ∀ v, |f v| ≤ C) (u : ℝ) : |thetaSemigroup hU t f u| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := P)
    (f := fun ω => f (thetaHat hU (unitPt u) t ω)) (C := C)
    (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hC _)
  simpa [thetaSemigroup, Real.norm_eq_abs, abs_of_nonneg (le_trans (abs_nonneg _) (hC 0))] using
    this

/-- `Q_t f + C` is nonnegative when `|f| ≤ C`. -/
theorem thetaSemigroup_add_const_nonneg (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0)
    {f : ℝ → ℝ} {C : ℝ} (hC : ∀ v, |f v| ≤ C) (u : ℝ) : 0 ≤ thetaSemigroup hU t f u + C := by
  have := abs_thetaSemigroup_le hU t hC u
  linarith [neg_abs_le (thetaSemigroup hU t f u)]

/-- `Q_t f(u) + C` as a lower integral. -/
theorem ofReal_thetaSemigroup_add (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) {f : ℝ → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ v, |f v| ≤ C) (u : ℝ) :
    ENNReal.ofReal (thetaSemigroup hU t f u + C) =
      ∫⁻ ω, ENNReal.ofReal (f (thetaHat hU (unitPt u) t ω) + C) ∂P := by
  have hm : Measurable fun ω => f (thetaHat hU (unitPt u) t ω) :=
    hf.comp (measurable_thetaHat hU (unitPt u) t)
  have hb : ∀ ω, |f (thetaHat hU (unitPt u) t ω)| ≤ C := fun ω => hC _
  have hint : Integrable (fun ω => f (thetaHat hU (unitPt u) t ω)) P :=
    (integrable_const C).mono' hm.aestronglyMeasurable
      (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hb ω)
  have hint2 : Integrable (fun ω => f (thetaHat hU (unitPt u) t ω) + C) P :=
    hint.add (integrable_const C)
  rw [← ofReal_integral_eq_lintegral_ofReal hint2
    (Eventually.of_forall fun ω => by
      have := hb ω
      simp only [Pi.zero_apply]
      linarith [neg_abs_le (f (thetaHat hU (unitPt u) t ω))]),
    integral_add hint (integrable_const C), integral_const]
  simp [thetaSemigroup]

end Basic

/-! ### The observable `F_t` and the restart kernel -/

/-- The observable `F_t(ξ, inc, _) = f(arg ξ / 2 + inc t) + C` (as an element of `ℝ≥0∞`). -/
noncomputable def thetaObs (f : ℝ → ℝ) (C : ℝ) (t : ℝ≥0)
    (p : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (f (Complex.arg p.1 / 2 + p.2.1 t) + C)

theorem measurable_thetaObs {f : ℝ → ℝ} (hf : Measurable f) (C : ℝ) (t : ℝ≥0) :
    Measurable (thetaObs f C t) := by
  unfold thetaObs
  refine ENNReal.measurable_ofReal.comp ((hf.comp ?_).add_const C)
  exact (Complex.measurable_arg.comp measurable_fst).div_const 2 |>.add
    ((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd))

/-- For `π`-periodic `f`: `f (arg (e^{2iθ}) / 2 + x) = f (θ + x)`. -/
theorem periodic_arg_exp_add {f : ℝ → ℝ} (hf : Periodic f π) (θ x : ℝ) :
    f (Complex.arg (Complex.exp (2 * Complex.I * (θ : ℂ))) / 2 + x) = f (θ + x) := by
  have h : 2 * Complex.I * (θ : ℂ) = ((2 * θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.arg_exp_mul_I, ← self_sub_toIocDiv_zsmul]
  have h2 : (2 * θ - toIocDiv Real.two_pi_pos (-π) (2 * θ) • (2 * π)) / 2 + x =
      (θ + x) - (toIocDiv Real.two_pi_pos (-π) (2 * θ) : ℝ) * π := by
    rw [zsmul_eq_mul]; ring
  rw [h2, hf.sub_int_mul_eq]

/-- The observable `F_t` at the path observable `Ξ_s`: `F_t(Ξ_s) = f(θ̂_{s+t}) + C`. -/
theorem thetaObs_pathObsAt (hU : IsSLEDriverAdapted a b c U P ℱ) {f : ℝ → ℝ} (hf : Periodic f π)
    (C : ℝ) (z : ℂ) (s t : ℝ≥0) (ω : Ω) :
    thetaObs f C t (pathObsAt hU z s ω) =
      ENNReal.ofReal (f (thetaHat hU z (s + t) ω) + C) := by
  unfold thetaObs pathObsAt
  simp only
  rw [periodic_arg_exp_add hf]
  congr 3
  ring

/-- The observable `F_t` at `obsC (w, β)`: `f(β + θ̂_t - θ̂_0) + C`. -/
theorem thetaObs_obsC {f : ℝ → ℝ} (hf : Periodic f π) (C : ℝ) (t : ℝ≥0) (w : CPath) (β : ℝ) :
    thetaObs f C t (obsC (w, β)) =
      ENNReal.ofReal (f (β + (thetaC t w (unitPt β) - thetaC 0 w (unitPt β))) + C) := by
  unfold thetaObs obsC polarInc
  simp only
  rw [periodic_arg_exp_add hf]

/-- If `θ̂_0 = [β]_{2π}` then `f (β + (x - θ̂_0)) = f x` for `π`-periodic `f`. -/
theorem periodic_add_sub_toIcoMod {f : ℝ → ℝ} (hf : Periodic f π) (x β : ℝ) :
    f (β + (x - toIcoMod Real.two_pi_pos 0 β)) = f x := by
  rw [← self_sub_toIcoDiv_zsmul, zsmul_eq_mul]
  have : β + (x - (β - (toIcoDiv Real.two_pi_pos 0 β : ℝ) * (2 * π))) =
      x + ((2 * toIcoDiv Real.two_pi_pos 0 β : ℤ) : ℝ) * π := by push_cast; ring
  rw [this]
  exact (hf.int_mul _) x

section Kernel

variable [IsProbabilityMeasure P]

/-- **The restart kernel of `F_t` is `Q_t f + C`**: for `f` measurable, `π`-periodic with
`|f| ≤ C`, `H_{F_t}(β) = ∫ (f(β + θ̂_t - θ̂_0) + C) dΛ = E (f(θ̂_t(e^{iβ})) + C)`. -/
theorem obsKernel_thetaObs (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a)
    (hc : c ^ 2 ≤ a * b) {f : ℝ → ℝ} (hf : Measurable f) (hper : Periodic f π) {C : ℝ}
    (hC : ∀ v, |f v| ≤ C) (t : ℝ≥0) (β : ℝ) :
    obsKernel (driverLaw hU) (thetaObs f C t) β = ENNReal.ofReal (thetaSemigroup hU t f β + C) := by
  rw [ofReal_thetaSemigroup_add hU t hf hC β]
  unfold obsKernel driverLaw
  have hmeas : Measurable fun w : CPath => thetaObs f C t (obsC (w, β)) :=
    (measurable_thetaObs hf C t).comp
      ((measurable_obsC hU).comp (measurable_id.prodMk measurable_const))
  rw [lintegral_map hmeas (CPath.measurable_ofDriver hU.cont fun _ => hU.adapted.measurable)]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_thetaHat_zero hU ha hc β] with ω h0
  rw [thetaObs_obsC hper]
  have e1 : thetaC t (CPath.ofDriver U hU.cont ω) (unitPt β) = thetaHat hU (unitPt β) t ω := rfl
  have e0 : thetaC 0 (CPath.ofDriver U hU.cont ω) (unitPt β) = thetaHat hU (unitPt β) 0 ω := rfl
  rw [e1, e0, h0, periodic_add_sub_toIcoMod hper]

/-- **`π`-periodicity of `Q_t f`** (from the reflection `obsKernel_add_pi`). -/
theorem thetaSemigroup_periodic (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a)
    (hc : c ^ 2 ≤ a * b) (t : ℝ≥0) {f : ℝ → ℝ} (hf : Measurable f) (hper : Periodic f π)
    (hb : ∃ C, ∀ v, |f v| ≤ C) : Periodic (thetaSemigroup hU t f) π := by
  obtain ⟨C, hC⟩ := hb
  intro β
  have h := obsKernel_add_pi hU ha hc (measurable_thetaObs hf C t) β
  rw [obsKernel_thetaObs hU ha hc hf hper hC, obsKernel_thetaObs hU ha hc hf hper hC] at h
  exact add_right_cancel ((ENNReal.ofReal_eq_ofReal_iff (thetaSemigroup_add_const_nonneg hU t hC _)
    (thetaSemigroup_add_const_nonneg hU t hC _)).1 h)

/-- **Chapman–Kolmogorov**: `Q_{s+t} f = Q_s (Q_t f)`, by the strong Markov restart at `σ_z(s)`. -/
theorem thetaSemigroup_add (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a)
    (hc : c ^ 2 ≤ a * b) (s t : ℝ≥0) {f : ℝ → ℝ} (hf : Measurable f) (hper : Periodic f π)
    (hb : ∃ C, ∀ v, |f v| ≤ C) (u : ℝ) :
    thetaSemigroup hU (s + t) f u = thetaSemigroup hU s (thetaSemigroup hU t f) u := by
  obtain ⟨C, hC⟩ := hb
  have hgm := measurable_thetaSemigroup hU t hf
  have hgb : ∀ v, |thetaSemigroup hU t f v| ≤ C := abs_thetaSemigroup_le hU t hC
  have h1 := ofReal_thetaSemigroup_add hU (s + t) hf hC u
  have h2 := ofReal_thetaSemigroup_add hU s hgm hgb u
  have hmain : ∫⁻ ω, ENNReal.ofReal (f (thetaHat hU (unitPt u) (s + t) ω) + C) ∂P =
      ∫⁻ ω, ENNReal.ofReal (thetaSemigroup hU t f (thetaHat hU (unitPt u) s ω) + C) ∂P := by
    have := lintegral_pathObsAt hU ha hc (unitPt_ne_zero u) s (measurable_thetaObs hf C t)
    simp only [thetaObs_pathObsAt hU hper] at this
    rw [this]
    refine lintegral_congr fun ω => ?_
    exact obsKernel_thetaObs hU ha hc hf hper hC t _
  have := h1.trans (hmain.trans h2.symm)
  exact add_right_cancel ((ENNReal.ofReal_eq_ofReal_iff
    (thetaSemigroup_add_const_nonneg hU _ hC _)
    (thetaSemigroup_add_const_nonneg hU _ hgb _)).1 this)

end Kernel

end ComplexSLE.Internal

end
