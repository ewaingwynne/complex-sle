/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.Law

/-!
# Uniform approximation of continuous `π`-periodic functions by smooth ones (M10-R4, step 4)

`exists_contDiff_periodic_approx`: every continuous `π`-periodic `f : ℝ → ℝ` is within `ε` (in
sup norm) of a `C²` `π`-periodic function. Proof: `f` descends to `F ∈ C(AddCircle π, ℂ)`; the
span of the monomials `fourier n` is dense (`span_fourier_closure_eq_top`), so some trigonometric
polynomial `q` has `‖F - q‖ < ε`; the real part of `q` restricted to `ℝ` is smooth and periodic.
-/

public section

open scoped Topology
open Set Function Real

namespace ComplexSLE.Internal

/-- Trigonometric polynomials are smooth on `ℝ`: for `q` in the span of the monomials,
`x ↦ q (x : AddCircle π)` is `C²`. -/
theorem contDiff_coe_of_mem_span_fourier {q : C(AddCircle π, ℂ)}
    (hq : q ∈ Submodule.span ℂ (range (@fourier π))) :
    ContDiff ℝ 2 fun x : ℝ => q (x : AddCircle π) := by
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨n, rfl⟩ := hq
    simp only [fourier_coe_apply]
    exact Complex.contDiff_exp.comp
      ((contDiff_const.mul Complex.ofRealCLM.contDiff).div_const _)
  | zero => simp only [ContinuousMap.zero_apply]; exact contDiff_const
  | add q₁ q₂ _ _ h₁ h₂ => simpa only [ContinuousMap.add_apply] using h₁.add h₂
  | smul a q _ h => simpa only [ContinuousMap.smul_apply, smul_eq_mul] using h.const_smul a

/-- **Smooth periodic approximation.** A continuous `π`-periodic real function is uniformly
within `ε` of a `C²` `π`-periodic function. -/
theorem exists_contDiff_periodic_approx {f : ℝ → ℝ} (hf : Continuous f)
    (hper : Periodic f π) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ Periodic g π ∧ ∀ x, |f x - g x| ≤ ε := by
  have hfc : Periodic (fun x => (f x : ℂ)) π := fun x => by simp only [hper x]
  let F : C(AddCircle π, ℂ) :=
    ⟨hfc.lift, continuous_coinduced_dom.mpr (Complex.continuous_ofReal.comp hf)⟩
  have hdense : Dense (Submodule.span ℂ (range (@fourier π)) : Set C(AddCircle π, ℂ)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr span_fourier_closure_eq_top
  obtain ⟨q, hq, hFq⟩ := hdense.exists_dist_lt F hε
  refine ⟨fun x => (q (x : AddCircle π)).re, ?_, fun x => ?_, fun x => ?_⟩
  · exact Complex.reCLM.contDiff.comp (contDiff_coe_of_mem_span_fourier hq)
  · simp only [AddCircle.coe_add_period]
  · have h1 : F (x : AddCircle π) = (f x : ℂ) := hfc.lift_coe x
    have h2 : ‖(F - q) (x : AddCircle π)‖ ≤ ‖F - q‖ := (F - q).norm_coe_le_norm _
    have h3 : f x - (q (x : AddCircle π)).re = ((F - q) (x : AddCircle π)).re := by
      simp [h1]
    rw [h3]
    calc |((F - q) (x : AddCircle π)).re| ≤ ‖(F - q) (x : AddCircle π)‖ :=
          Complex.abs_re_le_norm _
      _ ≤ ‖F - q‖ := h2
      _ ≤ ε := by rw [← dist_eq_norm]; exact hFq.le

end ComplexSLE.Internal

end
