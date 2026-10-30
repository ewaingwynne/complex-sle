/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Analysis.ODE.PicardLindelof

/-!
# Picard–Lindelöf with the solution confined to the ball

Mathlib's `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt` produces an integral
curve but forgets that the curve stays in the closed ball `closedBall x₀ a` on which the vector
field is controlled. We record that extra information (it is immediate from the construction).
-/

public section

open Set
open scoped NNReal

namespace ComplexSLE.Infrastructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : ℝ≥0}

/-- **Picard–Lindelöf**, differential form, with the solution confined to `closedBall x₀ a`. -/
theorem IsPicardLindelof.exists_eq_forall_mem_Icc_mem_closedBall_hasDerivWithinAt
    (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ Metric.closedBall x₀ r) :
    ∃ α : ℝ → E, α t₀ = x ∧ ∀ t ∈ Icc tmin tmax, α t ∈ Metric.closedBall x₀ a ∧
      HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t := by
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, by rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀],
    fun t ht ↦ ⟨α.compProj_mem_closedBall hf.mul_max_le, ?_⟩⟩
  apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
    α.continuous_compProj.continuousOn (fun _ ht' ↦ α.compProj_mem_closedBall hf.mul_max_le)
    x ht |>.congr_of_mem _ ht
  intro t' ht'
  nth_rw 1 [← hα]
  rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]

end ComplexSLE.Infrastructure

end
