/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Loewner.Duality

/-!
# Injectivity of the centered Loewner maps

`f_t = g_t - U_t` is injective on `ℂ ∖ L_t` (backward uniqueness of the Loewner flow). Proof: two
points `z₁, z₂ ∉ L_t` with `f_t z₁ = f_t z₂` have time reversals `k_j(r) = i (γ_j(t - r) - U_t)`
that solve the Loewner equation for the reversed driver on `[0, t]` (`closedSol_reverse`) from the
same point, hence agree at `t` (`closedSol_eq_endpoint`); at `r = t` this reads `i (z_j - U_t)`.
-/

public section

open scoped NNReal ENNReal
open Set

namespace ComplexSLE.Internal

variable {U : ℝ≥0 → ℂ}

/-- The time reversal of the solution from `z ∉ L_t`, as a solution for the reversed driver. -/
theorem exists_reversed_closedSol (hU : Continuous U) (t : ℝ≥0) (z : ↥(leftHull U t)ᶜ) :
    ∃ k : ℝ → ℂ, ClosedSol (fun s => revDriver U t s.toNNReal) t k ∧
      k 0 = Complex.I * centeredLoewnerMap U hU t z ∧ k t = Complex.I * (z.1 - U t) := by
  obtain ⟨γ, hγ, hmap⟩ := loewnerMap_exists_solution U hU z.1
  have ht : (t : ℝ≥0∞) < absorbingTime U z := notMem_leftHull_iff.1 z.2
  have hsol := closedSol_of_isLoewnerSolution hγ ht
  refine ⟨_, closedSol_reverse (W' := fun s => revDriver U t s.toNNReal) (a := Complex.I)
    (c := U t) Complex.I_mul_I hsol (fun s hs => by
      rw [revDriver_toNNReal U t hs, Real.toNNReal_of_nonneg (by linarith [hs.2])]), ?_, ?_⟩
  · have := hmap t z.2
    simp only [sub_zero, centeredLoewnerMap]
    rw [show loewnerMap U hU t z = γ t from this]
  · simp [hγ.1]

/-- **Backward uniqueness**: `f_t` is injective on `ℂ ∖ L_t`. -/
theorem centeredLoewnerMap_injective (hU : Continuous U) (t : ℝ≥0) :
    Function.Injective (centeredLoewnerMap U hU t) := by
  intro z₁ z₂ h
  obtain ⟨k₁, hk₁, h₁0, h₁t⟩ := exists_reversed_closedSol hU t z₁
  obtain ⟨k₂, hk₂, h₂0, h₂t⟩ := exists_reversed_closedSol hU t z₂
  have hend := closedSol_eq_endpoint (continuous_revDriver hU t)
    (z := Complex.I * centeredLoewnerMap U hU t z₁) h₁0 (by rw [h₂0, h]) hk₁ hk₂
  rw [h₁t, h₂t] at hend
  exact Subtype.ext (by simpa using hend)

end ComplexSLE.Internal

end
