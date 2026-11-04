/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Loewner.Injective
import all ComplexSLE.Internal.Loewner.Duality

/-!
# Locality of the hull and the map at time `t` in the driver

For a continuous driver `U` and `t : ℝ≥0`, a point `z` lies outside the left hull `L_t^U` iff there
is a solution of the Loewner equation on the closed interval `[0, t]` started at `z`
(`notMem_leftHull_iff_exists_closedSol`), and then `f_t^U (z) = γ t - U t` for every such
solution (`centeredLoewnerMap_eq_of_closedSol`). Since `ClosedSol` only involves `U` on `[0, t]`,
two continuous drivers that agree on `[0, t]` have the same `L_t` (`leftHull_congr`) and the same
`f_t` (`centeredLoewnerMap_congr`).
-/

public section

open scoped NNReal ENNReal
open Set

namespace ComplexSLE.Internal

variable {U V : ℝ≥0 → ℂ}

/-- `z ∉ L_t^U` iff the Loewner equation has a solution on the closed interval `[0, t]` from `z`. -/
theorem notMem_leftHull_iff_exists_closedSol (hU : Continuous U) (t : ℝ≥0) (z : ℂ) :
    z ∉ leftHull U t ↔ ∃ γ : ℝ → ℂ, γ 0 = z ∧ ClosedSol (fun s => U s.toNNReal) t γ := by
  constructor
  · intro h
    obtain ⟨γ, hγ, -⟩ := loewnerMap_exists_solution U hU z
    exact ⟨γ, hγ.1, closedSol_of_isLoewnerSolution hγ (notMem_leftHull_iff.1 h)⟩
  · rintro ⟨γ, h0, h⟩
    exact notMem_leftHull_iff.2 (lt_absorbingTime_of_closedSol hU h0 h)

/-- `ClosedSol` on `[0, t]` only depends on the driver on `[0, t]`. -/
theorem closedSol_congr {t : ℝ≥0} (h : ∀ s ≤ t, U s = V s) {γ : ℝ → ℂ} :
    ClosedSol (fun s => U s.toNNReal) t γ ↔ ClosedSol (fun s => V s.toNNReal) t γ := by
  have hs : ∀ s ∈ Icc (0 : ℝ) t, U s.toNNReal = V s.toNNReal := fun s hs =>
    h _ (Real.toNNReal_le_iff_le_coe.2 hs.2)
  simp only [ClosedSol]
  refine forall₂_congr fun s hs' => ?_
  rw [hs s hs']

/-- The hull `L_t^U` only depends on the driver on `[0, t]`. -/
theorem leftHull_congr (hU : Continuous U) (hV : Continuous V) {t : ℝ≥0}
    (h : ∀ s ≤ t, U s = V s) : leftHull U t = leftHull V t := by
  ext z
  refine not_iff_not.1 ?_
  rw [notMem_leftHull_iff_exists_closedSol hU, notMem_leftHull_iff_exists_closedSol hV]
  exact exists_congr fun γ => and_congr_right fun _ => closedSol_congr h

/-- `f_t^U (z) = γ t - U t` for every solution `γ` of the Loewner equation on `[0, t]` from `z`. -/
theorem centeredLoewnerMap_eq_of_closedSol (hU : Continuous U) {t : ℝ≥0} {z : ℂ} {γ : ℝ → ℂ}
    (h0 : γ 0 = z) (h : ClosedSol (fun s => U s.toNNReal) t γ) (hz : z ∈ (leftHull U t)ᶜ) :
    centeredLoewnerMap U hU t ⟨z, hz⟩ = γ t - U t := by
  obtain ⟨γ', hγ', hmap⟩ := loewnerMap_exists_solution U hU z
  have hs2 := closedSol_of_isLoewnerSolution hγ' (notMem_leftHull_iff.1 hz)
  have hend := closedSol_eq_endpoint hU hγ'.1 h0 hs2 h
  simp only [centeredLoewnerMap]
  rw [hmap t hz, hend]

/-- The map `f_t^U` only depends on the driver on `[0, t]`. -/
theorem centeredLoewnerMap_congr (hU : Continuous U) (hV : Continuous V) {t : ℝ≥0}
    (h : ∀ s ≤ t, U s = V s) {z : ℂ} (hzU : z ∈ (leftHull U t)ᶜ) (hzV : z ∈ (leftHull V t)ᶜ) :
    centeredLoewnerMap U hU t ⟨z, hzU⟩ = centeredLoewnerMap V hV t ⟨z, hzV⟩ := by
  obtain ⟨γ, h0, hγ⟩ := (notMem_leftHull_iff_exists_closedSol hU t z).1 hzU
  rw [centeredLoewnerMap_eq_of_closedSol hU h0 hγ hzU,
    centeredLoewnerMap_eq_of_closedSol hV h0 ((closedSol_congr h).1 hγ) hzV, h t le_rfl]

end ComplexSLE.Internal

end
