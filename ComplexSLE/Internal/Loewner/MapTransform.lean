/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.CenteredLoewnerMap
public import ComplexSLE.Frozen.LoewnerMap_Eq
public import ComplexSLE.Frozen.LoewnerMap_ExistsSolution
public import ComplexSLE.Internal.Loewner.Transform

/-!
# Transformation of the Loewner maps

Scaling, conjugation and negation of the driving function act on `g_t` and `f_t` by the expected
formulas. Proved from the characterization theorems `loewnerMap_eq`, `loewnerMap_exists_solution`.
-/

public section

open scoped NNReal ENNReal ComplexConjugate

namespace ComplexSLE.Internal

theorem loewnerMap_scale (U : ℝ≥0 → ℂ) (hU : Continuous U) (r : ℝ≥0) (hr : 0 < r) (t : ℝ≥0)
    (z : ℂ) (hz : z ∈ (leftHull (fun s => (r : ℂ) * U (s / r ^ 2)) t)ᶜ)
    (hz' : z / r ∈ (leftHull U (t / r ^ 2))ᶜ) :
    loewnerMap (fun s => (r : ℂ) * U (s / r ^ 2)) (by fun_prop) t ⟨z, hz⟩ =
      r * loewnerMap U hU (t / r ^ 2) ⟨z / r, hz'⟩ := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  obtain ⟨γ, hγ, hval⟩ := loewnerMap_exists_solution U hU (z / r)
  have hsol := isLoewnerSolution_scale r hr hγ
  rw [mul_div_cancel₀ _ hrc] at hsol
  have hlt : ((t / r ^ 2 : ℝ≥0) : ℝ≥0∞) < absorbingTime U (z / r) := by
    simpa [leftHull] using hz'
  have ht : (t : ℝ≥0∞) < ((r ^ 2 : ℝ≥0) : ℝ≥0∞) * absorbingTime U (z / r) := by
    have h2 : (r ^ 2 : ℝ≥0) ≠ 0 := by simpa using hr.ne'
    have := ENNReal.mul_lt_mul_left (a := ((r ^ 2 : ℝ≥0) : ℝ≥0∞)) (by simpa using h2)
      ENNReal.coe_ne_top hlt
    rw [← ENNReal.coe_mul, div_mul_cancel₀ _ h2, mul_comm] at this
    exact this
  rw [loewnerMap_eq _ _ t ⟨z, hz⟩ _ _ hsol ht, hval (t / r ^ 2) hz']
  congr 2

theorem loewnerMap_conj (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) (z : ℂ)
    (hz : z ∈ (leftHull (fun s => conj (U s)) t)ᶜ) (hz' : conj z ∈ (leftHull U t)ᶜ) :
    loewnerMap (fun s => conj (U s)) (by fun_prop) t ⟨z, hz⟩ =
      conj (loewnerMap U hU t ⟨conj z, hz'⟩) := by
  obtain ⟨γ, hγ, hval⟩ := loewnerMap_exists_solution U hU (conj z)
  have hsol := isLoewnerSolution_conj hγ
  rw [Complex.conj_conj] at hsol
  have ht : (t : ℝ≥0∞) < absorbingTime U (conj z) := by simpa [leftHull] using hz'
  rw [loewnerMap_eq _ _ t ⟨z, hz⟩ _ _ hsol ht, hval t hz']

theorem loewnerMap_neg (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) (z : ℂ)
    (hz : z ∈ (leftHull (fun s => -U s) t)ᶜ) (hz' : -z ∈ (leftHull U t)ᶜ) :
    loewnerMap (fun s => -U s) (by fun_prop) t ⟨z, hz⟩ =
      -loewnerMap U hU t ⟨-z, hz'⟩ := by
  obtain ⟨γ, hγ, hval⟩ := loewnerMap_exists_solution U hU (-z)
  have hsol := isLoewnerSolution_neg hγ
  rw [neg_neg] at hsol
  have ht : (t : ℝ≥0∞) < absorbingTime U (-z) := by simpa [leftHull] using hz'
  rw [loewnerMap_eq _ _ t ⟨z, hz⟩ _ _ hsol ht, hval t hz']

theorem centeredLoewnerMap_scale (U : ℝ≥0 → ℂ) (hU : Continuous U) (r : ℝ≥0) (hr : 0 < r)
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ (leftHull (fun s => (r : ℂ) * U (s / r ^ 2)) t)ᶜ)
    (hz' : z / r ∈ (leftHull U (t / r ^ 2))ᶜ) :
    centeredLoewnerMap (fun s => (r : ℂ) * U (s / r ^ 2)) (by fun_prop) t ⟨z, hz⟩ =
      r * centeredLoewnerMap U hU (t / r ^ 2) ⟨z / r, hz'⟩ := by
  simp only [centeredLoewnerMap]
  rw [loewnerMap_scale U hU r hr t z hz hz']
  ring

theorem centeredLoewnerMap_conj (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) (z : ℂ)
    (hz : z ∈ (leftHull (fun s => conj (U s)) t)ᶜ) (hz' : conj z ∈ (leftHull U t)ᶜ) :
    centeredLoewnerMap (fun s => conj (U s)) (by fun_prop) t ⟨z, hz⟩ =
      conj (centeredLoewnerMap U hU t ⟨conj z, hz'⟩) := by
  simp only [centeredLoewnerMap]
  rw [loewnerMap_conj U hU t z hz hz', map_sub]

theorem centeredLoewnerMap_neg (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) (z : ℂ)
    (hz : z ∈ (leftHull (fun s => -U s) t)ᶜ) (hz' : -z ∈ (leftHull U t)ᶜ) :
    centeredLoewnerMap (fun s => -U s) (by fun_prop) t ⟨z, hz⟩ =
      -centeredLoewnerMap U hU t ⟨-z, hz'⟩ := by
  simp only [centeredLoewnerMap]
  rw [loewnerMap_neg U hU t z hz hz']
  ring

end ComplexSLE.Internal

end
