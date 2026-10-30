/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.LeftHull
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Transformation of Loewner solutions

Solutions of the Loewner initial value problem transform under scaling `γ ↦ r γ(·/r²)`,
complex conjugation and negation. Consequently so do the absorbing times and the left hulls.
-/

public section

open scoped NNReal ENNReal ComplexConjugate
open Set

namespace ComplexSLE.Internal

/-- Scaling maps solutions to solutions. -/
theorem isLoewnerSolution_scale {U : ℝ≥0 → ℂ} {z : ℂ} {τ : ℝ≥0∞} {γ : ℝ → ℂ} (r : ℝ≥0)
    (hr : 0 < r) (h : IsLoewnerSolution U z τ γ) :
    IsLoewnerSolution (fun s => (r : ℂ) * U (s / r ^ 2)) ((r : ℂ) * z)
      (((r ^ 2 : ℝ≥0) : ℝ≥0∞) * τ) (fun t => (r : ℂ) * γ (t / (r : ℝ) ^ 2)) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hr2 : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  refine ⟨by simp [h.1], fun t ht htτ => ?_⟩
  have key : ENNReal.ofReal (t / (r : ℝ) ^ 2) < τ := by
    rw [ENNReal.ofReal_div_of_pos hr2]
    have h1 : ENNReal.ofReal ((r : ℝ) ^ 2) = ((r ^ 2 : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal]; simp
    rw [h1, ENNReal.div_lt_iff (Or.inl (by simpa using hr.ne'))
      (Or.inl ENNReal.coe_ne_top), mul_comm]
    exact htτ
  have hts : (t / (r : ℝ) ^ 2).toNNReal = t.toNNReal / r ^ 2 := by
    rw [Real.toNNReal_div ht, ← NNReal.coe_pow, Real.toNNReal_coe]
  obtain ⟨hne, hd⟩ := h.2 (t / (r : ℝ) ^ 2) (by positivity) key
  rw [hts] at hne hd
  refine ⟨?_, ?_⟩
  · simpa [hrc] using hne
  · have hh : HasDerivWithinAt (fun t : ℝ => t / (r : ℝ) ^ 2) (1 / (r : ℝ) ^ 2) (Ici 0) t :=
      (hasDerivWithinAt_id t _).div_const _
    have hmaps : MapsTo (fun t : ℝ => t / (r : ℝ) ^ 2) (Ici 0) (Ici 0) := fun x hx =>
      div_nonneg hx hr2.le
    have h2 := (hd.scomp t hh hmaps).const_mul (r : ℂ)
    refine h2.congr_deriv ?_
    have hne' : γ (t / (r : ℝ) ^ 2) - U (t.toNNReal / r ^ 2) ≠ 0 := sub_ne_zero.2 hne
    simp only [Complex.real_smul]
    push_cast
    have : ((r : ℂ)) ≠ 0 := hrc
    field_simp

/-- Absorbing times scale. -/
theorem absorbingTime_scale (U : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ≥0) (hr : 0 < r) :
    absorbingTime (fun s => (r : ℂ) * U (s / r ^ 2)) ((r : ℂ) * z) =
      ((r ^ 2 : ℝ≥0) : ℝ≥0∞) * absorbingTime U z := by
  have hr0 : (r⁻¹ : ℝ≥0) ≠ 0 := by simpa using hr.ne'
  apply le_antisymm
  · unfold absorbingTime
    refine sSup_le fun τ' ⟨γ, hγ⟩ => ?_
    have h2 := isLoewnerSolution_scale r⁻¹ (pos_iff_ne_zero.2 hr0) hγ
    have hU : (fun s : ℝ≥0 => ((r⁻¹ : ℝ≥0) : ℂ) *
        ((r : ℂ) * U (s / (r⁻¹) ^ 2 / r ^ 2))) = U := by
      funext s
      have : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      have h3 : s / (r⁻¹) ^ 2 / r ^ 2 = s := by
        field_simp
      rw [h3]; push_cast; field_simp
    have hz : ((r⁻¹ : ℝ≥0) : ℂ) * ((r : ℂ) * z) = z := by
      have : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      push_cast; field_simp
    rw [hU, hz] at h2
    have h4 := le_sSup (s := {τ | ∃ γ, IsLoewnerSolution U z τ γ}) ⟨_, h2⟩
    have h5 : τ' = ((r ^ 2 : ℝ≥0) : ℝ≥0∞) * (((r⁻¹ ^ 2 : ℝ≥0) : ℝ≥0∞) * τ') := by
      rw [← mul_assoc, ← ENNReal.coe_mul]
      have : r ^ 2 * (r⁻¹) ^ 2 = 1 := by field_simp
      rw [this]; simp
    rw [h5]
    exact mul_le_mul_right h4 _
  · rw [absorbingTime, ENNReal.mul_sSup]
    refine iSup₂_le fun τ ⟨γ, hγ⟩ => le_sSup ⟨_, isLoewnerSolution_scale r hr hγ⟩

/-- Complex conjugation maps solutions to solutions. -/
theorem isLoewnerSolution_conj {U : ℝ≥0 → ℂ} {z : ℂ} {τ : ℝ≥0∞} {γ : ℝ → ℂ}
    (h : IsLoewnerSolution U z τ γ) :
    IsLoewnerSolution (fun s => conj (U s)) (conj z) τ (fun t => conj (γ t)) := by
  refine ⟨by simp [h.1], fun t ht htτ => ?_⟩
  obtain ⟨hne, hd⟩ := h.2 t ht htτ
  refine ⟨fun h' => hne ((starRingEnd ℂ).injective h'), ?_⟩
  refine (HasDerivWithinAt.star hd).congr_deriv ?_
  simp

/-- Negation maps solutions to solutions. -/
theorem isLoewnerSolution_neg {U : ℝ≥0 → ℂ} {z : ℂ} {τ : ℝ≥0∞} {γ : ℝ → ℂ}
    (h : IsLoewnerSolution U z τ γ) :
    IsLoewnerSolution (fun s => -U s) (-z) τ (fun t => -γ t) := by
  refine ⟨by simp [h.1], fun t ht htτ => ?_⟩
  obtain ⟨hne, hd⟩ := h.2 t ht htτ
  refine ⟨fun h' => hne (by simpa using h'), ?_⟩
  refine (HasDerivWithinAt.neg hd).congr_deriv ?_
  have : -γ t - -U t.toNNReal = -(γ t - U t.toNNReal) := by ring
  show _ = 2 / (-γ t - -U t.toNNReal)
  rw [this, div_neg]

theorem absorbingTime_conj (U : ℝ≥0 → ℂ) (z : ℂ) :
    absorbingTime (fun s => conj (U s)) (conj z) = absorbingTime U z := by
  have key : ∀ (V : ℝ≥0 → ℂ) (w : ℂ),
      absorbingTime V w ≤ absorbingTime (fun s => conj (V s)) (conj w) := fun V w =>
    sSup_le fun τ ⟨γ, hγ⟩ => le_sSup ⟨_, isLoewnerSolution_conj hγ⟩
  apply le_antisymm
  · simpa using key (fun s => conj (U s)) (conj z)
  · exact key U z

theorem absorbingTime_neg (U : ℝ≥0 → ℂ) (z : ℂ) :
    absorbingTime (fun s => -U s) (-z) = absorbingTime U z := by
  have key : ∀ (V : ℝ≥0 → ℂ) (w : ℂ),
      absorbingTime V w ≤ absorbingTime (fun s => -V s) (-w) := fun V w =>
    sSup_le fun τ ⟨γ, hγ⟩ => le_sSup ⟨_, isLoewnerSolution_neg hγ⟩
  apply le_antisymm
  · simpa using key (fun s => -U s) (-z)
  · exact key U z

theorem leftHull_conj (U : ℝ≥0 → ℂ) (t : ℝ≥0) :
    leftHull (fun s => conj (U s)) t = conj '' leftHull U t := by
  ext w
  simp only [leftHull, mem_ofPred_eq, mem_image]
  constructor
  · intro h
    exact ⟨conj w, by simpa [← absorbingTime_conj U (conj w)] using h, by simp⟩
  · rintro ⟨v, hv, rfl⟩
    simpa [absorbingTime_conj U v] using hv

theorem leftHull_neg (U : ℝ≥0 → ℂ) (t : ℝ≥0) :
    leftHull (fun s => -U s) t = Neg.neg '' leftHull U t := by
  ext w
  simp only [leftHull, mem_ofPred_eq, mem_image]
  constructor
  · intro h
    exact ⟨-w, by simpa [← absorbingTime_neg U (-w)] using h, by simp⟩
  · rintro ⟨v, hv, rfl⟩
    simpa [absorbingTime_neg U v] using hv

theorem leftHull_scale (U : ℝ≥0 → ℂ) (r : ℝ≥0) (hr : 0 < r) (t : ℝ≥0) :
    leftHull (fun s => (r : ℂ) * U (s / r ^ 2)) t =
      (fun z => (r : ℂ) * z) '' leftHull U (t / r ^ 2) := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hc0 : ((r ^ 2 : ℝ≥0) : ℝ≥0∞) ≠ 0 := by simpa using hr.ne'
  ext w
  simp only [leftHull, mem_ofPred_eq, mem_image]
  constructor
  · intro h
    refine ⟨w / r, ?_, by field_simp⟩
    have h1 := absorbingTime_scale U (w / r) r hr
    rw [mul_div_cancel₀ _ hrc] at h1
    rw [h1] at h
    rw [ENNReal.coe_div (by simpa using hr.ne'), ENNReal.le_div_iff_mul_le (Or.inl hc0)
      (Or.inl ENNReal.coe_ne_top), mul_comm]
    exact h
  · rintro ⟨v, hv, rfl⟩
    rw [absorbingTime_scale U v r hr]
    rw [ENNReal.coe_div (by simpa using hr.ne'), ENNReal.le_div_iff_mul_le (Or.inl hc0)
      (Or.inl ENNReal.coe_ne_top), mul_comm] at hv
    exact hv

end ComplexSLE.Internal

end
