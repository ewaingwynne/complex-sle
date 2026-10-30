/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.RightHull
public import ComplexSLE.Internal.Loewner.MapTransform

/-!
# Provider for `ComplexSLE.reflection_rightHull`

Implementation module for the frozen anchor `ComplexSLE/Frozen/Reflection_RightHull.lean`.
The anchor is SEALED: it is proved by this module.
-/

public section

open scoped NNReal ComplexConjugate
open Set

namespace ComplexSLE.Internal

/-- Reflection property (2.2) for right hulls. -/
theorem reflection_rightHull (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) :
    rightHull (fun s => conj (U s)) (by fun_prop) t = conj '' rightHull U hU t ∧
      rightHull (fun s => -U s) (by fun_prop) t = Neg.neg '' rightHull U hU t := by
  have hc := centeredLoewnerMap_conj U hU t
  have hn := centeredLoewnerMap_neg U hU t
  constructor
  · have hbij : Function.Bijective (conj : ℂ → ℂ) := Function.Involutive.bijective Complex.conj_conj
    have hrange : Set.range (centeredLoewnerMap (fun s => conj (U s)) (by fun_prop) t) =
        conj '' Set.range (centeredLoewnerMap U hU t) := by
      ext w
      constructor
      · rintro ⟨⟨z, hz⟩, rfl⟩
        have hz' : conj z ∈ (leftHull U t)ᶜ := fun h => by
          apply hz
          rw [leftHull_conj]
          exact ⟨conj z, h, Complex.conj_conj z⟩
        exact ⟨_, ⟨⟨conj z, hz'⟩, rfl⟩, (hc z hz hz').symm⟩
      · rintro ⟨_, ⟨⟨y, hy⟩, rfl⟩, rfl⟩
        have hz : conj y ∈ (leftHull (fun s => conj (U s)) t)ᶜ := fun h => by
          rw [leftHull_conj] at h
          obtain ⟨y', hy', he⟩ := h
          exact hy (by rwa [← hbij.1 he])
        have hz' : conj (conj y) ∈ (leftHull U t)ᶜ := by rwa [Complex.conj_conj]
        refine ⟨⟨_, hz⟩, ?_⟩
        rw [hc _ hz hz']
        congr 2
        exact Subtype.ext (Complex.conj_conj y)
    unfold rightHull
    rw [hrange, ← Set.image_compl_eq hbij]
  · have hbij : Function.Bijective (Neg.neg : ℂ → ℂ) := Function.Involutive.bijective neg_neg
    have hrange : Set.range (centeredLoewnerMap (fun s => -U s) (by fun_prop) t) =
        Neg.neg '' Set.range (centeredLoewnerMap U hU t) := by
      ext w
      constructor
      · rintro ⟨⟨z, hz⟩, rfl⟩
        have hz' : -z ∈ (leftHull U t)ᶜ := fun h => by
          apply hz
          rw [leftHull_neg]
          exact ⟨-z, h, neg_neg z⟩
        exact ⟨_, ⟨⟨-z, hz'⟩, rfl⟩, (hn z hz hz').symm⟩
      · rintro ⟨_, ⟨⟨y, hy⟩, rfl⟩, rfl⟩
        have hz : -y ∈ (leftHull (fun s => -U s) t)ᶜ := fun h => by
          rw [leftHull_neg] at h
          obtain ⟨y', hy', he⟩ := h
          exact hy (by rwa [← hbij.1 he])
        have hz' : -(-y) ∈ (leftHull U t)ᶜ := by rwa [neg_neg]
        refine ⟨⟨_, hz⟩, ?_⟩
        rw [hn _ hz hz']
        congr 2
        exact Subtype.ext (neg_neg y)
    unfold rightHull
    rw [hrange, ← Set.image_compl_eq hbij]

end ComplexSLE.Internal

end
