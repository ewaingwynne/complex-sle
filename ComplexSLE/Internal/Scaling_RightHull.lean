/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.RightHull
public import ComplexSLE.Internal.Loewner.MapTransform

/-!
# Provider for `ComplexSLE.scaling_rightHull`

Implementation module for the frozen anchor `ComplexSLE/Frozen/Scaling_RightHull.lean`.
The anchor is SEALED: it is proved by this module.
-/

public section

open scoped NNReal ComplexConjugate
open Set

namespace ComplexSLE.Internal

/-- Scaling property (2.1) for right hulls. -/
theorem scaling_rightHull (U : ℝ≥0 → ℂ) (hU : Continuous U) (r : ℝ≥0) (hr : 0 < r) (t : ℝ≥0) :
    rightHull (fun s => (r : ℂ) * U (s / r ^ 2)) (by fun_prop) t =
      (fun z => (r : ℂ) * z) '' rightHull U hU (t / r ^ 2) := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hbij : Function.Bijective (fun z : ℂ => (r : ℂ) * z) :=
    ⟨mul_right_injective₀ hrc, fun w => ⟨w / r, by field_simp⟩⟩
  have hL := leftHull_scale U r hr t
  have hrange : Set.range (centeredLoewnerMap (fun s => (r : ℂ) * U (s / r ^ 2)) (by fun_prop) t) =
      (fun z => (r : ℂ) * z) '' Set.range (centeredLoewnerMap U hU (t / r ^ 2)) := by
    ext w
    constructor
    · rintro ⟨⟨z, hz⟩, rfl⟩
      have hz' : z / r ∈ (leftHull U (t / r ^ 2))ᶜ := fun h => by
        apply hz
        rw [hL]
        exact ⟨z / r, h, by field_simp⟩
      exact ⟨_, ⟨⟨z / r, hz'⟩, rfl⟩,
        (centeredLoewnerMap_scale U hU r hr t z hz hz').symm⟩
    · rintro ⟨_, ⟨⟨y, hy⟩, rfl⟩, rfl⟩
      have hz : (r : ℂ) * y ∈ (leftHull (fun s => (r : ℂ) * U (s / r ^ 2)) t)ᶜ := fun h => by
        rw [hL] at h
        obtain ⟨y', hy', he⟩ := h
        exact hy (by rwa [← hbij.1 he])
      have hz' : (r : ℂ) * y / r ∈ (leftHull U (t / r ^ 2))ᶜ := by
        rwa [mul_div_cancel_left₀ _ hrc]
      refine ⟨⟨_, hz⟩, ?_⟩
      rw [centeredLoewnerMap_scale U hU r hr t _ hz hz']
      congr 2
      exact Subtype.ext (mul_div_cancel_left₀ _ hrc)
  unfold rightHull
  rw [hrange, ← Set.image_compl_eq hbij]

end ComplexSLE.Internal

end
