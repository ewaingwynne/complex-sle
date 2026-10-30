/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.LeftHull
import ComplexSLE.Internal.Hull.Connected

/-!
# Provider for `ComplexSLE.lemma_2_4_leftHull`

Implementation module for the frozen anchor `ComplexSLE/Frozen/Lemma_2_4_LeftHull.lean`.

`L_t` is nonempty (`U 0 ∈ L_t`) and closed (EXTERNAL `loewnerMap_conformal`). If it were not
preconnected it would split as `L_t = A ⊔ B` with `A`, `B` disjoint, closed and nonempty; the
part not containing `U 0` is shown to be empty in
`ComplexSLE.Internal.leftHull_separation_eq_empty` (a maximum-principle argument replacing the
paper's loop/homotopy sketch, paper.tex:L658-666).
-/

public section

open scoped NNReal
open Set

namespace ComplexSLE.Internal

/-- See `ComplexSLE.lemma_2_4_leftHull`. -/
theorem lemma_2_4_leftHull (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) :
    IsConnected (leftHull U t) := by
  refine ⟨leftHull_nonempty U t, ?_⟩
  have hclosed : IsClosed (leftHull U t) :=
    isOpen_compl_iff.1 (External.loewnerMap_conformal U hU t).1
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hclosed]
  intro u v hu hv hsub hdisj
  have hU0 := driver_zero_mem_leftHull U t
  -- the part containing `U 0` contains all of `L_t`
  have key : ∀ {A B : Set ℂ}, IsClosed A → IsClosed B → Disjoint A B →
      leftHull U t ⊆ A ∪ B → U 0 ∈ A → leftHull U t ⊆ A := by
    intro A B hA hB hAB hsubAB hU0A
    have hunion : (A ∩ leftHull U t) ∪ (B ∩ leftHull U t) = leftHull U t := by
      rw [← union_inter_distrib_right]
      exact inter_eq_right.2 hsubAB
    have hempty := leftHull_separation_eq_empty hU t (hA.inter hclosed) (hB.inter hclosed)
      (hAB.mono inter_subset_left inter_subset_left) hunion ⟨hU0A, hU0⟩
    intro z hz
    rcases hsubAB hz with h | h
    · exact h
    · have hmem : z ∈ B ∩ leftHull U t := ⟨h, hz⟩
      rw [hempty] at hmem
      exact absurd hmem (notMem_empty z)
  rcases hsub hU0 with h | h
  · exact Or.inl (key hu hv hdisj hsub h)
  · exact Or.inr (key hv hu hdisj.symm (hsub.trans (union_comm u v).subset) h)

end ComplexSLE.Internal

end
