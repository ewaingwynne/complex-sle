/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Duality.Locality
import all ComplexSLE.Internal.Loewner.Duality

/-!
# Bootstrap tools for the Loewner equation away from the driver

Two general tools used for the deterministic form of Lemmas 4.4–4.6 (paper.tex:L2036-2138):

* `bootstrap_Icc`: a continuous-induction principle. If `g` is continuous on `[0, b]`,
  `1 ≤ g 0`, and `1 ≤ g` on `[0, x]` forces `1 < g x`, then `1 ≤ g` on `[0, b]`;
* `norm_sub_le_of_closedSol`: while `‖γ - W‖ ≥ 1` on `[0, x]`, a solution `γ` of the Loewner
  equation `γ' = 2 / (γ - W)` moves by at most `2 x` (the drift has modulus `≤ 2`).
-/

public section

open scoped NNReal ENNReal
open Set Filter Topology

namespace ComplexSLE.Internal

/-- **Continuous induction on `[0, b]`.** If `g` is continuous on `[0, b]`, `1 ≤ g 0`, and
`1 ≤ g` on `[0, x]` implies `1 < g x` (for `x < b`), then `1 ≤ g` on all of `[0, b]`. -/
theorem bootstrap_Icc {g : ℝ → ℝ} {b : ℝ} (hg : ContinuousOn g (Icc 0 b)) (h0 : 1 ≤ g 0)
    (step : ∀ x ∈ Ico 0 b, (∀ r ∈ Icc 0 x, 1 ≤ g r) → 1 < g x) :
    ∀ r ∈ Icc 0 b, 1 ≤ g r := by
  set s : Set ℝ := {x | ∀ r ∈ Icc 0 x, 1 ≤ g r} with hs
  have hK : IsClosed {y ∈ Icc 0 b | 1 ≤ g y} :=
    hg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hclosed : IsClosed (s ∩ Icc 0 b) := by
    rw [← closure_subset_iff_isClosed]
    intro x hx
    have hxb : x ∈ Icc 0 b := isClosed_Icc.closure_subset_iff.2 inter_subset_right hx
    refine ⟨fun r hr => ?_, hxb⟩
    rcases hr.2.eq_or_lt with rfl | hlt
    · have hsub : s ∩ Icc 0 b ⊆ {y ∈ Icc 0 b | 1 ≤ g y} := fun y hy =>
        ⟨hy.2, hy.1 y ⟨hy.2.1, le_rfl⟩⟩
      exact (hK.closure_subset_iff.2 hsub hx).2
    · obtain ⟨y, hy, hy'⟩ := mem_closure_iff.1 hx (Ioi r) isOpen_Ioi hlt
      exact hy'.1 r ⟨hr.1, (mem_Ioi.1 hy).le⟩
  have hgt : ∀ x ∈ s ∩ Ico 0 b, s ∈ 𝓝[>] x := by
    rintro x ⟨hxs, hx0, hxb⟩
    have hgx : 1 < g x := step x ⟨hx0, hxb⟩ hxs
    have hmem : Icc 0 b ∈ 𝓝[>] x :=
      mem_of_superset (Ioo_mem_nhdsGT hxb) (fun y hy => ⟨hx0.trans hy.1.le, hy.2.le⟩)
    have h1 : ∀ᶠ y in 𝓝[Icc 0 b] x, g y ∈ Ioi 1 :=
      (hg x ⟨hx0, hxb.le⟩).eventually (Ioi_mem_nhds hgx)
    have h2 : ∀ᶠ y in 𝓝[>] x, g y ∈ Ioi 1 := nhdsWithin_le_of_mem hmem h1
    obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 h2
    refine (mem_nhdsGT_iff_exists_Ioo_subset).2 ⟨u, hu, fun y hy r hr => ?_⟩
    rcases le_or_gt r x with hrx | hrx
    · exact hxs r ⟨hr.1, hrx⟩
    · exact le_of_lt (hsub ⟨hrx, lt_of_le_of_lt hr.2 hy.2⟩)
  have hmain := hclosed.Icc_subset_of_forall_mem_nhdsWithin (a := 0) (b := b)
    (fun r hr => by
      have : r = 0 := le_antisymm hr.2 hr.1
      subst this
      exact h0) hgt
  intro r hr
  exact (hmain hr) r ⟨hr.1, le_rfl⟩

/-- While `‖γ - W‖ ≥ 1` on `[0, x]`, a Loewner solution `γ` on `[0, b] ⊇ [0, x]` moves by at most
`2 x`. -/
theorem norm_sub_le_of_closedSol {W : ℝ → ℂ} {b : ℝ} {γ : ℝ → ℂ} (h : ClosedSol W b γ) {x : ℝ}
    (hx0 : 0 ≤ x) (hxb : x ≤ b) (hf : ∀ r ∈ Icc 0 x, 1 ≤ ‖γ r - W r‖) :
    ‖γ x - γ 0‖ ≤ 2 * x := by
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := γ)
    (f' := fun r => 2 / (γ r - W r)) (C := 2) (s := Icc 0 x) (x := 0) (y := x)
    (fun r hr => (h r ⟨hr.1, hr.2.trans hxb⟩).2.mono (Icc_subset_Icc_right hxb))
    (fun r hr => ?_) (convex_Icc 0 x) ⟨le_rfl, hx0⟩ ⟨hx0, le_rfl⟩
  · simpa [Real.norm_of_nonneg hx0] using key
  · have h1 := hf r hr
    have hpos : 0 < ‖γ r - W r‖ := lt_of_lt_of_le one_pos h1
    rw [norm_div, div_le_iff₀ hpos]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    linarith

end ComplexSLE.Internal

end
