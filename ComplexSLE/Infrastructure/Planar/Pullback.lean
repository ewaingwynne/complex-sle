/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.DisconnectsFromInfinity
public import Mathlib.Analysis.Complex.Basic

/-!
# Pullback of disconnection from infinity

Let `F` be a continuous map on `ℂ ∖ L` which avoids a set `R`, and which tends to infinity at
infinity. If `R ∪ L'` disconnects `F(V)` from infinity, then `L ∪ F⁻¹(L' ∖ R)` disconnects `V`
from infinity. This is the form in which the concatenation property
`L_{s+t} = L_t ∪ f_t⁻¹(L_{t,s+t} ∖ R_t)` is used.
-/

public section

open Set Metric Bornology

namespace ComplexSLE.Planar

/-- **Pullback of disconnection from infinity.** -/
theorem disconnectsFromInfinity_pullback {L R L' : Set ℂ} {F : ↥Lᶜ → ℂ} (hF : Continuous F)
    (hFR : ∀ z, F z ∉ R)
    (hgrowth : ∀ M : ℝ, ∃ M' : ℝ, ∀ z : ↥Lᶜ, M' ≤ ‖(z : ℂ)‖ → M ≤ ‖F z‖) {V : Set ℂ}
    (h : DisconnectsFromInfinity (R ∪ L') (F '' (Subtype.val ⁻¹' V))) :
    DisconnectsFromInfinity (L ∪ {z | ∃ hz : z ∈ Lᶜ, F ⟨z, hz⟩ ∈ L' \ R}) V := by
  intro x hx hxu
  set K₁ : Set ℂ := L ∪ {z | ∃ hz : z ∈ Lᶜ, F ⟨z, hz⟩ ∈ L' \ R} with hK₁
  set C : Set ℂ := connectedComponentIn K₁ᶜ x with hC
  have hCsub : C ⊆ K₁ᶜ := connectedComponentIn_subset _ _
  have hCL : C ⊆ Lᶜ := fun z hz hzL => hCsub hz (Or.inl hzL)
  have hCa : ∀ z (hzC : z ∈ C), F ⟨z, hCL hzC⟩ ∉ L' := by
    intro z hzC hFz
    exact hCsub hzC (Or.inr ⟨hCL hzC, hFz, hFR _⟩)
  classical
  let G : ℂ → ℂ := fun z => if hz : z ∈ Lᶜ then F ⟨z, hz⟩ else 0
  have hG : ∀ z (hz : z ∈ Lᶜ), G z = F ⟨z, hz⟩ := fun z hz => by
    simp only [G]
    exact dite_eq_left_of_eq_true (eq_true hz)
  have hGcont : ContinuousOn G C := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : C.domRestrict G = F ∘ fun z : C => (⟨z.1, hCL z.2⟩ : ↥Lᶜ) := by
      funext z
      exact hG z.1 (hCL z.2)
    rw [this]
    exact hF.comp (Continuous.subtype_mk continuous_subtype_val _)
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have himg : IsPreconnected (G '' C) := isPreconnected_connectedComponentIn.image G hGcont
  have hGav : G '' C ⊆ (R ∪ L')ᶜ := by
    rintro _ ⟨z, hzC, rfl⟩ hmem
    rw [hG z (hCL hzC)] at hmem
    rcases hmem with hR | hL'
    · exact hFR _ hR
    · exact hCa z hzC hL'
  have hGx : G x ∈ (R ∪ L')ᶜ := hGav ⟨x, hxC, rfl⟩
  have hsub : G '' C ⊆ connectedComponentIn (R ∪ L')ᶜ (G x) :=
    himg.subset_connectedComponentIn ⟨x, hxC, rfl⟩ hGav
  have hunb : ¬ IsBounded (connectedComponentIn (R ∪ L')ᶜ (G x)) := by
    intro hb
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 (hb.subset hsub)
    obtain ⟨M', hM'⟩ := hgrowth (M + 1)
    have : ∃ z ∈ C, M' ≤ ‖z‖ := by
      by_contra hcon
      apply hxu
      rw [isBounded_iff_subset_closedBall (0 : ℂ)]
      exact ⟨M', fun z hz => mem_closedBall_zero_iff.2
        (not_lt.1 fun hlt => hcon ⟨z, hz, hlt.le⟩)⟩
    obtain ⟨z, hzC, hz⟩ := this
    have h1 := hM' ⟨z, hCL hzC⟩ hz
    have h2 := hM (G z) ⟨z, hzC, rfl⟩
    rw [hG z (hCL hzC)] at h2
    linarith
  have hdis := h (G x) hGx hunb
  rw [Set.disjoint_left]
  intro z hzV hzC
  have hzL := hCL hzC
  have h1 : G z ∈ F '' (Subtype.val ⁻¹' V) := ⟨⟨z, hzL⟩, hzV, (hG z hzL).symm⟩
  exact Set.disjoint_left.1 hdis h1 (hsub ⟨z, hzC, rfl⟩)

end ComplexSLE.Planar

end
