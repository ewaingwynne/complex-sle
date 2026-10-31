/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Disconnect.Lemma41Hit
public import ComplexSLE.Internal.Disconnect.Growth
public import ComplexSLE.Internal.Duality.Deterministic
public import ComplexSLE.Frozen.Defs.RightHull
public import ComplexSLE.Frozen.Defs.CenteredLoewnerMap
public import ComplexSLE.Frozen.Defs.DisconnectsFromInfinity
import ComplexSLE.Frozen.Concatenation_LeftHull
import ComplexSLE.Frozen.Lemma_2_4_LeftHull
import ComplexSLE.Frozen.Lemma_2_4_RightHull
import ComplexSLE.Internal.Hull.ConnectedNoExt
import ComplexSLE.Internal.Phases.KoebeHit

/-!
# Lemma 4.1: hull-side facts

Deterministic ingredients of the proof of Lemma 4.1 (paper.tex:L2159-2195):

* `extMap`: the centered Loewner map `f_t` extended by `0` to all of `ℂ`, continuous on every set
  inside `ℂ ∖ L_t` (`continuousOn_extMap`);
* `isCompact_leftHull'`, `isCompact_rightHull`: the hulls are compact;
* `disconnectsFromInfinity_or`: pointwise alternatives for two sets give a global alternative;
* `lemma41_hull_side`: if `W` satisfies the estimates of Lemma 4.4 on the box `N(C)` and its
  restarted left hull `L_K(W')` is a thin vertical set reaching high and low, then `L_{K+2}(W)`
  is compact, connected, contains `0`, avoids `B_{3/4}(2 C)` and meets every compact connected set
  `R` of the type of `R_T` (Lemma 4.2) at a point of real part `≥ 2 C + 1/4`.
-/

public section

open scoped NNReal
open Set Metric ComplexSLE

namespace ComplexSLE.Internal

open scoped Classical in
/-- The centered Loewner map `f_t`, extended by `0` to all of `ℂ`. -/
noncomputable def extMap (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) (z : ℂ) : ℂ :=
  if h : z ∈ (leftHull U t)ᶜ then centeredLoewnerMap U hU t ⟨z, h⟩ else 0

theorem extMap_of_mem {U : ℝ≥0 → ℂ} {hU : Continuous U} {t : ℝ≥0} {z : ℂ}
    (h : z ∈ (leftHull U t)ᶜ) : extMap U hU t z = centeredLoewnerMap U hU t ⟨z, h⟩ := by
  simp [extMap, h]

theorem continuousOn_extMap {U : ℝ≥0 → ℂ} (hU : Continuous U) (t : ℝ≥0) {s : Set ℂ}
    (hs : s ⊆ (leftHull U t)ᶜ) : ContinuousOn (extMap U hU t) s := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : s.domRestrict (extMap U hU t) =
      centeredLoewnerMap U hU t ∘ fun z : s => (⟨z.1, hs z.2⟩ : ↥(leftHull U t)ᶜ) := by
    funext z
    exact extMap_of_mem (hs z.2)
  rw [this]
  exact (continuous_centeredLoewnerMap hU t).comp (Continuous.subtype_mk continuous_subtype_val _)

theorem isCompact_leftHull' {U : ℝ≥0 → ℂ} (hU : Continuous U) (t : ℝ≥0) :
    IsCompact (leftHull U t) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_leftHull' hU t) (isBounded_leftHull' hU t)

theorem isCompact_rightHull {U : ℝ≥0 → ℂ} (hU : Continuous U) (t : ℝ≥0) :
    IsCompact (rightHull U hU t) := by
  have e : (fun z : ℂ => -Complex.I * z) '' leftHull (dualDriver U t) t = rightHull U hU t := by
    rw [leftHull_dualDriver hU t, Set.image_image]
    have : (fun x : ℂ => -Complex.I * (Complex.I * x)) = id := by
      funext x
      simp only [id]
      linear_combination (-x) * Complex.I_mul_I
    rw [this, Set.image_id]
  rw [← e]
  exact (isCompact_leftHull' (continuous_dualDriver hU t) t).image (by fun_prop)

theorem disconnectsFromInfinity_iff_forall_singleton {K Y : Set ℂ} :
    DisconnectsFromInfinity K Y ↔ ∀ z ∈ Y, DisconnectsFromInfinity K {z} := by
  constructor
  · intro h z hz x hx hxu
    rw [Set.disjoint_singleton_left]
    exact Set.disjoint_left.1 (h x hx hxu) hz
  · intro h x hx hxu
    rw [Set.disjoint_left]
    intro z hz hzc
    exact Set.disjoint_singleton_left.1 (h z hz x hx hxu) hzc

theorem disconnectsFromInfinity_or {K Y₁ Y₂ : Set ℂ}
    (h : ∀ z₁ ∈ Y₁, ∀ z₂ ∈ Y₂,
      DisconnectsFromInfinity K {z₁} ∨ DisconnectsFromInfinity K {z₂}) :
    DisconnectsFromInfinity K Y₁ ∨ DisconnectsFromInfinity K Y₂ := by
  by_contra hcon
  rw [not_or, disconnectsFromInfinity_iff_forall_singleton,
    disconnectsFromInfinity_iff_forall_singleton] at hcon
  push Not at hcon
  obtain ⟨⟨z₁, hz₁, h₁⟩, ⟨z₂, hz₂, h₂⟩⟩ := hcon
  rcases h z₁ hz₁ z₂ hz₂ with h | h <;> contradiction

/-- **The restarted hull** (paper.tex:L2159-2195): see the module docstring. -/
theorem lemma41_hull_side {W : ℝ≥0 → ℂ} (hW : Continuous W) (hW0 : W 0 = 0) {C M : ℝ}
    (hC : 2 ≤ C) {K : ℝ≥0}
    (h44 : ∀ z : ℂ, 2 * C - 1 ≤ z.re → z.re ≤ 7 * C + 1 → |z.im| ≤ 1 →
      ∃ h : z ∈ (leftHull W 2)ᶜ, z.re - 6 * C ≤ (centeredLoewnerMap W hW 2 ⟨z, h⟩).re ∧
        (centeredLoewnerMap W hW 2 ⟨z, h⟩).re ≤ z.re - 3 * C ∧
        |(centeredLoewnerMap W hW 2 ⟨z, h⟩).im| ≤ M)
    (hB : ∀ w ∈ leftHull (fun r => W (r + 2) - W 2) K, |w.re| < 1 / 2)
    (hb₁ : ∃ b ∈ leftHull (fun r => W (r + 2) - W 2) K, M + 2 < b.im)
    (hb₂ : ∃ b ∈ leftHull (fun r => W (r + 2) - W 2) K, b.im < -(M + 2))
    {R : Set ℂ} (hR : IsCompact R) (hRc : IsPreconnected R) (hR0 : (0 : ℂ) ∈ R)
    {q : ℂ} (hqR : q ∈ R) (hq : 7 * C + 1 ≤ q.re) (hRim : ∀ w ∈ R, |w.im| < 1) :
    IsCompact (leftHull W (K + 2)) ∧ IsPreconnected (leftHull W (K + 2)) ∧
      (0 : ℂ) ∈ leftHull W (K + 2) ∧
      Disjoint (leftHull W (K + 2)) (ball ((2 * C : ℝ) : ℂ) (3 * (1 / 4))) ∧
      ∃ β ∈ R, β ∈ leftHull W (K + 2) ∧ (2 * C : ℝ) + 1 / 4 ≤ β.re := by
  set W' : ℝ≥0 → ℂ := fun r => W (r + 2) - W 2 with hW'def
  have hW' : Continuous W' := (hW.comp (continuous_id.add continuous_const)).sub continuous_const
  have hconc := concatenation_leftHull W hW K 2
  have hbox : hitBox C ⊆ (leftHull W 2)ᶜ := fun z hz => (h44 z hz.1 hz.2.1 hz.2.2).1
  have hFc : ContinuousOn (extMap W hW 2) (hitBox C) := continuousOn_extMap hW 2 hbox
  have hF : ∀ z ∈ hitBox C, z.re - 6 * C ≤ (extMap W hW 2 z).re ∧
      (extMap W hW 2 z).re ≤ z.re - 3 * C ∧ |(extMap W hW 2 z).im| ≤ M := by
    intro z hz
    obtain ⟨h, h1, h2, h3⟩ := h44 z hz.1 hz.2.1 hz.2.2
    rw [extMap_of_mem h]
    exact ⟨h1, h2, h3⟩
  obtain ⟨b₁, hb₁B, hb₁h⟩ := hb₁
  obtain ⟨b₂, hb₂B, hb₂h⟩ := hb₂
  obtain ⟨β, hβR, hβN, hFβ⟩ := exists_hit hC hR hRc hR0 hqR hq hRim hFc hF
    (isClosed_leftHull' hW' K) (lemma_2_4_leftHull W' hW' K).isPreconnected hB hb₁B hb₂B hb₁h hb₂h
  refine ⟨isCompact_leftHull' hW (K + 2), (lemma_2_4_leftHull W hW (K + 2)).isPreconnected,
    ?_, ?_, ?_⟩
  · have := driver_zero_mem_leftHull W (K + 2)
    rwa [hW0] at this
  · refine Set.disjoint_left.2 fun z hzL hzball => ?_
    have hz := mem_ball.1 hzball
    rw [dist_eq_norm] at hz
    have h1 := Complex.abs_re_le_norm (z - ((2 * C : ℝ) : ℂ))
    have h2 := Complex.abs_im_le_norm (z - ((2 * C : ℝ) : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
      sub_zero] at h1 h2
    have h1' := abs_lt.1 (h1.trans_lt hz)
    have h2' := abs_lt.1 (h2.trans_lt hz)
    have hzN : z ∈ hitBox C :=
      ⟨by linarith [h1'.1], by linarith [h1'.2],
        abs_le.2 ⟨by linarith [h2'.1], by linarith [h2'.2]⟩⟩
    rw [hconc] at hzL
    rcases hzL with hzL | ⟨h, hmem⟩
    · exact hbox hzN hzL
    · have hF' := (hF z hzN).2.1
      rw [← extMap_of_mem h] at hmem
      have h3 := (abs_lt.1 (hB _ hmem.1)).1
      linarith [h1'.2]
  · refine ⟨β, hβR, ?_, ?_⟩
    · rw [hconc]
      right
      refine ⟨hbox hβN, ?_⟩
      rw [← extMap_of_mem (hbox hβN)]
      exact ⟨hFβ, fun h => h ⟨⟨β, hbox hβN⟩, (extMap_of_mem (hbox hβN)).symm⟩⟩
    · have h3 := (hF β hβN).2.1
      have h4 := (abs_lt.1 (hB _ hFβ)).1
      linarith

end ComplexSLE.Internal

end
