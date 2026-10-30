/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.AbsorbingTime
public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Provider for `ComplexSLE.loewner_wellDefined`

Implementation module for the frozen anchor `ComplexSLE/Frozen/LoewnerWellDefined.lean`.
Quarantined while that anchor is `DRAFT_SORRY`: only the anchor itself may import it.

Uniqueness follows from Mathlib's Grönwall-type ODE uniqueness on compact intervals, using that
solutions stay a positive distance away from the driving function there. Existence on
`[0, T_z)` glues solutions on shorter intervals, which agree on overlaps by uniqueness.
-/

public section

open scoped NNReal ENNReal
open Set

namespace ComplexSLE.Internal

/-- Solutions restrict to shorter intervals. -/
theorem isLoewnerSolution_mono {U : ℝ≥0 → ℂ} {z : ℂ} {τ τ' : ℝ≥0∞} {γ : ℝ → ℂ}
    (h : IsLoewnerSolution U z τ γ) (hle : τ' ≤ τ) : IsLoewnerSolution U z τ' γ :=
  ⟨h.1, fun t ht ht' => h.2 t ht (lt_of_lt_of_le ht' hle)⟩

/-- The constant solution on the trivial interval `[0, 0)`. -/
theorem isLoewnerSolution_zero (U : ℝ≥0 → ℂ) (z : ℂ) :
    IsLoewnerSolution U z 0 (fun _ => z) :=
  ⟨rfl, fun t ht ht' => absurd ht' (by simp)⟩

/-- A continuous nonvanishing function on a compact interval is bounded below in norm. -/
theorem exists_pos_le_norm {f : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T) (hf : ContinuousOn f (Icc 0 T))
    (h0 : ∀ t ∈ Icc 0 T, f t ≠ 0) : ∃ δ > 0, ∀ t ∈ Icc 0 T, δ ≤ ‖f t‖ := by
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT) hf.norm
  exact ⟨‖f t₀‖, norm_pos_iff.2 (h0 t₀ ht₀), fun t ht => hmin ht⟩

/-- Uniqueness of solutions of the Loewner equation. -/
theorem loewner_unique {U : ℝ≥0 → ℂ} (hU : Continuous U) {z : ℂ} {τ : ℝ≥0∞}
    {γ₁ γ₂ : ℝ → ℂ} (h₁ : IsLoewnerSolution U z τ γ₁) (h₂ : IsLoewnerSolution U z τ γ₂) :
    EqOn γ₁ γ₂ {t | 0 ≤ t ∧ ENNReal.ofReal t < τ} := by
  rintro T ⟨hT, hTτ⟩
  have hmem : ∀ t ∈ Icc 0 T, ENNReal.ofReal t < τ := fun t ht =>
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ht.2) hTτ
  have hUc : Continuous fun t : ℝ => U t.toNNReal := hU.comp continuous_real_toNNReal
  have cont : ∀ γ : ℝ → ℂ, IsLoewnerSolution U z τ γ → ContinuousOn γ (Icc 0 T) :=
    fun γ h t ht =>
      ((h.2 t ht.1 (hmem t ht)).2.continuousWithinAt).mono (fun s hs => hs.1)
  have bound : ∀ γ : ℝ → ℂ, IsLoewnerSolution U z τ γ →
      ∃ δ > 0, ∀ t ∈ Icc 0 T, δ ≤ ‖γ t - U t.toNNReal‖ := fun γ h =>
    exists_pos_le_norm hT ((cont γ h).sub hUc.continuousOn)
      (fun t ht => sub_ne_zero.2 (h.2 t ht.1 (hmem t ht)).1)
  obtain ⟨δ₁, hδ₁, b₁⟩ := bound γ₁ h₁
  obtain ⟨δ₂, hδ₂, b₂⟩ := bound γ₂ h₂
  set δ := min δ₁ δ₂ with hδ
  have hδpos : 0 < δ := lt_min hδ₁ hδ₂
  let K : ℝ≥0 := ⟨2 / δ ^ 2, by positivity⟩
  have hLip : ∀ t ∈ Ico 0 T,
      LipschitzOnWith K (fun w : ℂ => 2 / (w - U t.toNNReal))
        {w | δ ≤ ‖w - U t.toNNReal‖} := by
    intro t _
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    have ha' : δ ≤ ‖a - U t.toNNReal‖ := ha
    have hb' : δ ≤ ‖b - U t.toNNReal‖ := hb
    have hane : a - U t.toNNReal ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hδpos ha')
    have hbne : b - U t.toNNReal ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hδpos hb')
    rw [dist_eq_norm, dist_eq_norm]
    have : 2 / (a - U t.toNNReal) - 2 / (b - U t.toNNReal) =
        2 * ((b - U t.toNNReal) - (a - U t.toNNReal)) /
          ((a - U t.toNNReal) * (b - U t.toNNReal)) := by
      field_simp
    rw [this, norm_div, norm_mul, norm_mul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    have hab : (b - U t.toNNReal) - (a - U t.toNNReal) = -(a - b) := by ring
    rw [h2, hab, norm_neg, ← dist_eq_norm]
    have hpos : 0 < ‖a - U t.toNNReal‖ * ‖b - U t.toNNReal‖ :=
      mul_pos (lt_of_lt_of_le hδpos ha') (lt_of_lt_of_le hδpos hb')
    rw [div_le_iff₀ hpos]
    have hsq : δ ^ 2 ≤ ‖a - U t.toNNReal‖ * ‖b - U t.toNNReal‖ := by
      rw [sq]; exact mul_le_mul ha' hb' hδpos.le (lt_of_lt_of_le hδpos ha').le
    have : (K : ℝ) = 2 / δ ^ 2 := rfl
    rw [this]
    have hd := dist_nonneg (x := a) (y := b)
    calc 2 * dist a b = 2 / δ ^ 2 * dist a b * δ ^ 2 := by field_simp
      _ ≤ 2 / δ ^ 2 * dist a b * (‖a - U t.toNNReal‖ * ‖b - U t.toNNReal‖) := by
        gcongr
  have hder : ∀ γ : ℝ → ℂ, IsLoewnerSolution U z τ γ → ∀ t ∈ Ico 0 T,
      HasDerivWithinAt γ ((fun w : ℂ => 2 / (w - U t.toNNReal)) (γ t)) (Ici t) t :=
    fun γ h t ht =>
      (h.2 t ht.1 (hmem t ⟨ht.1, ht.2.le⟩)).2.mono (fun s hs => le_trans ht.1 hs)
  have := ODE_solution_unique_of_mem_Icc_right (v := fun t w => 2 / (w - U t.toNNReal))
    (s := fun t => {w | δ ≤ ‖w - U t.toNNReal‖}) (K := K) (a := 0) (b := T) hLip
    (cont γ₁ h₁) (hder γ₁ h₁)
    (fun t ht => le_trans (min_le_left _ _) (b₁ t ⟨ht.1, ht.2.le⟩))
    (cont γ₂ h₂) (hder γ₂ h₂)
    (fun t ht => le_trans (min_le_right _ _) (b₂ t ⟨ht.1, ht.2.le⟩))
    (h₁.1.trans h₂.1.symm)
  exact this ⟨hT, le_rfl⟩

/-- Existence of a solution up to the absorbing time, and uniqueness. -/
theorem loewner_wellDefined (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) :
    (∃ γ, IsLoewnerSolution U z (absorbingTime U z) γ) ∧
      ∀ (τ : ℝ≥0∞) (γ₁ γ₂ : ℝ → ℂ), IsLoewnerSolution U z τ γ₁ → IsLoewnerSolution U z τ γ₂ →
          Set.EqOn γ₁ γ₂ {t | 0 ≤ t ∧ ENNReal.ofReal t < τ} := by
  refine ⟨?_, fun τ γ₁ γ₂ h₁ h₂ => loewner_unique hU h₁ h₂⟩
  set T := absorbingTime U z with hT
  by_cases hT0 : T = 0
  · exact ⟨fun _ => z, hT0 ▸ isLoewnerSolution_zero U z⟩
  have key : ∀ t : ℝ, ∃ (τ : ℝ≥0∞) (g : ℝ → ℂ), 0 ≤ t → ENNReal.ofReal t < T →
      ENNReal.ofReal t < τ ∧ IsLoewnerSolution U z τ g := by
    intro t
    by_cases h : 0 ≤ t ∧ ENNReal.ofReal t < T
    · obtain ⟨τ, ⟨g, hg⟩, hlt⟩ := lt_sSup_iff.1 h.2
      exact ⟨τ, g, fun _ _ => ⟨hlt, hg⟩⟩
    · exact ⟨0, fun _ => z, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose τf gf hgf using key
  have glue : ∀ s t : ℝ, 0 ≤ s → ENNReal.ofReal s < T → 0 ≤ t → ENNReal.ofReal t < T →
      ENNReal.ofReal s < τf t → gf s s = gf t s := by
    intro s t hs hsT ht htT hst
    obtain ⟨hs1, hs2⟩ := hgf s hs hsT
    obtain ⟨-, ht2⟩ := hgf t ht htT
    exact loewner_unique hU (isLoewnerSolution_mono hs2 (min_le_left (τf s) (τf t)))
      (isLoewnerSolution_mono ht2 (min_le_right (τf s) (τf t))) ⟨hs, lt_min hs1 hst⟩
  refine ⟨fun t => gf t t, ?_, ?_⟩
  · have h0 : ENNReal.ofReal 0 < T := by simpa [pos_iff_ne_zero] using hT0
    exact (hgf 0 le_rfl h0).2.1
  · intro t ht htT
    obtain ⟨htτ, hsol⟩ := hgf t ht htT
    have hev : (fun s => gf s s) =ᶠ[nhdsWithin t (Ici 0)] gf t := by
      have hopen : ∀ᶠ s in nhds t, ENNReal.ofReal s < τf t :=
        (ENNReal.continuous_ofReal.continuousAt).eventually (Iio_mem_nhds htτ)
      have hopen2 : ∀ᶠ s in nhds t, ENNReal.ofReal s < T :=
        (ENNReal.continuous_ofReal.continuousAt).eventually (Iio_mem_nhds htT)
      filter_upwards [nhdsWithin_le_nhds hopen, nhdsWithin_le_nhds hopen2,
        self_mem_nhdsWithin] with s h1 h2 h3
      exact glue s t h3 h2 ht htT h1
    have heq : gf t t = gf t t := rfl
    have hsT := hsol.2 t ht htτ
    refine ⟨hsT.1, ?_⟩
    exact hsT.2.congr_of_eventuallyEq hev heq

end ComplexSLE.Internal

end
