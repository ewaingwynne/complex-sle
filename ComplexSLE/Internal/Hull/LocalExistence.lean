/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Hull.Basic
public import ComplexSLE.Infrastructure.PicardLindelofBall
public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Local existence for the Loewner equation and the absorbing time

Picard–Lindelöf for the vector field `w ↦ 2/(w - U_s)` away from the singularity, gluing of a
local solution onto a solution on `[0, τ)`, and the two consequences used for the hulls:

* `absorbingTime_pos_of_ne`: `T_z > 0` for `z ≠ U 0`;
* `lt_absorbingTime_of_norm_sub_ge`: if a solution on `[0, τ)` stays at distance `≥ η` from the
  driver on a final interval `[a, τ)`, then `T_z > τ` (solutions only stop by approaching `U`).
-/

public section

open scoped NNReal ENNReal
open Set

namespace ComplexSLE.Internal

variable {U : ℝ≥0 → ℂ}

/-- The Loewner vector field `w ↦ 2/(w - c)` is Lipschitz on `{w | δ ≤ ‖w - c‖}`. -/
theorem lipschitzOnWith_loewner_field (c : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    LipschitzOnWith ⟨2 / δ ^ 2, by positivity⟩ (fun w : ℂ => 2 / (w - c))
      {w | δ ≤ ‖w - c‖} := by
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
  have ha' : δ ≤ ‖a - c‖ := ha
  have hb' : δ ≤ ‖b - c‖ := hb
  have hane : a - c ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hδ ha')
  have hbne : b - c ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hδ hb')
  rw [dist_eq_norm, dist_eq_norm]
  have : 2 / (a - c) - 2 / (b - c) = 2 * ((b - c) - (a - c)) / ((a - c) * (b - c)) := by
    field_simp
  rw [this, norm_div, norm_mul, norm_mul]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  have hab : (b - c) - (a - c) = -(a - b) := by ring
  rw [h2, hab, norm_neg, ← dist_eq_norm]
  have hpos : 0 < ‖a - c‖ * ‖b - c‖ := mul_pos (lt_of_lt_of_le hδ ha') (lt_of_lt_of_le hδ hb')
  rw [div_le_iff₀ hpos]
  have hsq : δ ^ 2 ≤ ‖a - c‖ * ‖b - c‖ := by
    rw [sq]; exact mul_le_mul ha' hb' hδ.le (lt_of_lt_of_le hδ ha').le
  change 2 * dist a b ≤ 2 / δ ^ 2 * dist a b * (‖a - c‖ * ‖b - c‖)
  have hd := dist_nonneg (x := a) (y := b)
  calc 2 * dist a b = 2 / δ ^ 2 * dist a b * δ ^ 2 := by field_simp
    _ ≤ 2 / δ ^ 2 * dist a b * (‖a - c‖ * ‖b - c‖) := by gcongr

/-- A continuous nonvanishing function on a compact interval is bounded below in norm. -/
theorem exists_pos_le_norm_Icc {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (h0 : ∀ t ∈ Icc a b, f t ≠ 0) : ∃ δ > 0, ∀ t ∈ Icc a b, δ ≤ ‖f t‖ := by
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab) hf.norm
  exact ⟨‖f t₀‖, norm_pos_iff.2 (h0 t₀ ht₀), fun t ht => hmin ht⟩

/-- **Local existence**, uniform in the initial time and point: given `η > 0` and a time horizon
`T`, there is `Δ > 0` such that from any `(s₁, w₀)` with `s₁ ∈ [0, T]` and `‖w₀ - U_{s₁}‖ ≥ η`
the Loewner equation has a solution on `[s₁ - Δ, s₁ + Δ]` avoiding the driver. -/
theorem exists_loewner_local_solution (hU : Continuous U) (T : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ Δ > 0, ∀ s₁ ∈ Icc 0 T, ∀ w₀ : ℂ, η ≤ ‖w₀ - U s₁.toNNReal‖ →
      ∃ σ : ℝ → ℂ, σ s₁ = w₀ ∧ ∀ s ∈ Icc (s₁ - Δ) (s₁ + Δ),
        σ s ≠ U s.toNNReal ∧
          HasDerivWithinAt σ (2 / (σ s - U s.toNNReal)) (Icc (s₁ - Δ) (s₁ + Δ)) s := by
  set V : ℝ → ℂ := fun s => U s.toNNReal with hV
  have hVc : Continuous V := hU.comp continuous_real_toNNReal
  have hunif := isCompact_Icc.uniformContinuousOn_of_continuous
    (s := Icc (-1) (T + 1)) hVc.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hunif
  obtain ⟨Δ₁, hΔ₁, hmod⟩ := hunif (η / 4) (by positivity)
  have hΔpos : 0 < min (Δ₁ / 2) (min 1 (η ^ 2 / 16)) := by positivity
  refine ⟨min (Δ₁ / 2) (min 1 (η ^ 2 / 16)), hΔpos, ?_⟩
  intro s₁ hs₁ w₀ hw₀
  set Δ := min (Δ₁ / 2) (min 1 (η ^ 2 / 16)) with hΔ
  have hΔ1 : Δ ≤ Δ₁ / 2 := min_le_left _ _
  have hΔ2 : Δ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hΔ3 : Δ ≤ η ^ 2 / 16 := (min_le_right _ _).trans (min_le_right _ _)
  have hsub : Icc (s₁ - Δ) (s₁ + Δ) ⊆ Icc (-1) (T + 1) := by
    intro s hs; constructor <;> linarith [hs.1, hs.2, hs₁.1, hs₁.2]
  have ht₀ : s₁ ∈ Icc (s₁ - Δ) (s₁ + Δ) := ⟨by linarith, by linarith⟩
  have key : ∀ s ∈ Icc (s₁ - Δ) (s₁ + Δ), ∀ w ∈ Metric.closedBall w₀ (η / 4),
      η / 2 ≤ ‖w - V s‖ := by
    intro s hs w hw
    have h1 : ‖w - w₀‖ ≤ η / 4 := by simpa [dist_eq_norm] using hw
    have h2 : ‖V s - V s₁‖ < η / 4 := by
      have := hmod s (hsub hs) s₁ (hsub ht₀) ?_
      · simpa [dist_eq_norm] using this
      · rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2]
    have h3 : ‖w₀ - V s₁‖ ≤ ‖w - V s‖ + ‖w - w₀‖ + ‖V s - V s₁‖ := by
      calc ‖w₀ - V s₁‖ = ‖(w - V s) - (w - w₀) + (V s - V s₁)‖ := by ring_nf
        _ ≤ ‖(w - V s) - (w - w₀)‖ + ‖V s - V s₁‖ := norm_add_le _ _
        _ ≤ ‖w - V s‖ + ‖w - w₀‖ + ‖V s - V s₁‖ := by gcongr; exact norm_sub_le _ _
    have hw₀' : η ≤ ‖w₀ - V s₁‖ := hw₀
    linarith
  have hne : ∀ s ∈ Icc (s₁ - Δ) (s₁ + Δ), ∀ w ∈ Metric.closedBall w₀ (η / 4), w - V s ≠ 0 :=
    fun s hs w hw => norm_pos_iff.1 (lt_of_lt_of_le (by positivity) (key s hs w hw))
  let a : ℝ≥0 := ⟨η / 4, by positivity⟩
  let L : ℝ≥0 := ⟨4 / η, by positivity⟩
  let K : ℝ≥0 := ⟨2 / (η / 2) ^ 2, by positivity⟩
  have hPL : IsPicardLindelof (fun s w => 2 / (w - V s))
      (⟨s₁, ht₀⟩ : Icc (s₁ - Δ) (s₁ + Δ)) w₀ a 0 L K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s hs
      exact (lipschitzOnWith_loewner_field (V s) (by positivity : 0 < η / 2)).mono
        (fun w hw => key s hs w hw)
    · intro w hw
      exact continuousOn_const.div (continuousOn_const.sub hVc.continuousOn)
        (fun s hs => hne s hs w hw)
    · intro s hs w hw
      have hpos : 0 < ‖w - V s‖ := lt_of_lt_of_le (by positivity) (key s hs w hw)
      change ‖2 / (w - V s)‖ ≤ 4 / η
      rw [norm_div, div_le_div_iff₀ hpos hη]
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      rw [h2]
      linarith [key s hs w hw]
    · change (4 / η) * max ((s₁ + Δ) - s₁) (s₁ - (s₁ - Δ)) ≤ η / 4 - 0
      have : max ((s₁ + Δ) - s₁) (s₁ - (s₁ - Δ)) = Δ := by
        rw [show (s₁ + Δ) - s₁ = Δ by ring, show s₁ - (s₁ - Δ) = Δ by ring, max_self]
      rw [this, sub_zero, div_mul_eq_mul_div, div_le_iff₀ hη]
      nlinarith
  obtain ⟨σ, hσ₀, hσ⟩ :=
    Infrastructure.IsPicardLindelof.exists_eq_forall_mem_Icc_mem_closedBall_hasDerivWithinAt hPL
      (Metric.mem_closedBall_self le_rfl)
  refine ⟨σ, hσ₀, fun s hs => ⟨?_, (hσ s hs).2⟩⟩
  exact fun h => hne s hs (σ s) (hσ s hs).1 (by rw [h, sub_self])

/-- Gluing a Loewner solution on `[0, τ)` with a local solution around a time `s₁ ∈ (0, τ)`
produces a solution on `[0, s₁ + Δ)`. -/
theorem isLoewnerSolution_glue (hU : Continuous U) {z : ℂ} {τ : ℝ} {γ : ℝ → ℂ}
    (hγ : IsLoewnerSolution U z (ENNReal.ofReal τ) γ) {s₁ Δ : ℝ} (hs₁ : 0 < s₁) (hs₁τ : s₁ < τ)
    (hΔ : 0 < Δ) {σ : ℝ → ℂ} (hσ₁ : σ s₁ = γ s₁)
    (hσ : ∀ s ∈ Icc (s₁ - Δ) (s₁ + Δ), σ s ≠ U s.toNNReal ∧
      HasDerivWithinAt σ (2 / (σ s - U s.toNNReal)) (Icc (s₁ - Δ) (s₁ + Δ)) s) :
    IsLoewnerSolution U z (ENNReal.ofReal (s₁ + Δ)) (fun s => if s < s₁ then γ s else σ s) := by
  set V : ℝ → ℂ := fun s => U s.toNNReal with hV
  have hVc : Continuous V := hU.comp continuous_real_toNNReal
  have hτ : 0 < τ := hs₁.trans hs₁τ
  -- the solution `γ` on `[0, τ)`
  have hγ' : ∀ s, 0 ≤ s → s < τ →
      γ s ≠ V s ∧ HasDerivWithinAt γ (2 / (γ s - V s)) (Ici 0) s := fun s hs hsτ =>
    hγ.2 s hs ((ENNReal.ofReal_lt_ofReal_iff hτ).2 hsτ)
  -- the uniqueness interval
  set Δ' := min Δ (min s₁ (τ - s₁)) / 2 with hΔ'
  have hΔ'pos : 0 < Δ' := by
    have : 0 < min Δ (min s₁ (τ - s₁)) := lt_min hΔ (lt_min hs₁ (by linarith))
    positivity
  have hΔ'1 : Δ' < Δ := by
    have : min Δ (min s₁ (τ - s₁)) ≤ Δ := min_le_left _ _
    linarith
  have hΔ'2 : Δ' < s₁ := by
    have : min Δ (min s₁ (τ - s₁)) ≤ s₁ := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hΔ'3 : Δ' < τ - s₁ := by
    have : min Δ (min s₁ (τ - s₁)) ≤ τ - s₁ := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  set a' := s₁ - Δ' with ha'
  set b' := s₁ + Δ' with hb'
  have ha'b' : a' ≤ b' := by linarith
  have hsubI : Icc a' b' ⊆ Icc (s₁ - Δ) (s₁ + Δ) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hγcont : ContinuousOn γ (Icc a' b') := fun s hs =>
    ((hγ' s (by linarith [hs.1]) (by linarith [hs.2])).2.continuousWithinAt).mono
      (fun u hu => le_trans (by linarith) hu.1)
  have hσcont : ContinuousOn σ (Icc a' b') := fun s hs =>
    ((hσ s (hsubI hs)).2.continuousWithinAt).mono hsubI
  have hγd : ∀ s ∈ Ioo a' b', HasDerivAt γ (2 / (γ s - V s)) s := fun s hs =>
    (hγ' s (by linarith [hs.1]) (by linarith [hs.2])).2.hasDerivAt
      (Ici_mem_nhds (by linarith [hs.1]))
  have hσd : ∀ s ∈ Ioo (s₁ - Δ) (s₁ + Δ), HasDerivAt σ (2 / (σ s - V s)) s := fun s hs =>
    (hσ s (Ioo_subset_Icc_self hs)).2.hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  -- distance to the driver on the uniqueness interval
  obtain ⟨δ₁, hδ₁, hb₁⟩ := exists_pos_le_norm_Icc ha'b' (hγcont.sub hVc.continuousOn)
    (fun s hs => sub_ne_zero.2 (hγ' s (by linarith [hs.1]) (by linarith [hs.2])).1)
  obtain ⟨δ₂, hδ₂, hb₂⟩ := exists_pos_le_norm_Icc ha'b' (hσcont.sub hVc.continuousOn)
    (fun s hs => sub_ne_zero.2 (hσ s (hsubI hs)).1)
  have hδ : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have heq : EqOn γ σ (Icc a' b') :=
    ODE_solution_unique_of_mem_Icc (v := fun t w => 2 / (w - V t))
      (s := fun t => {w | min δ₁ δ₂ ≤ ‖w - V t‖}) (K := ⟨2 / (min δ₁ δ₂) ^ 2, by positivity⟩)
      (fun t _ => lipschitzOnWith_loewner_field (V t) hδ)
      (⟨by linarith, by linarith⟩ : s₁ ∈ Ioo a' b') hγcont hγd
      (fun t ht => le_trans (min_le_left _ _) (hb₁ t (Ioo_subset_Icc_self ht)))
      hσcont (fun s hs => hσd s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      (fun t ht => le_trans (min_le_right _ _) (hb₂ t (Ioo_subset_Icc_self ht))) hσ₁.symm
  -- the glued function
  refine ⟨by simp [hs₁, hγ.1], fun s hs hsΔ => ?_⟩
  rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)] at hsΔ
  by_cases hlt : s < s₁
  · have hev : (fun u => if u < s₁ then γ u else σ u) =ᶠ[nhds s] γ :=
      Filter.eventuallyEq_of_mem (Iio_mem_nhds hlt) (fun u hu => ite_eq_left hu)
    have hgs : (if s < s₁ then γ s else σ s) = γ s := ite_eq_left hlt
    beta_reduce
    rw [hgs]
    refine ⟨(hγ' s hs (hlt.trans hs₁τ)).1, ?_⟩
    exact (hγ' s hs (hlt.trans hs₁τ)).2.congr_of_eventuallyEq
      (hev.filter_mono nhdsWithin_le_nhds) hgs
  · push Not at hlt
    have hev : (fun u => if u < s₁ then γ u else σ u) =ᶠ[nhds s] σ := by
      refine Filter.eventuallyEq_of_mem (Ioo_mem_nhds (by linarith) hsΔ : Ioo a' (s₁ + Δ) ∈ nhds s)
        (fun u hu => ?_)
      by_cases hu' : u < s₁
      · rw [ite_eq_left hu']
        exact heq ⟨hu.1.le, by linarith⟩
      · rw [ite_eq_right hu']
    have hgs : (if s < s₁ then γ s else σ s) = σ s := ite_eq_right (not_lt.2 hlt)
    beta_reduce
    rw [hgs]
    refine ⟨(hσ s ⟨by linarith, hsΔ.le⟩).1, ?_⟩
    exact ((hσd s ⟨by linarith, hsΔ⟩).congr_of_eventuallyEq hev).hasDerivWithinAt

/-- If a solution on `[0, τ)` stays at distance `≥ η` from the driver on `[a, τ)`, then the
absorbing time exceeds `τ`. -/
theorem lt_absorbingTime_of_norm_sub_ge (hU : Continuous U) {z : ℂ} {τ : ℝ} (hτ : 0 < τ)
    {γ : ℝ → ℂ} (hγ : IsLoewnerSolution U z (ENNReal.ofReal τ) γ) {a η : ℝ}
    (haτ : a < τ) (hη : 0 < η) (h : ∀ s ∈ Ico a τ, η ≤ ‖γ s - U s.toNNReal‖) :
    ENNReal.ofReal τ < absorbingTime U z := by
  obtain ⟨Δ, hΔ, hloc⟩ := exists_loewner_local_solution hU τ hη
  set s₁ := max a (max (τ / 2) (τ - Δ / 2)) with hs₁
  have hs₁a : a ≤ s₁ := le_max_left _ _
  have hs₁pos : 0 < s₁ :=
    lt_of_lt_of_le (by linarith) ((le_max_left _ _).trans (le_max_right _ _))
  have hs₁τ : s₁ < τ := max_lt haτ (max_lt (by linarith) (by linarith))
  have hs₁Δ : τ < s₁ + Δ := by
    have : τ - Δ / 2 ≤ s₁ := (le_max_right _ _).trans (le_max_right _ _)
    linarith
  obtain ⟨σ, hσ₁, hσ⟩ := hloc s₁ ⟨hs₁pos.le, hs₁τ.le⟩ (γ s₁) (h s₁ ⟨hs₁a, hs₁τ⟩)
  have hglue := isLoewnerSolution_glue hU hγ hs₁pos hs₁τ hΔ hσ₁ hσ
  calc ENNReal.ofReal τ < ENNReal.ofReal (s₁ + Δ) :=
        (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hs₁Δ
    _ ≤ _ := le_absorbingTime_of_isLoewnerSolution hglue

/-- Points other than `U 0` are not absorbed immediately. -/
theorem absorbingTime_pos_of_ne (hU : Continuous U) {z : ℂ} (hz : z ≠ U 0) :
    0 < absorbingTime U z := by
  have hη : 0 < ‖z - U 0‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  obtain ⟨Δ, hΔ, hloc⟩ := exists_loewner_local_solution hU 0 hη
  obtain ⟨σ, hσ₀, hσ⟩ := hloc 0 ⟨le_rfl, le_rfl⟩ z (by simp)
  have hsol : IsLoewnerSolution U z (ENNReal.ofReal Δ) σ := by
    refine ⟨hσ₀, fun s hs hsΔ => ?_⟩
    rw [ENNReal.ofReal_lt_ofReal_iff hΔ] at hsΔ
    have hmem : s ∈ Icc (0 - Δ) (0 + Δ) := ⟨by linarith, by linarith⟩
    refine ⟨(hσ s hmem).1, ?_⟩
    exact ((hσ s hmem).2.hasDerivAt (Icc_mem_nhds (by linarith) (by linarith))).hasDerivWithinAt
  calc (0 : ℝ≥0∞) < ENNReal.ofReal Δ := by simpa using hΔ
    _ ≤ _ := le_absorbingTime_of_isLoewnerSolution hsol

end ComplexSLE.Internal

end
