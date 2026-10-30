/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Hull.LocalExistence
public import ComplexSLE.Internal.Hull.BackwardBound
public import ComplexSLE.External.LoewnerMapConformal
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Left hulls admit no separation

The core of Lemma 2.4 for left hulls (paper.tex:L658-666). The paper's sketch (loops, homotopy
in `ℂ ∖ {0}`) is replaced by a maximum-principle argument. Suppose `L_t = A ⊔ B` with `A, B`
disjoint closed, `U 0 ∈ A`, `B ≠ ∅`. Let `z₀ ∈ B` minimize the absorbing time on `B`,
`τ = T_{z₀} ∈ (0, t]`, and let `V` be a small open thickening of `B` whose closure misses `A`.
Then for `s < τ` the whole of `closure V` lies outside `L_s`, so `1/f_s` is holomorphic on `V`
and continuous on its closure (the EXTERNAL input `loewnerMap_conformal` provides holomorphy).
On `∂V` (which misses `L_t`) the backward bound keeps `|f_s| ≥ η` for `s` slightly below `τ`,
so the maximum principle gives `|f_s(z₀)| ≥ η` as well; but since `z₀` is absorbed at time `τ`,
`|f_s(z₀)| < η` for some such `s` (`lt_absorbingTime_of_norm_sub_ge`). Contradiction.
-/

public section

open scoped NNReal ENNReal
open Set Metric Bornology

namespace ComplexSLE.Internal

variable {U : ℝ≥0 → ℂ}

/-- The absorbing time is lower semicontinuous (uses that `ℂ ∖ L_s` is open). -/
theorem lowerSemicontinuous_absorbingTime (hU : Continuous U) :
    LowerSemicontinuous (absorbingTime U) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro y
  rcases eq_or_ne y ⊤ with rfl | hy
  · simp
  · have : absorbingTime U ⁻¹' Ioi y = (leftHull U y.toNNReal)ᶜ := by
      ext z
      simp [mem_leftHull_iff, not_le, ENNReal.coe_toNNReal hy]
    rw [this]
    exact (External.loewnerMap_conformal U hU y.toNNReal).1

/-- **No separation of `L_t`.** If `L_t = A ∪ B` with `A`, `B` disjoint and closed and
`U 0 ∈ A`, then `B = ∅`. -/
theorem leftHull_separation_eq_empty (hU : Continuous U) (t : ℝ≥0) {A B : Set ℂ}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) (hunion : A ∪ B = leftHull U t)
    (hU0 : U 0 ∈ A) : B = ∅ := by
  by_contra hBne
  rw [← Ne, ← nonempty_iff_ne_empty] at hBne
  obtain ⟨-, hbdd_t, -⟩ := External.loewnerMap_conformal U hU t
  have hBsub : B ⊆ leftHull U t := hunion ▸ subset_union_right
  have hBcpt : IsCompact B := isCompact_of_isClosed_isBounded hB (hbdd_t.subset hBsub)
  -- a point of `B` with minimal absorbing time
  obtain ⟨z₀, hz₀B, hz₀min⟩ :=
    ((lowerSemicontinuous_absorbingTime hU).lowerSemicontinuousOn B).exists_isMinOn hBne hBcpt
  have hz₀t : absorbingTime U z₀ ≤ t := hBsub hz₀B
  set τ : ℝ≥0 := (absorbingTime U z₀).toNNReal with hτdef
  have hτeq : (τ : ℝ≥0∞) = absorbingTime U z₀ :=
    ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top hz₀t)
  have hτt : τ ≤ t := by rw [← ENNReal.coe_le_coe, hτeq]; exact hz₀t
  have hz₀ne : z₀ ≠ U 0 := fun h => disjoint_left.1 hAB hU0 (h ▸ hz₀B)
  have hτpos : 0 < τ := by
    have := absorbingTime_pos_of_ne hU hz₀ne
    rw [← hτeq] at this
    exact_mod_cast this
  have hτpos' : (0 : ℝ) < τ := by exact_mod_cast hτpos
  -- a thickening `V` of `B` whose closure misses `A`
  obtain ⟨δ, hδ, hdisj⟩ := hAB.symm.exists_cthickenings hBcpt hA
  set V := thickening δ B with hVdef
  have hVopen : IsOpen V := isOpen_thickening
  have hVbdd : IsBounded V := (hbdd_t.subset hBsub).thickening
  have hBV : B ⊆ V := self_subset_thickening hδ B
  have hclV : closure V ⊆ cthickening δ B := closure_thickening_subset_cthickening δ B
  have hclB : ∀ w ∈ closure V, w ∈ leftHull U t → w ∈ B := by
    intro w hw hwL
    rw [← hunion] at hwL
    rcases hwL with hwA | hwB
    · exact absurd (self_subset_cthickening _ hwA) (disjoint_left.1 hdisj (hclV hw))
    · exact hwB
  have hfrontier : ∀ w ∈ frontier V, w ∉ leftHull U t := by
    intro w hw hwL
    have hwB := hclB w (frontier_subset_closure hw) hwL
    rw [hVopen.frontier_eq] at hw
    exact hw.2 (hBV hwB)
  have hclV_s : ∀ s : ℝ≥0, s < τ → ∀ w ∈ closure V, w ∉ leftHull U s := by
    intro s hs w hw hwL
    by_cases hwt : w ∈ leftHull U t
    · have hwB := hclB w hw hwt
      have h1 : absorbingTime U z₀ ≤ absorbingTime U w := hz₀min hwB
      have h2 : absorbingTime U w ≤ s := hwL
      have h3 : (τ : ℝ≥0∞) ≤ s := by rw [hτeq]; exact h1.trans h2
      exact absurd (ENNReal.coe_le_coe.1 h3) (not_le.2 hs)
    · exact hwt (leftHull_mono (hs.le.trans hτt) hwL)
  -- the extended map at time `τ`, and a lower bound `2η` for `|f_τ|` on `∂V`
  obtain ⟨-, -, G, hG, hGdiff, -, -⟩ := External.loewnerMap_conformal U hU τ
  have hfrontier_τ : ∀ w ∈ frontier V, w ∉ leftHull U τ :=
    fun w hw h => hfrontier w hw (leftHull_mono hτt h)
  obtain ⟨η, hη, hηbound⟩ : ∃ η > 0, ∀ w ∈ frontier V, 2 * η ≤ ‖G w - U τ‖ := by
    have hfc : IsCompact (frontier V) :=
      isCompact_of_isClosed_isBounded isClosed_frontier
        (hVbdd.closure.subset frontier_subset_closure)
    have hcont : ContinuousOn (fun w => ‖G w - U τ‖) (frontier V) :=
      ((hGdiff.continuousOn.mono (fun w hw => hfrontier_τ w hw)).sub continuousOn_const).norm
    rcases (frontier V).eq_empty_or_nonempty with hemp | hne
    · exact ⟨1, one_pos, fun w hw => absurd hw (by simp [hemp])⟩
    · obtain ⟨w₀, hw₀, hmin⟩ := hfc.exists_isMinOn hne hcont
      have hne0 : G w₀ - U τ ≠ 0 := by
        have hGw : G w₀ = loewnerMap U hU τ ⟨w₀, hfrontier_τ w₀ hw₀⟩ :=
          hG ⟨w₀, hfrontier_τ w₀ hw₀⟩
        rw [hGw]
        exact sub_ne_zero.2 (loewnerMap_ne_driver hU τ _)
      have hpos : 0 < ‖G w₀ - U τ‖ := norm_pos_iff.2 hne0
      refine ⟨‖G w₀ - U τ‖ / 2, by positivity, fun w hw => ?_⟩
      have h : ‖G w₀ - U τ‖ ≤ ‖G w - U τ‖ := by simpa [isMinOn_iff] using hmin hw
      linarith
  -- modulus of continuity of the driver near `τ`
  set W : ℝ → ℂ := fun s => U s.toNNReal with hWdef
  have hWc : Continuous W := hU.comp continuous_real_toNNReal
  have hWτ : W τ = U τ := by simp [hWdef]
  obtain ⟨ε₁, hε₁, hmod⟩ :=
    Metric.continuousAt_iff.1 (hWc.continuousAt (x := (τ : ℝ))) (η / 4) (by positivity)
  set ε := min (ε₁ / 2) (min (η ^ 2 / 16) (τ : ℝ)) with hεdef
  have hεpos : 0 < ε := lt_min (by positivity) (lt_min (by positivity) hτpos')
  have hε1 : ε ≤ ε₁ / 2 := min_le_left _ _
  have hε2 : ε ≤ η ^ 2 / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hε3 : ε ≤ τ := (min_le_right _ _).trans (min_le_right _ _)
  set a : ℝ := τ - ε with hadef
  have ha0 : 0 ≤ a := by linarith
  have haτ : a < τ := by linarith
  have hUmod : ∀ u ∈ Icc a (τ : ℝ), ‖W u - W τ‖ ≤ η / 4 := by
    intro u hu
    have hd : dist u τ < ε₁ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hu.1, hu.2]
    have := hmod hd
    rw [dist_eq_norm] at this
    exact this.le
  -- boundary estimate: `|f_s| ≥ η` on `∂V` for `s ∈ [a, τ)`
  have hbdry : ∀ s : ℝ≥0, a ≤ s → s < τ → ∀ w (hw : w ∉ leftHull U s), w ∈ frontier V →
      η ≤ ‖loewnerMap U hU s ⟨w, hw⟩ - U s‖ := by
    intro s hsa hsτ w hw hwfr
    have hwt : w ∉ leftHull U t := hfrontier w hwfr
    have hwT : (t : ℝ≥0∞) < absorbingTime U w := notMem_leftHull_iff.1 hwt
    obtain ⟨γ, hγ, hγmap⟩ := loewnerMap_exists_solution U hU w
    have hγ' : ∀ u ∈ Icc a (τ : ℝ), HasDerivWithinAt γ (2 / (γ u - W u)) (Icc a τ) u := by
      intro u hu
      have hu0 : 0 ≤ u := ha0.trans hu.1
      have huT : ENNReal.ofReal u < absorbingTime U w := by
        calc ENNReal.ofReal u ≤ ENNReal.ofReal τ := ENNReal.ofReal_le_ofReal hu.2
          _ = (τ : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
          _ ≤ t := by exact_mod_cast hτt
          _ < _ := hwT
      exact (hγ.2 u hu0 huT).2.mono (fun v hv => ha0.trans hv.1)
    have hγτ : γ τ = G w := by
      have hGw : G w = loewnerMap U hU τ ⟨w, hfrontier_τ w hwfr⟩ := hG ⟨w, hfrontier_τ w hwfr⟩
      rw [hGw, hγmap τ (hfrontier_τ w hwfr)]
    have hb : 2 * η ≤ ‖γ τ - W τ‖ := by
      rw [hγτ, hWτ]; exact hηbound w hwfr
    have hlen : 8 * ((τ : ℝ) - a) ≤ η ^ 2 := by rw [hadef]; linarith
    have hall := norm_sub_driver_ge_of_Icc hU hγ' hη hb hUmod hlen
    have hs' := hall s ⟨hsa, hsτ.le⟩
    rw [hγmap s hw]
    simpa [hWdef] using hs'
  -- `z₀` is absorbed at time `τ`: `|f_s(z₀)| < η` for some `s ∈ [a, τ)`
  obtain ⟨γ₀, hγ₀, hγ₀map⟩ := loewnerMap_exists_solution U hU z₀
  have hγ₀' : IsLoewnerSolution U z₀ (ENNReal.ofReal τ) γ₀ := by
    rwa [ENNReal.ofReal_coe_nnreal, hτeq]
  obtain ⟨s, hs, hslt⟩ : ∃ s ∈ Ico a (τ : ℝ), ‖γ₀ s - W s‖ < η := by
    by_contra hcon
    push Not at hcon
    have := lt_absorbingTime_of_norm_sub_ge hU hτpos' hγ₀' haτ hη hcon
    rw [ENNReal.ofReal_coe_nnreal, hτeq] at this
    exact lt_irrefl _ this
  have hs0 : 0 ≤ s := ha0.trans hs.1
  set s' : ℝ≥0 := s.toNNReal with hs'def
  have hs'eq : (s' : ℝ) = s := Real.coe_toNNReal s hs0
  have hs'τ : s' < τ := by rw [← NNReal.coe_lt_coe, hs'eq]; exact hs.2
  have hs'a : a ≤ s' := by rw [hs'eq]; exact hs.1
  have hWs : W s = U s' := rfl
  -- the extended map at time `s'` and the maximum principle for `1/f_{s'}` on `V`
  obtain ⟨-, -, G', hG', hG'diff, -, -⟩ := External.loewnerMap_conformal U hU s'
  have hclV_s' : closure V ⊆ (leftHull U s')ᶜ := fun w hw => hclV_s s' hs'τ w hw
  have hne' : ∀ w ∈ closure V, G' w - U s' ≠ 0 := by
    intro w hw
    have hGw : G' w = loewnerMap U hU s' ⟨w, hclV_s' hw⟩ := hG' ⟨w, hclV_s' hw⟩
    rw [hGw]
    exact sub_ne_zero.2 (loewnerMap_ne_driver hU s' _)
  have hdiff : DifferentiableOn ℂ (fun w => (G' w - U s')⁻¹) (closure V) :=
    ((hG'diff.mono hclV_s').sub (differentiableOn_const _)).inv hne'
  have hz₀cl : z₀ ∈ closure V := subset_closure (hBV hz₀B)
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le hVbdd hdiff.diffContOnCl
    (C := η⁻¹) ?_ hz₀cl
  · have hz₀eq : G' z₀ = γ₀ s := by
      have h1 : G' z₀ = loewnerMap U hU s' ⟨z₀, hclV_s' hz₀cl⟩ := hG' ⟨z₀, hclV_s' hz₀cl⟩
      rw [h1, hγ₀map s' _, hs'eq]
    have hpos : 0 < ‖γ₀ s - W s‖ := by
      refine norm_pos_iff.2 (sub_ne_zero.2 ?_)
      exact (hγ₀'.2 s hs0 ((ENNReal.ofReal_lt_ofReal_iff hτpos').2 hs.2)).1
    rw [hz₀eq, norm_inv, ← hWs] at hmax
    have := inv_strictAnti₀ hpos hslt
    linarith
  · intro w hw
    have hwfr := hbdry s' hs'a hs'τ w (hclV_s' (frontier_subset_closure hw)) hw
    have hGw : G' w = loewnerMap U hU s' ⟨w, hclV_s' (frontier_subset_closure hw)⟩ :=
      hG' ⟨w, hclV_s' (frontier_subset_closure hw)⟩
    change ‖(G' w - U s')⁻¹‖ ≤ η⁻¹
    rw [hGw, norm_inv]
    exact inv_anti₀ hη hwfr

end ComplexSLE.Internal

end
