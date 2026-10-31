/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Hull.LocalExistence
public import ComplexSLE.Internal.Hull.BackwardBound
public import ComplexSLE.Internal.Loewner.Duality
public import ComplexSLE.Frozen.Defs.RightHull
import ComplexSLE.Internal.Polar.PolarDeriv
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Lemma 2.4 without the external `loewnerMap_conformal`

External-free version of `ComplexSLE/Internal/Hull/Connected.lean`: the three uses of the
external `loewnerMap_conformal` there are replaced by in-project results.

* openness of `ℂ ∖ L_t`: `ComplexSLE.Internal.Polar.isOpen_compl_leftHull`;
* holomorphy of `g_t` on `ℂ ∖ L_t`: the extension `w ↦ solPath U hU w t` is holomorphic by
  `Polar.differentiableOn_solPath_initial` and agrees with `loewnerMap U hU t` by
  `Polar.loewnerMap_eq_solPath`;
* boundedness of `L_t`: if `‖z‖ ≥ M + 2 + 2t` with `M ≥ sup_{[0,t]} ‖U‖`, then as long as the
  Loewner solution from `z` stays at distance `≥ 1` from the driver its speed is `≤ 2`, so it
  moves by at most `2s` up to time `s` and hence stays at distance `≥ ‖z‖ - M - 2s > 2` from the
  driver; so `z ∉ L_t` (`isBounded_leftHull'`).

The core maximum-principle argument (`leftHull_separation_eq_empty'`) is then unchanged: suppose
`L_t = A ⊔ B` with `A, B` disjoint closed, `U 0 ∈ A`, `B ≠ ∅`. Let `z₀ ∈ B` minimize the
absorbing time on `B`, `τ = T_{z₀} ∈ (0, t]`, and let `V` be a small open thickening of `B` whose
closure misses `A`. For `s < τ` the whole of `closure V` lies outside `L_s`, so `1/f_s` is
holomorphic on `V` and continuous on its closure. On `∂V` (which misses `L_t`) the backward bound
keeps `|f_s| ≥ η` for `s` slightly below `τ`, so the maximum principle gives `|f_s(z₀)| ≥ η`;
but `z₀` is absorbed at time `τ`, so `|f_s(z₀)| < η` for some such `s`
(`lt_absorbingTime_of_norm_sub_ge`). Contradiction.
-/

public section

open scoped NNReal ENNReal
open Set Metric Bornology

namespace ComplexSLE.Internal

variable {U : ℝ≥0 → ℂ}

/-! ### Closedness, holomorphic extension -/

/-- `L_t` is closed (the complement is open: `Polar.isOpen_compl_leftHull`). -/
theorem isClosed_leftHull' (hU : Continuous U) (t : ℝ≥0) : IsClosed (leftHull U t) :=
  isOpen_compl_iff.1 (Polar.isOpen_compl_leftHull U hU t)

/-- The absorbing time is lower semicontinuous (uses that `ℂ ∖ L_s` is open). -/
theorem lowerSemicontinuous_absorbingTime' (hU : Continuous U) :
    LowerSemicontinuous (absorbingTime U) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro y
  rcases eq_or_ne y ⊤ with rfl | hy
  · simp
  · have : absorbingTime U ⁻¹' Ioi y = (leftHull U y.toNNReal)ᶜ := by
      ext z
      simp [mem_leftHull_iff, not_le, ENNReal.coe_toNNReal hy]
    rw [this]
    exact Polar.isOpen_compl_leftHull U hU y.toNNReal

/-- `g_t` extends to a function holomorphic on `ℂ ∖ L_t`. -/
theorem exists_differentiableOn_extension_loewnerMap (hU : Continuous U) (t : ℝ≥0) :
    ∃ G : ℂ → ℂ, (∀ z : ↥(leftHull U t)ᶜ, G z = loewnerMap U hU t z) ∧
      DifferentiableOn ℂ G (leftHull U t)ᶜ :=
  ⟨fun w => Polar.solPath U hU w t, fun z => (Polar.loewnerMap_eq_solPath hU t z.2).symm,
    Polar.differentiableOn_solPath_initial hU t⟩

/-! ### Boundedness of `L_t` -/

/-- A Loewner solution started far from the driver stays far from it: if `‖U‖ ≤ M` on `[0, τ)`
and `M + 2 + 2τ ≤ ‖z‖`, then `‖γ u - U u‖ ≥ 1` for all `u ∈ [0, τ)`. -/
theorem one_le_norm_sub_driver_of_far (hU : Continuous U) {γ : ℝ → ℂ} {z : ℂ} {τ M : ℝ}
    (hγ0 : γ 0 = z)
    (hγ : ∀ u ∈ Ico 0 τ, γ u ≠ U u.toNNReal ∧
      HasDerivWithinAt γ (2 / (γ u - U u.toNNReal)) (Ici 0) u)
    (hM : ∀ u ∈ Ico 0 τ, ‖U u.toNNReal‖ ≤ M) (hz : M + 2 + 2 * τ ≤ ‖z‖) :
    ∀ u ∈ Ico 0 τ, 1 ≤ ‖γ u - U u.toNNReal‖ := by
  set V : ℝ → ℂ := fun s => U s.toNNReal with hV
  have hVc : Continuous V := hU.comp continuous_real_toNNReal
  by_contra hcon
  push Not at hcon
  obtain ⟨s, hs, hslt⟩ := hcon
  have hsτ : s < τ := hs.2
  have hγcont : ContinuousOn γ (Icc 0 s) := fun u hu =>
    ((hγ u ⟨hu.1, hu.2.trans_lt hsτ⟩).2.continuousWithinAt).mono
      (fun v hv => hv.1)
  have hfcont : ContinuousOn (fun u => ‖γ u - V u‖) (Icc 0 s) :=
    (hγcont.sub hVc.continuousOn).norm
  -- the first time in `[0, s]` at which the distance to the driver is `≤ 1`
  set W := Icc 0 s ∩ (fun u => ‖γ u - V u‖) ⁻¹' Iic 1 with hW
  have hWclosed : IsClosed W :=
    hfcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hWne : W.Nonempty := ⟨s, ⟨hs.1, le_rfl⟩, hslt.le⟩
  have hWbdd : BddBelow W := ⟨0, fun u hu => hu.1.1⟩
  set u₀ := sInf W with hu₀
  have hu₀W : u₀ ∈ W := hWclosed.csInf_mem hWne hWbdd
  have hu₀le : ‖γ u₀ - V u₀‖ ≤ 1 := hu₀W.2
  have hu₀s : u₀ ≤ s := hu₀W.1.2
  have hu₀0 : 0 ≤ u₀ := hu₀W.1.1
  have hu₀τ : u₀ ∈ Ico 0 τ := ⟨hu₀0, hu₀s.trans_lt hsτ⟩
  have hgt : ∀ u ∈ Ico 0 u₀, 1 < ‖γ u - V u‖ := by
    intro u hu
    by_contra h
    push Not at h
    have hmem : u ∈ W := ⟨⟨hu.1, hu.2.le.trans hu₀s⟩, h⟩
    exact absurd (csInf_le hWbdd hmem) (not_le.2 hu.2)
  -- the solution moves at speed `≤ 2` on `[0, u₀)`
  have hclose : ‖γ u₀ - z‖ ≤ 2 * u₀ := by
    rcases hu₀0.eq_or_lt with h0 | hpos
    · rw [← h0, hγ0, sub_self, norm_zero]; simp
    · have hderiv : ∀ u ∈ Ico 0 u₀,
          HasDerivWithinAt γ (2 / (γ u - V u)) (Ico 0 u₀) u := fun u hu =>
        (hγ u ⟨hu.1, hu.2.trans_le hu₀s |>.trans hsτ⟩).2.mono (fun v hv => hv.1)
      have hbound : ∀ u ∈ Ico 0 u₀, ‖2 / (γ u - V u)‖ ≤ 2 := by
        intro u hu
        have h1 := hgt u hu
        rw [norm_div, show ‖(2 : ℂ)‖ = 2 by simp, div_le_iff₀ (by linarith)]
        nlinarith
      have hmvt : ∀ y ∈ Ico 0 u₀, ‖γ y - z‖ ≤ 2 * y := by
        intro y hy
        have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
          (convex_Ico 0 u₀) (⟨le_rfl, hpos⟩ : (0 : ℝ) ∈ Ico 0 u₀) hy
        rw [hγ0, Real.norm_eq_abs, sub_zero, abs_of_nonneg hy.1] at this
        exact this
      have hC : IsClosed (Icc 0 s ∩ (fun u => ‖γ u - z‖ - 2 * u) ⁻¹' Iic 0) :=
        ((hγcont.sub continuousOn_const).norm.sub
          (continuousOn_const.mul continuousOn_id)).preimage_isClosed_of_isClosed isClosed_Icc
          isClosed_Iic
      have hsub : Ico 0 u₀ ⊆ Icc 0 s ∩ (fun u => ‖γ u - z‖ - 2 * u) ⁻¹' Iic 0 := fun y hy =>
        ⟨⟨hy.1, hy.2.le.trans hu₀s⟩, sub_nonpos.2 (hmvt y hy)⟩
      have := hC.closure_subset_iff.2 hsub
      rw [closure_Ico hpos.ne] at this
      exact sub_nonpos.1 (this ⟨hpos.le, le_rfl⟩).2
  have hMu₀ : ‖V u₀‖ ≤ M := hM u₀ hu₀τ
  have h3 : ‖z‖ ≤ ‖γ u₀ - V u₀‖ + ‖γ u₀ - z‖ + ‖V u₀‖ := by
    calc ‖z‖ = ‖(γ u₀ - V u₀) - (γ u₀ - z) + V u₀‖ := by ring_nf
      _ ≤ ‖(γ u₀ - V u₀) - (γ u₀ - z)‖ + ‖V u₀‖ := norm_add_le _ _
      _ ≤ ‖γ u₀ - V u₀‖ + ‖γ u₀ - z‖ + ‖V u₀‖ := by gcongr; exact norm_sub_le _ _
  have : u₀ < τ := hu₀τ.2
  linarith

/-- **`L_t` is bounded** (proved here directly, without the external). -/
theorem isBounded_leftHull' (hU : Continuous U) (t : ℝ≥0) : IsBounded (leftHull U t) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := (t : ℝ))).exists_bound_of_continuousOn
    (f := fun u : ℝ => U u.toNNReal) (hU.comp continuous_real_toNNReal).continuousOn
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := M + 2 + 2 * t)).subset fun z hz => ?_
  by_contra hzR
  rw [mem_closedBall_zero_iff, not_le] at hzR
  have hzt : absorbingTime U z ≤ t := hz
  have hTtop : absorbingTime U z ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hzt
  have hU0 : ‖U 0‖ ≤ M := by
    simpa using hM 0 ⟨le_rfl, t.2⟩
  have ht0 : (0 : ℝ) ≤ t := t.2
  have hzne : z ≠ U 0 := by
    rintro rfl
    linarith
  have hTpos : 0 < absorbingTime U z := absorbingTime_pos_of_ne hU hzne
  set τ : ℝ := (absorbingTime U z).toReal with hτdef
  have hτpos : 0 < τ := ENNReal.toReal_pos hTpos.ne' hTtop
  have hτt : τ ≤ t := by
    have := ENNReal.toReal_mono ENNReal.coe_ne_top hzt
    simpa using this
  obtain ⟨γ, hγ, -⟩ := loewnerMap_exists_solution U hU z
  have hγτ : IsLoewnerSolution U z (ENNReal.ofReal τ) γ := by
    rwa [hτdef, ENNReal.ofReal_toReal hTtop]
  have hγ' : ∀ u ∈ Ico 0 τ, γ u ≠ U u.toNNReal ∧
      HasDerivWithinAt γ (2 / (γ u - U u.toNNReal)) (Ici 0) u := fun u hu =>
    hγτ.2 u hu.1 ((ENNReal.ofReal_lt_ofReal_iff hτpos).2 hu.2)
  have hMτ : ∀ u ∈ Ico 0 τ, ‖U u.toNNReal‖ ≤ M := fun u hu => hM u ⟨hu.1, hu.2.le.trans hτt⟩
  have hfar := one_le_norm_sub_driver_of_far hU hγτ.1 hγ' hMτ
    (by linarith [mul_le_mul_of_nonneg_left hτt (show (0 : ℝ) ≤ 2 by norm_num)])
  have := lt_absorbingTime_of_norm_sub_ge hU hτpos hγτ hτpos one_pos hfar
  rw [hτdef, ENNReal.ofReal_toReal hTtop] at this
  exact lt_irrefl _ this

/-! ### No separation -/

/-- **No separation of `L_t`.** If `L_t = A ∪ B` with `A`, `B` disjoint and closed and
`U 0 ∈ A`, then `B = ∅`. -/
theorem leftHull_separation_eq_empty' (hU : Continuous U) (t : ℝ≥0) {A B : Set ℂ}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) (hunion : A ∪ B = leftHull U t)
    (hU0 : U 0 ∈ A) : B = ∅ := by
  by_contra hBne
  rw [← Ne, ← nonempty_iff_ne_empty] at hBne
  have hbdd_t : IsBounded (leftHull U t) := isBounded_leftHull' hU t
  have hBsub : B ⊆ leftHull U t := hunion ▸ subset_union_right
  have hBcpt : IsCompact B := isCompact_of_isClosed_isBounded hB (hbdd_t.subset hBsub)
  -- a point of `B` with minimal absorbing time
  obtain ⟨z₀, hz₀B, hz₀min⟩ :=
    ((lowerSemicontinuous_absorbingTime' hU).lowerSemicontinuousOn B).exists_isMinOn hBne hBcpt
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
  obtain ⟨G, hG, hGdiff⟩ := exists_differentiableOn_extension_loewnerMap hU τ
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
  obtain ⟨G', hG', hG'diff⟩ := exists_differentiableOn_extension_loewnerMap hU s'
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

/-! ### Lemma 2.4 -/

/-- **Lemma 2.4, left hulls, without externals** (paper.tex:L658-666): for continuous `U`, each
`L_t` is connected. Same type as `ComplexSLE.lemma_2_4_leftHull`. -/
theorem lemma_2_4_leftHull' (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) :
    IsConnected (leftHull U t) := by
  refine ⟨leftHull_nonempty U t, ?_⟩
  have hclosed : IsClosed (leftHull U t) := isClosed_leftHull' hU t
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
    have hempty := leftHull_separation_eq_empty' hU t (hA.inter hclosed) (hB.inter hclosed)
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

/-- **Lemma 2.4, right hulls, without externals** (paper.tex:L658-666): for continuous `U`, each
`R_t` is connected. Same type as `ComplexSLE.lemma_2_4_rightHull`. By the duality (2.4),
`R_t^U = (-i) L_t^V` for the reversed driver `V`, and `L_t^V` is connected by
`lemma_2_4_leftHull'`. -/
theorem lemma_2_4_rightHull' (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) :
    IsConnected (rightHull U hU t) := by
  rw [rightHull_eq_image_leftHull_revDriver hU t]
  exact (lemma_2_4_leftHull' (revDriver U t) (continuous_revDriver hU t) t).image _
    (by fun_prop)

end ComplexSLE.Internal

end
