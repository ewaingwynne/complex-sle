/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.CenteredLoewnerMap
public import ComplexSLE.Frozen.LoewnerMap_Eq
public import ComplexSLE.Internal.Hull.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Concatenation of Loewner solutions

For a driver `U` and a time `t`, a solution `γ` of the Loewner problem from `z` on `[0, τ)`,
`t < τ`, gives the solution `r ↦ γ (r + t) - U t` of the problem driven by `V = U (· + t) - U t`
from `γ t - U t = f_t z` on `[0, τ - t)` (`isLoewnerSolution_shift`). Conversely a solution of the
`V`-problem from `f_t z` glues onto `γ|[0,t]` (`isLoewnerSolution_glue_shift`). Consequently
`T_z = t + T^V_{f_t z}` for `z ∉ L_t` (`absorbingTime_eq_add_shift`), which is the engine of the
concatenation property (2.3) (paper.tex:L559-565).
-/

public section

open scoped NNReal ENNReal
open Set

namespace ComplexSLE.Internal

variable {U : ℝ≥0 → ℂ}

/-- Shifting a solution: `r ↦ γ (r + t) - U t` solves the problem driven by `U (· + t) - U t`. -/
theorem isLoewnerSolution_shift {z : ℂ} {τ : ℝ≥0∞} {γ : ℝ → ℂ} (t : ℝ≥0)
    (h : IsLoewnerSolution U z τ γ) :
    IsLoewnerSolution (fun r => U (r + t) - U t) (γ t - U t) (τ - t)
      (fun r => γ (r + t) - U t) := by
  refine ⟨by simp, fun r hr hrτ => ?_⟩
  have hrt : (r + t).toNNReal = r.toNNReal + t := by
    rw [Real.toNNReal_add hr (NNReal.coe_nonneg t), Real.toNNReal_coe]
  have hlt : ENNReal.ofReal (r + t) < τ := by
    rw [ENNReal.ofReal_add hr (NNReal.coe_nonneg t), ENNReal.ofReal_coe_nnreal]
    exact lt_tsub_iff_right.1 hrτ
  obtain ⟨hne, hd⟩ := h.2 (r + t) (by positivity) hlt
  rw [hrt] at hne hd
  have hsub : γ (r + t) - U t - (U (r.toNNReal + t) - U t) = γ (r + t) - U (r.toNNReal + t) := by
    ring
  refine ⟨?_, ?_⟩
  · intro heq
    exact hne (by simpa [sub_eq_zero] using heq)
  · have hh : HasDerivWithinAt (fun r : ℝ => r + (t : ℝ)) 1 (Ici 0) r :=
      (hasDerivWithinAt_id r _).add_const _
    have hmaps : MapsTo (fun r : ℝ => r + (t : ℝ)) (Ici 0) (Ici 0) := fun x hx =>
      add_nonneg hx (NNReal.coe_nonneg t)
    have h2 := (hd.scomp r hh hmaps).sub_const (U t)
    refine h2.congr_deriv ?_
    simp only [one_smul]
    rw [hsub]

/-- Gluing: a solution `η` of the `V`-problem from `γ t - U t` on `[0, σ)` extends `γ|[0, t]` to a
solution of the `U`-problem from `z` on `[0, t + σ)`. -/
theorem isLoewnerSolution_glue_shift {z : ℂ} {τ : ℝ≥0∞} {γ : ℝ → ℂ} (t : ℝ≥0)
    (h : IsLoewnerSolution U z τ γ) (ht : (t : ℝ≥0∞) < τ) {σ : ℝ≥0∞} {η : ℝ → ℂ}
    (hη : IsLoewnerSolution (fun r => U (r + t) - U t) (γ t - U t) σ η) :
    IsLoewnerSolution U z (t + σ) (fun r => if r ≤ t then γ r else η (r - t) + U t) := by
  have htτ : ∀ r : ℝ, 0 ≤ r → r ≤ t → ENNReal.ofReal r < τ := fun r _ hr =>
    lt_of_le_of_lt (by rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal hr) ht
  have hGt : ∀ r : ℝ, t ≤ r → (if r ≤ t then γ r else η (r - t) + U t) = η (r - t) + U t := by
    intro r hr
    by_cases hrt : r ≤ t
    · have : r = t := le_antisymm hrt hr
      subst this
      simp [hη.1]
    · simp [hrt]
  refine ⟨by simp [h.1], fun r hr hrσ => ?_⟩
  by_cases hrt : r < t
  · -- left of the gluing time
    have hev : (fun r => if r ≤ (t : ℝ) then γ r else η (r - t) + U t) =ᶠ[nhds r] γ :=
      Filter.eventuallyEq_of_mem (Iio_mem_nhds hrt) (fun u hu => ite_eq_left (le_of_lt hu))
    have hgs : (if r ≤ (t : ℝ) then γ r else η (r - t) + U t) = γ r := ite_eq_left hrt.le
    obtain ⟨hne, hd⟩ := h.2 r hr (htτ r hr hrt.le)
    beta_reduce
    rw [hgs]
    exact ⟨hne, hd.congr_of_eventuallyEq (hev.filter_mono nhdsWithin_le_nhds) hgs⟩
  · push Not at hrt
    have hr' : 0 ≤ r - t := by linarith
    have hlt : ENNReal.ofReal (r - t) < σ := by
      have h1 : ENNReal.ofReal r = t + ENNReal.ofReal (r - t) := by
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add (NNReal.coe_nonneg t) hr']
        congr 1; ring
      rw [h1] at hrσ
      exact (ENNReal.add_lt_add_iff_left ENNReal.coe_ne_top).1 hrσ
    have hrt' : (r - t).toNNReal + t = r.toNNReal := by
      apply NNReal.coe_injective
      rw [NNReal.coe_add, Real.coe_toNNReal _ hr', Real.coe_toNNReal _ hr]
      ring
    obtain ⟨hηne, hηd⟩ := hη.2 (r - t) hr' hlt
    simp only [hrt'] at hηne hηd
    rcases hrt.eq_or_lt with hrt | hrt
    · -- the gluing time itself
      subst hrt
      have hσ0 : 0 < σ := by
        by_contra hσ
        rw [not_lt, nonpos_iff_eq_zero] at hσ
        rw [hσ, add_zero, ENNReal.ofReal_coe_nnreal] at hrσ
        exact lt_irrefl _ hrσ
      obtain ⟨hne, hd⟩ := h.2 t hr (htτ t hr le_rfl)
      obtain ⟨-, hηd0⟩ := hη.2 0 le_rfl (by simpa using hσ0)
      have hgt : (if (t : ℝ) ≤ t then γ t else η (t - t) + U t) = γ t := ite_eq_left le_rfl
      beta_reduce
      rw [hgt]
      refine ⟨hne, ?_⟩
      have hleft : HasDerivWithinAt (fun r => if r ≤ (t : ℝ) then γ r else η (r - t) + U t)
          (2 / (γ t - U (t : ℝ).toNNReal)) (Icc 0 (t : ℝ)) t :=
        (hd.mono Icc_subset_Ici_self).congr (fun x hx => ite_eq_left hx.2) hgt
      have hright : HasDerivWithinAt (fun r => if r ≤ (t : ℝ) then γ r else η (r - t) + U t)
          (2 / (γ t - U (t : ℝ).toNNReal)) (Ici (t : ℝ)) t := by
        have hh : HasDerivWithinAt (fun x : ℝ => x - (t : ℝ)) 1 (Ici (t : ℝ)) t :=
          HasDerivWithinAt.sub_const (t : ℝ) (hasDerivWithinAt_id (t : ℝ) (Ici (t : ℝ)))
        have hmaps : MapsTo (fun x : ℝ => x - (t : ℝ)) (Ici (t : ℝ)) (Ici 0) := fun x hx =>
          sub_nonneg.2 hx
        have h2 := (hηd0.scomp_of_eq (t : ℝ) hh hmaps (by simp)).add_const (U t)
        refine (h2.congr (fun x hx => hGt x hx) (hGt t le_rfl)).congr_deriv ?_
        simp [hη.1]
      have := hleft.union hright
      rwa [Icc_union_Ici_eq_Ici (NNReal.coe_nonneg t)] at this
    · -- right of the gluing time
      have hr0 : 0 < r - t := by linarith
      have hev : (fun r => if r ≤ (t : ℝ) then γ r else η (r - t) + U t) =ᶠ[nhds r]
          (fun x => η (x - t) + U t) :=
        Filter.eventuallyEq_of_mem (Ioi_mem_nhds hrt) (fun u hu => hGt u (le_of_lt hu))
      have hgs : (if r ≤ (t : ℝ) then γ r else η (r - t) + U t) = η (r - t) + U t :=
        hGt r hrt.le
      beta_reduce
      rw [hgs]
      refine ⟨fun heq => hηne (by linear_combination heq), ?_⟩
      have h3 := ((hηd.hasDerivAt (Ici_mem_nhds hr0)).comp_sub_const r t).add_const (U t)
      refine (h3.hasDerivWithinAt.congr_of_eventuallyEq
        (hev.filter_mono nhdsWithin_le_nhds) hgs).congr_deriv ?_
      congr 1
      ring

/-- `T_z = t + T^V_{f_t z}` for `z ∉ L_t`, with `V = U (· + t) - U t` and `f_t z = g_t z - U t`. -/
theorem absorbingTime_eq_add_shift (hU : Continuous U) (t : ℝ≥0) (z : ℂ)
    (hz : z ∈ (leftHull U t)ᶜ) :
    absorbingTime U z =
      t + absorbingTime (fun r => U (r + t) - U t) (centeredLoewnerMap U hU t ⟨z, hz⟩) := by
  obtain ⟨γ, hγ, hmap⟩ := loewnerMap_exists_solution U hU z
  have ht : (t : ℝ≥0∞) < absorbingTime U z := notMem_leftHull_iff.1 hz
  have hfz : centeredLoewnerMap U hU t ⟨z, hz⟩ = γ t - U t := by
    simp only [centeredLoewnerMap]
    rw [hmap t hz]
  rw [hfz]
  apply le_antisymm
  · -- `T_z - t ≤ T^V`: the shifted solution
    rw [← tsub_le_iff_left]
    exact le_absorbingTime_of_isLoewnerSolution (isLoewnerSolution_shift t hγ)
  · -- `t + T^V ≤ T_z`: gluing
    have key : absorbingTime (fun r => U (r + t) - U t) (γ t - U t) ≤
        absorbingTime U z - t := by
      refine sSup_le fun σ ⟨η, hη⟩ => ?_
      have hglue := isLoewnerSolution_glue_shift t hγ ht hη
      have := le_absorbingTime_of_isLoewnerSolution hglue
      exact (ENNReal.le_sub_of_add_le_left ENNReal.coe_ne_top this)
    calc t + absorbingTime (fun r => U (r + t) - U t) (γ t - U t)
        ≤ t + (absorbingTime U z - t) := by gcongr
      _ = absorbingTime U z := add_tsub_cancel_of_le ht.le

/-- For `z ∉ L_t`: `z ∈ L_{s+t} ↔ f_t z ∈ L^V_s`. -/
theorem mem_leftHull_add_iff (hU : Continuous U) (s t : ℝ≥0) (z : ℂ) (hz : z ∈ (leftHull U t)ᶜ) :
    z ∈ leftHull U (s + t) ↔
      centeredLoewnerMap U hU t ⟨z, hz⟩ ∈ leftHull (fun r => U (r + t) - U t) s := by
  rw [mem_leftHull_iff, mem_leftHull_iff, absorbingTime_eq_add_shift hU t z hz, ENNReal.coe_add,
    add_comm (s : ℝ≥0∞) t]
  exact ENNReal.add_le_add_iff_left ENNReal.coe_ne_top

/-- The maps formula of (2.3): `f_{s+t} = f^V_s ∘ f_t` on `ℂ ∖ L_{s+t}`. -/
theorem centeredLoewnerMap_add_eq (hU : Continuous U) (s t : ℝ≥0) (z : ℂ)
    (hz : z ∈ (leftHull U (s + t))ᶜ) (hz₁ : z ∈ (leftHull U t)ᶜ)
    (hz₂ : centeredLoewnerMap U hU t ⟨z, hz₁⟩ ∈ (leftHull (fun r => U (r + t) - U t) s)ᶜ) :
    centeredLoewnerMap U hU (s + t) ⟨z, hz⟩ =
      centeredLoewnerMap (fun r => U (r + t) - U t) (by fun_prop) s
        ⟨centeredLoewnerMap U hU t ⟨z, hz₁⟩, hz₂⟩ := by
  obtain ⟨γ, hγ, hmap⟩ := loewnerMap_exists_solution U hU z
  have hst : ((s + t : ℝ≥0) : ℝ≥0∞) < absorbingTime U z := notMem_leftHull_iff.1 hz
  have hfz : centeredLoewnerMap U hU t ⟨z, hz₁⟩ = γ t - U t := by
    simp only [centeredLoewnerMap]
    rw [hmap t hz₁]
  have hs : (s : ℝ≥0∞) < absorbingTime U z - t := by
    rw [lt_tsub_iff_right, ← ENNReal.coe_add]
    exact hst
  have hsol : IsLoewnerSolution (fun r => U (r + t) - U t)
      (centeredLoewnerMap U hU t ⟨z, hz₁⟩) (absorbingTime U z - t) (fun r => γ (r + t) - U t) := by
    rw [hfz]
    exact isLoewnerSolution_shift t hγ
  have hg := loewnerMap_eq (fun r => U (r + t) - U t) (by fun_prop) s
    ⟨centeredLoewnerMap U hU t ⟨z, hz₁⟩, hz₂⟩ _ _ hsol hs
  have e₁ : centeredLoewnerMap U hU (s + t) ⟨z, hz⟩ = loewnerMap U hU (s + t) ⟨z, hz⟩ - U (s + t) :=
    rfl
  have e₂ : centeredLoewnerMap (fun r => U (r + t) - U t) (by fun_prop) s
      ⟨centeredLoewnerMap U hU t ⟨z, hz₁⟩, hz₂⟩ =
      loewnerMap (fun r => U (r + t) - U t) (by fun_prop) s
        ⟨centeredLoewnerMap U hU t ⟨z, hz₁⟩, hz₂⟩ - (U (s + t) - U t) := rfl
  rw [e₁, e₂, hg, hmap (s + t) hz]
  push_cast
  ring

/-- The range of `f_{s+t}` is the image under `f^V_s` of those points of `ℂ ∖ L^V_s` that lie in
the range of `f_t`. -/
theorem mem_range_centeredLoewnerMap_add_iff (hU : Continuous U) (s t : ℝ≥0) (u : ℂ) :
    u ∈ Set.range (centeredLoewnerMap U hU (s + t)) ↔
      ∃ w : ↥(leftHull (fun r => U (r + t) - U t) s)ᶜ,
        (w : ℂ) ∈ Set.range (centeredLoewnerMap U hU t) ∧
          centeredLoewnerMap (fun r => U (r + t) - U t) (by fun_prop) s w = u := by
  constructor
  · rintro ⟨⟨z, hz⟩, rfl⟩
    have hz₁ : z ∈ (leftHull U t)ᶜ := fun h => hz (leftHull_mono le_add_self h)
    have hz₂ : centeredLoewnerMap U hU t ⟨z, hz₁⟩ ∈ (leftHull (fun r => U (r + t) - U t) s)ᶜ :=
      fun h => hz ((mem_leftHull_add_iff hU s t z hz₁).2 h)
    exact ⟨⟨_, hz₂⟩, ⟨⟨z, hz₁⟩, rfl⟩, (centeredLoewnerMap_add_eq hU s t z hz hz₁ hz₂).symm⟩
  · rintro ⟨⟨w, hw⟩, ⟨⟨z, hz₁⟩, hzw⟩, rfl⟩
    have hz₂ : centeredLoewnerMap U hU t ⟨z, hz₁⟩ ∈ (leftHull (fun r => U (r + t) - U t) s)ᶜ := by
      rw [hzw]; exact hw
    have hz : z ∈ (leftHull U (s + t))ᶜ := fun h => hz₂ ((mem_leftHull_add_iff hU s t z hz₁).1 h)
    refine ⟨⟨z, hz⟩, ?_⟩
    rw [centeredLoewnerMap_add_eq hU s t z hz hz₁ hz₂]
    exact congrArg _ (Subtype.ext hzw)

end ComplexSLE.Internal

end
