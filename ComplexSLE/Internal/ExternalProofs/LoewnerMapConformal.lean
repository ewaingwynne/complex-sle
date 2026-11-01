/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.LoewnerMap
public import ComplexSLE.Internal.ExternalProofs.LoewnerFar
import ComplexSLE.Internal.Hull.ConnectedNoExt
import ComplexSLE.Internal.Loewner.Injective
import ComplexSLE.Internal.Polar.PolarDerivShift

/-!
# Conformality of the Loewner maps (proved)

An in-project proof of the statement of `ComplexSLE.External.loewnerMap_conformal`, with the same
type, that imports no `ComplexSLE.External` module. The ingredients are all in-project:

* `ℂ ∖ L_t` is open: `Polar.isOpen_compl_leftHull`;
* `L_t` is bounded: `isBounded_leftHull'`;
* `g_t` extends holomorphically: `exists_differentiableOn_extension_loewnerMap`;
* injectivity: `centeredLoewnerMap_injective` (backward uniqueness);
* the expansion `z (g_t(z) - z) → 2 t`: for a far starting point the solution `γ` stays far from
  the driver, and `h(s) = z (γ(s) - z) - 2 s` has derivative of norm `O(1/‖z‖)`
  (`norm_mul_sub_sub_two_mul_le`).
-/

public section

open scoped NNReal Topology
open Filter

namespace ComplexSLE.Internal.ExternalProofs

/-- **Conformality of `g_t`** (same statement as `ComplexSLE.External.loewnerMap_conformal`, here
proved): for continuous `U` and `t ≥ 0`, `ℂ ∖ L_t` is open, `L_t` is bounded, and `g_t` extends to a
function that is holomorphic and injective on `ℂ ∖ L_t` with `z (g_t(z) - z) → 2t` as `z → ∞`. -/
theorem loewnerMap_conformal (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) :
    IsOpen (leftHull U t)ᶜ ∧ Bornology.IsBounded (leftHull U t) ∧
      ∃ G : ℂ → ℂ, (∀ z : ↥(leftHull U t)ᶜ, G z = loewnerMap U hU t z) ∧
        DifferentiableOn ℂ G (leftHull U t)ᶜ ∧ Set.InjOn G (leftHull U t)ᶜ ∧
        Tendsto (fun z => z * (G z - z)) (Bornology.cobounded ℂ) (𝓝 (2 * (t : ℂ))) := by
  refine ⟨Polar.isOpen_compl_leftHull U hU t, isBounded_leftHull' hU t, ?_⟩
  obtain ⟨G, hG, hGd⟩ := exists_differentiableOn_extension_loewnerMap hU t
  refine ⟨G, hG, hGd, ?_, ?_⟩
  · intro z₁ hz₁ z₂ hz₂ h
    have h' : centeredLoewnerMap U hU t ⟨z₁, hz₁⟩ = centeredLoewnerMap U hU t ⟨z₂, hz₂⟩ := by
      simp only [centeredLoewnerMap, ← hG ⟨z₁, hz₁⟩, ← hG ⟨z₂, hz₂⟩]
      exact congrArg (· - U t) h
    exact congrArg Subtype.val (centeredLoewnerMap_injective hU t h')
  · rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := (t : ℝ))).exists_bound_of_continuousOn
      (f := fun u : ℝ => U u.toNNReal) (hU.comp continuous_real_toNNReal).continuousOn
    have ht0 : (0 : ℝ) ≤ t := t.2
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (by simpa using hM 0 ⟨le_rfl, ht0⟩)
    set R : ℝ := M + 2 + 2 * t + 2 * (2 * t + M) * t / ε + 1 with hR
    have h1 : ∀ᶠ z in Bornology.cobounded ℂ, z ∉ leftHull U t :=
      Bornology.isBounded_def.1 (isBounded_leftHull' hU t)
    have h2 : ∀ᶠ z in Bornology.cobounded ℂ, R ≤ ‖z‖ := eventually_cobounded_le_norm R
    filter_upwards [h1, h2] with z hz hRz
    have hlife : (t : ℝ) ∈ Polar.lifeSet U z := Polar.coe_mem_lifeSet_iff.2 hz
    set γ := Polar.solPath U hU z with hγ
    have hGz : G z = γ t := by
      rw [show G z = loewnerMap U hU t ⟨z, hz⟩ from hG ⟨z, hz⟩, Polar.loewnerMap_eq_solPath hU t hz]
    have hcs : ∀ s ∈ Set.Icc (0 : ℝ) t, γ s ≠ U s.toNNReal ∧
        HasDerivWithinAt γ (2 / (γ s - U s.toNNReal)) (Set.Icc 0 (t : ℝ)) s := by
      intro s hs
      have hsl : s ∈ Polar.lifeSet U z := Polar.mem_lifeSet_of_le hlife hs.1 hs.2
      refine ⟨sub_ne_zero.1 (Polar.fPath_ne_zero hU hsl), ?_⟩
      exact (Polar.hasDerivWithinAt_solPath hU hsl).mono Set.Icc_subset_Ici_self
    have hMt : ∀ u ∈ Set.Icc (0 : ℝ) t, ‖U u.toNNReal‖ ≤ M := fun u hu => by
      simpa using hM u hu
    have hz_far : M + 2 + 2 * t ≤ ‖z‖ := by
      have : 0 ≤ 2 * (2 * (t : ℝ) + M) * t / ε := by positivity
      linarith
    have hest := norm_mul_sub_sub_two_mul_le hU (Polar.solPath_zero hU z) hcs hMt hz_far
    rw [dist_eq_norm, hGz]
    refine lt_of_le_of_lt hest ?_
    set A : ℝ := 2 * (2 * t + M) * t / ε with hA
    have hDpos : A + 3 ≤ ‖z‖ - M - 2 * t := by rw [hR] at hRz; linarith
    have hApos : 0 ≤ A := by positivity
    have hDp : 0 < ‖z‖ - M - 2 * t := by linarith
    rw [div_mul_eq_mul_div, div_lt_iff₀ hDp]
    have : 2 * (2 * (t : ℝ) + M) * t = A * ε := by
      rw [hA]; field_simp
    rw [this]
    nlinarith

end ComplexSLE.Internal.ExternalProofs

end
