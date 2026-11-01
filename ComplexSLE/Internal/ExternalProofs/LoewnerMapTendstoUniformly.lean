/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.LoewnerMap
import ComplexSLE.Internal.ExternalProofs.StabilityExplicit
import ComplexSLE.Internal.ExternalProofs.UniformLowerBound
import ComplexSLE.Internal.Hull.ConnectedNoExt

/-!
# Convergence of Loewner maps under driver convergence (proved)

An in-project proof of the statement of `ComplexSLE.External.loewnerMap_tendstoUniformly`, with the
same type, that imports no `ComplexSLE.External` module.

Let `η₀` be the uniform lower bound of `‖f_s(z)‖` on `[0, T]` for `z` at distance `≥ ε` from `L_T`
(`exists_uniform_lower_bound`). Such `z` lie outside `L_t` for `t ≤ T`. Apply the explicit stability
estimate (`stability_explicit`) at time `T` with `K = 4/η₀²`: if `‖V n - U‖ ≤ δ` on `[0, T]` with
`δ < η₀/4 · e^{-K T}` then `z` is alive for `V n` on `[0, T]` and `‖f^{V n}_s(z) - f^U_s(z)‖ ≤
e^{K T} δ`; since `g = f + driver`, `‖g^{V n}_t(z) - g^U_t(z)‖ ≤ (e^{K T} + 1) δ`.
-/

public section

open scoped NNReal Topology
open Filter

namespace ComplexSLE.Internal.ExternalProofs

open ComplexSLE.Internal.Polar

/-- **Loewner convergence** (same statement as `ComplexSLE.External.loewnerMap_tendstoUniformly`,
here proved): if continuous drivers `V n → U` locally uniformly, then for every `T`, `ε > 0`,
eventually every `z` at distance `≥ ε` from `L_T` lies outside the hulls `L^{V n}_t`, `t ≤ T`, and
`g^{V n}_t(z) → g_t(z)` uniformly in such `(t, z)`. -/
theorem loewnerMap_tendstoUniformly (U : ℝ≥0 → ℂ) (hU : Continuous U) (V : ℕ → ℝ≥0 → ℂ)
    (hV : ∀ n, Continuous (V n)) (hconv : TendstoLocallyUniformly V U atTop) (T : ℝ≥0)
    (ε : ℝ) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ t ≤ T, ∀ z : ℂ, ε ≤ Metric.infDist z (leftHull U T) →
      ∃ (h₁ : z ∈ (leftHull (V n) t)ᶜ) (h₂ : z ∈ (leftHull U t)ᶜ),
        ‖loewnerMap (V n) (hV n) t ⟨z, h₁⟩ - loewnerMap U hU t ⟨z, h₂⟩‖ < η := by
  obtain ⟨η₀, hη₀, hlow⟩ := exists_uniform_lower_bound hU T hε
  set K : ℝ := 4 / η₀ ^ 2 with hK
  have hT0 : (0 : ℝ) ≤ T := T.2
  set ρ : ℝ := η₀ / 4 * Real.exp (-(K * T)) with hρ
  have hρpos : 0 < ρ := by positivity
  have hexp1 : 1 ≤ Real.exp (K * T) := Real.one_le_exp (by positivity)
  set δ : ℝ := min (ρ / 2) (η / (2 * (Real.exp (K * T) + 1))) with hδ
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  have hδρ : δ < ρ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδη : (Real.exp (K * T) + 1) * δ < η := by
    have h1 : δ ≤ η / (2 * (Real.exp (K * T) + 1)) := min_le_right _ _
    have h2 : 0 < Real.exp (K * T) + 1 := by positivity
    calc (Real.exp (K * T) + 1) * δ ≤ (Real.exp (K * T) + 1) *
          (η / (2 * (Real.exp (K * T) + 1))) := by gcongr
      _ = η / 2 := by field_simp
      _ < η := by linarith
  have hunif : TendstoUniformlyOn V U atTop (Set.Icc (0 : ℝ≥0) T) :=
    tendstoLocallyUniformly_iff_forall_isCompact.1 hconv _ isCompact_Icc
  have hev := Metric.tendstoUniformlyOn_iff.1 hunif δ hδpos
  filter_upwards [hev] with n hn t ht z hz
  have hzL : z ∉ leftHull U T := notMem_leftHull_of_le_infDist hε hz
  obtain ⟨hlife, hbd⟩ := hlow z hz
  have hdist : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖U s.toNNReal - V n s.toNNReal‖ ≤ δ := by
    intro s hs
    have hsT : s.toNNReal ∈ Set.Icc (0 : ℝ≥0) T :=
      ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hs.2⟩
    have := hn s.toNNReal hsT
    rw [dist_eq_norm] at this
    exact this.le
  obtain ⟨hlife', hbound⟩ := stability_explicit hU hlife hη₀ hbd (V n) (hV n) δ hδρ hdist
  have htT : (t : ℝ) ≤ T := by exact_mod_cast ht
  have h₁ : z ∈ (leftHull (V n) t)ᶜ :=
    coe_mem_lifeSet_iff.1 (mem_lifeSet_of_le hlife' t.2 htT)
  have h₂ : z ∈ (leftHull U t)ᶜ := fun h => hzL (leftHull_mono ht h)
  refine ⟨h₁, h₂, ?_⟩
  rw [loewnerMap_eq_solPath (hV n) t h₁, loewnerMap_eq_solPath hU t h₂]
  have hf := hbound t ⟨t.2, htT⟩
  have hdt := hdist t ⟨t.2, htT⟩
  simp only [fPath, Real.toNNReal_coe] at hf hdt
  have e : Polar.solPath (V n) (hV n) z t - Polar.solPath U hU z t =
      ((Polar.solPath (V n) (hV n) z t - V n t) - (Polar.solPath U hU z t - U t)) +
        (V n t - U t) := by ring
  rw [e]
  refine lt_of_le_of_lt (norm_add_le _ _) ?_
  have hd2 : ‖V n t - U t‖ ≤ δ := by rw [norm_sub_rev]; exact hdt
  have hf' : ‖(Polar.solPath (V n) (hV n) z t - V n t) - (Polar.solPath U hU z t - U t)‖ ≤
      Real.exp (K * T) * δ := hf
  calc _ ≤ Real.exp (K * T) * δ + δ := add_le_add hf' hd2
    _ = (Real.exp (K * T) + 1) * δ := by ring
    _ < η := hδη

end ComplexSLE.Internal.ExternalProofs

end
