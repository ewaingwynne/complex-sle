/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsDiffusionSolution
public import ComplexSLE.Infrastructure.Stochastic.CondShift
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Conditioning a diffusion solution on the past (the Markov property at a fixed time)

For `X` solving the martingale problem `IsDiffusionSolution ℱ α β X P` with continuous
coefficients and everywhere-continuous paths, a deterministic time `s : ℝ≥0` and `A ∈ ℱ s` with
`P A ≠ 0`, the shifted process `Y t = X (s + t)` solves the same martingale problem for the
shifted filtration `t ↦ ℱ (s + t)` under `P[|A]` (`isDiffusionSolution_cond_shift`).

With `M_t = X_t - X_0 - ∫₀ᵗ α(X)` and `I_t = ∫₀ᵗ β(X)²`, the process of `Y` is
`M_{s+t} - M_s`, and `(M_{s+t} - M_s)² - (I_{s+t} - I_s) = (Q_{s+t} - Q_s) - 2 M_s (M_{s+t} - M_s)`
with `Q = M² - I`; the cross term is a continuous local martingale because `M_s` is
`ℱ_s`-measurable (`IsContLocalMartingale.initial_mul`).

`isDiffusionSolution_sub_const` records that the property is invariant under `X ↦ X - c` when
`α` and `β²` are `c`-periodic (used with `c = nπ`).

No external input is used.
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}

/-! ### The path integral -/

/-- The path integral of a continuous path is continuous in the upper limit. -/
theorem continuous_pathIntegral {ξ : ℝ≥0 → Ω → ℝ} {ω : Ω} (h : Continuous fun t => ξ t ω) :
    Continuous fun t => pathIntegral ξ t ω := by
  unfold pathIntegral
  have hc : Continuous fun r : ℝ => ξ (Real.toNNReal r) ω := h.comp continuous_real_toNNReal
  exact (intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) 0).comp
    NNReal.continuous_coe

/-- The path integral of the time-shifted path. -/
theorem pathIntegral_shift {ξ : ℝ≥0 → Ω → ℝ} {ω : Ω} (h : Continuous fun t => ξ t ω)
    (s t : ℝ≥0) :
    pathIntegral (fun u ω => ξ (s + u) ω) t ω =
      pathIntegral ξ (s + t) ω - pathIntegral ξ s ω := by
  unfold pathIntegral
  set φ : ℝ → ℝ := fun r => ξ (Real.toNNReal r) ω with hφ
  have hc : Continuous φ := h.comp continuous_real_toNNReal
  have h1 : ∫ u in (0 : ℝ)..(t : ℝ), ξ (s + Real.toNNReal u) ω =
      ∫ u in (0 : ℝ)..(t : ℝ), φ ((s : ℝ) + u) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le t.coe_nonneg] at hu
    simp only [hφ]
    congr 2
    rw [Real.toNNReal_add s.coe_nonneg hu.1, Real.toNNReal_coe]
  rw [h1, intervalIntegral.integral_comp_add_left φ (s : ℝ), NNReal.coe_add, add_zero]
  exact (intervalIntegral.integral_interval_sub_left (a := 0) (b := (s : ℝ) + t) (c := (s : ℝ))
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)).symm

/-! ### Conditioning on the past -/

/-- **Markov property at a fixed time, martingale form.** Let `X` solve the martingale problem
for continuous coefficients `α, β` with everywhere-continuous paths. For `A ∈ ℱ s` with
`P A ≠ 0`, the shifted process `t ↦ X (s + t)` (started at `X s`) solves the same martingale
problem with respect to the shifted filtration `t ↦ ℱ (s + t)` under `P[|A]`. -/
theorem isDiffusionSolution_cond_shift [IsFiniteMeasure P] {α β : ℝ → ℝ} (hα : Continuous α)
    (hβ : Continuous β) {X : ℝ≥0 → Ω → ℝ} (hX : IsDiffusionSolution ℱ α β X P)
    (hXc : ∀ ω, Continuous fun t => X t ω) (s : ℝ≥0) {A : Set Ω} (hA : MeasurableSet[ℱ s] A)
    (hA0 : P A ≠ 0) :
    IsDiffusionSolution (shiftFiltration ℱ s) α β (fun t ω => X (s + t) ω) P[|A] := by
  obtain ⟨hprog, -, hM, hQ⟩ := hX
  -- the processes of `X`
  set Mx : ℝ≥0 → Ω → ℝ := fun t ω =>
    X t ω - X 0 ω - pathIntegral (fun u ω => α (X u ω)) t ω with hMx
  set Ix : ℝ≥0 → Ω → ℝ := fun t ω => pathIntegral (fun u ω => β (X u ω) ^ 2) t ω with hIx
  have hMxc : ∀ ω, Continuous fun t => Mx t ω := fun ω =>
    ((hXc ω).sub continuous_const).sub (continuous_pathIntegral (hα.comp (hXc ω)))
  have hIxc : ∀ ω, Continuous fun t => Ix t ω := fun ω =>
    continuous_pathIntegral ((hβ.comp (hXc ω)).pow 2)
  have hQc : ∀ ω, Continuous fun t => Mx t ω ^ 2 - Ix t ω := fun ω =>
    ((hMxc ω).pow 2).sub (hIxc ω)
  -- the conditioned local martingales
  have hM' := hM.shift_cond s hA hA0
  have hQ' : IsContLocalMartingale (shiftFiltration ℱ s)
      (fun t ω => (Mx (s + t) ω ^ 2 - Ix (s + t) ω) - (Mx s ω ^ 2 - Ix s ω)) P[|A] :=
    hQ.shift_cond s hA hA0
  have hξ : StronglyMeasurable[shiftFiltration ℱ s 0] fun ω => 2 * Mx s ω :=
    (stronglyMeasurable_const.mul
      ((hM.1.stronglyAdapted s).mono (ℱ.mono (add_zero s).ge)))
  have hcross := hM'.initial_mul (fun ω => by simp) hξ
  have hMc' : ∀ ω, Continuous fun t => Mx (s + t) ω - Mx s ω := fun ω =>
    ((hMxc ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have hQc' : ∀ ω, Continuous fun t =>
      (Mx (s + t) ω ^ 2 - Ix (s + t) ω) - (Mx s ω ^ 2 - Ix s ω) := fun ω =>
    ((hQc ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have hsub := hQ'.sub hcross hQc' fun ω => continuous_const.mul (hMc' ω)
  -- identification of the shifted processes
  have hpiα : ∀ ω t, pathIntegral (fun u ω => α (X (s + u) ω)) t ω =
      pathIntegral (fun u ω => α (X u ω)) (s + t) ω - pathIntegral (fun u ω => α (X u ω)) s ω :=
    fun ω t => pathIntegral_shift (ξ := fun u ω => α (X u ω)) (hα.comp (hXc ω)) s t
  have hpiβ : ∀ ω t, pathIntegral (fun u ω => β (X (s + u) ω) ^ 2) t ω =
      pathIntegral (fun u ω => β (X u ω) ^ 2) (s + t) ω -
        pathIntegral (fun u ω => β (X u ω) ^ 2) s ω :=
    fun ω t => pathIntegral_shift (ξ := fun u ω => β (X u ω) ^ 2) ((hβ.comp (hXc ω)).pow 2) s t
  have hMid : ∀ ω t, X (s + t) ω - X (s + 0) ω -
      pathIntegral (fun u ω => α (X (s + u) ω)) t ω = Mx (s + t) ω - Mx s ω := by
    intro ω t
    simp only [hMx, hpiα, add_zero]
    ring
  refine ⟨isStronglyProgressive_shift hprog s,
    ae_of_all _ fun ω => (hXc ω).comp (continuous_const.add continuous_id), ?_, ?_⟩
  · convert hM' using 1
    funext t ω
    exact hMid ω t
  · convert hsub using 1
    funext t ω
    simp only [Pi.sub_apply]
    rw [hMid ω t]
    simp only [hMx, hIx, hpiβ] at *
    ring

/-! ### Invariance under a periodic shift of the state -/

/-- If `α` and `β²` are `c`-periodic, `X - c` solves the martingale problem whenever `X` does. -/
theorem isDiffusionSolution_sub_const {α β : ℝ → ℝ} {X : ℝ≥0 → Ω → ℝ} (c : ℝ)
    (hα : ∀ v, α (v - c) = α v) (hβ : ∀ v, β (v - c) ^ 2 = β v ^ 2)
    (hX : IsDiffusionSolution ℱ α β X P) :
    IsDiffusionSolution ℱ α β (fun t ω => X t ω - c) P := by
  obtain ⟨hprog, hcont, hM, hQ⟩ := hX
  refine ⟨hprog.sub (isStronglyProgressive_const ℱ c), ?_, ?_, ?_⟩
  · filter_upwards [hcont] with ω h using h.sub continuous_const
  · convert hM using 1
    funext t ω
    simp only [hα]
    ring
  · convert hQ using 1
    funext t ω
    simp only [hα, hβ]
    ring

end ComplexSLE

end
