/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Ito.Setting

/-!
# The drift part of the discretized Itô expansion

Pathwise (for a path with locally integrable `A`, `Q`) the drift sums `wSum` converge to the drift
integral `∫ₛᵗ itoDrift` (`tendsto_wSum_of_paths`) and are bounded uniformly in `m`
(`abs_wSum_le_of_paths`); both statements are the deterministic results of `Riemann.lean`
applied to the paths of the process.
-/

@[expose] public section

open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Infrastructure.Ito

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {n : ℕ} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m0}
  {X A : ℝ≥0 → Ω → (Fin n → ℝ)} {Q : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ} {C : ℝ}
  {F : (Fin n → ℝ) → ℝ}

theorem intervalIntegrable_toNNReal_mono {f : ℝ → ℝ} {t : ℝ≥0}
    (hf : IntervalIntegrable f volume 0 (t : ℝ)) {s t' : ℝ≥0} (hs : s ≤ t') (ht' : t' ≤ t) :
    IntervalIntegrable f volume (s : ℝ) (t' : ℝ) := by
  refine hf.mono_set ?_
  rw [uIcc_of_le t.coe_nonneg, uIcc_of_le (NNReal.coe_le_coe.2 hs)]
  exact Icc_subset_Icc s.coe_nonneg (NNReal.coe_le_coe.2 ht')

theorem integral_abs_le_of_le {f : ℝ → ℝ} {t : ℝ≥0} (hf : IntervalIntegrable f volume 0 (t : ℝ))
    {s : ℝ≥0} (hst : s ≤ t) :
    ∫ x in (s : ℝ)..(t : ℝ), |f x| ≤ ∫ x in (0 : ℝ)..(t : ℝ), |f x| := by
  have h0s : IntervalIntegrable f volume 0 (s : ℝ) := by
    refine hf.mono_set ?_
    rw [uIcc_of_le t.coe_nonneg, uIcc_of_le s.coe_nonneg]
    exact Icc_subset_Icc le_rfl (NNReal.coe_le_coe.2 hst)
  have h1 : IntervalIntegrable f volume (s : ℝ) (t : ℝ) :=
    intervalIntegrable_toNNReal_mono hf hst le_rfl
  have := intervalIntegral.integral_add_adjacent_intervals h0s.abs h1.abs
  have hnn : 0 ≤ ∫ x in (0 : ℝ)..(s : ℝ), |f x| :=
    intervalIntegral.integral_nonneg s.coe_nonneg fun x _ => abs_nonneg _
  linarith

/-- The drift sums converge to the drift integral along a path with locally integrable `A`, `Q`. -/
theorem tendsto_wSum_of_paths (hF : ContDiff ℝ 2 F) (hX : ∀ ω, Continuous fun t => X t ω)
    {ω : Ω}
    (hA : ∀ i (t : ℝ≥0), IntervalIntegrable (fun s : ℝ => A s.toNNReal ω i) volume 0 t)
    (hQ : ∀ i j (t : ℝ≥0), IntervalIntegrable (fun s : ℝ => Q s.toNNReal ω i j) volume 0 t)
    {s t : ℝ≥0} (hst : s ≤ t) :
    Tendsto (fun m : ℕ => wSum F X A Q s t m ω) atTop
      (𝓝 (∫ u in (s : ℝ)..(t : ℝ), itoDrift F X A Q u.toNNReal ω)) := by
  have hcX : Continuous fun u : ℝ => X u.toNNReal ω := (hX ω).comp continuous_real_toNNReal
  have hAt : ∀ i, IntervalIntegrable (fun u : ℝ => A u.toNNReal ω i) volume (s : ℝ) (t : ℝ) :=
    fun i => intervalIntegrable_toNNReal_mono (hA i t) hst le_rfl
  have hQt : ∀ i j, IntervalIntegrable (fun u : ℝ => Q u.toNNReal ω i j) volume (s : ℝ) (t : ℝ) :=
    fun i j => intervalIntegrable_toNNReal_mono (hQ i j t) hst le_rfl
  have hMc : ∀ i, Continuous fun u : ℝ => Mp X A i u.toNNReal ω := fun i => by
    have h1 : Continuous fun t : ℝ≥0 => X t ω i := (continuous_apply i).comp (hX ω)
    have h2 := continuous_pathIntegral (ξ := fun s ω => A s ω i) (hA i)
    exact ((h1.sub continuous_const).sub h2).comp continuous_real_toNNReal
  rw [show (fun m : ℕ => wSum F X A Q s t m ω) = fun m => driftSum (s : ℝ) (t : ℝ) m
      (fun i u => gF F i (X u.toNNReal ω)) (fun i j u => HF F i j (X u.toNNReal ω))
      (fun i u => A u.toNNReal ω i) (fun i j u => Q u.toNNReal ω i j)
      (fun i u => Mp X A i u.toNNReal ω) from funext fun m => wSum_eq_driftSum hst m ω]
  exact tendsto_driftSum (NNReal.coe_le_coe.2 hst) (fun i => (continuous_gF hF i).comp hcX)
    (fun i j => (continuous_HF hF i j).comp hcX) hAt hQt hMc

/-- The drift sums are bounded uniformly in `m` and in the path. -/
theorem abs_wSum_le_of_paths {L₁ L₂ : ℝ} (hL₁ : ∀ i x, |gF F i x| ≤ L₁)
    (hL₂ : ∀ i j x, |HF F i j x| ≤ L₂) {ω : Ω}
    (hA : ∀ i (t : ℝ≥0), IntervalIntegrable (fun s : ℝ => A s.toNNReal ω i) volume 0 t)
    (hQ : ∀ i j (t : ℝ≥0), IntervalIntegrable (fun s : ℝ => Q s.toNNReal ω i j) volume 0 t)
    (hAC : ∀ i (t : ℝ≥0), ∫ s in (0 : ℝ)..(t : ℝ), |A s.toNNReal ω i| ≤ C)
    (hQC : ∀ i j (t : ℝ≥0), ∫ s in (0 : ℝ)..(t : ℝ), |Q s.toNNReal ω i j| ≤ C)
    (hMb : ∀ i (t : ℝ≥0), |Mp X A i t ω| ≤ C) {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) :
    |wSum F X A Q s t m ω| ≤ ∑ _i : Fin n, L₁ * C +
      (1 / 2) * ∑ _i : Fin n, ∑ _j : Fin n, L₂ * (C + (C + C) * C + (C + C) * C + C * C) := by
  rw [wSum_eq_driftSum hst]
  refine abs_driftSum_le (NNReal.coe_le_coe.2 hst) (fun i u _ => hL₁ i _)
    (fun i j u _ => hL₂ i j _) (fun i => intervalIntegrable_toNNReal_mono (hA i t) hst le_rfl)
    (fun i j => intervalIntegrable_toNNReal_mono (hQ i j t) hst le_rfl)
    (fun i => (integral_abs_le_of_le (hA i t) hst).trans (hAC i t))
    (fun i j => (integral_abs_le_of_le (hQ i j t) hst).trans (hQC i j t)) ?_ m
  intro i u hu v hv
  exact (abs_sub _ _).trans (add_le_add (hMb i _) (hMb i _))

end ComplexSLE.Infrastructure.Ito

end
