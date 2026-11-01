/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Ito.Setting

/-!
# The martingale part of the discretized Itô expansion

Under `BoundedSetting`, the martingale part `zTerm` of a one-step expansion between `u ≤ v` is a.s.
bounded and has mean zero on every `B ∈ ℱ u` (`BoundedSetting.nullOn_zTerm`): each summand is a
bounded `ℱ u`-measurable factor times an increment of one of the martingales `Mⁱ`, `Nⁱʲ`. Hence
`zSum` has mean zero on every `B ∈ ℱ s` (`BoundedSetting.setIntegral_zSum_eq_zero`).
-/

@[expose] public section

open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Infrastructure.Ito

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {n : ℕ} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m0}
  {X A : ℝ≥0 → Ω → (Fin n → ℝ)} {Q : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ} {C : ℝ}
  {F : (Fin n → ℝ) → ℝ}

/-- The martingale part of a one-step expansion has mean zero on every `B ∈ ℱ u`. -/
theorem BoundedSetting.nullOn_zTerm [IsProbabilityMeasure P] (h : BoundedSetting ℱ P X A Q C)
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) {u v : ℝ≥0} (huv : u ≤ v) {B : Set Ω}
    (hB : MeasurableSet[ℱ u] B) : NullOn P B (zTerm F X A Q u v) := by
  obtain ⟨L₀, L₁, L₂, -, hL₁, hL₂, -⟩ := exists_bounds hF hFc
  have hXu := h.stronglyMeasurable_X u
  have hMu : ∀ i, StronglyMeasurable[ℱ u] (Mp X A i u) := fun i => (h.mart_M i).stronglyMeasurable u
  have hgm : ∀ i, StronglyMeasurable[ℱ u] fun ω => gF F i (X u ω) := fun i =>
    (continuous_gF hF i).comp_stronglyMeasurable hXu
  have hHm : ∀ i j, StronglyMeasurable[ℱ u] fun ω => HF F i j (X u ω) := fun i j =>
    (continuous_HF hF i j).comp_stronglyMeasurable hXu
  have hMb : ∀ᵐ ω ∂P, ∀ i t, |Mp X A i t ω| ≤ C := h.bd_M
  have hNb := h.abs_Np_le
  unfold zTerm
  refine NullOn.add (NullOn.finset_sum _ fun i _ => ?_) (NullOn.const_mul _
    (NullOn.finset_sum _ fun i _ => NullOn.finset_sum _ fun j _ =>
      NullOn.sub (NullOn.sub ?_ ?_) ?_))
  · exact NullOn.of_martingale (h.mart_M i) huv (hgm i) (L := L₁)
      (Filter.Eventually.of_forall fun ω => hL₁ i _)
      (by filter_upwards [hMb] with ω hω using hω i u)
      (by filter_upwards [hMb] with ω hω using hω i v)
      hB
  · exact NullOn.of_martingale (h.mart_N i j) huv (hHm i j) (L := L₂)
      (Filter.Eventually.of_forall fun ω => hL₂ i j _) (K := C ^ 2 + C)
      (by filter_upwards [hNb] with ω hω using hω i j u)
      (by filter_upwards [hNb] with ω hω using hω i j v) hB
  · refine NullOn.of_martingale (h.mart_M i) huv ((hHm i j).mul (hMu j)) (L := L₂ * C)
      ?_ (by filter_upwards [hMb] with ω hω using hω i u)
      (by filter_upwards [hMb] with ω hω using hω i v) hB
    filter_upwards [hMb] with ω hω
    rw [abs_mul]
    exact mul_le_mul (hL₂ i j _) (hω j u) (abs_nonneg _) ((abs_nonneg _).trans (hL₂ i j (X u ω)))
  · refine NullOn.of_martingale (h.mart_M j) huv ((hHm i j).mul (hMu i)) (L := L₂ * C)
      ?_ (by filter_upwards [hMb] with ω hω using hω j u)
      (by filter_upwards [hMb] with ω hω using hω j v) hB
    filter_upwards [hMb] with ω hω
    rw [abs_mul]
    exact mul_le_mul (hL₂ i j _) (hω i u) (abs_nonneg _) ((abs_nonneg _).trans (hL₂ i j (X u ω)))

/-- The martingale part of the discretized expansion is a.s. bounded and has mean zero on every
`B ∈ ℱ s`. -/
theorem BoundedSetting.nullOn_zSum [IsProbabilityMeasure P]
    (h : BoundedSetting ℱ P X A Q C) (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) {B : Set Ω} (hB : MeasurableSet[ℱ s] B) :
    NullOn P B (zSum F X A Q s t m) :=
  NullOn.finset_sum (P := P) (B := B) (Finset.range (m + 1))
    (f := fun k => zTerm F X A Q (pt s t m k) (pt s t m (k + 1))) fun k _ =>
      h.nullOn_zTerm hF hFc (pt_mono hst m (Nat.le_succ k)) (ℱ.mono (le_pt hst m k) _ hB)

theorem BoundedSetting.setIntegral_zSum_eq_zero [IsProbabilityMeasure P]
    (h : BoundedSetting ℱ P X A Q C) (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) {B : Set Ω} (hB : MeasurableSet[ℱ s] B) :
    ∫ ω in B, zSum F X A Q s t m ω ∂P = 0 :=
  (h.nullOn_zSum hF hFc hst m hB).2

end ComplexSLE.Infrastructure.Ito

end
