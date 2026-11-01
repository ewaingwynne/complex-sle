/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Ito.Partition
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Deterministic limit of the drift part of the discretized Itô expansion

For continuous `gᵢ`, `Hᵢⱼ`, `Mᵢ` and interval integrable `aᵢ`, `qᵢⱼ` on `[s, t]`, the drift sums

`∑ᵢ ∑ₖ gᵢ(tₖ) ∫_{tₖ}^{tₖ₊₁} aᵢ + ½ ∑ᵢⱼ ∑ₖ Hᵢⱼ(tₖ)(∫ qᵢⱼ + ΔMᵢ ∫ aⱼ + ΔMⱼ ∫ aᵢ + ∫ aᵢ ∫ aⱼ)`

over the uniform partitions of `[s, t]` converge to `∫ₛᵗ (∑ gᵢ aᵢ + ½ ∑ Hᵢⱼ qᵢⱼ)`
(`tendsto_driftSum`) and are uniformly bounded in terms of `∫|aᵢ|`, `∫|qᵢⱼ|` and the oscillation of
`Mᵢ` (`abs_driftSum_le`). The cross terms vanish in the limit because the oscillation of a
continuous path over the pieces tends to zero while `∑ₖ |∫_{tₖ}^{tₖ₊₁} b| ≤ ∫|b|`
(`tendsto_sum_cross`).
-/

@[expose] public section

open scoped NNReal Topology
open MeasureTheory Filter Set

namespace ComplexSLE.Infrastructure.Ito

/-- The integral of `a` over the `k`-th piece of the partition. -/
noncomputable def pieceInt (a : ℝ → ℝ) (s t : ℝ) (m k : ℕ) : ℝ :=
  ∫ u in ptR s t m k..ptR s t m (k + 1), a u

theorem tendsto_sum_cross {H φ b : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hH : ContinuousOn H (Icc s t)) (hφ : ContinuousOn φ (Icc s t))
    (hb : IntervalIntegrable b volume s t) :
    Tendsto (fun m : ℕ => ∑ k ∈ Finset.range (m + 1), H (ptR s t m k) *
      ((φ (ptR s t m (k + 1)) - φ (ptR s t m k)) * pieceInt b s t m k)) atTop (𝓝 0) := by
  obtain ⟨HB, hHB⟩ := isCompact_Icc.exists_bound_of_continuousOn hH
  have hHB0 : 0 ≤ HB := (norm_nonneg _).trans (hHB s ⟨le_rfl, hst⟩)
  set I : ℝ := ∫ u in s..t, |b u| with hI
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg hst fun u _ => abs_nonneg _
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hpos : 0 < (HB + 1) * (I + 1) := by positivity
  have hε' : 0 < ε / ((HB + 1) * (I + 1)) := div_pos hε hpos
  obtain ⟨M, hM⟩ := eventually_atTop.1 (eventually_dist_ptR_succ_le hφ hst hε')
  refine ⟨M, fun m hm => ?_⟩
  rw [Real.dist_eq, sub_zero]
  have hterm : ∀ k ∈ Finset.range (m + 1), |H (ptR s t m k) *
      ((φ (ptR s t m (k + 1)) - φ (ptR s t m k)) * pieceInt b s t m k)| ≤
      HB * (ε / ((HB + 1) * (I + 1))) * |pieceInt b s t m k| := by
    intro k hk
    have hk' : k ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    rw [abs_mul, abs_mul]
    have h1 : |H (ptR s t m k)| ≤ HB := by
      have := hHB _ (ptR_mem_Icc hst m (hk'.trans (Nat.le_succ m)))
      simpa [Real.norm_eq_abs] using this
    have h2 : |φ (ptR s t m (k + 1)) - φ (ptR s t m k)| ≤ ε / ((HB + 1) * (I + 1)) := by
      have := hM m hm k hk'
      rwa [Real.dist_eq] at this
    calc |H (ptR s t m k)| * (|φ (ptR s t m (k + 1)) - φ (ptR s t m k)| *
          |pieceInt b s t m k|) ≤ HB * (ε / ((HB + 1) * (I + 1)) * |pieceInt b s t m k|) :=
        mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 (abs_nonneg _)) (by positivity) hHB0
      _ = _ := by ring
  calc |∑ k ∈ Finset.range (m + 1), H (ptR s t m k) *
        ((φ (ptR s t m (k + 1)) - φ (ptR s t m k)) * pieceInt b s t m k)|
      ≤ ∑ k ∈ Finset.range (m + 1), |H (ptR s t m k) *
        ((φ (ptR s t m (k + 1)) - φ (ptR s t m k)) * pieceInt b s t m k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (m + 1), HB * (ε / ((HB + 1) * (I + 1))) *
        |pieceInt b s t m k| := Finset.sum_le_sum hterm
    _ = HB * (ε / ((HB + 1) * (I + 1))) *
        ∑ k ∈ Finset.range (m + 1), |pieceInt b s t m k| := by rw [Finset.mul_sum]
    _ ≤ HB * (ε / ((HB + 1) * (I + 1))) * I := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact sum_abs_integral_ptR_le hst hb m
    _ < ε := by
        have : HB * I < (HB + 1) * (I + 1) := by nlinarith
        calc HB * (ε / ((HB + 1) * (I + 1))) * I = ε * (HB * I) / ((HB + 1) * (I + 1)) := by
              field_simp
          _ < ε := by
              rw [div_lt_iff₀ hpos]
              nlinarith


theorem intervalIntegrable_sum' {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {a b : ℝ}
    (h : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun u => ∑ i ∈ s, f i u) volume a b := by
  convert IntervalIntegrable.sum s h using 1
  ext u
  simp

section Drift

variable {n : ℕ}

/-- The drift part `W'` of the discretized Itô expansion over the `(m + 1)`-piece partition. -/
noncomputable def driftSum (s t : ℝ) (m : ℕ) (g : Fin n → ℝ → ℝ) (H : Fin n → Fin n → ℝ → ℝ)
    (a : Fin n → ℝ → ℝ) (q : Fin n → Fin n → ℝ → ℝ) (M : Fin n → ℝ → ℝ) : ℝ :=
  ∑ i, ∑ k ∈ Finset.range (m + 1), g i (ptR s t m k) * pieceInt (a i) s t m k +
    (1 / 2) * ∑ i, ∑ j, ∑ k ∈ Finset.range (m + 1), H i j (ptR s t m k) *
      (pieceInt (q i j) s t m k +
        (M i (ptR s t m (k + 1)) - M i (ptR s t m k)) * pieceInt (a j) s t m k +
        (M j (ptR s t m (k + 1)) - M j (ptR s t m k)) * pieceInt (a i) s t m k +
        pieceInt (a i) s t m k * pieceInt (a j) s t m k)

theorem pieceInt_eq_sub {a : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (ha : IntervalIntegrable a volume s t) (m k : ℕ) (hk : k ≤ m) :
    pieceInt a s t m k = (∫ u in s..ptR s t m (k + 1), a u) - ∫ u in s..ptR s t m k, a u := by
  have h1 : IntervalIntegrable a volume s (ptR s t m (k + 1)) := by
    refine ha.mono_set ?_
    rw [uIcc_of_le hst, uIcc_of_le (ptR_mem_Icc hst m (Nat.succ_le_succ hk)).1]
    exact Icc_subset_Icc le_rfl (ptR_mem_Icc hst m (Nat.succ_le_succ hk)).2
  have h2 : IntervalIntegrable a volume s (ptR s t m k) := by
    refine ha.mono_set ?_
    rw [uIcc_of_le hst, uIcc_of_le (ptR_mem_Icc hst m (hk.trans (Nat.le_succ m))).1]
    exact Icc_subset_Icc le_rfl (ptR_mem_Icc hst m (hk.trans (Nat.le_succ m))).2
  unfold pieceInt
  rw [intervalIntegral.integral_interval_sub_left h1 h2]

/-- The drift sums converge to `∫ₛᵗ (∑ gᵢ aᵢ + ½ ∑ Hᵢⱼ qᵢⱼ)`. -/
theorem tendsto_driftSum {s t : ℝ} (hst : s ≤ t) {g : Fin n → ℝ → ℝ} {H : Fin n → Fin n → ℝ → ℝ}
    {a : Fin n → ℝ → ℝ} {q : Fin n → Fin n → ℝ → ℝ} {M : Fin n → ℝ → ℝ}
    (hg : ∀ i, Continuous (g i)) (hH : ∀ i j, Continuous (H i j))
    (ha : ∀ i, IntervalIntegrable (a i) volume s t)
    (hq : ∀ i j, IntervalIntegrable (q i j) volume s t) (hM : ∀ i, Continuous (M i)) :
    Tendsto (fun m : ℕ => driftSum s t m g H a q M) atTop
      (𝓝 (∫ u in s..t, (∑ i, g i u * a i u +
        (1 / 2) * ∑ i, ∑ j, H i j u * q i j u))) := by
  have hga : ∀ i, IntervalIntegrable (fun u => g i u * a i u) volume s t := fun i =>
    (ha i).continuousOn_mul (hg i).continuousOn
  have hHq : ∀ i j, IntervalIntegrable (fun u => H i j u * q i j u) volume s t := fun i j =>
    (hq i j).continuousOn_mul (hH i j).continuousOn
  have hΦ : ∀ i, ContinuousOn (fun u => ∫ x in s..u, a i x) (Icc s t) := fun i => by
    have := intervalIntegral.continuousOn_primitive_interval' (ha i)
      (left_mem_uIcc (a := s) (b := t))
    rwa [uIcc_of_le hst] at this
  -- the limit
  have hlim : ∫ u in s..t, (∑ i, g i u * a i u + (1 / 2) * ∑ i, ∑ j, H i j u * q i j u) =
      (∑ i, ∫ u in s..t, g i u * a i u) +
        (1 / 2) * ∑ i, ∑ j, ∫ u in s..t, H i j u * q i j u := by
    have h1 : IntervalIntegrable (fun u => ∑ i, g i u * a i u) volume s t :=
      intervalIntegrable_sum' Finset.univ (fun i _ => hga i)
    have h2 : ∀ i, IntervalIntegrable (fun u => ∑ j, H i j u * q i j u) volume s t := fun i =>
      intervalIntegrable_sum' Finset.univ (fun j _ => hHq i j)
    have h3 : IntervalIntegrable (fun u => ∑ i, ∑ j, H i j u * q i j u) volume s t :=
      intervalIntegrable_sum' Finset.univ (fun i _ => h2 i)
    rw [intervalIntegral.integral_add h1 (h3.const_mul _),
      intervalIntegral.integral_finsetSum fun i _ => hga i, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum fun i _ => h2 i]
    congr 3
    funext i
    rw [intervalIntegral.integral_finsetSum fun j _ => hHq i j]
  rw [hlim]
  have hP1 : Tendsto (fun m : ℕ => ∑ i, ∑ k ∈ Finset.range (m + 1),
      g i (ptR s t m k) * pieceInt (a i) s t m k) atTop
      (𝓝 (∑ i, ∫ u in s..t, g i u * a i u)) :=
    tendsto_finsetSum _ fun i _ => tendsto_sum_mul_integral_ptR (hg i) hst (ha i)
  unfold driftSum
  refine hP1.add (Tendsto.const_mul _ (tendsto_finsetSum _ fun i _ =>
    tendsto_finsetSum _ fun j _ => ?_))
  have hsplit : ∀ m : ℕ, ∑ k ∈ Finset.range (m + 1), H i j (ptR s t m k) *
      (pieceInt (q i j) s t m k +
        (M i (ptR s t m (k + 1)) - M i (ptR s t m k)) * pieceInt (a j) s t m k +
        (M j (ptR s t m (k + 1)) - M j (ptR s t m k)) * pieceInt (a i) s t m k +
        pieceInt (a i) s t m k * pieceInt (a j) s t m k) =
      ∑ k ∈ Finset.range (m + 1), H i j (ptR s t m k) * pieceInt (q i j) s t m k +
      (∑ k ∈ Finset.range (m + 1), H i j (ptR s t m k) *
        ((M i (ptR s t m (k + 1)) - M i (ptR s t m k)) * pieceInt (a j) s t m k) +
      (∑ k ∈ Finset.range (m + 1), H i j (ptR s t m k) *
        ((M j (ptR s t m (k + 1)) - M j (ptR s t m k)) * pieceInt (a i) s t m k) +
      ∑ k ∈ Finset.range (m + 1), H i j (ptR s t m k) *
        (((∫ x in s..ptR s t m (k + 1), a i x) - ∫ x in s..ptR s t m k, a i x) *
          pieceInt (a j) s t m k))) := by
    intro m
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    rw [← pieceInt_eq_sub hst (ha i) m k hk']
    ring
  simp only [hsplit]
  have h0 := ((tendsto_sum_cross hst (hH i j).continuousOn (hM i).continuousOn (ha j)).add
    ((tendsto_sum_cross hst (hH i j).continuousOn (hM j).continuousOn (ha i)).add
      (tendsto_sum_cross hst (hH i j).continuousOn (hΦ i) (ha j))))
  have h1 : Tendsto (fun m : ℕ => ∑ k ∈ Finset.range (m + 1),
      H i j (ptR s t m k) * pieceInt (q i j) s t m k) atTop
      (𝓝 (∫ u in s..t, H i j u * q i j u)) :=
    tendsto_sum_mul_integral_ptR (hH i j) hst (hq i j)
  simpa using h1.add h0

/-- A uniform bound for the drift sums. -/
theorem abs_driftSum_le {s t : ℝ} (hst : s ≤ t) {g : Fin n → ℝ → ℝ}
    {H : Fin n → Fin n → ℝ → ℝ} {a : Fin n → ℝ → ℝ} {q : Fin n → Fin n → ℝ → ℝ}
    {M : Fin n → ℝ → ℝ} {L₁ L₂ C C' : ℝ}
    (hgb : ∀ i, ∀ u ∈ Icc s t, |g i u| ≤ L₁) (hHb : ∀ i j, ∀ u ∈ Icc s t, |H i j u| ≤ L₂)
    (ha : ∀ i, IntervalIntegrable (a i) volume s t)
    (hq : ∀ i j, IntervalIntegrable (q i j) volume s t)
    (haC : ∀ i, ∫ u in s..t, |a i u| ≤ C) (hqC : ∀ i j, ∫ u in s..t, |q i j u| ≤ C)
    (hMb : ∀ i, ∀ u ∈ Icc s t, ∀ v ∈ Icc s t, |M i u - M i v| ≤ C') (m : ℕ) :
    |driftSum s t m g H a q M| ≤ ∑ _i : Fin n, L₁ * C +
      (1 / 2) * ∑ _i : Fin n, ∑ _j : Fin n, L₂ * (C + C' * C + C' * C + C * C) := by
  have hpt : ∀ k, k ≤ m + 1 → ptR s t m k ∈ Icc s t := fun k hk => ptR_mem_Icc hst m hk
  -- single pieces are bounded by `C`
  have hJa : ∀ i k, k ≤ m → |pieceInt (a i) s t m k| ≤ C := fun i k hk =>
    (abs_integral_ptR_le hst (ha i) m k hk).trans (haC i)
  have hsumJa : ∀ i, ∑ k ∈ Finset.range (m + 1), |pieceInt (a i) s t m k| ≤ C := fun i =>
    (sum_abs_integral_ptR_le hst (ha i) m).trans (haC i)
  have hsumJq : ∀ i j, ∑ k ∈ Finset.range (m + 1), |pieceInt (q i j) s t m k| ≤ C := fun i j =>
    (sum_abs_integral_ptR_le hst (hq i j) m).trans (hqC i j)
  have hk_mem : ∀ k ∈ Finset.range (m + 1), k ≤ m := fun k hk =>
    Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  unfold driftSum
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hL₁ : 0 ≤ L₁ := (abs_nonneg _).trans (hgb i s ⟨le_rfl, hst⟩)
    calc ∑ k ∈ Finset.range (m + 1), |g i (ptR s t m k) * pieceInt (a i) s t m k|
        ≤ ∑ k ∈ Finset.range (m + 1), L₁ * |pieceInt (a i) s t m k| := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hgb i _ (hpt k ((hk_mem k hk).trans (Nat.le_succ m))))
            (abs_nonneg _)
      _ = L₁ * ∑ k ∈ Finset.range (m + 1), |pieceInt (a i) s t m k| := by rw [Finset.mul_sum]
      _ ≤ L₁ * C := mul_le_mul_of_nonneg_left (hsumJa i) hL₁
  · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hL₂ : 0 ≤ L₂ := (abs_nonneg _).trans (hHb i j s ⟨le_rfl, hst⟩)
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hJa i 0 (Nat.zero_le m))
    have hC'0 : 0 ≤ C' := by
      have := hMb i s ⟨le_rfl, hst⟩ s ⟨le_rfl, hst⟩
      simpa using this
    have hterm : ∀ k ∈ Finset.range (m + 1), |H i j (ptR s t m k) *
        (pieceInt (q i j) s t m k +
          (M i (ptR s t m (k + 1)) - M i (ptR s t m k)) * pieceInt (a j) s t m k +
          (M j (ptR s t m (k + 1)) - M j (ptR s t m k)) * pieceInt (a i) s t m k +
          pieceInt (a i) s t m k * pieceInt (a j) s t m k)| ≤
        L₂ * (|pieceInt (q i j) s t m k| + C' * |pieceInt (a j) s t m k| +
          C' * |pieceInt (a i) s t m k| + C * |pieceInt (a j) s t m k|) := by
      intro k hk
      have hk' := hk_mem k hk
      rw [abs_mul]
      refine mul_le_mul (hHb i j _ (hpt k (hk'.trans (Nat.le_succ m)))) ?_ (abs_nonneg _) hL₂
      have h1 := hMb i _ (hpt (k + 1) (Nat.succ_le_succ hk')) _ (hpt k (hk'.trans (Nat.le_succ m)))
      have h2 := hMb j _ (hpt (k + 1) (Nat.succ_le_succ hk')) _ (hpt k (hk'.trans (Nat.le_succ m)))
      have h3 : |pieceInt (a i) s t m k * pieceInt (a j) s t m k| ≤
          C * |pieceInt (a j) s t m k| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hJa i k hk') (abs_nonneg _)
      calc _ ≤ |pieceInt (q i j) s t m k| +
              |(M i (ptR s t m (k + 1)) - M i (ptR s t m k)) * pieceInt (a j) s t m k| +
              |(M j (ptR s t m (k + 1)) - M j (ptR s t m k)) * pieceInt (a i) s t m k| +
              |pieceInt (a i) s t m k * pieceInt (a j) s t m k| := by
            refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
              (add_le_add ((abs_add_le _ _).trans (add_le_add le_rfl le_rfl)) le_rfl)) le_rfl)
        _ ≤ _ := by
            rw [abs_mul, abs_mul]
            have := mul_le_mul_of_nonneg_right h1 (abs_nonneg (pieceInt (a j) s t m k))
            have := mul_le_mul_of_nonneg_right h2 (abs_nonneg (pieceInt (a i) s t m k))
            linarith
    calc _ ≤ ∑ k ∈ Finset.range (m + 1), L₂ * (|pieceInt (q i j) s t m k| +
          C' * |pieceInt (a j) s t m k| + C' * |pieceInt (a i) s t m k| +
          C * |pieceInt (a j) s t m k|) := Finset.sum_le_sum hterm
      _ = L₂ * (∑ k ∈ Finset.range (m + 1), |pieceInt (q i j) s t m k| +
          C' * ∑ k ∈ Finset.range (m + 1), |pieceInt (a j) s t m k| +
          C' * ∑ k ∈ Finset.range (m + 1), |pieceInt (a i) s t m k| +
          C * ∑ k ∈ Finset.range (m + 1), |pieceInt (a j) s t m k|) := by
          rw [← Finset.mul_sum]
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ L₂ * (C + C' * C + C' * C + C * C) := by
          refine mul_le_mul_of_nonneg_left ?_ hL₂
          have := hsumJq i j
          have := hsumJa j
          have := hsumJa i
          have h1 := mul_le_mul_of_nonneg_left (hsumJa j) hC'0
          have h2 := mul_le_mul_of_nonneg_left (hsumJa i) hC'0
          have h3 := mul_le_mul_of_nonneg_left (hsumJa j) hC0
          linarith

end Drift

end ComplexSLE.Infrastructure.Ito

end
