/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Uniform partitions and Riemann sums against an integrable density

Deterministic analysis for the bounded core of Itô's formula (`ComplexSLE.Infrastructure.Ito`).

* `ptR s t m k = s + (t - s) k / (m + 1)` is the `k`-th point of the uniform partition of `[s, t]`
  into `m + 1` pieces; `pt` is the same point as a nonnegative real.
* `tendsto_dist_ptR_le`: along the partitions, the oscillation of a continuous path over every piece
  tends to zero (uniform continuity on `[s, t]`).
* `tendsto_sum_mul_integral_ptR`: Riemann sums `∑ₖ ψ(tₖ) ∫_{tₖ}^{tₖ₊₁} a` converge to `∫ₛᵗ ψ a`
  for continuous `ψ` and interval integrable `a`.
* `sum_abs_integral_ptR_le`: `∑ₖ |∫_{tₖ}^{tₖ₊₁} a| ≤ ∫ₛᵗ |a|`.
-/

@[expose] public section

open scoped NNReal Topology
open MeasureTheory Filter Set

namespace ComplexSLE.Infrastructure.Ito

/-- The `k`-th point of the uniform partition of `[s, t]` into `m + 1` pieces (real version). -/
noncomputable def ptR (s t : ℝ) (m k : ℕ) : ℝ := s + (t - s) * k / (m + 1)

/-- The `k`-th point of the uniform partition of `[s, t]` into `m + 1` pieces (`ℝ≥0` version). -/
noncomputable def pt (s t : ℝ≥0) (m k : ℕ) : ℝ≥0 := Real.toNNReal (ptR s t m k)

theorem ptR_zero (s t : ℝ) (m : ℕ) : ptR s t m 0 = s := by simp [ptR]

theorem ptR_last (s t : ℝ) (m : ℕ) : ptR s t m (m + 1) = t := by
  have : ((m : ℝ) + 1) ≠ 0 := by positivity
  simp only [ptR]; push_cast; field_simp; ring

theorem ptR_succ_sub (s t : ℝ) (m k : ℕ) : ptR s t m (k + 1) - ptR s t m k = (t - s) / (m + 1) := by
  simp only [ptR]; push_cast; ring

theorem ptR_mono {s t : ℝ} (hst : s ≤ t) (m : ℕ) : Monotone (ptR s t m) := by
  intro j k hjk
  simp only [ptR]
  have h1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have h2 : (j : ℝ) ≤ k := by exact_mod_cast hjk
  have : (t - s) * j / (m + 1) ≤ (t - s) * k / (m + 1) := by
    apply div_le_div_of_nonneg_right _ h1.le
    exact mul_le_mul_of_nonneg_left h2 (sub_nonneg.2 hst)
  linarith

theorem ptR_mem_Icc {s t : ℝ} (hst : s ≤ t) (m : ℕ) {k : ℕ} (hk : k ≤ m + 1) :
    ptR s t m k ∈ Icc s t := by
  refine ⟨?_, ?_⟩
  · simpa [ptR_zero] using ptR_mono hst m (Nat.zero_le k)
  · simpa [ptR_last] using ptR_mono hst m hk

theorem coe_pt {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) {k : ℕ} (hk : k ≤ m + 1) :
    (pt s t m k : ℝ) = ptR s t m k := by
  have h := ptR_mem_Icc (s := (s : ℝ)) (t := (t : ℝ)) (by exact_mod_cast hst) m hk
  exact Real.coe_toNNReal _ ((NNReal.coe_nonneg s).trans h.1)

theorem pt_zero (s t : ℝ≥0) (m : ℕ) : pt s t m 0 = s := by
  simp [pt, ptR_zero]

theorem pt_last (s t : ℝ≥0) (m : ℕ) : pt s t m (m + 1) = t := by
  simp [pt, ptR_last]

theorem pt_mono {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) : Monotone (pt s t m) := by
  intro j k hjk
  exact Real.toNNReal_le_toNNReal (ptR_mono (by exact_mod_cast hst) m hjk)

theorem le_pt {s t : ℝ≥0} (hst : s ≤ t) (m k : ℕ) : s ≤ pt s t m k := by
  simpa [pt_zero] using pt_mono hst m (Nat.zero_le k)

/-! ### Oscillation along the partitions -/

/-- For a continuous path, the oscillation over the pieces of the uniform partitions tends to
`0`. -/
theorem eventually_dist_ptR_le {E : Type*} [PseudoMetricSpace E] {ψ : ℝ → E} {s t : ℝ}
    (hψ : ContinuousOn ψ (Icc s t)) (hst : s ≤ t) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ k, k ≤ m → ∀ u ∈ Icc (ptR s t m k) (ptR s t m (k + 1)),
      dist (ψ u) (ψ (ptR s t m k)) ≤ ε := by
  have huc : UniformContinuousOn ψ (Icc s t) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hψ
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt ((t - s) / δ)
  filter_upwards [eventually_ge_atTop M] with m hm k hk u hu
  have hmem1 := ptR_mem_Icc hst m (Nat.succ_le_succ hk)
  have hmem2 := ptR_mem_Icc hst m (hk.trans (Nat.le_succ m))
  have hmemu : u ∈ Icc s t := ⟨hmem2.1.trans hu.1, hu.2.trans hmem1.2⟩
  refine (hδε _ hmemu _ hmem2 ?_).le
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hu.1)]
  have h3 : u - ptR s t m k ≤ ptR s t m (k + 1) - ptR s t m k := by linarith [hu.2]
  refine lt_of_le_of_lt h3 ?_
  rw [ptR_succ_sub, div_lt_iff₀ (by positivity)]
  have h1 : (M : ℝ) ≤ m := by exact_mod_cast hm
  have h2 : (t - s) < M * δ := (div_lt_iff₀ hδ).1 hM
  nlinarith

theorem eventually_dist_ptR_succ_le {E : Type*} [PseudoMetricSpace E] {ψ : ℝ → E} {s t : ℝ}
    (hψ : ContinuousOn ψ (Icc s t)) (hst : s ≤ t) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ k, k ≤ m →
      dist (ψ (ptR s t m (k + 1))) (ψ (ptR s t m k)) ≤ ε := by
  filter_upwards [eventually_dist_ptR_le hψ hst hε] with m hm k hk
  exact hm k hk _ ⟨ptR_mono hst m (Nat.le_succ k), le_rfl⟩

/-! ### Integrals over the pieces -/

theorem intervalIntegrable_ptR {a : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (ha : IntervalIntegrable a volume s t) (m : ℕ) {k : ℕ} (hk : k ≤ m) :
    IntervalIntegrable a volume (ptR s t m k) (ptR s t m (k + 1)) := by
  refine ha.mono_set ?_
  rw [uIcc_of_le hst, uIcc_of_le (ptR_mono hst m (Nat.le_succ k))]
  exact Icc_subset_Icc (ptR_mem_Icc hst m (hk.trans (Nat.le_succ m))).1
    (ptR_mem_Icc hst m (Nat.succ_le_succ hk)).2

/-- The integral over `[s, t]` is the sum of the integrals over the pieces. -/
theorem sum_integral_ptR {a : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (ha : IntervalIntegrable a volume s t) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), ∫ u in ptR s t m k..ptR s t m (k + 1), a u =
      ∫ u in s..t, a u := by
  have := intervalIntegral.sum_integral_adjacent_intervals (f := a) (μ := volume)
    (a := ptR s t m) (n := m + 1)
    (fun k hk => intervalIntegrable_ptR hst ha m (Nat.lt_succ_iff.1 hk))
  rw [this, ptR_zero, ptR_last]

/-- `∑ₖ |∫_{tₖ}^{tₖ₊₁} a| ≤ ∫ₛᵗ |a|`. -/
theorem sum_abs_integral_ptR_le {a : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (ha : IntervalIntegrable a volume s t) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), |∫ u in ptR s t m k..ptR s t m (k + 1), a u| ≤
      ∫ u in s..t, |a u| := by
  rw [← sum_integral_ptR hst ha.abs m]
  refine Finset.sum_le_sum fun k hk => ?_
  exact intervalIntegral.abs_integral_le_integral_abs (ptR_mono hst m (Nat.le_succ k))

/-- `|∫_{tₖ}^{tₖ₊₁} a| ≤ ∫ₛᵗ |a|` for a single piece. -/
theorem abs_integral_ptR_le {a : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (ha : IntervalIntegrable a volume s t) (m k : ℕ) (hk : k ≤ m) :
    |∫ u in ptR s t m k..ptR s t m (k + 1), a u| ≤ ∫ u in s..t, |a u| := by
  refine le_trans ?_ (sum_abs_integral_ptR_le hst ha m)
  exact Finset.single_le_sum (f := fun k => |∫ u in ptR s t m k..ptR s t m (k + 1), a u|)
    (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))

/-! ### Riemann sums -/

/-- **Riemann sums against an integrable density.** -/
theorem tendsto_sum_mul_integral_ptR {ψ a : ℝ → ℝ} (hψ : Continuous ψ) {s t : ℝ} (hst : s ≤ t)
    (ha : IntervalIntegrable a volume s t) :
    Tendsto (fun m : ℕ => ∑ k ∈ Finset.range (m + 1),
      ψ (ptR s t m k) * ∫ u in ptR s t m k..ptR s t m (k + 1), a u) atTop
      (𝓝 (∫ u in s..t, ψ u * a u)) := by
  set I : ℝ := ∫ u in s..t, |a u| with hI
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg hst fun u _ => abs_nonneg _
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε' : 0 < ε / (I + 1) := div_pos hε (by linarith)
  obtain ⟨M, hM⟩ := eventually_atTop.1 (eventually_dist_ptR_le hψ.continuousOn hst hε')
  refine ⟨M, fun m hm => ?_⟩
  have hint : ∀ k ≤ m, IntervalIntegrable (fun u => ψ u * a u) volume (ptR s t m k)
      (ptR s t m (k + 1)) := fun k hk =>
    (intervalIntegrable_ptR hst ha m hk).continuousOn_mul hψ.continuousOn
  have hsum : ∑ k ∈ Finset.range (m + 1), ∫ u in ptR s t m k..ptR s t m (k + 1), ψ u * a u =
      ∫ u in s..t, ψ u * a u := by
    have := intervalIntegral.sum_integral_adjacent_intervals (f := fun u => ψ u * a u)
      (μ := volume) (a := ptR s t m) (n := m + 1)
      (fun k hk => hint k (Nat.lt_succ_iff.1 hk))
    rw [this, ptR_zero, ptR_last]
  rw [Real.dist_eq, ← hsum, ← Finset.sum_sub_distrib]
  have hpiece : ∀ k ∈ Finset.range (m + 1),
      |ψ (ptR s t m k) * (∫ u in ptR s t m k..ptR s t m (k + 1), a u) -
        ∫ u in ptR s t m k..ptR s t m (k + 1), ψ u * a u| ≤
      ε / (I + 1) * ∫ u in ptR s t m k..ptR s t m (k + 1), |a u| := by
    intro k hk
    have hk' : k ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have hle := ptR_mono hst m (Nat.le_succ k)
    have h1 : ψ (ptR s t m k) * (∫ u in ptR s t m k..ptR s t m (k + 1), a u) -
        ∫ u in ptR s t m k..ptR s t m (k + 1), ψ u * a u =
        ∫ u in ptR s t m k..ptR s t m (k + 1), (ψ (ptR s t m k) - ψ u) * a u := by
      have e1 : ψ (ptR s t m k) * (∫ u in ptR s t m k..ptR s t m (k + 1), a u) =
          ∫ u in ptR s t m k..ptR s t m (k + 1), ψ (ptR s t m k) * a u :=
        (intervalIntegral.integral_const_mul _ _).symm
      rw [e1, ← intervalIntegral.integral_sub
        ((intervalIntegrable_ptR hst ha m hk').const_mul _) (hint k hk')]
      congr 1; funext u; ring
    rw [h1, ← intervalIntegral.integral_const_mul]
    have hn := intervalIntegral.norm_integral_le_of_norm_le
      (f := fun u => (ψ (ptR s t m k) - ψ u) * a u) (g := fun u => ε / (I + 1) * |a u|)
      (a := ptR s t m k) (b := ptR s t m (k + 1)) (μ := volume) hle
      (Filter.Eventually.of_forall fun u hu => ?_)
      ((intervalIntegrable_ptR hst ha m hk').abs.const_mul _)
    · simpa [Real.norm_eq_abs] using hn
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      have := hM m hm k hk' u ⟨hu.1.le, hu.2⟩
      rw [Real.dist_eq, abs_sub_comm] at this
      exact this
  calc |∑ k ∈ Finset.range (m + 1),
        (ψ (ptR s t m k) * (∫ u in ptR s t m k..ptR s t m (k + 1), a u) -
        ∫ u in ptR s t m k..ptR s t m (k + 1), ψ u * a u)|
      ≤ ∑ k ∈ Finset.range (m + 1), |ψ (ptR s t m k) *
          (∫ u in ptR s t m k..ptR s t m (k + 1), a u) -
          ∫ u in ptR s t m k..ptR s t m (k + 1), ψ u * a u| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (m + 1), ε / (I + 1) *
          ∫ u in ptR s t m k..ptR s t m (k + 1), |a u| := Finset.sum_le_sum hpiece
    _ = ε / (I + 1) * I := by
        rw [← Finset.mul_sum, sum_integral_ptR hst ha.abs m]
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith

end ComplexSLE.Infrastructure.Ito

end
