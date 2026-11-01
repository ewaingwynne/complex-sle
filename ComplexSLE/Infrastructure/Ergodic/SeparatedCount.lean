/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Counting `ε`-separated points of a sublinearly growing real sequence

Deterministic ingredients of the proof of recurrence of stationary sums:

* `card_le_of_separated`: a finite family of `ε`-separated reals in `[-R, R]` has at most
  `2 R / ε + 2` elements (the map `x ↦ ⌊x / ε⌋` is injective into an interval of integers);
* `tendsto_card_div_of_separated`: if `x n / n → 0` and the set of indices `k` that are
  `ε`-separated from every later `x j` has the property below, then its density in `[0, N)` tends
  to `0`.
-/

public section

open Filter Topology Finset

namespace ComplexSLE.Infrastructure.Ergodic

/-- A finite family of `ε`-separated reals in `[-R, R]` (with `0 ≤ R`) has at most
`2 R / ε + 2` elements. -/
theorem card_le_of_separated {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) (s : Finset ℕ)
    (x : ℕ → ℝ) (hx : ∀ k ∈ s, |x k| ≤ R) (hsep : ∀ j ∈ s, ∀ k ∈ s, j < k → ε ≤ |x k - x j|) :
    (s.card : ℝ) ≤ 2 * R / ε + 2 := by
  have hinj : Set.InjOn (fun k => ⌊x k / ε⌋) (s : Set ℕ) := by
    intro j hj k hk hjk
    by_contra hne
    simp only at hjk
    have key : ∀ a ∈ s, ∀ b ∈ s, a < b → ⌊x a / ε⌋ = ⌊x b / ε⌋ → False := by
      intro a ha b hb hab hfl
      have h1 := Int.abs_sub_lt_one_of_floor_eq_floor hfl
      have h2 : |x b - x a| < ε := by
        have : x b / ε - x a / ε = (x b - x a) / ε := by ring
        have h3 : |x a / ε - x b / ε| = |x b - x a| / ε := by
          rw [← abs_neg, neg_sub, this, abs_div, abs_of_pos hε]
        rw [h3, div_lt_one hε] at h1
        exact h1
      exact absurd (hsep a ha b hb hab) (not_le.2 h2)
    rcases lt_or_gt_of_ne hne with h | h
    · exact key j hj k hk h hjk
    · exact key k hk j hj h hjk.symm
  have hmaps : ∀ k ∈ s, ⌊x k / ε⌋ ∈ Finset.Icc ⌊-R / ε⌋ ⌊R / ε⌋ := by
    intro k hk
    have hk' := abs_le.1 (hx k hk)
    rw [Finset.mem_Icc]
    constructor
    · exact Int.floor_mono (by rw [div_le_div_iff_of_pos_right hε]; exact hk'.1)
    · exact Int.floor_mono (by rw [div_le_div_iff_of_pos_right hε]; exact hk'.2)
  have hcard : s.card ≤ (Finset.Icc ⌊-R / ε⌋ ⌊R / ε⌋).card :=
    Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Int.card_Icc] at hcard
  have hle : ⌊-R / ε⌋ ≤ ⌊R / ε⌋ :=
    Int.floor_mono (by rw [div_le_div_iff_of_pos_right hε]; linarith)
  have h5 : (0 : ℤ) ≤ ⌊R / ε⌋ + 1 - ⌊-R / ε⌋ := by omega
  have hcard' : (s.card : ℤ) ≤ ⌊R / ε⌋ + 1 - ⌊-R / ε⌋ := by
    have := Int.toNat_of_nonneg h5
    omega
  have hcard'' : (s.card : ℝ) ≤ (⌊R / ε⌋ : ℝ) + 1 - (⌊-R / ε⌋ : ℝ) := by
    exact_mod_cast hcard'
  have h1 := Int.floor_le (R / ε)
  have h2 := Int.lt_floor_add_one (-R / ε)
  have h3 : (-R / ε) = -(R / ε) := by ring
  have h4 : 2 * R / ε = R / ε + R / ε := by ring
  have h2' : -(R / ε) < (⌊-R / ε⌋ : ℝ) + 1 := by rw [← h3]; exact h2
  rw [h4]
  linarith

/-- If `x n / n → 0`, then for every `η > 0` there is a constant `C ≥ 0` with
`|x k| ≤ C + η k` for all `k`. -/
theorem exists_bound_of_tendsto_div {x : ℕ → ℝ} (hx : Tendsto (fun n : ℕ => x n / n) atTop (𝓝 0))
    {η : ℝ} (hη : 0 < η) : ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, |x k| ≤ C + η * k := by
  obtain ⟨n0, hn0⟩ := Metric.tendsto_atTop.1 hx η hη
  refine ⟨∑ i ∈ range (n0 + 1), |x i|, Finset.sum_nonneg (fun i _ => abs_nonneg _), fun k => ?_⟩
  have hη' : 0 ≤ η * k := by positivity
  by_cases hk : k < n0 + 1
  · have : |x k| ≤ ∑ i ∈ range (n0 + 1), |x i| :=
      Finset.single_le_sum (f := fun i => |x i|) (fun i _ => abs_nonneg _) (Finset.mem_range.2 hk)
    linarith
  · have hk' : n0 ≤ k := by omega
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have h := hn0 k hk'
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hkpos, div_lt_iff₀ hkpos] at h
    have hC : 0 ≤ ∑ i ∈ range (n0 + 1), |x i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    linarith

/-- **Density of separated indices.** Let `x n / n → 0`, and let `p` be a predicate on indices
such that `x k` is at distance at least `ε > 0` from `x j` whenever `j < k` and `p j`. Then the
proportion of `k < N` with `p k` tends to `0`. -/
theorem tendsto_card_div_of_separated {ε : ℝ} (hε : 0 < ε) (x : ℕ → ℝ) (p : ℕ → Prop)
    [DecidablePred p] (hx : Tendsto (fun n : ℕ => x n / n) atTop (𝓝 0))
    (hsep : ∀ j k, j < k → p j → ε ≤ |x k - x j|) :
    Tendsto (fun N : ℕ => (((Finset.range N).filter p).card : ℝ) / N) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_tendsto_div hx (show 0 < ε * δ / 4 by positivity)
  refine ⟨⌈(2 * C / ε + 2) * 2 / δ⌉₊ + 1, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNge : (2 * C / ε + 2) * 2 / δ < N := by
    have h1 := Nat.le_ceil ((2 * C / ε + 2) * 2 / δ)
    have h2 : ((⌈(2 * C / ε + 2) * 2 / δ⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
    push_cast at h2
    linarith
  -- the cardinality bound
  have hcard : (((Finset.range N).filter p).card : ℝ) ≤
      2 * (C + ε * δ / 4 * N) / ε + 2 := by
    refine card_le_of_separated hε (by positivity) _ x ?_ ?_
    · intro k hk
      have hkN : (k : ℝ) ≤ N := by
        exact_mod_cast (Finset.mem_range.1 (Finset.mem_filter.1 hk).1).le
      have := hC k
      have h0 : 0 ≤ ε * δ / 4 := by positivity
      nlinarith
    · intro j hj k hk hjk
      exact hsep j k hjk (Finset.mem_filter.1 hj).2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hNpos]
  have h3 : 2 * (C + ε * δ / 4 * N) / ε + 2 = (2 * C / ε + 2) + δ / 2 * N := by
    field_simp
    ring
  have h4 : (2 * C / ε + 2) < δ / 2 * N := by
    have := (div_lt_iff₀ hδ).1 hNge
    nlinarith
  linarith

end ComplexSLE.Infrastructure.Ergodic

end
