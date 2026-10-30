/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Data.Finset.Sort

/-!
# Finite monotone chains through a finite set of times

For a finite set `K ⊆ ℝ≥0`, `exists_chain K` gives a monotone sequence `p : ℕ → ℝ≥0` with
`p 0 = 0`, constant from index `M` on, whose values on `0, …, M` are exactly `{0} ∪ K` (sorted).
It is used to reduce statements about finitely many times of a process with independent
increments to statements about a finite family of independent increments.
-/

public section

open scoped NNReal

namespace ComplexSLE.Internal

/-- **A monotone chain through a finite set.** For every finite `K ⊆ ℝ≥0` there are `p : ℕ → ℝ≥0`
and `M : ℕ` with: `p` monotone, `p 0 = 0`, every element of `K` is some `p i` with `i ≤ M`, all
values `p n` lie in `{0} ∪ K`, and `p n ≤ p M` for all `n`. -/
theorem exists_chain (K : Finset ℝ≥0) :
    ∃ (p : ℕ → ℝ≥0) (M : ℕ), Monotone p ∧ p 0 = 0 ∧ (∀ s ∈ K, ∃ i, i ≤ M ∧ p i = s) ∧
      (∀ n, p n ∈ insert 0 K) ∧ ∀ n, p n ≤ p M := by
  classical
  set K' : Finset ℝ≥0 := insert 0 K with hK'
  have hpos : 0 < K'.card := Finset.card_pos.2 ⟨0, Finset.mem_insert_self _ _⟩
  set e := K'.orderEmbOfFin rfl with he
  let p : ℕ → ℝ≥0 := fun n => e ⟨min n (K'.card - 1), by omega⟩
  have hmono : Monotone p := fun m n hmn => by
    apply e.monotone
    change min m (K'.card - 1) ≤ min n (K'.card - 1)
    omega
  have hp0 : p 0 = 0 := by
    have h1 : p 0 = K'.min' ⟨0, Finset.mem_insert_self _ _⟩ := by
      have := Finset.orderEmbOfFin_zero (s := K') rfl hpos
      simpa [p] using this
    rw [h1]
    exact le_antisymm (Finset.min'_le _ _ (Finset.mem_insert_self _ _)) zero_le
  have hmem : ∀ n, p n ∈ K' := fun n => by
    exact Finset.orderEmbOfFin_mem K' rfl ⟨min n (K'.card - 1), by omega⟩
  refine ⟨p, K'.card - 1, hmono, hp0, ?_, hmem, ?_⟩
  · intro s hs
    have hs' : s ∈ Set.range e := by
      rw [he, Finset.range_orderEmbOfFin]
      exact Finset.mem_insert_of_mem hs
    obtain ⟨j, hj⟩ := hs'
    refine ⟨j.val, by omega, ?_⟩
    have : min j.val (K'.card - 1) = j.val := by omega
    simp only [p, this]
    exact hj
  · intro n
    apply e.monotone
    change min n (K'.card - 1) ≤ min (K'.card - 1) (K'.card - 1)
    omega

end ComplexSLE.Internal

end
