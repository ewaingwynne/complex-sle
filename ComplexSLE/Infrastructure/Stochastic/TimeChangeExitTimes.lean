/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Zipper.QuantumZipper.Proofs.ItoLite.OptionalStopping
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Probability.Process.Stopping

/-!
# Exit times of a continuous adapted real process (external-free)

For a process `M : ℝ≥0 → Ω → ℝ` with everywhere continuous paths, adapted to `ℱ`, let
`capExitTime M n` be the first time `t ≤ n` with `|M t| ≥ n`, and `n` if there is none (the hitting
time of the closed set `[n, ∞)` by `|M|`, capped at `n`). Then

* `isStoppingTime_capExitTime`: it is an `ℱ`-stopping time;
* `abs_apply_le_max_of_le_capExitTime`: `|M u| ≤ max n |M 0|` for `u ≤ capExitTime M n`;
* `exists_forall_le_capExitTime`: for every `t` and `ω`, `t ≤ capExitTime M n ω` for all large `n`.

These give the bounded localising sequence used in the time change of a continuous local
martingale: `M^{τ n ∧ capExitTime M n}` is dominated by the integrable `n + |M 0|`.
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory Filter Set

namespace ComplexSLE.Infrastructure

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}

/-- The (capped) exit time of the ball of radius `n`: the hitting time of `{|x| ≥ n}` by `M`
before time `n`, and `n` if there is none. -/
noncomputable def capExitTime (M : ℝ≥0 → Ω → ℝ) (n : ℕ) : Ω → ℝ≥0 :=
  hittingBtwn (fun t ω => |M t ω|) (Set.Ici (n : ℝ)) 0 (n : ℝ≥0)

/-- The exit time of a continuous adapted process is a stopping time. -/
theorem isStoppingTime_capExitTime (hM : StronglyAdapted ℱ M)
    (hMc : ∀ ω, Continuous fun t => M t ω) (n : ℕ) :
    IsStoppingTime ℱ fun ω => (capExitTime M n ω : WithTop ℝ≥0) :=
  QuantumZipper.ItoLite.isStoppingTime_hittingBtwn_of_isClosed
    (U := fun t ω => |M t ω|)
    (fun t => continuous_abs.measurable.comp (hM t).measurable)
    (fun ω => continuous_abs.comp (hMc ω)) isClosed_Ici (n : ℝ≥0)

/-- Before the exit time, `|M| < n`. -/
theorem abs_apply_lt_of_lt_capExitTime {n : ℕ} {ω : Ω} {u : ℝ≥0} (hu : u < capExitTime M n ω) :
    |M u ω| < n := by
  have h := notMem_of_lt_hittingBtwn (u := fun t ω => |M t ω|) (s := Set.Ici (n : ℝ))
    (n := 0) (m := (n : ℝ≥0)) (ω := ω) (k := u) hu zero_le
  simpa only [mem_Ici, not_le] using h

/-- Up to and including the exit time, `|M| ≤ max n |M 0|`. -/
theorem abs_apply_le_max_of_le_capExitTime (hMc : ∀ ω, Continuous fun t => M t ω) (n : ℕ) (ω : Ω)
    {u : ℝ≥0} (hu : u ≤ capExitTime M n ω) : |M u ω| ≤ max (n : ℝ) |M 0 ω| := by
  rcases eq_or_ne u 0 with rfl | hu0
  · exact le_max_right _ _
  · have hupos : 0 < u := pos_iff_ne_zero.2 hu0
    have hsub : Iio u ⊆ {k : ℝ≥0 | |M k ω| ≤ n} := fun k hk =>
      (abs_apply_lt_of_lt_capExitTime (hk.trans_le hu)).le
    have hcl : IsClosed {k : ℝ≥0 | |M k ω| ≤ n} :=
      isClosed_le (continuous_abs.comp (hMc ω)) continuous_const
    have hmem : u ∈ closure (Iio u) := by
      rw [closure_Iio' (a := u) ⟨0, hupos⟩]; exact mem_Iic.2 le_rfl
    exact (hcl.closure_subset_iff.2 hsub hmem).trans (le_max_left _ _)

/-- The exit times eventually exceed any fixed level. -/
theorem exists_forall_le_capExitTime (hMc : ∀ ω, Continuous fun t => M t ω) (ω : Ω) (t : ℝ≥0) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → t ≤ capExitTime M n ω := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_bound_of_continuousOn
    (hMc ω).continuousOn
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (max (t : ℝ) (C + 1))
  refine ⟨N₀, fun n hn => ?_⟩
  have hnN : (max (t : ℝ) (C + 1)) ≤ n := hN₀.trans (by exact_mod_cast hn)
  have htn : t ≤ (n : ℝ≥0) := by
    have : (t : ℝ) ≤ n := (le_max_left _ _).trans hnN
    exact_mod_cast this
  have hB : ∀ u ≤ t, |M u ω| < n := fun u hu => by
    have h1 := hC u ⟨zero_le, hu⟩
    rw [Real.norm_eq_abs] at h1
    linarith [(le_max_right (t : ℝ) (C + 1)).trans hnN]
  unfold capExitTime
  rw [hittingBtwn_def]
  beta_reduce
  split_ifs with h
  · obtain ⟨j, hj, hjK⟩ := h
    refine le_csInf ⟨j, hj, hjK⟩ fun b hb => ?_
    by_contra hbt
    have hbt' : b < t := not_le.1 hbt
    have h1 := hB b hbt'.le
    have h2 : (n : ℝ) ≤ |M b ω| := hb.2
    exact absurd h2 (not_le.2 h1)
  · exact htn

end ComplexSLE.Infrastructure
