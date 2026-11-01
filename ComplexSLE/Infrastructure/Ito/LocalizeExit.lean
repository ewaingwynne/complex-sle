/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Zipper.QuantumZipper.Proofs.ItoLite.OptionalStopping
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Exhaustion of an open set and exit times of a continuous adapted process

Source-independent tools for the localisation of Itô's formula.

* `expU D n = ball 0 n \ cthickening (1/(n+1)) Dᶜ` is an increasing sequence of open sets that
  exhausts the open set `D` (`exists_expU_subset`: every compact subset of `D` lies in one of them),
  with compact closures `closure (expU D n) ⊆ expK D n ⊆ D` (`isCompact_expK`, `expK_subset`).
* `exhaustionExitTime X D n`, the first time `≤ n` that the continuous adapted process `X` leaves
  `expU D n`, and `n` if there is none, is a stopping time of any filtration (hitting time of a
  closed set), is `0` when `X 0 ∉ expU D n`, and keeps `X` in `closure (expU D n)` up to that time
  when `X 0 ∈ expU D n`.
-/

@[expose] public section

open scoped NNReal ENNReal Topology
open MeasureTheory Filter Set Metric

namespace ComplexSLE.Infrastructure

section Exhaustion

variable {d : ℕ}

/-- The open sets exhausting an open set `D ⊆ ℝᵈ`. -/
noncomputable def expU (D : Set (Fin d → ℝ)) (n : ℕ) : Set (Fin d → ℝ) :=
  ball (0 : Fin d → ℝ) (n : ℝ) \ cthickening (1 / ((n : ℝ) + 1)) Dᶜ

/-- Compact sets between `closure (expU D n)` and `D`. -/
noncomputable def expK (D : Set (Fin d → ℝ)) (n : ℕ) : Set (Fin d → ℝ) :=
  closedBall (0 : Fin d → ℝ) (n : ℝ) \ thickening (1 / ((n : ℝ) + 1)) Dᶜ

theorem isOpen_expU (D : Set (Fin d → ℝ)) (n : ℕ) : IsOpen (expU D n) :=
  isOpen_ball.sdiff isClosed_cthickening

theorem isClosed_expK (D : Set (Fin d → ℝ)) (n : ℕ) : IsClosed (expK D n) :=
  isClosed_closedBall.sdiff isOpen_thickening

theorem isCompact_expK (D : Set (Fin d → ℝ)) (n : ℕ) : IsCompact (expK D n) :=
  (isCompact_closedBall (0 : Fin d → ℝ) (n : ℝ)).of_isClosed_subset (isClosed_expK D n)
    sdiff_subset

theorem expU_subset_expK (D : Set (Fin d → ℝ)) (n : ℕ) : expU D n ⊆ expK D n :=
  fun _ ⟨hb, hc⟩ => ⟨ball_subset_closedBall hb, fun ht => hc (thickening_subset_cthickening _ _ ht)⟩

theorem closure_expU_subset (D : Set (Fin d → ℝ)) (n : ℕ) : closure (expU D n) ⊆ expK D n :=
  closure_minimal (expU_subset_expK D n) (isClosed_expK D n)

theorem expK_subset (D : Set (Fin d → ℝ)) (n : ℕ) : expK D n ⊆ D := by
  intro x hx
  by_contra hxD
  exact hx.2 (self_subset_thickening (by positivity) _ hxD)

theorem expU_subset (D : Set (Fin d → ℝ)) (n : ℕ) : expU D n ⊆ D :=
  (expU_subset_expK D n).trans (expK_subset D n)

theorem expU_mono (D : Set (Fin d → ℝ)) : Monotone (expU D) := by
  intro n m hnm x hx
  refine ⟨ball_subset_ball (by exact_mod_cast hnm) hx.1, fun hxm => hx.2 ?_⟩
  refine cthickening_mono ?_ _ hxm
  have : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
  exact one_div_le_one_div_of_le (by positivity) this

theorem subset_iUnion_expU {D : Set (Fin d → ℝ)} (hD : IsOpen D) : D ⊆ ⋃ n, expU D n := by
  intro x hxD
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.1 hD x hxD
  obtain ⟨n, hn⟩ := exists_nat_gt (max ‖x‖ (1 / ε))
  rw [mem_iUnion]
  refine ⟨n, ?_, fun hxc => ?_⟩
  · rw [mem_ball_zero_iff]
    exact lt_of_le_of_lt (le_max_left _ _) hn
  · have hlt : 1 / ((n : ℝ) + 1) < ε := by
      have h1 : 1 / ε < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hε] at h1
      nlinarith
    obtain ⟨y, hyE, hxy⟩ := mem_thickening_iff.1
      (cthickening_subset_thickening' hε hlt _ hxc)
    exact hyE (hεD (by rwa [mem_ball, dist_comm]))

/-- Every compact subset of the open set `D` lies in one of the sets `expU D n`. -/
theorem exists_expU_subset {D C : Set (Fin d → ℝ)} (hD : IsOpen D) (hC : IsCompact C)
    (hCD : C ⊆ D) : ∃ n, C ⊆ expU D n :=
  hC.elim_directed_cover (expU D) (isOpen_expU D) (hCD.trans (subset_iUnion_expU hD))
    (expU_mono D).directed_le

end Exhaustion

section ExitTime

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m} {d : ℕ}
  {X : ℝ≥0 → Ω → (Fin d → ℝ)}

/-- The first time `≤ n` at which `X` is outside `expU D n`, and `n` if there is none. -/
noncomputable def exhaustionExitTime (X : ℝ≥0 → Ω → (Fin d → ℝ)) (D : Set (Fin d → ℝ))
    (n : ℕ) : Ω → ℝ≥0 :=
  hittingBtwn X (expU D n)ᶜ 0 (n : ℝ≥0)

/-- The exit time of a continuous adapted process is a stopping time (hitting time of a closed
set). -/
theorem isStoppingTime_exhaustionExitTime (hX : StronglyAdapted ℱ X)
    (hXc : ∀ ω, Continuous fun t => X t ω) (D : Set (Fin d → ℝ)) (n : ℕ) :
    IsStoppingTime ℱ fun ω => (exhaustionExitTime X D n ω : WithTop ℝ≥0) :=
  QuantumZipper.ItoLite.isStoppingTime_hittingBtwn_of_isClosed (U := X)
    (fun t => (hX t).measurable) hXc (isOpen_expU D n).isClosed_compl (n : ℝ≥0)

theorem exhaustionExitTime_le (D : Set (Fin d → ℝ)) (n : ℕ) (ω : Ω) :
    exhaustionExitTime X D n ω ≤ n :=
  hittingBtwn_le ω

/-- Strictly before the exit time, the process is in `expU D n`. -/
theorem mem_expU_of_lt_exhaustionExitTime {D : Set (Fin d → ℝ)} {n : ℕ} {ω : Ω} {u : ℝ≥0}
    (hu : u < exhaustionExitTime X D n ω) : X u ω ∈ expU D n := by
  have h := notMem_of_lt_hittingBtwn (u := X) (s := (expU D n)ᶜ) (n := 0) (m := (n : ℝ≥0))
    (ω := ω) (k := u) hu zero_le
  simpa using h

/-- If the process starts in `expU D n`, it stays in `closure (expU D n)` up to the exit time. -/
theorem mem_closure_of_le_exhaustionExitTime (hXc : ∀ ω, Continuous fun t => X t ω)
    {D : Set (Fin d → ℝ)} {n : ℕ} {ω : Ω} (h0 : X 0 ω ∈ expU D n) {u : ℝ≥0}
    (hu : u ≤ exhaustionExitTime X D n ω) : X u ω ∈ closure (expU D n) := by
  rcases hu.lt_or_eq with hlt | heq
  · exact subset_closure (mem_expU_of_lt_exhaustionExitTime hlt)
  · rcases eq_or_ne u 0 with rfl | hu0
    · exact subset_closure h0
    · have hpos : (0 : ℝ≥0) < u := pos_iff_ne_zero.2 hu0
      have hne : (𝓝[<] u).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
      refine mem_closure_of_tendsto (b := 𝓝[<] u)
        (((hXc ω).tendsto u).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact mem_expU_of_lt_exhaustionExitTime (heq ▸ hs)

/-- If the process starts outside `expU D n`, the exit time is `0`. -/
theorem exhaustionExitTime_eq_zero {D : Set (Fin d → ℝ)} {n : ℕ} {ω : Ω} (h0 : X 0 ω ∉ expU D n) :
    exhaustionExitTime X D n ω = 0 :=
  le_antisymm (hittingBtwn_le_of_mem (le_refl 0) zero_le h0) zero_le

/-- The exit time is at least `t ≤ n` when the process stays in `expU D n` during `[0, t]`. -/
theorem le_exhaustionExitTime {D : Set (Fin d → ℝ)} {n : ℕ} {ω : Ω} {t : ℝ≥0} (htn : t ≤ n)
    (h : ∀ u ≤ t, X u ω ∈ expU D n) : t ≤ exhaustionExitTime X D n ω := by
  unfold exhaustionExitTime hittingBtwn
  split_ifs with hex
  · refine le_csInf (by obtain ⟨j, hj, hjK⟩ := hex; exact ⟨j, hj, hjK⟩) fun j hj => ?_
    by_contra hjt
    rw [not_le] at hjt
    exact hj.2 (h j hjt.le)
  · exact htn

end ExitTime

end ComplexSLE.Infrastructure

end
