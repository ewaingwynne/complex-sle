/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.DisconnectsFromInfinity
public import ComplexSLE.Infrastructure.Planar.Disconnect
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Separation.CompletelyRegular

/-!
# A countable criterion for "a point is disconnected from `∞` by a closed set"

Let `e = denseSeq ℂ` be a fixed dense sequence in `ℂ`. For a closed nonempty `K ⊆ ℂ` and an index
`i` with `e i ∉ K`, the *chain-reachable* indices `reachIdx K i n` are defined by recursion on the
number `n` of steps: `i` is reachable in `0` steps, and `j` is reachable in `n + 1` steps if it is
reachable in `n` steps, or if there is `k` reachable in `n` steps with
`‖e k - e j‖ < dist(e k, K)` (the ball `B(e k, dist(e k, K))` is a connected subset of `Kᶜ`).

`discCrit K z` says that for some `i`, `z ∈ B(e i, dist(e i, K))` and the chain-reachable points
of `e i` are bounded. The main result is

* `discAt_iff_discCrit`: for a closed nonempty `K`,
  `z ∉ K ∧ DisconnectsFromInfinity K {z} ↔ discCrit K z`.

The proof shows that the union `O` of the balls `B(e j, dist(e j, K))` over the reachable `j` is
both open and relatively closed in `Kᶜ` (`isOpen_compl_inter_compl_reachBalls`), so contains the
component of `e i` in `Kᶜ` (`connectedComponentIn_subset_reachBalls`); the other inclusion is
`mem_connectedComponentIn_of_reach`.

Since `discCrit` is a countable Boolean combination of the conditions `‖z - e i‖ < dist(e i, K)`
and `‖e k - e j‖ < dist(e k, K)`, it is measurable whenever `x ↦ dist(a, K x)` is measurable for
every `a` (`measurableSet_discCrit`).
-/

@[expose] public section

open scoped NNReal ENNReal
open Set Metric MeasureTheory

namespace ComplexSLE.Internal

/-- The fixed dense sequence of `ℂ`. -/
noncomputable def denseSeqC : ℕ → ℂ := TopologicalSpace.denseSeq ℂ

theorem denseRange_denseSeqC : DenseRange denseSeqC := TopologicalSpace.denseRange_denseSeq ℂ

/-- Indices reachable in `n` steps from `i` by chains in which each step goes from `e k` to a
point of the ball `B(e k, dist(e k, K))`. -/
def reachIdx (K : Set ℂ) (i : ℕ) : ℕ → Set ℕ
  | 0 => {i}
  | n + 1 => reachIdx K i n ∪
      {j | ∃ k ∈ reachIdx K i n, ‖denseSeqC k - denseSeqC j‖ < infDist (denseSeqC k) K}

/-- The countable criterion: `z` lies in `B(e i, dist(e i, K))` for some `i` whose reachable set
is bounded. -/
def discCrit (K : Set ℂ) (z : ℂ) : Prop :=
  ∃ i : ℕ, ‖z - denseSeqC i‖ < infDist (denseSeqC i) K ∧
    ∃ R : ℕ, ∀ n : ℕ, ∀ j ∈ reachIdx K i n, ‖denseSeqC j‖ ≤ R

theorem mem_reachIdx_succ_of_step {K : Set ℂ} {i n k j : ℕ} (hk : k ∈ reachIdx K i n)
    (h : ‖denseSeqC k - denseSeqC j‖ < infDist (denseSeqC k) K) : j ∈ reachIdx K i (n + 1) :=
  Or.inr ⟨k, hk, h⟩

/-- Every reachable point lies in the component of `e i` in `Kᶜ`. -/
theorem mem_connectedComponentIn_of_reach {K : Set ℂ} {i : ℕ} (hi : denseSeqC i ∉ K) :
    ∀ (n j : ℕ), j ∈ reachIdx K i n →
      denseSeqC j ∈ connectedComponentIn Kᶜ (denseSeqC i) := by
  intro n
  induction n with
  | zero =>
    intro j hj
    have : j = i := hj
    subst this
    exact mem_connectedComponentIn hi
  | succ n ih =>
    intro j hj
    rcases hj with hj | ⟨k, hk, hkj⟩
    · exact ih j hj
    · have hkc := ih k hk
      have hpos : 0 < infDist (denseSeqC k) K := lt_of_le_of_lt (norm_nonneg _) hkj
      have hball : ball (denseSeqC k) (infDist (denseSeqC k) K) ⊆
          connectedComponentIn Kᶜ (denseSeqC k) :=
        (convex_ball _ _).isPreconnected.subset_connectedComponentIn (mem_ball_self hpos)
          ball_infDist_subset_compl
      have hj : denseSeqC j ∈ connectedComponentIn Kᶜ (denseSeqC k) := by
        refine hball ?_
        rw [mem_ball, dist_comm, dist_eq_norm]
        exact hkj
      rw [connectedComponentIn_eq hkc]
      exact hj

/-- The union of the balls around the reachable points. -/
noncomputable def reachBalls (K : Set ℂ) (i : ℕ) : Set ℂ :=
  ⋃ n : ℕ, ⋃ j ∈ reachIdx K i n, ball (denseSeqC j) (infDist (denseSeqC j) K)

theorem isOpen_reachBalls (K : Set ℂ) (i : ℕ) : IsOpen (reachBalls K i) :=
  isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball

/-- The complement of the union of the reach balls is open inside `Kᶜ`. -/
theorem isOpen_compl_inter_compl_reachBalls {K : Set ℂ} (hne : K.Nonempty) (hK : IsClosed K)
    (i : ℕ) : IsOpen (Kᶜ ∩ (reachBalls K i)ᶜ) := by
  rw [Metric.isOpen_iff]
  rintro w ⟨hwK, hwO⟩
  have hρ : 0 < infDist w K := (hK.notMem_iff_infDist_pos hne).1 hwK
  set ρ : ℝ := infDist w K with hρdef
  refine ⟨ρ / 2, half_pos hρ, fun y hy => ⟨?_, ?_⟩⟩
  · exact ball_infDist_subset_compl (ball_subset_ball (by linarith) hy)
  · intro hyO
    simp only [reachBalls, mem_iUnion] at hyO
    obtain ⟨n, j, hj, hyj⟩ := hyO
    have hopen : IsOpen (ball w (ρ / 2) ∩ ball (denseSeqC j) (infDist (denseSeqC j) K)) :=
      isOpen_ball.inter isOpen_ball
    obtain ⟨m, hm⟩ := denseRange_denseSeqC.exists_mem_open hopen ⟨y, hy, hyj⟩
    have hmreach : m ∈ reachIdx K i (n + 1) := by
      refine mem_reachIdx_succ_of_step hj ?_
      have := mem_ball.1 hm.2
      rw [dist_comm, dist_eq_norm] at this
      exact this
    have h1 : dist w (denseSeqC m) < ρ / 2 := mem_ball.1 hm.1 |> fun h => by
      rw [dist_comm]; exact h
    have h2 : ρ ≤ infDist (denseSeqC m) K + dist w (denseSeqC m) := infDist_le_infDist_add_dist
    apply hwO
    simp only [reachBalls, mem_iUnion]
    refine ⟨n + 1, m, hmreach, ?_⟩
    rw [mem_ball]
    linarith

/-- The component of `e i` in `Kᶜ` is contained in the union of the reach balls. -/
theorem connectedComponentIn_subset_reachBalls {K : Set ℂ} (hne : K.Nonempty) (hK : IsClosed K)
    {i : ℕ} (hi : denseSeqC i ∉ K) :
    connectedComponentIn Kᶜ (denseSeqC i) ⊆ reachBalls K i := by
  have hpos : 0 < infDist (denseSeqC i) K := (hK.notMem_iff_infDist_pos hne).1 hi
  have hmem : denseSeqC i ∈ reachBalls K i := by
    simp only [reachBalls, mem_iUnion]
    exact ⟨0, i, rfl, mem_ball_self hpos⟩
  refine isPreconnected_connectedComponentIn.subset_left_of_subset_union (isOpen_reachBalls K i)
    (isOpen_compl_inter_compl_reachBalls hne hK i) ?_ ?_ ?_
  · rw [Set.disjoint_left]
    rintro w hw ⟨-, hw'⟩
    exact hw' hw
  · intro w hw
    by_cases h : w ∈ reachBalls K i
    · exact Or.inl h
    · exact Or.inr ⟨connectedComponentIn_subset _ _ hw, h⟩
  · exact ⟨denseSeqC i, mem_connectedComponentIn hi, hmem⟩

/-- **The countable criterion.** For a closed nonempty `K`, `z ∉ K` and `K` disconnects `z` from
`∞` iff `discCrit K z`. -/
theorem discAt_iff_discCrit {K : Set ℂ} (hne : K.Nonempty) (hK : IsClosed K) (z : ℂ) :
    (z ∉ K ∧ DisconnectsFromInfinity K {z}) ↔ discCrit K z := by
  constructor
  · rintro ⟨hz, hdis⟩
    have hbdd : Bornology.IsBounded (connectedComponentIn Kᶜ z) := by
      rcases Planar.disconnectsFromInfinity_singleton_iff.1 hdis with h | h
      · exact absurd h hz
      · exact h
    have hρ : 0 < infDist z K := (hK.notMem_iff_infDist_pos hne).1 hz
    obtain ⟨i, hi⟩ := denseRange_denseSeqC.exists_mem_open
      (isOpen_ball (x := z) (ε := infDist z K / 2)) ⟨z, mem_ball_self (half_pos hρ)⟩
    have h1 : dist z (denseSeqC i) < infDist z K / 2 := by
      rw [dist_comm]; exact mem_ball.1 hi
    have h2 : infDist z K ≤ infDist (denseSeqC i) K + dist z (denseSeqC i) :=
      infDist_le_infDist_add_dist
    have h3 : ‖z - denseSeqC i‖ < infDist (denseSeqC i) K := by
      rw [← dist_eq_norm]; linarith
    have hpos : 0 < infDist (denseSeqC i) K := lt_of_le_of_lt (norm_nonneg _) h3
    have hiK : denseSeqC i ∉ K := (hK.notMem_iff_infDist_pos hne).2 hpos
    have hzc : z ∈ connectedComponentIn Kᶜ (denseSeqC i) :=
      (convex_ball _ _).isPreconnected.subset_connectedComponentIn (mem_ball_self hpos)
        ball_infDist_subset_compl (mem_ball.2 (by rwa [dist_eq_norm]))
    have hbdd' : Bornology.IsBounded (connectedComponentIn Kᶜ (denseSeqC i)) := by
      rw [connectedComponentIn_eq hzc]; exact hbdd
    obtain ⟨R₀, hR₀⟩ := isBounded_iff_forall_norm_le.1 hbdd'
    refine ⟨i, h3, ⌈R₀⌉₊, fun n j hj => ?_⟩
    exact (hR₀ _ (mem_connectedComponentIn_of_reach hiK n j hj)).trans (Nat.le_ceil R₀)
  · rintro ⟨i, hz, R, hR⟩
    have hz' : z ∈ ball (denseSeqC i) (infDist (denseSeqC i) K) := by
      rw [mem_ball, dist_eq_norm]; exact hz
    have hzK : z ∉ K := ball_infDist_subset_compl hz'
    have hpos : 0 < infDist (denseSeqC i) K := lt_of_le_of_lt (norm_nonneg _) hz
    have hiK : denseSeqC i ∉ K := (hK.notMem_iff_infDist_pos hne).2 hpos
    refine ⟨hzK, Planar.disconnectsFromInfinity_singleton_iff.2 (Or.inr ?_)⟩
    have hzc : z ∈ connectedComponentIn Kᶜ (denseSeqC i) :=
      (convex_ball _ _).isPreconnected.subset_connectedComponentIn (mem_ball_self hpos)
        ball_infDist_subset_compl hz'
    rw [← connectedComponentIn_eq hzc]
    obtain ⟨k₀, hk₀⟩ := hne
    rw [isBounded_iff_forall_norm_le]
    refine ⟨2 * R + ‖k₀‖, fun y hy => ?_⟩
    have hyO := connectedComponentIn_subset_reachBalls ⟨k₀, hk₀⟩ hK hiK hy
    simp only [reachBalls, mem_iUnion] at hyO
    obtain ⟨n, j, hj, hyj⟩ := hyO
    have hjR := hR n j hj
    have h1 : dist y (denseSeqC j) < infDist (denseSeqC j) K := mem_ball.1 hyj
    have h2 : infDist (denseSeqC j) K ≤ dist (denseSeqC j) k₀ := infDist_le_dist_of_mem hk₀
    have h3 : dist y (denseSeqC j) = ‖y - denseSeqC j‖ := dist_eq_norm _ _
    have h4 : dist (denseSeqC j) k₀ ≤ ‖denseSeqC j‖ + ‖k₀‖ := by
      rw [dist_eq_norm]; exact norm_sub_le _ _
    have h5 : ‖y‖ ≤ ‖denseSeqC j‖ + ‖y - denseSeqC j‖ := by
      calc ‖y‖ = ‖denseSeqC j + (y - denseSeqC j)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    linarith

/-! ### Measurability of the criterion -/

section Measurability

variable {X : Type*} [MeasurableSpace X] {K : X → Set ℂ}

theorem measurableSet_mem_reachIdx (hK : ∀ a : ℂ, Measurable fun x => infDist a (K x))
    (i n j : ℕ) : MeasurableSet {x | j ∈ reachIdx (K x) i n} := by
  induction n generalizing j with
  | zero =>
    by_cases h : j = i
    · simp [reachIdx, h]
    · simp [reachIdx, h]
  | succ n ih =>
    have : {x | j ∈ reachIdx (K x) i (n + 1)} = {x | j ∈ reachIdx (K x) i n} ∪
        ⋃ k : ℕ, ({x | k ∈ reachIdx (K x) i n} ∩
          {x | ‖denseSeqC k - denseSeqC j‖ < infDist (denseSeqC k) (K x)}) := by
      ext x
      simp [reachIdx]
    rw [this]
    exact (ih j).union (MeasurableSet.iUnion fun k =>
      (ih k).inter (measurableSet_lt measurable_const (hK _)))

theorem measurableSet_reachBdd (hK : ∀ a : ℂ, Measurable fun x => infDist a (K x)) (i R : ℕ) :
    MeasurableSet {x | ∀ n : ℕ, ∀ j ∈ reachIdx (K x) i n, ‖denseSeqC j‖ ≤ R} := by
  have : {x | ∀ n : ℕ, ∀ j ∈ reachIdx (K x) i n, ‖denseSeqC j‖ ≤ R} =
      ⋂ n : ℕ, ⋂ j : ℕ, ({x | j ∈ reachIdx (K x) i n}ᶜ ∪ {_x | ‖denseSeqC j‖ ≤ (R : ℝ)}) := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff]
    refine forall_congr' fun n => forall_congr' fun j => ?_
    tauto
  rw [this]
  exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun j =>
    (measurableSet_mem_reachIdx hK i n j).compl.union (MeasurableSet.const _)

/-- **The criterion is measurable**: if `x ↦ dist(a, K x)` is measurable for every `a`, then
`{(x, z) | discCrit (K x) z}` is measurable. -/
theorem measurableSet_discCrit (hK : ∀ a : ℂ, Measurable fun x => infDist a (K x)) :
    MeasurableSet {p : X × ℂ | discCrit (K p.1) p.2} := by
  have : {p : X × ℂ | discCrit (K p.1) p.2} = ⋃ i : ℕ,
      ({p : X × ℂ | ‖p.2 - denseSeqC i‖ < infDist (denseSeqC i) (K p.1)} ∩
        Prod.fst ⁻¹' ⋃ R : ℕ, {x | ∀ n : ℕ, ∀ j ∈ reachIdx (K x) i n, ‖denseSeqC j‖ ≤ R}) := by
    ext p
    simp [discCrit]
  rw [this]
  refine MeasurableSet.iUnion fun i => MeasurableSet.inter ?_ ?_
  · exact measurableSet_lt ((measurable_snd.sub_const _).norm) ((hK _).comp measurable_fst)
  · exact measurable_fst (MeasurableSet.iUnion fun R => measurableSet_reachBdd hK i R)

end Measurability

end ComplexSLE.Internal

end
