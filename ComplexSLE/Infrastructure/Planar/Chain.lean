/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.Connected.Basic

/-!
# Chains in preconnected sets

In a preconnected subset `s` of a pseudometric space, two points `x, y ∈ s` can be joined by a
finite `ρ`-chain in `s`: a finite sequence of points of `s` from `x` to `y` whose consecutive
distances are `< ρ`. The proof shows that the set of points of `s` reachable from `x` by
`ρ`-chains in `s` is relatively clopen in `s`.
-/

public section

open Set Metric

namespace ComplexSLE.Planar

variable {E : Type*} [PseudoMetricSpace E]

/-- `ReachableByChain s ρ x y`: there is a `ρ`-chain in `s` from `x` to `y`. -/
def ReachableByChain (s : Set E) (ρ : ℝ) (x y : E) : Prop :=
  ∃ (n : ℕ) (β : Fin (n + 1) → E), β 0 = x ∧ β (Fin.last n) = y ∧ (∀ k, β k ∈ s) ∧
    ∀ k : Fin n, dist (β k.castSucc) (β k.succ) < ρ

lemma ReachableByChain.refl {s : Set E} {ρ : ℝ} {x : E} (hx : x ∈ s) :
    ReachableByChain s ρ x x :=
  ⟨0, fun _ => x, rfl, rfl, fun _ => hx, fun k => k.elim0⟩

lemma ReachableByChain.step {s : Set E} {ρ : ℝ} {x y z : E} (h : ReachableByChain s ρ x y)
    (hz : z ∈ s) (hyz : dist y z < ρ) : ReachableByChain s ρ x z := by
  obtain ⟨n, β, h0, hl, hs, hd⟩ := h
  refine ⟨n + 1, Fin.snoc β z, ?_, ?_, ?_, ?_⟩
  · have : (0 : Fin (n + 2)) = Fin.castSucc (0 : Fin (n + 1)) := rfl
    rw [this, Fin.snoc_castSucc, h0]
  · simp
  · intro k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simpa using hz
    · rw [Fin.snoc_castSucc]; exact hs j
  · intro k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simpa [hl] using hyz
    · have h1 : (Fin.castSucc j).succ = j.succ.castSucc := (Fin.succ_castSucc j).symm
      rw [h1, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hd j

/-- In a preconnected set `s`, any two points can be joined by a finite `ρ`-chain in `s`. -/
theorem exists_chain_of_isPreconnected {s : Set E} (hs : IsPreconnected s) {x y : E} (hx : x ∈ s)
    (hy : y ∈ s) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (n : ℕ) (β : Fin (n + 1) → E), β 0 = x ∧ β (Fin.last n) = y ∧ (∀ k, β k ∈ s) ∧
      ∀ k : Fin n, dist (β k.castSucc) (β k.succ) < ρ := by
  change ReachableByChain s ρ x y
  by_contra hxy
  set R : Set E := {z | z ∈ s ∧ ReachableByChain s ρ x z} with hR
  have hxR : x ∈ R := ⟨hx, ReachableByChain.refl hx⟩
  have hyR : y ∉ R := fun h => hxy h.2
  have key := hs (⋃ z ∈ R, ball z ρ) (⋃ z ∈ s \ R, ball z ρ)
    (isOpen_biUnion fun _ _ => isOpen_ball) (isOpen_biUnion fun _ _ => isOpen_ball)
    (fun w hw => by
      by_cases hwR : w ∈ R
      · exact Or.inl (mem_biUnion hwR (mem_ball_self hρ))
      · exact Or.inr (mem_biUnion ⟨hw, hwR⟩ (mem_ball_self hρ)))
    ⟨x, hx, mem_biUnion hxR (mem_ball_self hρ)⟩
    ⟨y, hy, mem_biUnion ⟨hy, hyR⟩ (mem_ball_self hρ)⟩
  obtain ⟨w, hws, hw1, hw2⟩ := key
  obtain ⟨z, hzR, hwz⟩ := mem_iUnion₂.1 hw1
  obtain ⟨z', hz'R, hwz'⟩ := mem_iUnion₂.1 hw2
  have hwR : w ∈ R := ⟨hws, hzR.2.step hws (by rwa [mem_ball, dist_comm] at hwz)⟩
  exact hz'R.2 ⟨hz'R.1, hwR.2.step hz'R.1 (mem_ball.1 hwz')⟩

end ComplexSLE.Planar

end
