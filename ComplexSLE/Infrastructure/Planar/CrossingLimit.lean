/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Planar.Crossing
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# A compactness limit of chain crossings

If a compact set `S` carries, for every `ρ > 0`, a `ρ`-chain in `S` whose image under a continuous
map `F` satisfies the hypotheses of the chain crossing lemma
(`exists_dist_le_of_chain_crossing`) for a closed connected set `B`, then `F` maps some point
of `S` into `B`.
-/

public section

open Set Metric

namespace ComplexSLE.Planar

/-- **Limit of chain crossings.** The uniform-in-`ρ` hypotheses `hchain` on the chains are those of
`exists_dist_le_of_chain_crossing` for the chain `F ∘ β`. -/
theorem exists_mem_image_of_chain_crossing {S : Set ℂ} (hS : IsCompact S) {F : ℂ → ℂ}
    (hF : ContinuousOn F S) {B : Set ℂ} (hB : IsClosed B) (hBc : IsPreconnected B)
    {ε h : ℝ} (hBre : ∀ w ∈ B, |w.re| < ε) {b₁ b₂ : ℂ} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    (hb₁h : h < b₁.im) (hb₂h : b₂.im < -h)
    (hchain : ∀ ρ : ℝ, 0 < ρ → ∃ (n : ℕ) (β : Fin (n + 1) → ℂ), (∀ k, β k ∈ S) ∧
      (∀ k : Fin n, dist (F (β k.castSucc)) (F (β k.succ)) < ρ) ∧
      (∀ k, |(F (β k)).im| + 2 * ρ ≤ h) ∧ (F (β 0)).re ≤ -ε ∧
      ε ≤ (F (β (Fin.last n))).re) :
    ∃ s ∈ S, F s ∈ B := by
  have hcross : ∀ ρ : ℝ, 0 < ρ → ∃ s ∈ S, ∃ w ∈ B, dist (F s) w ≤ ρ := by
    intro ρ hρ
    obtain ⟨n, β, hβS, hβd, hβim, hβ0, hβl⟩ := hchain ρ hρ
    obtain ⟨k, w, hwB, hk⟩ := exists_dist_le_of_chain_crossing hBc hBre hb₁ hb₂ hb₁h hb₂h
      (fun k => F (β k)) hβd hβim hβ0 hβl
    exact ⟨β k, hβS k, w, hwB, hk⟩
  obtain ⟨s₀, hs₀S, -⟩ := hcross 1 one_pos
  have hcont : ContinuousOn (fun s => infDist (F s) B) S :=
    (continuous_infDist_pt B).comp_continuousOn hF
  obtain ⟨s, hsS, hmin⟩ := hS.exists_isMinOn ⟨s₀, hs₀S⟩ hcont
  refine ⟨s, hsS, ?_⟩
  have hBne : B.Nonempty := ⟨b₁, hb₁⟩
  rw [← hB.closure_eq, mem_closure_iff_infDist_zero hBne]
  by_contra hne
  have hpos : 0 < infDist (F s) B := lt_of_le_of_ne infDist_nonneg (Ne.symm hne)
  obtain ⟨s', hs'S, w, hwB, hw⟩ := hcross (infDist (F s) B / 2) (by positivity)
  have h1 : infDist (F s') B ≤ dist (F s') w := infDist_le_dist_of_mem hwB
  have h2 : infDist (F s) B ≤ infDist (F s') B := hmin hs'S
  linarith

end ComplexSLE.Planar

end
