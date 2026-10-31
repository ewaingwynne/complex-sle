/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.DisconnectsFromInfinity
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Basic facts on `DisconnectsFromInfinity`

Monotonicity, spreading from a point to a preconnected set, openness, uniqueness of the unbounded
complementary component of a compact set, and invariance under homeomorphisms of `ℂ` that preserve
boundedness (complex conjugation, nonzero complex scalings).
-/

public section

open Set Metric Bornology

namespace ComplexSLE.Planar

/-- A point is disconnected from infinity by `K` iff it lies in `K` or its component in `Kᶜ` is
bounded. -/
theorem disconnectsFromInfinity_singleton_iff {K : Set ℂ} {z : ℂ} :
    DisconnectsFromInfinity K {z} ↔ z ∈ K ∨ IsBounded (connectedComponentIn Kᶜ z) := by
  constructor
  · intro h
    by_cases hz : z ∈ K
    · exact Or.inl hz
    · refine Or.inr ?_
      by_contra hb
      have := h z hz hb
      rw [Set.disjoint_singleton_left] at this
      exact this (mem_connectedComponentIn hz)
  · intro h x hx hxu
    rw [Set.disjoint_singleton_left]
    intro hzx
    have hz : z ∈ Kᶜ := connectedComponentIn_subset _ _ hzx
    have heq := connectedComponentIn_eq hzx
    rcases h with h | h
    · exact hz h
    · exact hxu (heq ▸ h)

/-- Monotonicity in the disconnecting set. -/
theorem disconnectsFromInfinity_mono {K K' W : Set ℂ} (hKK : K ⊆ K')
    (h : DisconnectsFromInfinity K W) : DisconnectsFromInfinity K' W := by
  intro x hx hxu
  have hx' : x ∈ Kᶜ := fun hxK => hx (hKK hxK)
  have hsub : connectedComponentIn K'ᶜ x ⊆ connectedComponentIn Kᶜ x :=
    connectedComponentIn_mono x (compl_subset_compl.2 hKK)
  exact (h x hx' fun hb => hxu (hb.subset hsub)).mono_right hsub

/-- A point of a preconnected set `W ⊆ Kᶜ` disconnected from infinity by `K` spreads to all of
`W`. -/
theorem disconnectsFromInfinity_of_preconnected {K W : Set ℂ} (hW : IsPreconnected W)
    (hWK : Disjoint W K) {z : ℂ} (hz : z ∈ W) (h : DisconnectsFromInfinity K {z}) :
    DisconnectsFromInfinity K W := by
  intro x hx hxu
  rw [Set.disjoint_left]
  intro w hwW hwx
  have hWc : W ⊆ Kᶜ := fun v hv hvK => Set.disjoint_left.1 hWK hv hvK
  have hsub : W ⊆ connectedComponentIn Kᶜ w := hW.subset_connectedComponentIn hwW hWc
  have heq := connectedComponentIn_eq hwx
  have hzx : z ∈ connectedComponentIn Kᶜ x := heq ▸ hsub hz
  exact Set.disjoint_singleton_left.1 (h x hx hxu) hzx

/-- Disconnection of a point from infinity by a closed set is an open condition. -/
theorem exists_ball_disconnectsFromInfinity {K : Set ℂ} (hK : IsClosed K) {z : ℂ} (hz : z ∉ K)
    (h : DisconnectsFromInfinity K {z}) :
    ∃ r > 0, ball z r ⊆ Kᶜ ∧ DisconnectsFromInfinity K (ball z r) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hK.isOpen_compl z hz
  refine ⟨r, hr, hball, ?_⟩
  refine disconnectsFromInfinity_of_preconnected (convex_ball z r).isPreconnected ?_
    (mem_ball_self hr) h
  rw [Set.disjoint_left]
  intro w hw hwK
  exact hball hw hwK

/-- The exterior of a closed ball in `ℂ` is preconnected. -/
theorem isPreconnected_norm_gt {R : ℝ} (hR : 0 ≤ R) : IsPreconnected {w : ℂ | R < ‖w‖} := by
  have h1 : IsPreconnected (Ioi R) := isPreconnected_Ioi
  have h2 : IsPreconnected (sphere (0 : ℂ) 1) :=
    (isConnected_sphere (by rw [Complex.rank_real_complex]; norm_num) 0 zero_le_one).isPreconnected
  have h3 := (h1.prod h2).image (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2)
    (by fun_prop : Continuous fun p : ℝ × ℂ => (p.1 : ℂ) * p.2).continuousOn
  convert h3 using 1
  ext w
  constructor
  · intro hw
    have hw' : R < ‖w‖ := hw
    have hn : ‖w‖ ≠ 0 := by linarith
    refine ⟨(‖w‖, w / (‖w‖ : ℂ)), ⟨hw', ?_⟩, ?_⟩
    · simp [hn]
    · have hn' : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hn
      field_simp
  · rintro ⟨⟨r, u⟩, ⟨hr, hu⟩, rfl⟩
    have hu' : ‖u‖ = 1 := by simpa using hu
    change R < ‖(r : ℂ) * u‖
    rw [norm_mul, hu', mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact lt_of_lt_of_le (show R < r from hr) (le_abs_self r)

/-- For a compact set `K`, any two unbounded components of `Kᶜ` coincide. -/
theorem connectedComponentIn_eq_of_unbounded {K : Set ℂ} (hK : IsBounded K) {x y : ℂ}
    (hbx : ¬ IsBounded (connectedComponentIn Kᶜ x))
    (hby : ¬ IsBounded (connectedComponentIn Kᶜ y)) :
    connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ y := by
  obtain ⟨R₀, hR₀⟩ := hK.subset_closedBall 0
  set R : ℝ := max R₀ 0 with hRdef
  have hR : 0 ≤ R := le_max_right _ _
  have hKR : K ⊆ closedBall (0 : ℂ) R := hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hE : IsPreconnected {w : ℂ | R < ‖w‖} := isPreconnected_norm_gt hR
  have hEK : {w : ℂ | R < ‖w‖} ⊆ Kᶜ := by
    intro w hw hwK
    have := hKR hwK
    rw [mem_closedBall_zero_iff] at this
    exact absurd hw (not_lt.2 this)
  have key : ∀ {x : ℂ}, ¬ IsBounded (connectedComponentIn Kᶜ x) →
      {w : ℂ | R < ‖w‖} ⊆ connectedComponentIn Kᶜ x ∧
        ∃ w, w ∈ {w : ℂ | R < ‖w‖} := by
    intro x hbx
    have : ∃ w ∈ connectedComponentIn Kᶜ x, R < ‖w‖ := by
      by_contra hcon
      apply hbx
      rw [isBounded_iff_subset_closedBall (0 : ℂ)]
      exact ⟨R, fun w hw => mem_closedBall_zero_iff.2
        (not_lt.1 fun hwR => hcon ⟨w, hw, hwR⟩)⟩
    obtain ⟨w, hwx, hwR⟩ := this
    have hsub : {w : ℂ | R < ‖w‖} ⊆ connectedComponentIn Kᶜ w :=
      hE.subset_connectedComponentIn hwR hEK
    exact ⟨(connectedComponentIn_eq hwx) ▸ hsub, w, hwR⟩
  obtain ⟨hx1, w, hw⟩ := key hbx
  obtain ⟨hy1, -⟩ := key hby
  have h1 := connectedComponentIn_eq (hx1 hw)
  have h2 := connectedComponentIn_eq (hy1 hw)
  exact h1.trans h2.symm

/-- Invariance of `DisconnectsFromInfinity` under a homeomorphism of `ℂ` preserving boundedness
in both directions. -/
theorem disconnectsFromInfinity_image (f : ℂ ≃ₜ ℂ)
    (hf : ∀ S : Set ℂ, IsBounded (f '' S) ↔ IsBounded S) (K W : Set ℂ) :
    DisconnectsFromInfinity (f '' K) (f '' W) ↔ DisconnectsFromInfinity K W := by
  have hcomp : ∀ S : Set ℂ, (f '' S)ᶜ = f '' Sᶜ := fun S =>
    (Set.image_compl_eq f.bijective).symm
  have hcc : ∀ (S : Set ℂ) {x : ℂ}, x ∈ Sᶜ →
      connectedComponentIn (f '' S)ᶜ (f x) = f '' connectedComponentIn Sᶜ x := by
    intro S x hx
    rw [hcomp S, f.image_connectedComponentIn hx]
  constructor
  · intro H x hx hxu
    have hfx : f x ∈ (f '' K)ᶜ := by rw [hcomp]; exact mem_image_of_mem f hx
    have := H (f x) hfx (by rw [hcc K hx]; exact fun hb => hxu ((hf _).1 hb))
    rw [hcc K hx] at this
    exact (Set.disjoint_image_iff f.injective).1 this
  · intro H y hy hyu
    obtain ⟨x, hx⟩ : ∃ x, f x = y := f.surjective y
    subst hx
    have hx' : x ∈ Kᶜ := by
      rw [hcomp] at hy
      obtain ⟨x', hx', hxx'⟩ := hy
      rwa [← f.injective hxx']
    rw [hcc K hx'] at hyu ⊢
    exact (Set.disjoint_image_iff f.injective).2 (H x hx' fun hb => hyu ((hf _).2 hb))

/-- Images of bounded sets under a map with `‖f z‖ ≤ c ‖z‖` are bounded. -/
lemma isBounded_image_of_norm_le {f : ℂ → ℂ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ z, ‖f z‖ ≤ c * ‖z‖)
    {S : Set ℂ} (hS : IsBounded S) : IsBounded (f '' S) := by
  rw [isBounded_iff_forall_norm_le] at hS ⊢
  obtain ⟨C, hC⟩ := hS
  refine ⟨c * C, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact (h z).trans (mul_le_mul_of_nonneg_left (hC z hz) hc)

/-- `DisconnectsFromInfinity` is invariant under complex conjugation. -/
theorem disconnectsFromInfinity_conj (K W : Set ℂ) :
    DisconnectsFromInfinity ((starRingEnd ℂ) '' K) ((starRingEnd ℂ) '' W) ↔
      DisconnectsFromInfinity K W := by
  refine disconnectsFromInfinity_image Complex.conjCLE.toHomeomorph (fun S => ⟨fun hS => ?_,
    fun hS => isBounded_image_of_norm_le zero_le_one (fun z => by simp) hS⟩) K W
  have hS' : IsBounded ((starRingEnd ℂ) '' S) := hS
  have h := isBounded_image_of_norm_le (f := starRingEnd ℂ) zero_le_one
    (fun z => by simp) hS'
  have himg : (starRingEnd ℂ) '' ((starRingEnd ℂ) '' S) = S := by
    rw [Set.image_image]; simp
  rwa [himg] at h

/-- `DisconnectsFromInfinity` is invariant under multiplication by a nonzero complex number. -/
theorem disconnectsFromInfinity_mul {r : ℂ} (hr : r ≠ 0) (K W : Set ℂ) :
    DisconnectsFromInfinity ((fun z => r * z) '' K) ((fun z => r * z) '' W) ↔
      DisconnectsFromInfinity K W := by
  refine disconnectsFromInfinity_image (Homeomorph.mulLeft₀ r hr) (fun S => ⟨fun hS => ?_,
    fun hS => isBounded_image_of_norm_le (norm_nonneg r) (fun z => by simp) hS⟩) K W
  have h := isBounded_image_of_norm_le (f := fun z => r⁻¹ * z) (norm_nonneg r⁻¹)
    (fun z => by simp) hS
  have himg : (fun z => r⁻¹ * z) '' ((Homeomorph.mulLeft₀ r hr) '' S) = S := by
    rw [Set.image_image]; simp [hr]
  rwa [himg] at h

end ComplexSLE.Planar

end
