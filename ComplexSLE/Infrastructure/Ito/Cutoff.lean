/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Smooth cutoff of a `C²` function near a compact set

`exists_cutoff`: if `F` is `C²` on an open set `D` and `K ⊆ D` is compact, there is a `C²` function
`F'` with compact support on `ℝⁿ` that agrees with `F` on a neighbourhood of every point of `K`
(multiply `F` by a smooth bump equal to `1` on a thickening of `K` and supported in a smaller
thickening that stays inside `D`). Its first and second derivatives at points of `K` are those of
`F`, so Itô's formula for `F'` (compact support, hence globally bounded derivatives) gives the one
for `F` along paths that stay in `K`.
-/

@[expose] public section

open scoped Topology
open Set Metric Filter

namespace ComplexSLE.Infrastructure.Ito

/-- A `C²` function on a neighbourhood of a compact set agrees, near the compact set, with a `C²`
function of compact support. -/
theorem exists_cutoff {n : ℕ} {K D : Set (Fin n → ℝ)} (hK : IsCompact K) (hD : IsOpen D)
    (hKD : K ⊆ D) {F : (Fin n → ℝ) → ℝ} (hF : ContDiffOn ℝ 2 F D) :
    ∃ F' : (Fin n → ℝ) → ℝ, ContDiff ℝ 2 F' ∧ HasCompactSupport F' ∧
      ∀ x ∈ K, F' =ᶠ[𝓝 x] F := by
  obtain ⟨δ, hδ, hδD⟩ := hK.exists_cthickening_subset_open hD hKD
  obtain ⟨χ, hχ, -, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_thickening (δ := δ) (E := K))
    (isClosed_cthickening (δ := δ / 2) (E := K))
    (cthickening_subset_thickening' hδ (by linarith) K)
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (WithTop.coe_le_coe.2 le_top)
  have hsupp : ∀ x ∉ cthickening δ K, χ x = 0 := fun x hx => by
    by_contra hne
    have : x ∈ Function.support χ := hne
    rw [hχs] at this
    exact hx (thickening_subset_cthickening δ K this)
  refine ⟨fun x => χ x * F x, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ D
    · exact (hχ2.contDiffAt).mul (hF.contDiffAt (hD.mem_nhds hx))
    · have hxc : x ∉ cthickening δ K := fun h => hx (hδD h)
      have hev : (fun x => χ x * F x) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        have : (cthickening δ K)ᶜ ∈ 𝓝 x := isClosed_cthickening.isOpen_compl.mem_nhds hxc
        filter_upwards [this] with y hy
        simp [hsupp y hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · exact HasCompactSupport.intro (hK.cthickening (r := δ)) fun x hx => by simp [hsupp x hx]
  · intro x hx
    have hU : thickening (δ / 2) K ∈ 𝓝 x :=
      isOpen_thickening.mem_nhds (self_subset_thickening (by linarith) K hx)
    filter_upwards [hU] with y hy
    have : χ y = 1 := (hχ1 y).1 (thickening_subset_cthickening _ _ hy)
    simp [this]

end ComplexSLE.Infrastructure.Ito

end
