/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.LoewnerMap
public import ComplexSLE.Frozen.LoewnerMap_ExistsSolution

/-!
# Elementary facts about absorbing times and left hulls

Membership in `L_t`, monotonicity in `t`, `U 0 ∈ L_t` (so the hulls are nonempty), and the fact
that `g_t(z) ≠ U_t` for `z ∉ L_t`.
-/

public section

open scoped NNReal ENNReal
open Set

namespace ComplexSLE.Internal

variable {U : ℝ≥0 → ℂ}

theorem mem_leftHull_iff {t : ℝ≥0} {z : ℂ} : z ∈ leftHull U t ↔ absorbingTime U z ≤ t :=
  Iff.rfl

theorem notMem_leftHull_iff {t : ℝ≥0} {z : ℂ} :
    z ∉ leftHull U t ↔ (t : ℝ≥0∞) < absorbingTime U z := by
  simp [mem_leftHull_iff, not_le]

theorem leftHull_mono {s t : ℝ≥0} (h : s ≤ t) : leftHull U s ⊆ leftHull U t := by
  intro z hz
  rw [mem_leftHull_iff] at hz ⊢
  exact le_trans hz (by exact_mod_cast h)

/-- A solution on `[0, τ)` forces `τ ≤ T_z`. -/
theorem le_absorbingTime_of_isLoewnerSolution {z : ℂ} {τ : ℝ≥0∞} {γ : ℝ → ℂ}
    (h : IsLoewnerSolution U z τ γ) : τ ≤ absorbingTime U z :=
  le_sSup ⟨γ, h⟩

/-- The starting point of the driver is absorbed immediately. -/
theorem absorbingTime_driver_zero (U : ℝ≥0 → ℂ) : absorbingTime U (U 0) = 0 := by
  refine le_antisymm (sSup_le ?_) bot_le
  rintro τ ⟨γ, hγ⟩
  by_contra h
  have hpos : (0 : ℝ≥0∞) < τ := pos_iff_ne_zero.2 fun h0 => h (h0 ▸ le_rfl)
  have := (hγ.2 0 le_rfl (by simpa using hpos)).1
  simp [hγ.1] at this

theorem driver_zero_mem_leftHull (U : ℝ≥0 → ℂ) (t : ℝ≥0) : U 0 ∈ leftHull U t := by
  rw [mem_leftHull_iff, absorbingTime_driver_zero]; exact bot_le

theorem leftHull_nonempty (U : ℝ≥0 → ℂ) (t : ℝ≥0) : (leftHull U t).Nonempty :=
  ⟨U 0, driver_zero_mem_leftHull U t⟩

/-- For `z ∉ L_t`, `g_t(z) ≠ U_t`. -/
theorem loewnerMap_ne_driver (hU : Continuous U) (t : ℝ≥0) (z : ↥(leftHull U t)ᶜ) :
    loewnerMap U hU t z ≠ U t := by
  obtain ⟨γ, hγ, hmap⟩ := loewnerMap_exists_solution U hU z
  have ht : (t : ℝ≥0∞) < absorbingTime U z := notMem_leftHull_iff.1 z.2
  have := (hγ.2 t t.2 (by rwa [ENNReal.ofReal_coe_nnreal])).1
  rw [hmap t z.2]
  simpa using this

end ComplexSLE.Internal

end
