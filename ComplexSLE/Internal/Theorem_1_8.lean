/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsThinPhase
public import ComplexSLE.Frozen.Defs.IsSwallowingPhase
public import ComplexSLE.Frozen.Defs.IsHittingPhase
public import ComplexSLE.Frozen.Defs.IsDensePhase
public import ComplexSLE.Frozen.Defs.IsAdmissibleDensity
public import ComplexSLE.Frozen.Defs.IntegralI
public import ComplexSLE.Frozen.Defs.IntegralII
import ComplexSLE.Frozen.Proposition_3_1_A
import ComplexSLE.Frozen.Proposition_3_1_B
import ComplexSLE.Frozen.Proposition_3_2_A
import ComplexSLE.Frozen.Proposition_3_2_B
import ComplexSLE.Internal.Hull.Basic

/-!
# Provider for `ComplexSLE.theorem_1_8`

Implementation module for the frozen anchor `ComplexSLE/Frozen/Theorem_1_8.lean`. The anchor is
SEALED. The proof is paper.tex:L1930-1932: each phase is the conjunction of one alternative of
Proposition 3.1 (`T_z = ∞` a.s. if `(I) ≥ 0`, `T_z < ∞` a.s. if `(I) < 0`) and one alternative of
Proposition 3.2 (in the `ε`-forms of ruling R14: `dist(z, L_t)` stays bounded below for `t < T_z`
a.s. if `(II) > 0`, and comes arbitrarily close to `0` if `(II) < 0`). It consumes only the four
sealed anchors `proposition_3_1_a`, `proposition_3_1_b`, `proposition_3_2_a`, `proposition_3_2_b`;
the remaining glue (below) is deterministic, using that every hull `L_t` contains `U 0`.
-/

public section

open scoped NNReal ENNReal
open MeasureTheory Metric Set

namespace ComplexSLE.Internal

/-- A point at distance at least `ε > 0` from every point of `s` is not in the closure of `s`. -/
theorem notMem_closure_of_le_dist {s : Set ℂ} {z : ℂ} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ w ∈ s, ε ≤ dist z w) : z ∉ closure s := by
  rw [Metric.mem_closure_iff]
  push Not
  exact ⟨ε, hε, h⟩

/-- If `infDist z (L_t) < ε` for some `t` in a given set of times, for every `ε > 0`, then `z` is in
the closure of the union of those hulls. -/
theorem mem_closure_of_infDist_lt (U : ℝ≥0 → ℂ) (z : ℂ) (S : Set ℝ≥0)
    (h : ∀ ε > 0, ∃ t ∈ S, infDist z (leftHull U t) < ε) :
    z ∈ closure (⋃ t ∈ S, leftHull U t) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨t, ht, hd⟩ := h ε hε
  obtain ⟨w, hw, hzw⟩ := (Metric.infDist_lt_iff (leftHull_nonempty U t)).1 hd
  exact ⟨w, mem_iUnion₂.2 ⟨t, ht, hw⟩, hzw⟩

theorem theorem_1_8 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (p : ℝ → ℝ) (hp : IsAdmissibleDensity a b c p) :
    (0 ≤ integralI a b c p → 0 < integralII a b c p → IsThinPhase a b c) ∧
    (integralI a b c p < 0 → 0 < integralII a b c p → IsSwallowingPhase a b c) ∧
    (integralI a b c p < 0 → integralII a b c p < 0 → IsHittingPhase a b c) ∧
    (0 ≤ integralI a b c p → integralII a b c p < 0 → IsDensePhase a b c) := by
  refine ⟨fun hI hII => ?_, fun hI hII => ?_, fun hI hII => ?_, fun hI hII => ?_⟩
  · -- thin: `T_z = ∞` and `dist(z, L_t) ≥ ε` for all `t`
    intro Ω _ P _ U hU z hz
    filter_upwards [_root_.ComplexSLE.proposition_3_1_a a b c ha hb hc p hp hI Ω P U hU z hz,
      _root_.ComplexSLE.proposition_3_2_b a b c ha hb hc p hp hII Ω P U hU z hz]
      with ω hT ⟨ε, hε, h⟩
    refine notMem_closure_of_le_dist hε fun w hw => ?_
    obtain ⟨t, hw⟩ := mem_iUnion.1 hw
    exact (h t (by rw [hT]; exact ENNReal.coe_lt_top)).trans (infDist_le_dist_of_mem hw)
  · -- swallowing: `T_z < ∞` and `dist(z, L_t) ≥ ε` for all `t < T_z`
    intro Ω _ P _ U hU z hz
    filter_upwards [_root_.ComplexSLE.proposition_3_1_b a b c ha hb hc p hp hI Ω P U hU z hz,
      _root_.ComplexSLE.proposition_3_2_b a b c ha hb hc p hp hII Ω P U hU z hz]
      with ω hT ⟨ε, hε, h⟩
    refine ⟨hT, notMem_closure_of_le_dist hε fun w hw => ?_⟩
    obtain ⟨t, ht, hw⟩ := mem_iUnion₂.1 hw
    exact (h t ht).trans (infDist_le_dist_of_mem hw)
  · -- hitting: `T_z < ∞` and `dist(z, L_t) → 0` along `t < T_z`
    intro Ω _ P _ U hU z hz
    filter_upwards [_root_.ComplexSLE.proposition_3_1_b a b c ha hb hc p hp hI Ω P U hU z hz,
      _root_.ComplexSLE.proposition_3_2_a a b c ha hb hc p hp hII Ω P U hU z hz]
      with ω hT h
    exact ⟨hT, mem_closure_of_infDist_lt (U · ω) z {t | (t : ℝ≥0∞) < absorbingTime (U · ω) z}
      fun ε hε => (h ε hε).imp fun _ ht => ⟨ht.1, ht.2⟩⟩
  · -- dense: `T_z = ∞` (so `z ∉ L_t`) and `dist(z, L_t) → 0`
    intro Ω _ P _ U hU z hz
    filter_upwards [_root_.ComplexSLE.proposition_3_1_a a b c ha hb hc p hp hI Ω P U hU z hz,
      _root_.ComplexSLE.proposition_3_2_a a b c ha hb hc p hp hII Ω P U hU z hz]
      with ω hT h
    refine ⟨?_, ?_⟩
    · have := mem_closure_of_infDist_lt (U · ω) z univ
        fun ε hε => (h ε hε).imp fun _ ht => ⟨mem_univ _, ht.2⟩
      simpa only [mem_univ, iUnion_true] using this
    · rw [mem_iUnion]
      rintro ⟨t, ht⟩
      have ht' : absorbingTime (U · ω) z ≤ t := ht
      rw [hT] at ht'
      exact ENNReal.coe_ne_top (top_le_iff.1 ht')

end ComplexSLE.Internal

end
