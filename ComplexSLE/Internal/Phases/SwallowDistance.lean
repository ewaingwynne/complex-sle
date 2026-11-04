/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Hull.EndpointCont
public import ComplexSLE.Internal.Polar.Sigma

/-!
# Lemma 3.6 (`lem-swallow-distance`) in σ-time: deterministic part (M7/C1)

Source: paper.tex:L1389-1398. For a continuous driver `U` and a point `z` with
`sigmaDom = [0, ∞)` (`clockSup = ∞`, a.s. by Remark 2.12) and `T_z < ∞`,

  `log|f̂_s(z)| = log|f_{σ_z(s)}(z)| → -∞` as `s → ∞`.

The proof is the paper's: by Lemma 2.5 (`tendsto_log_norm_fPath_nhdsWithin`),
`log|f_t(z)| → -∞` as `t → T_z⁻`, and `σ_z(s) → T_z⁻` as `s → ∞` because `σ_z` maps `[0, ∞)`
monotonically onto `[0, T_z)` (`image_sigmaTime`, `tendsto_sigmaTime_nhdsWithin`).

The almost sure statement for an adapted driver is in `SwallowDistanceAE.lean`. No external input
is used here.
-/

public section

open scoped NNReal ENNReal Topology
open Set Filter

namespace ComplexSLE.Internal.Polar

variable {U : ℝ≥0 → ℂ}

/-- `σ_z(s) → T_z⁻` as `s → ∞` (`σ_z(∞) = T_z`, Remark 2.12): for `sigmaDom = [0, ∞)` and
`T_z < ∞`, `σ_z` tends to `T_z` within the life set `[0, T_z)`. -/
theorem tendsto_sigmaTime_nhdsWithin (hU : Continuous U) {z : ℂ}
    (hdom : sigmaDom U hU z = Ici 0) (hT : absorbingTime U z ≠ ⊤) :
    Tendsto (sigmaTime U hU z) atTop (𝓝[lifeSet U z] (absorbingTime U z).toReal) := by
  set T := (absorbingTime U z).toReal with hTdef
  have hmem : ∀ s : ℝ, 0 ≤ s → sigmaTime U hU z s ∈ lifeSet U z := fun s hs =>
    sigmaTime_mem_lifeSet hU (by rw [hdom]; exact hs)
  have h0life : (0 : ℝ) ∈ lifeSet U z := by
    have := hmem 0 le_rfl
    exact mem_lifeSet_of_le this le_rfl this.1
  have hTpos : 0 < T := by
    have := (lifeSet_eq_Ico hT ▸ h0life : (0 : ℝ) ∈ Ico 0 T)
    exact this.2
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
    · -- a time `t₀` in the life set above `a`; beyond `A(t₀)` the σ-time exceeds `t₀`
      set t₀ := max 0 ((a + T) / 2) with ht₀def
      have ht₀T : t₀ < T := max_lt hTpos (by linarith)
      have ht₀ : t₀ ∈ lifeSet U z := by
        rw [lifeSet_eq_Ico hT]; exact ⟨le_max_left _ _, ht₀T⟩
      have hat₀ : a < t₀ := lt_of_lt_of_le (by linarith) (le_max_right _ _)
      have hcdom : clock U hU z t₀ ∈ sigmaDom U hU z := clock_mem_sigmaDom hU ht₀
      filter_upwards [eventually_ge_atTop (clock U hU z t₀)] with s hs
      have hsdom : s ∈ sigmaDom U hU z := by
        rw [hdom]; exact (clock_nonneg hU ht₀).trans hs
      have := sigmaTime_monotoneOn hU z hcdom hsdom hs
      rw [sigmaTime_clock hU ht₀] at this
      exact lt_of_lt_of_le hat₀ this
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
      have := (lifeSet_eq_Ico hT ▸ hmem s hs : sigmaTime U hU z s ∈ Ico 0 T)
      exact lt_trans this.2 hb
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs using hmem s hs

/-- **Lemma 3.6** (`lem-swallow-distance`, paper.tex:L1389-1398), deterministic form: for a
continuous driver `U` and `z` with `sigmaDom = [0, ∞)` and `T_z < ∞`, `log|f̂_s(z)| → -∞` as
`s → ∞`, where `f̂_s(z) = f_{σ_z(s)}(z)`. -/
theorem tendsto_log_norm_fPath_sigmaTime (hU : Continuous U) {z : ℂ}
    (hdom : sigmaDom U hU z = Ici 0) (hT : absorbingTime U z ≠ ⊤) :
    Tendsto (fun s : ℝ => Real.log ‖fPath U hU z (sigmaTime U hU z s)‖) atTop atBot :=
  (tendsto_log_norm_fPath_nhdsWithin hU hT).comp (tendsto_sigmaTime_nhdsWithin hU hdom hT)

/-- The `ℝ≥0`-indexed form of `tendsto_log_norm_fPath_sigmaTime`
(the process `s ↦ log|f̂_s(z)|`, `s : ℝ≥0`). -/
theorem tendsto_log_norm_fPath_sigmaTime_nnreal (hU : Continuous U) {z : ℂ}
    (hdom : sigmaDom U hU z = Ici 0) (hT : absorbingTime U z ≠ ⊤) :
    Tendsto (fun s : ℝ≥0 => Real.log ‖fPath U hU z (sigmaTime U hU z (s : ℝ))‖) atTop atBot :=
  (tendsto_log_norm_fPath_sigmaTime hU hdom hT).comp (NNReal.tendsto_coe_atTop.2 tendsto_id)

end ComplexSLE.Internal.Polar

end
