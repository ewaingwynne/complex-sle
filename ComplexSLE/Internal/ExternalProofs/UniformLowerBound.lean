/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.ExternalProofs.LoewnerFar
public import ComplexSLE.Internal.Polar.PolarDerivShift
import ComplexSLE.Internal.Hull.ConnectedNoExt

/-!
# A uniform lower bound for `|f_s(z)|` away from the left hull

For a continuous driver `U`, a time `T` and `ε > 0` there is `η₀ > 0` such that every `z` with
`dist z L_T ≥ ε` is alive on `[0, T]` (`z ∉ L_T`) and `‖f_s(z)‖ ≥ η₀` for all `s ∈ [0, T]`.

Proof: on a bounded set of such `z` (a compact set) the bound is local by the Lipschitz dependence
on the initial point (`Polar.exists_lipschitz_initial`) and globalises by compactness; for `‖z‖`
large the solution is far from the driver (`far_closedSol`).
-/

public section

open scoped NNReal ENNReal
open Set Metric

namespace ComplexSLE.Internal.ExternalProofs

open ComplexSLE.Internal.Polar

variable {U : ℝ≥0 → ℂ}

/-- A point at distance `≥ ε > 0` from `L_T` is not in `L_T`. -/
theorem notMem_leftHull_of_le_infDist {T : ℝ≥0} {ε : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : ε ≤ infDist z (leftHull U T)) : z ∉ leftHull U T := fun h => by
  rw [infDist_zero_of_mem h] at hz
  exact absurd hz (not_le.2 hε)

/-- **Uniform lower bound for `‖f_s(z)‖` away from the hull.** -/
theorem exists_uniform_lower_bound (hU : Continuous U) (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ z : ℂ, ε ≤ infDist z (leftHull U T) →
      (T : ℝ) ∈ lifeSet U z ∧ ∀ s ∈ Icc (0 : ℝ) T, η ≤ ‖fPath U hU z s‖ := by
  have hT0 : (0 : ℝ) ≤ T := T.2
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := (T : ℝ))).exists_bound_of_continuousOn
    (f := fun u : ℝ => U u.toNNReal) (hU.comp continuous_real_toNNReal).continuousOn
  set R : ℝ := M + 2 + 2 * T with hR
  set A : Set ℂ := {z | ε ≤ infDist z (leftHull U T)} with hA
  have hAclosed : IsClosed A := isClosed_le continuous_const (continuous_infDist_pt _)
  have hS : IsCompact (A ∩ closedBall (0 : ℂ) R) :=
    (isCompact_closedBall (0 : ℂ) R).inter_left hAclosed
  have hAlife : ∀ z ∈ A, (T : ℝ) ∈ lifeSet U z := fun z hz =>
    coe_mem_lifeSet_iff.2 (notMem_leftHull_of_le_infDist hε hz)
  -- the bound on the compact part: local by Lipschitz dependence, global by compactness
  have hcpt : ∃ η > 0, ∀ z ∈ A ∩ closedBall (0 : ℂ) R, ∀ s ∈ Icc (0 : ℝ) T,
      η ≤ ‖fPath U hU z s‖ := by
    refine hS.induction_on (p := fun S => ∃ η > 0, ∀ z ∈ S, ∀ s ∈ Icc (0 : ℝ) T,
      η ≤ ‖fPath U hU z s‖) ?_ ?_ ?_ ?_
    · exact ⟨1, one_pos, fun z hz => absurd hz (notMem_empty z)⟩
    · rintro S S' hSS' ⟨η, hη, h⟩
      exact ⟨η, hη, fun z hz => h z (hSS' hz)⟩
    · rintro S S' ⟨η, hη, h⟩ ⟨η', hη', h'⟩
      refine ⟨min η η', lt_min hη hη', fun z hz s hs => ?_⟩
      rcases hz with hz | hz
      · exact (min_le_left _ _).trans (h z hz s hs)
      · exact (min_le_right _ _).trans (h' z hz s hs)
    · intro x hx
      have hxl := hAlife x hx.1
      obtain ⟨ρ, hρ, C, hC0, hC⟩ := exists_lipschitz_initial hU hxl
      obtain ⟨η₂, hη₂, hη₂le⟩ := exists_pos_le_norm_fPath hU hxl
      set r : ℝ := min ρ (η₂ / (2 * (C + 1))) with hr
      have hrpos : 0 < r := lt_min hρ (by positivity)
      refine ⟨ball x r, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hrpos), η₂ / 2,
        by positivity, ?_⟩
      intro w hw s hs
      have hwx : ‖w - x‖ < r := by rwa [mem_ball, dist_eq_norm] at hw
      obtain ⟨-, hwb⟩ := hC w (hwx.trans_le (min_le_left _ _))
      have h1 := hwb s hs
      have h2 := hη₂le s hs
      have h3 : ‖fPath U hU x s‖ - ‖fPath U hU w s‖ ≤ ‖fPath U hU w s - fPath U hU x s‖ := by
        rw [← norm_neg (fPath U hU w s - fPath U hU x s), neg_sub]
        exact norm_sub_norm_le _ _
      have h4 : C * ‖w - x‖ ≤ η₂ / 2 := by
        have hwr : ‖w - x‖ ≤ η₂ / (2 * (C + 1)) := hwx.le.trans (min_le_right _ _)
        calc C * ‖w - x‖ ≤ C * (η₂ / (2 * (C + 1))) := by gcongr
          _ ≤ η₂ / 2 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
      linarith
  obtain ⟨η₁, hη₁, hbd₁⟩ := hcpt
  refine ⟨min η₁ 1, lt_min hη₁ one_pos, fun z hz => ⟨hAlife z hz, fun s hs => ?_⟩⟩
  by_cases hzR : z ∈ closedBall (0 : ℂ) R
  · exact (min_le_left _ _).trans (hbd₁ z ⟨hz, hzR⟩ s hs)
  · -- far from the origin: the solution stays at distance `≥ 1` from the driver
    refine (min_le_right _ _).trans ?_
    have hzR' : R ≤ ‖z‖ := by
      rw [mem_closedBall_zero_iff, not_le] at hzR
      exact hzR.le
    have hlife := hAlife z hz
    have hcs : ∀ u ∈ Icc (0 : ℝ) T, Polar.solPath U hU z u ≠ U u.toNNReal ∧
        HasDerivWithinAt (Polar.solPath U hU z) (2 / (Polar.solPath U hU z u - U u.toNNReal))
          (Icc 0 (T : ℝ)) u := by
      intro u hu
      have hul : u ∈ lifeSet U z := mem_lifeSet_of_le hlife hu.1 hu.2
      refine ⟨sub_ne_zero.1 (fPath_ne_zero hU hul), ?_⟩
      exact (hasDerivWithinAt_solPath hU hul).mono Icc_subset_Ici_self
    have hMt : ∀ u ∈ Icc (0 : ℝ) T, ‖U u.toNNReal‖ ≤ M := fun u hu => by
      simpa using hM u hu
    have := (far_closedSol hU (solPath_zero hU z) hcs hMt hzR' s hs).2
    have hsT : s ≤ T := hs.2
    change 1 ≤ ‖Polar.solPath U hU z s - U s.toNNReal‖
    have hR2 : R = M + 2 + 2 * T := hR
    linarith

end ComplexSLE.Internal.ExternalProofs

end
