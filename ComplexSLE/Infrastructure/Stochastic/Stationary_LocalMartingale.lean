/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsContLocalMartingale
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Bounded continuous local martingales have constant expectation

A continuous local martingale (`ComplexSLE.IsContLocalMartingale`) that vanishes at time `0` and
is a.s. bounded on `[0, t]` by a constant has `∫ M t = 0`: the stopped processes `M^{τ n}` are
martingales, so have zero expectation, and they converge to `M t` dominatedly. This is the
"the local martingale part is a true martingale" step of `step:kol-ito-expectation`.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Infrastructure

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ≥0 m}

/-- The stopped process at time `t` is a value of `M` at a time `≤ t`. -/
theorem abs_stoppedProcess_le {M : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0} {t : ℝ≥0} {C : ℝ}
    {ω : Ω} (hC : ∀ s ≤ t, |M s ω| ≤ C) : |stoppedProcess M τ t ω| ≤ C :=
  hC _ (WithTop.untopA_le (min_le_left _ _))

/-- A continuous local martingale `M` with `M 0 = 0` that is a.s. bounded by a constant on
`[0, t]` has zero expectation at time `t`. -/
theorem IsContLocalMartingale.integral_eq_zero {M : ℝ≥0 → Ω → ℝ}
    (hM : IsContLocalMartingale ℱ M P) (h0 : ∀ ω, M 0 ω = 0) {t : ℝ≥0} {C : ℝ}
    (hC : ∀ᵐ ω ∂P, ∀ s ≤ t, |M s ω| ≤ C) : ∫ ω, M t ω ∂P = 0 := by
  obtain ⟨-, -, τ, hτ, hτ_tend, hmart⟩ := hM
  -- each stopped process has zero expectation
  have hzero : ∀ n, ∫ ω, stoppedProcess M (τ n) t ω ∂P = 0 := by
    intro n
    have h := (hmart n).setIntegral_eq (by simp : (0 : ℝ≥0) ≤ t) (MeasurableSet.univ (m := ℱ 0))
    simp only [Measure.restrict_univ] at h
    rw [← h]
    have : ∀ ω, stoppedProcess M (τ n) 0 ω = 0 := fun ω => by
      rw [stoppedProcess_eq_of_le (by simp), h0]
    simp [this]
  -- dominated convergence
  have hlim : Tendsto (fun n => ∫ ω, stoppedProcess M (τ n) t ω ∂P) atTop
      (𝓝 (∫ ω, M t ω ∂P)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => C) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun n =>
        (((hmart n).stronglyMeasurable t).mono (ℱ.le t)).aestronglyMeasurable
    · refine Eventually.of_forall fun n => ?_
      filter_upwards [hC] with ω hω
      simpa [Real.norm_eq_abs] using abs_stoppedProcess_le hω
    · exact integrable_const _
    · filter_upwards [hτ_tend] with ω hω
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hω t] with n hn
      exact (stoppedProcess_eq_of_le hn).symm
  simp only [hzero] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

end ComplexSLE.Infrastructure

end
