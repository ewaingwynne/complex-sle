/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsContLocalMartingale
public import ComplexSLE.Infrastructure.Stochastic.ContinuousOptionalStopping

/-!
# Algebra of continuous local martingales; external-free stopping

`IsContLocalMartingale` is closed under scalar multiples, negation, sums and differences (the sum
and difference need *everywhere* continuous paths of both summands, so that the stopped processes
`M^{τ n}` of one summand can be stopped again at the localising times of the other, by
`Martingale.stoppedProcess_of_continuous`; a common localising sequence is the minimum of the two),
and a continuous local martingale with everywhere continuous paths stays one after stopping at any
stopping time.

The last statement is `IsContLocalMartingale.stopped_min_of_continuous`.
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}

/-- The time `t ↦ (t ∧ c).untopA` is continuous for any (possibly infinite) cap `c`. -/
theorem continuous_untopA_min (c : WithTop ℝ≥0) :
    Continuous fun t : ℝ≥0 => (min (t : WithTop ℝ≥0) c).untopA := by
  cases c with
  | top =>
    have : (fun t : ℝ≥0 => (min (t : WithTop ℝ≥0) ⊤).untopA) = fun t => t := by
      funext t; rw [min_top_right]; rfl
    rw [this]; exact continuous_id
  | coe a =>
    have : (fun t : ℝ≥0 => (min (t : WithTop ℝ≥0) (a : WithTop ℝ≥0)).untopA) =
        fun t => min t a := by
      funext t; rw [← WithTop.coe_min]; rfl
    rw [this]; exact continuous_id.min continuous_const

/-- Stopping preserves everywhere-continuity of paths. -/
theorem continuous_stoppedProcess {M : ℝ≥0 → Ω → ℝ} (hMc : ∀ ω, Continuous fun t => M t ω)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) : Continuous fun t => stoppedProcess M τ t ω :=
  (hMc ω).comp (continuous_untopA_min (τ ω))

/-- `(M^σ)^τ = M^{τ ∧ σ}`. -/
theorem stoppedProcess_stoppedProcess_min {M : ℝ≥0 → Ω → ℝ} (σ τ : Ω → WithTop ℝ≥0) :
    stoppedProcess (stoppedProcess M σ) τ = stoppedProcess M (fun ω => min (τ ω) (σ ω)) :=
  stoppedProcess_stoppedProcess'

/-! ### Scalar multiples -/

/-- A constant multiple of a continuous local martingale is a continuous local martingale. -/
theorem IsContLocalMartingale.const_smul {M : ℝ≥0 → Ω → ℝ} (c : ℝ)
    (hM : IsContLocalMartingale ℱ M P) : IsContLocalMartingale ℱ (c • M) P := by
  obtain ⟨hprog, hcont, τ, hτ, hτev, hmart⟩ := hM
  refine ⟨fun i => (hprog i).const_smul c, ?_, τ, hτ, hτev, fun n => ?_⟩
  · filter_upwards [hcont] with ω h using h.const_smul c
  · rw [stoppedProcess_const_smul]
    exact (hmart n).smul c

/-- `fun t ω => c * M t ω` form of `IsContLocalMartingale.const_smul`. -/
theorem IsContLocalMartingale.const_mul {M : ℝ≥0 → Ω → ℝ} (c : ℝ)
    (hM : IsContLocalMartingale ℱ M P) :
    IsContLocalMartingale ℱ (fun t ω => c * M t ω) P :=
  hM.const_smul c

/-- The negative of a continuous local martingale is a continuous local martingale. -/
theorem IsContLocalMartingale.neg {M : ℝ≥0 → Ω → ℝ} (hM : IsContLocalMartingale ℱ M P) :
    IsContLocalMartingale ℱ (-M) P := by
  have h := hM.const_smul (-1)
  rwa [neg_one_smul] at h

variable [IsFiniteMeasure P]

/-! ### Stopping, external-free -/

/-- **Stopped continuous local martingale, external-free.** If `M` is an `ℱ`-local martingale with
everywhere continuous paths and `ρ` is an arbitrary `ℱ`-stopping time, then `M^ρ` is a continuous
`ℱ`-local martingale. -/
theorem IsContLocalMartingale.stoppedProcess_of_continuous {M : ℝ≥0 → Ω → ℝ}
    (hM : IsContLocalMartingale ℱ M P) (hMc : ∀ ω, Continuous fun t => M t ω)
    {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime ℱ ρ) :
    IsContLocalMartingale ℱ (stoppedProcess M ρ) P := by
  obtain ⟨hprog, -, τ, hτ, hτev, hmart⟩ := hM
  refine ⟨hprog.stoppedProcess hρ, ae_of_all _ (continuous_stoppedProcess hMc ρ), τ, hτ, hτev,
    fun n => ?_⟩
  have h := (hmart n).stoppedProcess_of_continuous (continuous_stoppedProcess hMc (τ n)) hρ
  rw [stoppedProcess_stoppedProcess_min] at h
  rwa [stoppedProcess_stoppedProcess_min, funext fun ω => min_comm (τ n ω) (ρ ω)]

/-- `t ↦ M (t ∧ ρ)` is a continuous local martingale for an everywhere-continuous local martingale
`M` and a finite stopping time `ρ`. -/
theorem IsContLocalMartingale.stopped_min_of_continuous (ℱ : Filtration ℝ≥0 m)
    {M : ℝ≥0 → Ω → ℝ} (hM : IsContLocalMartingale ℱ M P) (hMc : ∀ ω, Continuous fun t => M t ω)
    {ρ : Ω → ℝ≥0} (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0)) :
    IsContLocalMartingale ℱ (fun t ω => M (min t (ρ ω)) ω) P := by
  have h := hM.stoppedProcess_of_continuous hMc hρ
  have hfun : (fun t ω => M (min t (ρ ω)) ω) =
      stoppedProcess M fun ω => (ρ ω : WithTop ℝ≥0) := by
    funext t ω
    simp only [stoppedProcess]
    rw [← WithTop.coe_min]
    rfl
  rwa [hfun]

/-! ### Sums and differences -/

/-- The sum of two continuous local martingales with everywhere continuous paths is a continuous
local martingale (common localising sequence: the pointwise minimum of the two). -/
theorem IsContLocalMartingale.add {M N : ℝ≥0 → Ω → ℝ} (hM : IsContLocalMartingale ℱ M P)
    (hN : IsContLocalMartingale ℱ N P) (hMc : ∀ ω, Continuous fun t => M t ω)
    (hNc : ∀ ω, Continuous fun t => N t ω) : IsContLocalMartingale ℱ (M + N) P := by
  obtain ⟨hprogM, hcontM, τ, hτ, hτev, hmartM⟩ := hM
  obtain ⟨hprogN, hcontN, σ, hσ, hσev, hmartN⟩ := hN
  refine ⟨hprogM.add hprogN, ?_, fun n ω => min (τ n ω) (σ n ω),
    fun n => (hτ n).min (hσ n), ?_, fun n => ?_⟩
  · filter_upwards [hcontM, hcontN] with ω h1 h2 using h1.add h2
  · filter_upwards [hτev, hσev] with ω h1 h2 t
    filter_upwards [h1 t, h2 t] with n a b using le_min a b
  · rw [stoppedProcess_add]
    refine Martingale.add ?_ ?_
    · have h := (hmartM n).stoppedProcess_of_continuous (continuous_stoppedProcess hMc (τ n))
        (hσ n)
      rwa [stoppedProcess_stoppedProcess_min, funext fun ω => min_comm (σ n ω) (τ n ω)] at h
    · exact (stoppedProcess_stoppedProcess_min (σ n) (τ n)) ▸
        (hmartN n).stoppedProcess_of_continuous (continuous_stoppedProcess hNc (σ n)) (hτ n)

/-- The difference of two continuous local martingales with everywhere continuous paths is a
continuous local martingale. -/
theorem IsContLocalMartingale.sub {M N : ℝ≥0 → Ω → ℝ} (hM : IsContLocalMartingale ℱ M P)
    (hN : IsContLocalMartingale ℱ N P) (hMc : ∀ ω, Continuous fun t => M t ω)
    (hNc : ∀ ω, Continuous fun t => N t ω) : IsContLocalMartingale ℱ (M - N) P := by
  have h := hM.add hN.neg hMc fun ω => (hNc ω).neg
  rwa [← sub_eq_add_neg] at h

end ComplexSLE
