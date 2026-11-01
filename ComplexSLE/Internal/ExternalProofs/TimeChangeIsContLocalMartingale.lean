/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsContLocalMartingale
public import ComplexSLE.Infrastructure.Stochastic.ContinuousOptionalStopping
public import ComplexSLE.Infrastructure.Stochastic.LocalMartingaleAlgebra
public import ComplexSLE.Infrastructure.Stochastic.TimeChangeExitTimes
public import ComplexSLE.Infrastructure.Stochastic.TimeChangeMartingale

/-!
# Time change of a continuous local martingale (proof of the external input)

A complete proof of the exact statement of
`ComplexSLE.External.timeChange_isContLocalMartingale` (E2c, Revuz–Yor V.1.5).

Route. Let `τ n` be the localising times of `M` and `ρ n` the exit times of `[-n, n]`
(`Infrastructure.capExitTime`, stopping times by path continuity), and put `τ'_n = τ n ∧ ρ n`.

* `N_n = M^{τ'_n}` is a martingale with continuous paths (`Martingale.stoppedProcess_of_continuous`
  twice), dominated by the integrable `n + |M 0|` (`M 0 = (M^{τ n}) 0` is integrable).
* Integrated optional sampling for the finite stopping times `σ s ≤ σ t`, truncation at integer
  horizons and dominated convergence give that `s ↦ N_n (σ s)` is a `𝒢`-martingale
  (`Infrastructure.martingale_timeChange`).
* The localising times of `M ∘ σ` are `ρ'_n = inf {s | τ'_n ≤ σ s}`; they are `𝒢`-stopping times
  since `{ρ'_n ≤ s} = {τ'_n ≤ σ s} ∈ ℱ_{σ s} = 𝒢 s`, they are eventually above every level, and
  `(M ∘ σ)^{ρ'_n} = N_n ∘ σ` because `σ (s ∧ ρ'_n) = σ s ∧ τ'_n` (`σ 0 = 0` is used when
  `ρ'_n = 0`).
* `M ∘ σ` is `𝒢`-adapted (`M` is progressive, `σ s` are stopping times) with continuous paths, hence
  progressive.

This module deliberately does not import `ComplexSLE.External.*`; the statement is a verbatim copy.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Internal.ExternalProofs

open ComplexSLE.Infrastructure

/-- **Time change of continuous local martingales (Revuz–Yor V.1.5).** Same statement as
`ComplexSLE.External.timeChange_isContLocalMartingale`, proved. -/
theorem timeChange_isContLocalMartingale {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 ‹_›) (M : ℝ≥0 → Ω → ℝ)
    (hM : IsContLocalMartingale ℱ M P) (hMc : ∀ ω, Continuous fun t => M t ω)
    (σ : ℝ≥0 → Ω → ℝ≥0)
    (hσ : ∀ s, IsStoppingTime ℱ fun ω => (σ s ω : WithTop ℝ≥0)) (hσ0 : ∀ ω, σ 0 ω = 0)
    (hσc : ∀ ω, Continuous (fun s => σ s ω) ∧ Monotone (fun s => σ s ω))
    (𝒢 : Filtration ℝ≥0 ‹_›) (h𝒢 : ∀ s, 𝒢 s = (hσ s).measurableSpace) :
    IsContLocalMartingale 𝒢 (fun s ω => M (σ s ω) ω) P := by
  obtain ⟨hprog, -, τ, hτ, hτev, hmart⟩ := hM
  have hσcont : ∀ ω, Continuous fun s => σ s ω := fun ω => (hσc ω).1
  have hσmono : ∀ ω, Monotone fun s => σ s ω := fun ω => (hσc ω).2
  have hadapt : StronglyAdapted ℱ M := hprog.stronglyAdapted
  -- `M 0` is integrable: it is `(M^{τ 0}) 0`
  have hM0 : Integrable (M 0) P := by
    have h := (hmart 0).integrable 0
    have hfun : stoppedProcess M (τ 0) 0 = M 0 := by
      funext ω
      simp only [stoppedProcess]
      rw [min_eq_left (by simp)]
      rfl
    rwa [hfun] at h
  -- the bounded localising sequence `τ' n = τ n ∧ capExitTime M n`
  have hρ : ∀ n : ℕ, IsStoppingTime ℱ fun ω => (capExitTime M n ω : WithTop ℝ≥0) := fun n =>
    isStoppingTime_capExitTime hadapt hMc n
  set τ' : ℕ → Ω → WithTop ℝ≥0 := fun n ω => min (τ n ω) (capExitTime M n ω : WithTop ℝ≥0)
    with hτ'def
  have hτ' : ∀ n, IsStoppingTime ℱ (τ' n) := fun n => (hτ n).min (hρ n)
  have hN : ∀ n, Martingale (stoppedProcess M (τ' n)) ℱ P := by
    intro n
    have h := (hmart n).stoppedProcess_of_continuous (continuous_stoppedProcess hMc (τ n))
      (hρ n)
    have e : τ' n = fun ω => min ((capExitTime M n ω : ℝ≥0) : WithTop ℝ≥0) (τ n ω) :=
      funext fun ω => min_comm _ _
    rwa [stoppedProcess_stoppedProcess_min, ← e] at h
  have hNc : ∀ n ω, Continuous fun t => stoppedProcess M (τ' n) t ω := fun n ω =>
    continuous_stoppedProcess hMc (τ' n) ω
  have hZ : ∀ n : ℕ, Integrable (fun ω => (n : ℝ) + |M 0 ω|) P := fun n =>
    (integrable_const _).add hM0.abs
  have hNZ : ∀ (n : ℕ) (t : ℝ≥0) (ω : Ω),
      |stoppedProcess M (τ' n) t ω| ≤ (n : ℝ) + |M 0 ω| := by
    intro n t ω
    simp only [stoppedProcess]
    have hle : (min (t : WithTop ℝ≥0) (τ' n ω)).untopA ≤ capExitTime M n ω := by
      have h1 : min (t : WithTop ℝ≥0) (τ' n ω) ≤ (capExitTime M n ω : WithTop ℝ≥0) :=
        (min_le_right _ _).trans (min_le_right _ _)
      exact WithTop.untopA_mono WithTop.coe_ne_top h1
    refine (abs_apply_le_max_of_le_capExitTime hMc n ω hle).trans ?_
    rw [max_le_iff]
    constructor
    · linarith [abs_nonneg (M 0 ω)]
    · linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  refine ⟨?_, ae_of_all _ fun ω => (hMc ω).comp (hσcont ω), fun n => timeChangeInv σ (τ' n),
    fun n => isStoppingTime_timeChangeInv hσ hσcont hσmono (hτ' n) 𝒢 h𝒢, ?_, fun n => ?_⟩
  · exact (stronglyAdapted_timeChange hprog hσ 𝒢 h𝒢).isStronglyProgressive_of_continuous
      fun ω => (hMc ω).comp (hσcont ω)
  · filter_upwards [hτev] with ω hω s
    refine eventually_le_timeChangeInv (hσcont ω) (hσmono ω) (T := τ') (fun u => ?_) s
    obtain ⟨N₀, hN₀⟩ := exists_forall_le_capExitTime hMc ω u
    filter_upwards [hω u, eventually_ge_atTop N₀] with n hn hnN
    exact le_min hn (WithTop.coe_le_coe.2 (hN₀ n hnN))
  · rw [stoppedProcess_timeChange M hσcont hσmono hσ0 (τ' n)]
    exact martingale_timeChange (hN n) (hNc n) (hZ n) (hNZ n) hσ hσmono 𝒢 h𝒢

end ComplexSLE.Internal.ExternalProofs

end
