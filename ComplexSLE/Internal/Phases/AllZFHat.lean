/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.PolarThetaHat

/-!
# The state `f_{σ_z(s)}(z)` at the σ-time is `ℱ_{σ_z(s)}`-measurable

`fHat hU z s ω = f_{σ_z(s)}(z)` (set to `0` off the a.s. full domain `sigmaDom`). Exactly as for
`θ̂` (`isStronglyProgressive_thetaHat` in `PolarThetaHat.lean`), it is the pointwise limit of
`1_{s < A(τ_k)} f_{σ^k_s ∧ τ_k}(z)`, and each term is measurable for the stopped σ-time σ-algebra
`ℱ_{σ^k_s} ≤ ℱ_{σ_z(s)}` (`stoppedF` is progressive, `σ^k_s` a bounded stopping time).

* `measurable_fHat`: `fHat hU z s` is `sigmaFiltration hU z s`-measurable, i.e. measurable for
  `(isStoppingTime_sigmaTop hU z s).measurableSpace`;
* `fHat_eq_fPath`: on `{s ∈ sigmaDom}`, `fHat s = f_{σ_z(s)}(z)`.

It is the random value `f_τ(z)` at the stopping time `τ = σ_z(s)` used in the strong Markov step
of Lemma 3.2.
-/

public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal.Polar

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

variable (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ)

open Classical in
/-- `f̂_s = f_{σ_z(s)}(z)` on `sigmaDom` (a.s. all of `[0, ∞)`), and `0` elsewhere. -/
@[expose] noncomputable def fHat (s : ℝ≥0) (ω : Ω) : ℂ :=
  if (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z then
    fPath (fun r => U r ω) (hU.cont ω) z (sigmaTime (fun r => U r ω) (hU.cont ω) z s) else 0

variable {z}

theorem fHat_of_mem {s : ℝ≥0} {ω : Ω}
    (hs : (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z) :
    fHat hU z s ω =
      fPath (fun r => U r ω) (hU.cont ω) z (sigmaTime (fun r => U r ω) (hU.cont ω) z s) := by
  rw [fHat, ite_eq_left hs]

theorem fHat_of_notMem {s : ℝ≥0} {ω : Ω}
    (hs : (s : ℝ) ∉ sigmaDom (fun r => U r ω) (hU.cont ω) z) : fHat hU z s ω = 0 := by
  rw [fHat, ite_eq_right hs]

/-- On `{s < A(τ_k)}`, `f̂_s = f̃^k_{σ^k_s}` (the stopped state at the stopped σ-time). -/
theorem fHat_eq_stoppedF_sigmaStop {k : ℕ} {s : ℝ≥0} {ω : Ω} (h : s < clockExit hU z k ω) :
    fHat hU z s ω = stoppedF hU z k (sigmaStop hU z k s ω) ω := by
  have hlt := (sigmaStop_lt_exitNN_iff hU).2 h
  obtain ⟨hs, heq⟩ := of_sigmaStop_lt_exitNN hU hlt
  have hz := pos_absorbingTime_of_mem_sigmaDom (hU.cont ω) hs
  rw [fHat_of_mem hU hs, stoppedF_eq hU z k hz, coe_sigmaStop,
    min_eq_left (sigmaStopR_le_exitR hU k s ω), heq]

theorem fHat_eq_zero_of_forall_le {s : ℝ≥0} {ω : Ω} (h : ∀ k, clockExit hU z k ω ≤ s) :
    fHat hU z s ω = 0 := by
  refine fHat_of_notMem hU fun hs => ?_
  obtain ⟨k, hk⟩ := exists_lt_clockExit_of_mem_sigmaDom hU hs
  exact absurd hk (not_lt.2 (h k))

/-- `f̂_s` is measurable for the σ-time σ-algebra `ℱ_{σ_z(s)}`. -/
theorem measurable_fHat (s : ℝ≥0) :
    Measurable[sigmaFiltration hU z s] (fHat hU z s) := by
  let X : ℕ → Ω → ℂ := fun K ω =>
    (if (s : WithTop ℝ≥0) < (clockExit hU z K ω : WithTop ℝ≥0) then (1 : ℂ) else 0) *
      stoppedF hU z K (sigmaStop hU z K s ω) ω
  have hX : ∀ K, StronglyMeasurable[sigmaFiltration hU z s] (X K) := fun K => by
    have h1 : StronglyMeasurable[sigmaFiltration hU z s]
        (fun ω => if (s : WithTop ℝ≥0) < (clockExit hU z K ω : WithTop ℝ≥0) then (1 : ℝ) else 0) :=
      (Infrastructure.isStronglyProgressive_indicator_lt
        (isStoppingTime_clockExit hU K)).stronglyAdapted s
    have h2 : StronglyMeasurable[sigmaFiltration hU z s]
        (fun ω => stoppedF hU z K (sigmaStop hU z K s ω) ω) := by
      have h := measurable_stoppedValue (isStronglyProgressive_stoppedF hU z K)
        (isStoppingTime_sigmaStop hU z K s)
      have e : stoppedValue (stoppedF hU z K) (fun ω => ((sigmaStop hU z K s ω : ℝ≥0) :
          WithTop ℝ≥0)) = fun ω => stoppedF hU z K (sigmaStop hU z K s ω) ω := by
        funext ω; rfl
      rw [e] at h
      exact (h.mono (sigmaStopFiltration_le hU K s) le_rfl).stronglyMeasurable
    have h1' : StronglyMeasurable[sigmaFiltration hU z s]
        (fun ω => if (s : WithTop ℝ≥0) < (clockExit hU z K ω : WithTop ℝ≥0) then (1 : ℂ)
          else 0) := by
      have := (Complex.continuous_ofReal.comp_stronglyMeasurable h1)
      convert this using 2 with ω
      split_ifs <;> simp
    exact h1'.mul h2
  refine (stronglyMeasurable_of_tendsto atTop hX ?_).measurable
  rw [tendsto_pi_nhds]
  intro ω
  by_cases h : ∃ k, s < clockExit hU z k ω
  · obtain ⟨k, hk⟩ := h
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop k] with K hK
    have hK' : s < clockExit hU z K ω := lt_of_lt_of_le hk (clockExit_mono hU ω hK)
    simp only [X, WithTop.coe_lt_coe, hK', ite_true, one_mul]
    exact fHat_eq_stoppedF_sigmaStop hU hK'
  · push Not at h
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun K => ?_)
    have : ¬ ((s : ℝ≥0) : WithTop ℝ≥0) < (clockExit hU z K ω : WithTop ℝ≥0) := by
      rw [WithTop.coe_lt_coe]; exact not_lt.2 (h K)
    simp only [X, this, ite_false, zero_mul]
    exact fHat_eq_zero_of_forall_le hU h

end ComplexSLE.Internal.Polar

end
