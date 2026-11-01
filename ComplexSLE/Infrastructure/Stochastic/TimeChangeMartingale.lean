/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Stochastic.TimeChangeOptionalSampling
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Probability.Process.Stopping

/-!
# Time change of a dominated continuous martingale; first-reach times

External-free ingredients of the time change of a continuous local martingale
(`ComplexSLE.Internal.ExternalProofs.timeChange_isContLocalMartingale`).

Let `σ : ℝ≥0 → Ω → ℝ≥0` be a family of `ℱ`-stopping times, nondecreasing in `s`, and let
`𝒢 s = ℱ_{σ s}`.

* `stronglyAdapted_timeChange`: for a progressive process `X`, `s ↦ X_{σ s}` is `𝒢`-adapted.
* `martingale_timeChange`: if `N` is an `ℱ`-martingale with everywhere continuous paths and
  `|N_t| ≤ Z` for an integrable `Z`, then `s ↦ N_{σ s}` is a `𝒢`-martingale (integrated optional
  sampling at the finite stopping times `σ s ≤ σ t`).
* `firstReach g t`: for a continuous nondecreasing path `g`, the first time `s` with `t ≤ g s`
  (`⊤` if there is none); `firstReach_le_iff` (`firstReach g t ≤ s ↔ t ≤ g s`),
  `le_of_le_firstReach` and `firstReach_stopped` (`g (s ∧ firstReach g t) = g s ∧ t` when
  `g 0 = 0`).
* `timeChangeInv σ T`: the pathwise `firstReach`. For an `ℱ`-stopping time `T` it is a
  `𝒢`-stopping time (`isStoppingTime_timeChangeInv`), and the time-changed process stopped at it
  is the time change of the process stopped at `T` (`stoppedProcess_timeChange`).
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory Filter Set

namespace ComplexSLE.Infrastructure

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}

/-! ### Adaptedness and the martingale property of `s ↦ N_{σ s}` -/

/-- A progressive process evaluated at the stopping times `σ s` is adapted to `𝒢 s = ℱ_{σ s}`. -/
theorem stronglyAdapted_timeChange {X : ℝ≥0 → Ω → ℝ} (hX : IsStronglyProgressive ℱ X)
    {σ : ℝ≥0 → Ω → ℝ≥0} (hσ : ∀ s, IsStoppingTime ℱ fun ω => (σ s ω : WithTop ℝ≥0))
    (𝒢 : Filtration ℝ≥0 m) (h𝒢 : ∀ s, 𝒢 s = (hσ s).measurableSpace) :
    StronglyAdapted 𝒢 fun s ω => X (σ s ω) ω := by
  intro s
  have h := measurable_stoppedValue hX (hσ s)
  rw [h𝒢 s]
  exact h.stronglyMeasurable

section TimeChange

variable [IsFiniteMeasure P]

/-- **Time change of a dominated continuous martingale.** If `N` is an `ℱ`-martingale with
everywhere continuous paths, `|N_t| ≤ Z` for an integrable `Z`, `σ s` are `ℝ≥0`-valued
`ℱ`-stopping times, nondecreasing in `s`, and `𝒢 s = ℱ_{σ s}`, then `s ↦ N_{σ s}` is a
`𝒢`-martingale. -/
theorem martingale_timeChange {N : ℝ≥0 → Ω → ℝ} (hN : Martingale N ℱ P)
    (hNc : ∀ ω, Continuous fun t => N t ω) {Z : Ω → ℝ} (hZ : Integrable Z P)
    (hNZ : ∀ t ω, |N t ω| ≤ Z ω) {σ : ℝ≥0 → Ω → ℝ≥0}
    (hσ : ∀ s, IsStoppingTime ℱ fun ω => (σ s ω : WithTop ℝ≥0))
    (hσm : ∀ ω, Monotone fun s => σ s ω) (𝒢 : Filtration ℝ≥0 m)
    (h𝒢 : ∀ s, 𝒢 s = (hσ s).measurableSpace) :
    Martingale (fun s ω => N (σ s ω) ω) 𝒢 P := by
  have hprog : IsStronglyProgressive ℱ N :=
    hN.stronglyAdapted.isStronglyProgressive_of_continuous hNc
  have hadapt := stronglyAdapted_timeChange hprog hσ 𝒢 h𝒢
  have hint : ∀ t, Integrable (fun ω => N (σ t ω) ω) P := fun t =>
    hZ.mono' ((hadapt t).mono (𝒢.le t)).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hNZ _ _)
  refine ⟨hadapt, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝒢.le s) (hint t)
    (fun A _ _ => (hint s).integrableOn) (fun A hA _ => ?_)
    (hadapt s).aestronglyMeasurable).symm
  have hA' : MeasurableSet[(hσ s).measurableSpace] A := by rw [← h𝒢 s]; exact hA
  exact (setIntegral_apply_eq_of_le_of_dominated hN hNc hZ hNZ (hσ s) (hσ t)
    (fun ω => hσm ω hst) hA').symm

end TimeChange

/-! ### First-reach times of a continuous nondecreasing path -/

/-- The first time `s` at which the path `g` reaches the level `t`, i.e. `t ≤ g s`; `⊤` if it never
does. -/
noncomputable def firstReach (g : ℝ≥0 → ℝ≥0) (t : WithTop ℝ≥0) : WithTop ℝ≥0 :=
  open scoped Classical in
  if ∃ s : ℝ≥0, t ≤ (g s : WithTop ℝ≥0) then
    ((sInf {s : ℝ≥0 | t ≤ (g s : WithTop ℝ≥0)} : ℝ≥0) : WithTop ℝ≥0) else ⊤

theorem isClosed_le_coe (t : WithTop ℝ≥0) : IsClosed {x : ℝ≥0 | t ≤ (x : WithTop ℝ≥0)} := by
  cases t with
  | top =>
    have : {x : ℝ≥0 | (⊤ : WithTop ℝ≥0) ≤ (x : WithTop ℝ≥0)} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact WithTop.not_top_le_coe x
    rw [this]; exact isClosed_empty
  | coe a =>
    have : {x : ℝ≥0 | (a : WithTop ℝ≥0) ≤ (x : WithTop ℝ≥0)} = Ici a := by
      ext x; simp only [mem_ofPred_eq, mem_Ici]; exact WithTop.coe_le_coe
    rw [this]; exact isClosed_Ici

section FirstReach

variable {g : ℝ≥0 → ℝ≥0} {t : WithTop ℝ≥0}

theorem firstReach_of_exists (h : ∃ s : ℝ≥0, t ≤ (g s : WithTop ℝ≥0)) :
    firstReach g t = ((sInf {s : ℝ≥0 | t ≤ (g s : WithTop ℝ≥0)} : ℝ≥0) : WithTop ℝ≥0) := by
  unfold firstReach
  exact ite_eq_left h

theorem firstReach_of_not_exists (h : ¬ ∃ s : ℝ≥0, t ≤ (g s : WithTop ℝ≥0)) :
    firstReach g t = ⊤ := by
  unfold firstReach
  exact ite_eq_right h

/-- `firstReach g t ≤ s` iff `t ≤ g s` (continuous nondecreasing `g`). -/
theorem firstReach_le_iff (hc : Continuous g) (hm : Monotone g) (s : ℝ≥0) :
    firstReach g t ≤ (s : WithTop ℝ≥0) ↔ t ≤ (g s : WithTop ℝ≥0) := by
  constructor
  · intro h
    by_cases hex : ∃ u : ℝ≥0, t ≤ (g u : WithTop ℝ≥0)
    · rw [firstReach_of_exists hex, WithTop.coe_le_coe] at h
      have hS : IsClosed {u : ℝ≥0 | t ≤ (g u : WithTop ℝ≥0)} :=
        (isClosed_le_coe t).preimage hc
      have hmem := hS.csInf_mem hex (OrderBot.bddBelow _)
      exact hmem.trans (WithTop.coe_le_coe.2 (hm h))
    · rw [firstReach_of_not_exists hex] at h
      exact absurd h (WithTop.not_top_le_coe _)
  · intro h
    have hex : ∃ u : ℝ≥0, t ≤ (g u : WithTop ℝ≥0) := ⟨s, h⟩
    rw [firstReach_of_exists hex, WithTop.coe_le_coe]
    exact csInf_le (OrderBot.bddBelow _) h

/-- Before `firstReach g t`, the path stays below `t` (also at the first-reach time itself, where
`g 0 = 0` is needed in case it is `0`). -/
theorem coe_le_of_le_firstReach (hc : Continuous g) (h0 : g 0 = 0) {s : ℝ≥0}
    (hs : (s : WithTop ℝ≥0) ≤ firstReach g t) : (g s : WithTop ℝ≥0) ≤ t := by
  cases t with
  | top => exact le_top
  | coe a =>
    by_cases hex : ∃ u : ℝ≥0, ((a : ℝ≥0) : WithTop ℝ≥0) ≤ (g u : WithTop ℝ≥0)
    · rw [firstReach_of_exists hex, WithTop.coe_le_coe] at hs
      set r := sInf {u : ℝ≥0 | ((a : ℝ≥0) : WithTop ℝ≥0) ≤ (g u : WithTop ℝ≥0)} with hr
      have hlt : ∀ u, u < r → g u < a := by
        intro u hu
        by_contra hcon
        have : ((a : ℝ≥0) : WithTop ℝ≥0) ≤ (g u : WithTop ℝ≥0) :=
          WithTop.coe_le_coe.2 (not_lt.1 hcon)
        exact absurd (csInf_le (OrderBot.bddBelow _) this) (not_le.2 hu)
      rw [WithTop.coe_le_coe]
      rcases eq_or_lt_of_le hs with hsr | hsr
      · -- `s = r`
        rcases eq_or_ne r 0 with hr0 | hr0
        · rw [hsr, hr0, h0]; exact zero_le
        · have hrpos : 0 < r := pos_iff_ne_zero.2 hr0
          have hcl : IsClosed {u : ℝ≥0 | g u ≤ a} := isClosed_le hc continuous_const
          have hsub : Iio r ⊆ {u : ℝ≥0 | g u ≤ a} := fun u hu => (hlt u hu).le
          have : r ∈ closure (Iio r) := by
            rw [closure_Iio' (a := r) ⟨0, hrpos⟩]; exact mem_Iic.2 le_rfl
          rw [hsr]
          exact hcl.closure_subset_iff.2 hsub this
      · exact (hlt s hsr).le
    · push Not at hex
      exact (hex s).le

/-- **Stopping a time-changed path.** For a continuous nondecreasing `g` with `g 0 = 0`,
`g (s ∧ firstReach g t) = g s ∧ t` (as elements of `WithTop ℝ≥0`). -/
theorem coe_apply_min_firstReach (hc : Continuous g) (hm : Monotone g) (h0 : g 0 = 0)
    (s : ℝ≥0) :
    (g (min (s : WithTop ℝ≥0) (firstReach g t)).untopA : WithTop ℝ≥0) =
      min (g s : WithTop ℝ≥0) t := by
  rcases le_or_gt (s : WithTop ℝ≥0) (firstReach g t) with hs | hs
  · rw [min_eq_left hs]
    have := coe_le_of_le_firstReach hc h0 hs
    rw [min_eq_left this]
    rfl
  · rw [min_eq_right hs.le]
    have hne : firstReach g t ≠ ⊤ := ne_top_of_lt hs
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne
    have hrs : r ≤ s := by
      rw [← hr] at hs
      exact (WithTop.coe_lt_coe.1 hs).le
    have h1 : (g r : WithTop ℝ≥0) ≤ t := coe_le_of_le_firstReach hc h0 hr.le
    have h2 : t ≤ (g r : WithTop ℝ≥0) := (firstReach_le_iff hc hm r).1 hr.ge
    have h3 : t = (g r : WithTop ℝ≥0) := le_antisymm h2 h1
    rw [← hr]
    change (g r : WithTop ℝ≥0) = min (g s : WithTop ℝ≥0) t
    rw [h3, min_eq_right (WithTop.coe_le_coe.2 (hm hrs))]

/-- If `t' n` is eventually above every level, then `firstReach g (t' n)` is eventually above
every level. -/
theorem eventually_le_firstReach (hc : Continuous g) (hm : Monotone g) {t' : ℕ → WithTop ℝ≥0}
    (ht : ∀ u : ℝ≥0, ∀ᶠ n in atTop, (u : WithTop ℝ≥0) ≤ t' n) (s : ℝ≥0) :
    ∀ᶠ n in atTop, (s : WithTop ℝ≥0) ≤ firstReach g (t' n) := by
  filter_upwards [ht (g s + 1)] with n hn
  refine (not_le.1 fun h => ?_).le
  have h' := (firstReach_le_iff hc hm s).1 h
  have : ((g s + 1 : ℝ≥0) : WithTop ℝ≥0) ≤ (g s : WithTop ℝ≥0) := hn.trans h'
  have := WithTop.coe_le_coe.1 this
  exact absurd this (not_le.2 (lt_add_one _))

end FirstReach

/-! ### The inverse time change as a stopping time -/

/-- The pathwise first-reach time of the random level `T` by the time change `σ`. -/
noncomputable def timeChangeInv (σ : ℝ≥0 → Ω → ℝ≥0) (T : Ω → WithTop ℝ≥0) (ω : Ω) :
    WithTop ℝ≥0 :=
  firstReach (fun s => σ s ω) (T ω)

/-- If the levels `T n ω` are eventually above every level, so are the first-reach times
`timeChangeInv σ (T n) ω`. -/
theorem eventually_le_timeChangeInv {σ : ℝ≥0 → Ω → ℝ≥0} {ω : Ω}
    (hσc : Continuous fun s => σ s ω) (hσm : Monotone fun s => σ s ω)
    {T : ℕ → Ω → WithTop ℝ≥0} (hT : ∀ u : ℝ≥0, ∀ᶠ n in atTop, (u : WithTop ℝ≥0) ≤ T n ω)
    (s : ℝ≥0) : ∀ᶠ n in atTop, (s : WithTop ℝ≥0) ≤ timeChangeInv σ (T n) ω :=
  eventually_le_firstReach hσc hσm (t' := fun n => T n ω) hT s

/-- `inf {s | T ≤ σ s}` is a stopping time for the time-changed filtration `𝒢 s = ℱ_{σ s}`. -/
theorem isStoppingTime_timeChangeInv {σ : ℝ≥0 → Ω → ℝ≥0}
    (hσ : ∀ s, IsStoppingTime ℱ fun ω => (σ s ω : WithTop ℝ≥0))
    (hσc : ∀ ω, Continuous fun s => σ s ω) (hσm : ∀ ω, Monotone fun s => σ s ω)
    {T : Ω → WithTop ℝ≥0} (hT : IsStoppingTime ℱ T) (𝒢 : Filtration ℝ≥0 m)
    (h𝒢 : ∀ s, 𝒢 s = (hσ s).measurableSpace) : IsStoppingTime 𝒢 (timeChangeInv σ T) := by
  intro s
  have hset : {ω | timeChangeInv σ T ω ≤ (s : WithTop ℝ≥0)} =
      {ω | T ω ≤ (σ s ω : WithTop ℝ≥0)} := by
    ext ω
    exact firstReach_le_iff (hσc ω) (hσm ω) s
  rw [hset, h𝒢 s]
  exact IsStoppingTime.measurableSet_stopping_time_le hT (hσ s)

/-- `(M ∘ σ)^{inf {s | T ≤ σ s}} = (M^T) ∘ σ`. -/
theorem stoppedProcess_timeChange (M : ℝ≥0 → Ω → ℝ) {σ : ℝ≥0 → Ω → ℝ≥0}
    (hσc : ∀ ω, Continuous fun s => σ s ω) (hσm : ∀ ω, Monotone fun s => σ s ω)
    (hσ0 : ∀ ω, σ 0 ω = 0) (T : Ω → WithTop ℝ≥0) :
    stoppedProcess (fun s ω => M (σ s ω) ω) (timeChangeInv σ T) =
      fun s ω => stoppedProcess M T (σ s ω) ω := by
  funext s ω
  have h := coe_apply_min_firstReach (g := fun s => σ s ω) (t := T ω) (hσc ω) (hσm ω) (hσ0 ω) s
  have h' := congrArg WithTop.untopA h
  simp only [stoppedProcess]
  exact congrArg (fun u => M u ω) h'

end ComplexSLE.Infrastructure
