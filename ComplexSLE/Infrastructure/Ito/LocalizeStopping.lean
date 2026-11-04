/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Stochastic.ContinuousModification
public import ComplexSLE.Infrastructure.Stochastic.ContinuousOptionalStopping
public import ComplexSLE.Infrastructure.Stochastic.LocalMartingaleAlgebra
public import ComplexSLE.Infrastructure.Stochastic.ProgressiveTools

/-!
# Stopping and localisation of almost surely continuous local martingales (external-free)

Source-independent tools for the localisation of Itô's formula for an arbitrary filtration (neither
complete nor right-continuous).

* `martingale_stoppedProcess_of_ae_continuous`: a progressively measurable martingale with *almost
  surely* continuous paths, stopped at an arbitrary stopping time, is a martingale. (Route: pass to
  the everywhere continuous version for the completed filtration, stop it there, and transfer the
  result back with `martingale_of_ae_eq_of_le_sup_null`.)
* `isContLocalMartingale_stoppedProcess_of_ae_continuous`: the same for continuous local
  martingales.
* `isContLocalMartingale_of_martingale`: a progressive martingale with a.s. continuous paths is a
  continuous local martingale (localising sequence `τ n = ∞`).
* `martingale_of_isContLocalMartingale_of_bounded`: a continuous local martingale that is almost
  surely bounded in absolute value by a constant is a martingale (dominated convergence along the
  localising sequence).
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Infrastructure

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}

/-- **Optional stopping for martingales with almost surely continuous paths.** A progressively
measurable `ℱ`-martingale `M` whose paths are continuous almost surely (the exceptional null set
need not belong to `ℱ`) stays a martingale after stopping at an arbitrary `ℱ`-stopping time. -/
theorem martingale_stoppedProcess_of_ae_continuous [IsFiniteMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ P) (hprog : IsStronglyProgressive ℱ M)
    (hMc : ∀ᵐ ω ∂P, Continuous fun t => M t ω) {ρ : Ω → WithTop ℝ≥0}
    (hρ : IsStoppingTime ℱ ρ) : Martingale (stoppedProcess M ρ) ℱ P := by
  obtain ⟨N, hNmeas, hN0, hNcont⟩ := exists_null_measurableSet_continuous hMc
  let 𝒢 : Filtration ℝ≥0 m :=
    { seq := fun t => ℱ t ⊔ MeasurableSpace.generateFrom
        {N : Set Ω | MeasurableSet[m] N ∧ P N = 0}
      mono' := fun _ _ hst => sup_le_sup_right (ℱ.mono hst) _
      le' := fun t => sup_le (ℱ.le t) (MeasurableSpace.generateFrom_le fun _ hN => hN.1) }
  have hℱ𝒢 : ∀ t, ℱ t ≤ 𝒢 t := fun t => le_sup_left
  have hN𝒢 : MeasurableSet[𝒢 0] N :=
    (le_sup_right : _ ≤ ℱ 0 ⊔ MeasurableSpace.generateFrom
      {N : Set Ω | MeasurableSet[m] N ∧ P N = 0}) _
      (MeasurableSpace.measurableSet_generateFrom ⟨hNmeas, hN0⟩)
  have hae : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  -- the everywhere continuous version `M'`
  set M' : ℝ≥0 → Ω → ℝ := fun t ω => Nᶜ.indicator (M t) ω with hM'
  have hM'c : ∀ ω, Continuous fun t => M' t ω := fun ω => by
    by_cases hω : ω ∈ N
    · have : (fun t => M' t ω) = fun _ => (0 : ℝ) := funext fun t => by simp [hM', hω]
      rw [this]; exact continuous_const
    · have : (fun t => M' t ω) = fun t => M t ω := funext fun t => by simp [hM', hω]
      rw [this]; exact hNcont ω hω
  have hM'ad : StronglyAdapted 𝒢 M' := fun t =>
    ((hM.stronglyAdapted t).mono (hℱ𝒢 t)).indicator
      ((𝒢.mono (zero_le : (0 : ℝ≥0) ≤ t) _ hN𝒢).compl)
  have hM'ae : ∀ t, M' t =ᵐ[P] M t := fun t => by
    filter_upwards [hae] with ω hω
    simp [hM', hω]
  have hM'mart : Martingale M' 𝒢 P :=
    martingale_of_ae_eq_of_le_sup_null (fun t => le_rfl) hM hM'ad hM'ae
  have hρ𝒢 : IsStoppingTime 𝒢 ρ := fun t => hℱ𝒢 t _ (hρ t)
  have h1 : Martingale (stoppedProcess M' ρ) 𝒢 P := hM'mart.stoppedProcess_of_continuous hM'c hρ𝒢
  refine martingale_of_ae_eq_of_le_sup_null (ℱ := 𝒢) (𝒢 := ℱ)
    (fun t => (hℱ𝒢 t).trans le_sup_left) h1 (hprog.stronglyAdapted_stoppedProcess hρ) fun t => ?_
  filter_upwards [hae] with ω hω
  simp [stoppedProcess, hM', hω]

/-- A progressive martingale with almost surely continuous paths is a continuous local martingale
(localising sequence `τ n = ∞`). -/
theorem isContLocalMartingale_of_martingale {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ P)
    (hprog : IsStronglyProgressive ℱ M) (hc : ∀ᵐ ω ∂P, Continuous fun t => M t ω) :
    IsContLocalMartingale ℱ M P := by
  refine ⟨hprog, hc, fun _ _ => ⊤, fun n => ?_, ?_, fun n => ?_⟩
  · intro i
    have : {ω : Ω | (⊤ : WithTop ℝ≥0) ≤ (i : WithTop ℝ≥0)} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, top_le_iff]
      exact WithTop.coe_ne_top
    rw [this]
    exact @MeasurableSet.empty _ (ℱ i)
  · exact Eventually.of_forall fun ω t => Eventually.of_forall fun n => le_top
  · have : stoppedProcess M (fun _ => (⊤ : WithTop ℝ≥0)) = M := by
      ext t ω
      exact stoppedProcess_eq_of_le le_top
    rw [this]
    exact hM

/-- **Stopping a continuous local martingale (a.s. continuity suffices).** For an `ℱ`-continuous
local martingale `M` and an arbitrary `ℱ`-stopping time `ρ`, the stopped process `M^ρ` is again a
continuous local martingale. No everywhere continuity of the paths is needed. -/
theorem isContLocalMartingale_stoppedProcess_of_ae_continuous [IsFiniteMeasure P]
    {M : ℝ≥0 → Ω → ℝ} (hM : IsContLocalMartingale ℱ M P) {ρ : Ω → WithTop ℝ≥0}
    (hρ : IsStoppingTime ℱ ρ) : IsContLocalMartingale ℱ (stoppedProcess M ρ) P := by
  obtain ⟨hprog, hcont, τ, hτ, hτev, hmart⟩ := hM
  refine ⟨hprog.stoppedProcess hρ, ?_, τ, hτ, hτev, fun n => ?_⟩
  · filter_upwards [hcont] with ω h
    exact h.comp (continuous_untopA_min (ρ ω))
  · have h1 : stoppedProcess (stoppedProcess M ρ) (τ n) =
        stoppedProcess (stoppedProcess M (τ n)) ρ := by
      rw [stoppedProcess_stoppedProcess_min, stoppedProcess_stoppedProcess_min]
      congr 1
      funext ω
      exact min_comm _ _
    rw [h1]
    refine martingale_stoppedProcess_of_ae_continuous (hmart n) (hprog.stoppedProcess (hτ n)) ?_ hρ
    filter_upwards [hcont] with ω h
    exact h.comp (continuous_untopA_min (τ n ω))

/-- **A bounded continuous local martingale is a martingale.** Along the localising sequence the
stopped processes are martingales, they converge pointwise to `M`, and they are dominated by the
bound `C`. -/
theorem martingale_of_isContLocalMartingale_of_bounded [IsFiniteMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : IsContLocalMartingale ℱ M P) {C : ℝ} (hb : ∀ᵐ ω ∂P, ∀ t, |M t ω| ≤ C) :
    Martingale M ℱ P := by
  obtain ⟨hprog, -, τ, hτ, hτev, hmart⟩ := hM
  have had := hprog.stronglyAdapted
  have hint : ∀ t, Integrable (M t) P := fun t =>
    Integrable.mono' (integrable_const C) ((had t).mono (ℱ.le t)).aestronglyMeasurable
      (by filter_upwards [hb] with ω h; simpa [Real.norm_eq_abs] using h t)
  refine ⟨had, fun i j hij => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le i) (hint j)
    (fun A _ _ => (hint i).integrableOn) (fun A hA _ => ?_) (had i).aestronglyMeasurable).symm
  have hlim : ∀ t, Tendsto (fun n => ∫ ω in A, stoppedProcess M (τ n) t ω ∂P) atTop
      (𝓝 (∫ ω in A, M t ω ∂P)) := fun t => by
    refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun n => ?_)
      (integrable_const C) (fun n => ?_) ?_
    · exact ((hmart n).integrable t).aestronglyMeasurable.restrict
    · refine ae_restrict_of_ae ?_
      filter_upwards [hb] with ω h
      rw [Real.norm_eq_abs]
      exact h _
    · refine ae_restrict_of_ae ?_
      filter_upwards [hτev] with ω hω
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hω t] with n hn
      exact (stoppedProcess_eq_of_le hn).symm
  have heq : ∀ n, ∫ ω in A, stoppedProcess M (τ n) i ω ∂P =
      ∫ ω in A, stoppedProcess M (τ n) j ω ∂P := fun n => (hmart n).setIntegral_eq hij hA
  have h2 : Tendsto (fun n => ∫ ω in A, stoppedProcess M (τ n) i ω ∂P) atTop
      (𝓝 (∫ ω in A, M j ω ∂P)) := by
    simp only [heq]; exact hlim j
  exact tendsto_nhds_unique (hlim i) h2

end ComplexSLE.Infrastructure

end
