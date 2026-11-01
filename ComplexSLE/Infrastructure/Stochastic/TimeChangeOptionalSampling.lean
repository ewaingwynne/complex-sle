/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Stochastic.ContinuousOptionalStopping
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Optional sampling at two finite stopping times (external-free)

For a martingale `M : ℝ≥0 → Ω → ℝ` with everywhere continuous paths, and `ℝ≥0`-valued stopping
times `S ≤ R`:

* `setIntegral_apply_eq_of_le_of_le_const`: if `R ≤ T` is bounded, then `∫_A M_R = ∫_A M_S` for
  every `A ∈ ℱ_S`. Both stopping times are approximated from above by the dyadic ceilings
  `⌈2^k ·⌉ / 2^k` (countable range, so Mathlib's discrete optional sampling applies); the integrals
  over `A` converge by `integrable_and_tendsto_setIntegral_apply` (uniform integrability of
  `E[M_{T+1} | ℱ_{ρ_k}]`).
* `setIntegral_apply_eq_of_le_of_dominated`: the same for arbitrary finite stopping times when
  `|M_t| ≤ Z` for an integrable `Z`, by truncation at the horizons `k : ℕ` and dominated
  convergence.

No external input is used. These are the optional-sampling inputs of the time change of a local
martingale (`TimeChangeMartingale.lean`).
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory Filter Set

namespace ComplexSLE.Infrastructure

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}

/-- The dyadic ceiling is monotone. -/
theorem dyadicCeil_mono (k : ℕ) {x y : ℝ≥0} (hxy : x ≤ y) : dyadicCeil k x ≤ dyadicCeil k y := by
  exact (dyadicCeil_le_iff k x _).2 (hxy.trans ((dyadicCeil_le_iff k y _).1 le_rfl))

/-- The σ-algebra of a stopping time only depends on the stopping time as a function. -/
theorem measurableSpace_congr_fun {τ₁ τ₂ : Ω → WithTop ℝ≥0} (h₁ : IsStoppingTime ℱ τ₁)
    (h₂ : IsStoppingTime ℱ τ₂) (h : τ₁ = τ₂) : h₁.measurableSpace = h₂.measurableSpace := by
  subst h; rfl

section OptionalSampling

variable [IsFiniteMeasure P]

/-- **Optional sampling at two bounded stopping times** for a continuous martingale:
if `S ≤ R ≤ T` are `ℝ≥0`-valued stopping times and `A ∈ ℱ_S`, then `∫_A M_R = ∫_A M_S`. -/
theorem setIntegral_apply_eq_of_le_of_le_const {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ P)
    (hc : ∀ ω, Continuous fun t => M t ω) {S R : Ω → ℝ≥0}
    (hS : IsStoppingTime ℱ fun ω => (S ω : WithTop ℝ≥0))
    (hR : IsStoppingTime ℱ fun ω => (R ω : WithTop ℝ≥0)) (hSR : ∀ ω, S ω ≤ R ω) {T : ℝ≥0}
    (hRT : ∀ ω, R ω ≤ T) {A : Set Ω} (hA : MeasurableSet[hS.measurableSpace] A) :
    ∫ ω in A, M (R ω) ω ∂P = ∫ ω in A, M (S ω) ω ∂P := by
  have hleR : ∀ k ω, dyadicCeil k (R ω) ≤ T + 1 := fun k ω =>
    ((dyadicCeil_lt k (R ω)).trans_le (add_le_add_left (hRT ω) 1)).le
  have hleS : ∀ k ω, dyadicCeil k (S ω) ≤ T + 1 := fun k ω =>
    ((dyadicCeil_lt k (S ω)).trans_le (add_le_add_left ((hSR ω).trans (hRT ω)) 1)).le
  have hRk := fun k => isStoppingTime_dyadicCeil hR k
  have hSk := fun k => isStoppingTime_dyadicCeil hS k
  have h1 := (integrable_and_tendsto_setIntegral_apply hM hc (n := T + 1)
    (ρ := fun k ω => dyadicCeil k (R ω)) hRk (fun k => countable_range_dyadicCeil R k) hleR
    (fun ω => tendsto_dyadicCeil (R ω))).2 A
  have h2 := (integrable_and_tendsto_setIntegral_apply hM hc (n := T + 1)
    (ρ := fun k ω => dyadicCeil k (S ω)) hSk (fun k => countable_range_dyadicCeil S k) hleS
    (fun ω => tendsto_dyadicCeil (S ω))).2 A
  have heq : ∀ k, ∫ ω in A, M (dyadicCeil k (R ω)) ω ∂P =
      ∫ ω in A, M (dyadicCeil k (S ω)) ω ∂P := by
    intro k
    have hAk : MeasurableSet[(hSk k).measurableSpace] A :=
      hS.measurableSpace_mono (hSk k)
        (fun ω => WithTop.coe_le_coe.2 (le_dyadicCeil k (S ω))) A hA
    have hce := hM.stoppedValue_ae_eq_condExp_of_le_of_countable_range (hRk k) (hSk k)
      (fun ω => WithTop.coe_le_coe.2 (dyadicCeil_mono k (hSR ω)))
      (fun ω => WithTop.coe_le_coe.2 (hleR k ω)) (n := T + 1)
      (countable_range_coe (countable_range_dyadicCeil R k))
      (countable_range_coe (countable_range_dyadicCeil S k))
    rw [stoppedValue_coe, stoppedValue_coe] at hce
    have hint := integrable_apply_nnreal hM (hRk k) (countable_range_dyadicCeil R k) (hleR k)
    have hint' := integrable_apply_nnreal hM (hSk k) (countable_range_dyadicCeil S k) (hleS k)
    have hmeas : MeasurableSet A := (hS.measurableSpace_le) A hA
    rw [← setIntegral_condExp (hSk k).measurableSpace_le hint hAk]
    exact (setIntegral_congr_ae hmeas (by filter_upwards [hce] with ω hω _ using hω)).symm
  exact tendsto_nhds_unique h1 (h2.congr fun k => (heq k).symm)

/-- **Optional sampling at two finite stopping times** for a continuous martingale dominated by an
integrable function: if `S ≤ R` are `ℝ≥0`-valued stopping times, `|M_t| ≤ Z` with `Z` integrable
and `A ∈ ℱ_S`, then `∫_A M_R = ∫_A M_S`. -/
theorem setIntegral_apply_eq_of_le_of_dominated {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ P)
    (hc : ∀ ω, Continuous fun t => M t ω) {Z : Ω → ℝ} (hZ : Integrable Z P)
    (hMZ : ∀ t ω, |M t ω| ≤ Z ω) {S R : Ω → ℝ≥0}
    (hS : IsStoppingTime ℱ fun ω => (S ω : WithTop ℝ≥0))
    (hR : IsStoppingTime ℱ fun ω => (R ω : WithTop ℝ≥0)) (hSR : ∀ ω, S ω ≤ R ω)
    {A : Set Ω} (hA : MeasurableSet[hS.measurableSpace] A) :
    ∫ ω in A, M (R ω) ω ∂P = ∫ ω in A, M (S ω) ω ∂P := by
  have hAm : MeasurableSet A := hS.measurableSpace_le A hA
  set Ak : ℕ → Set Ω := fun k => A ∩ {ω | (S ω : WithTop ℝ≥0) ≤ ((k : ℝ≥0) : WithTop ℝ≥0)}
    with hAkdef
  have hSk : ∀ k : ℕ, IsStoppingTime ℱ fun ω => ((min (k : ℝ≥0) (S ω) : ℝ≥0) : WithTop ℝ≥0) :=
    fun k => isStoppingTime_min_const_nnreal hS k
  have hAk : ∀ k : ℕ, MeasurableSet[(hSk k).measurableSpace] (Ak k) := by
    intro k
    have h2 := (hS.measurableSet_inter_le_const_iff A (k : ℝ≥0)).1
      (hA.inter (hS.measurableSet_le' (k : ℝ≥0)))
    have hcongr := measurableSpace_congr_fun (hS.min_const (k : ℝ≥0)) (hSk k)
      (funext fun ω => by simp only [WithTop.coe_min, min_comm])
    rw [hcongr] at h2
    exact h2
  have hAkm : ∀ k : ℕ, MeasurableSet (Ak k) := fun k => (hSk k).measurableSpace_le _ (hAk k)
  -- the truncated statement
  have key : ∀ (X : Ω → ℝ≥0), (∀ ω, S ω ≤ X ω) →
      IsStoppingTime ℱ (fun ω => (X ω : WithTop ℝ≥0)) →
      Tendsto (fun k : ℕ => ∫ ω in Ak k, M (min (k : ℝ≥0) (X ω)) ω ∂P) atTop
        (𝓝 (∫ ω in A, M (X ω) ω ∂P)) := by
    intro X hSX hX
    have hXk : ∀ k : ℕ, IsStoppingTime ℱ fun ω => ((min (k : ℝ≥0) (X ω) : ℝ≥0) : WithTop ℝ≥0) :=
      fun k => isStoppingTime_min_const_nnreal hX k
    simp only [← integral_indicator (hAkm _)]
    rw [← integral_indicator hAm]
    refine tendsto_integral_of_dominated_convergence Z (fun k => ?_) hZ (fun k => ?_) ?_
    · exact ((integrable_apply_stoppingTime hM hc (hXk k) (t := (k : ℝ≥0))
        (fun ω => min_le_left _ _)).indicator (hAkm k)).aestronglyMeasurable
    · refine ae_of_all _ fun ω => ?_
      refine (norm_indicator_le_norm_self _ _).trans ?_
      rw [Real.norm_eq_abs]
      exact hMZ _ ω
    · refine ae_of_all _ fun ω => ?_
      obtain ⟨K, hK⟩ := exists_nat_ge (X ω)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop K] with k hk
      have hXk' : X ω ≤ (k : ℝ≥0) := hK.trans (by exact_mod_cast hk)
      have hSk' : S ω ≤ (k : ℝ≥0) := (hSX ω).trans hXk'
      have hmem : ω ∈ Ak k ↔ ω ∈ A := by
        simp only [hAkdef, mem_inter_iff, mem_ofPred_eq, WithTop.coe_le_coe, hSk', and_true]
      by_cases hωA : ω ∈ A
      · rw [indicator_of_mem hωA, indicator_of_mem (hmem.2 hωA), min_eq_right hXk']
      · rw [indicator_of_notMem hωA, indicator_of_notMem (fun h => hωA (hmem.1 h))]
  have h1 := key R hSR hR
  have h2 := key S (fun _ => le_rfl) hS
  have hstep : ∀ k : ℕ, ∫ ω in Ak k, M (min (k : ℝ≥0) (R ω)) ω ∂P =
      ∫ ω in Ak k, M (min (k : ℝ≥0) (S ω)) ω ∂P := fun k =>
    setIntegral_apply_eq_of_le_of_le_const hM hc (hSk k)
      (isStoppingTime_min_const_nnreal hR k) (fun ω => min_le_min_left _ (hSR ω)) (T := k)
      (fun ω => min_le_left _ _) (hAk k)
  exact tendsto_nhds_unique h1 (h2.congr fun k => (hstep k).symm)

end OptionalSampling

end ComplexSLE.Infrastructure
