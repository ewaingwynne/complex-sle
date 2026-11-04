/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsSLEDriverAdapted
public import ComplexSLE.Infrastructure.Stochastic.ContinuousModification
import ComplexSLE.Internal.Driver.BridgeVersion
import ComplexSLE.Internal.Driver.Shift

/-!
# From `IsSLEDriver` to an adapted driver

`IsSLEDriver a b c U P` lives on an arbitrary probability space without filtration, with
almost-sure path continuity. The polar layer (`ComplexSLE.Internal.Polar`) needs
`IsSLEDriverAdapted a b c U' P ℱ`: every path continuous, `U'` adapted to `ℱ`, increments
independent of `ℱ s`.

For `hU : IsSLEDriver a b c U P` this file produces

* the everywhere-continuous measurable version `U'` of `U`
  (`ComplexSLE.IsSLEDriver.exists_measurable_version`),
* the filtration `ℱ = bridgeFiltration P U' _`: the natural filtration of `U'` enlarged by the
  measurable `P`-null sets (`bridgeFiltration`),

and proves `IsSLEDriverAdapted a b c U' P ℱ` (`IsSLEDriver.exists_adapted`). The independence of
`U' t - U' s` from `ℱ s` comes from the Markov property at a deterministic time
(`IsSLEDriver.indep_shift_past`) together with the fact that the null sets are independent of
everything (`indep_sup_generateFrom_null`).

No positivity of the covariance (`0 < a`, `c² ≤ a b`) is needed.
-/

@[expose] public section

open scoped NNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE

open Infrastructure

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω}

/-- Null sets do not spoil independence: if `m₁` is independent of `m₂`, it is independent of
`m₂` enlarged by the measurable `P`-null sets. -/
theorem indep_sup_generateFrom_null {m₁ m₂ : MeasurableSpace Ω} (h : Indep m₁ m₂ P) :
    Indep m₁ (m₂ ⊔ MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet[m] N ∧ P N = 0}) P := by
  rw [Indep_iff] at h ⊢
  intro A B hA hB
  obtain ⟨B₀, hB₀, hBB₀⟩ := exists_ae_eq_of_measurableSet_sup hB
  rw [measure_congr (Filter.EventuallyEqSet.inter Filter.EventuallyEq.rfl hBB₀), measure_congr hBB₀]
  exact h A B₀ hA hB₀

/-- The filtration of the bridge: the natural filtration of a measurable process `U`, enlarged by
the measurable `P`-null sets, `ℱ t = σ(U s : s ≤ t) ⊔ σ(null sets)`. -/
noncomputable def bridgeFiltration (P : Measure Ω) (U : ℝ≥0 → Ω → ℂ)
    (hU : ∀ t, Measurable[m] (U t)) : Filtration ℝ≥0 m where
  seq t := Filtration.natural U (fun t => (hU t).stronglyMeasurable) t ⊔
    MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet[m] N ∧ P N = 0}
  mono' _ _ hst := sup_le_sup_right ((Filtration.natural U _).mono hst) _
  le' t := sup_le ((Filtration.natural U _).le t)
    (MeasurableSpace.generateFrom_le fun _ hN => hN.1)

theorem bridgeFiltration_apply (P : Measure Ω) (U : ℝ≥0 → Ω → ℂ) (hU : ∀ t, Measurable[m] (U t))
    (t : ℝ≥0) :
    bridgeFiltration P U hU t =
      Filtration.natural U (fun t => (hU t).stronglyMeasurable) t ⊔
        MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet[m] N ∧ P N = 0} := rfl

/-- Measurable `P`-null sets belong to `ℱ 0`. -/
theorem measurableSet_bridgeFiltration_zero_of_null (P : Measure Ω) (U : ℝ≥0 → Ω → ℂ)
    (hU : ∀ t, Measurable[m] (U t)) {N : Set Ω} (hN : MeasurableSet[m] N) (hN0 : P N = 0) :
    MeasurableSet[bridgeFiltration P U hU 0] N := by
  rw [bridgeFiltration_apply]
  exact (le_sup_right : _ ≤ Filtration.natural U (fun t => (hU t).stronglyMeasurable) 0 ⊔
    MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet[m] N ∧ P N = 0}) _
    (MeasurableSpace.measurableSet_generateFrom ⟨hN, hN0⟩)

theorem le_bridgeFiltration (P : Measure Ω) (U : ℝ≥0 → Ω → ℂ) (hU : ∀ t, Measurable[m] (U t))
    (t : ℝ≥0) :
    Filtration.natural U (fun t => (hU t).stronglyMeasurable) t ≤ bridgeFiltration P U hU t :=
  le_sup_left

namespace IsSLEDriver

variable {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- The increment `U t - U s` is independent of the natural filtration of `U` at time `s`
(Markov property at a deterministic time). -/
theorem indep_increment_natural (hU : IsSLEDriver a b c U P) (hm : ∀ t, Measurable[m] (U t))
    {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (fun ω => U t ω - U s ω) inferInstance)
      (Filtration.natural U (fun t => (hm t).stronglyMeasurable) s) P := by
  rw [Filtration.natural_eq_comap]
  refine indep_of_indep_of_le_left (hU.indep_shift_past s) ?_
  have hh : Measurable (fun y : ℝ≥0 → ℂ => y (t - s)) := measurable_pi_apply _
  have hfun : (fun ω => U t ω - U s ω) =
      (fun y : ℝ≥0 → ℂ => y (t - s)) ∘ (fun ω (r : ℝ≥0) => U (r + s) ω - U s ω) := by
    funext ω
    simp [tsub_add_cancel_of_le hst]
  rw [hfun, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hh.comap_le

/-- **Enlarging by null sets keeps adaptedness.** If `U` is `ℱ`-adapted and `𝒢` is a filtration with
`ℱ t ≤ 𝒢 t ≤ ℱ t ⊔ σ(measurable null sets)`, then `U` is `𝒢`-adapted. -/
theorem _root_.ComplexSLE.IsSLEDriverAdapted.of_le_sup_null {ℱ 𝒢 : Filtration ℝ≥0 m}
    (hU : IsSLEDriverAdapted a b c U P ℱ) (hℱ𝒢 : ∀ t, ℱ t ≤ 𝒢 t)
    (h𝒢 : ∀ t, 𝒢 t ≤
      ℱ t ⊔ MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet[m] N ∧ P N = 0}) :
    IsSLEDriverAdapted a b c U P 𝒢 :=
  ⟨hU.toIsSLEDriver, hU.cont, fun t => (hU.adapted t).mono (hℱ𝒢 t) le_rfl, fun s t hst =>
    indep_of_indep_of_le_right (indep_sup_generateFrom_null (hU.indep_increment s t hst))
      (h𝒢 s)⟩

/-- **Adaptedness of a measurable continuous driver.** If `U` is an `SLE_Σ` driver, every path of
`U` is continuous and every `U t` is measurable, then `U` is an `IsSLEDriverAdapted` driver for
its natural filtration enlarged by the measurable null sets. -/
theorem isAdapted_bridgeFiltration (hU : IsSLEDriver a b c U P)
    (hc : ∀ ω, Continuous fun t => U t ω) (hm : ∀ t, Measurable[m] (U t)) :
    IsSLEDriverAdapted a b c U P (bridgeFiltration P U hm) := by
  refine ⟨hU, hc, fun t => ?_, fun s t hst => ?_⟩
  · exact (comap_measurable (U t)).mono
      (le_trans (le_iSup₂ (f := fun j (_ : j ≤ t) => MeasurableSpace.comap (U j) inferInstance)
        t le_rfl) (le_bridgeFiltration P U hm t)) le_rfl
  · rw [bridgeFiltration_apply]
    exact indep_sup_generateFrom_null (hU.indep_increment_natural hm hst)

/-- **Step 1 of the driver bridge: an adapted version.** For an `SLE_Σ` driver `U` there are a
filtration `ℱ` (the natural filtration of a version `U'` of `U`, enlarged by the measurable
`P`-null sets, which therefore lie in `ℱ 0`) and a process `U'` with `U' = U` a.s. (for all times
simultaneously) such that `IsSLEDriverAdapted a b c U' P ℱ`. Moreover `U' 0 = 0` everywhere. -/
theorem exists_adapted (hU : IsSLEDriver a b c U P) :
    ∃ (ℱ : Filtration ℝ≥0 m) (U' : ℝ≥0 → Ω → ℂ),
      (∀ᵐ ω ∂P, ∀ t, U' t ω = U t ω) ∧ (∀ ω, U' 0 ω = 0) ∧
      (∀ N : Set Ω, MeasurableSet[m] N → P N = 0 → MeasurableSet[ℱ 0] N) ∧
      IsSLEDriverAdapted a b c U' P ℱ := by
  obtain ⟨N, U', hNm, hN0, hout, -, hcont, hzero, hmeas, hU'⟩ := hU.exists_measurable_version
  refine ⟨bridgeFiltration P U' hmeas, U', ?_, hzero,
    fun N' hN' hN'0 => measurableSet_bridgeFiltration_zero_of_null P U' hmeas hN' hN'0,
    hU'.isAdapted_bridgeFiltration hcont hmeas⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω t using hout ω hω t

end IsSLEDriver

end ComplexSLE

end
