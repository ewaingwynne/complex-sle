/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.External.StrongMarkovSLEDriver
public import ComplexSLE.Internal.Phases.AllZDriverLaw
public import ComplexSLE.Internal.Polar.DriverBridge
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# The strong Markov step of Lemma 3.2

For an adapted `SLE_Σ` driver `U` and an a.s. finite `ℱ`-stopping time `τ`, the post-`τ` driver
`V_s = U_{τ+s} - U_τ` (`postDriver`) is again an `SLE_Σ` driver, independent of `ℱ_τ`
(`External.strongMarkov_sleDriver`, EXTERNAL E3). Combined with the uniqueness of the path law
(`AllZDriverLaw.lean`) this gives the conditional form used in the proof of Lemma 3.2
(paper.tex:L1315-1318, "the conditional law of this latter Loewner chain given `(f_t)_{t ≤ τ}` is
the same as the law of `(f_t)_{t ≥ 0}`"):

* `ae_mem_postDriver`: let `M ⊆ (ℝ≥0 → ℂ) × ℂ` be a measurable set of (path, point) pairs, `X` an
  `ℱ_τ`-measurable random point, and `Z` a set of points such that for every `ξ ∈ Z`, a.s. the
  path of `U` lies in the section `M_ξ`. If `X ∈ Z` a.s., then a.s. the post-`τ` path lies in the
  section `M_X`. (Fubini on the independent pair `(V, X)`; for every fixed `ξ` the law of `V`
  equals the law of `U`.)

Uses the EXTERNAL `strongMarkov_sleDriver`.
-/

public section

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Internal

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- The post-`τ` driver `V_s = U_{τ+s} - U_τ` (with `U_{τ}` read at `(τ ω).untopA`, junk on
`{τ = ⊤}`), the process of the strong Markov property. -/
@[expose] noncomputable def postDriver (U : ℝ≥0 → Ω → ℂ) (τ : Ω → WithTop ℝ≥0) (s : ℝ≥0)
    (ω : Ω) : ℂ :=
  U ((τ ω).untopA + s) ω - U (τ ω).untopA ω

/-- The value of a continuous adapted driver at a measurable random time is measurable. -/
theorem measurable_apply_time (hU : IsSLEDriverAdapted a b c U P ℱ) {T : Ω → ℝ≥0}
    (hT : Measurable T) : Measurable fun ω => U (T ω) ω := by
  have hjoint : Measurable (Function.uncurry U) :=
    measurable_uncurry_of_continuous_of_measurable (fun ω => hU.cont ω) fun t =>
      hU.adapted.measurable
  exact hjoint.comp (hT.prodMk measurable_id)

theorem measurable_postDriver (hU : IsSLEDriverAdapted a b c U P ℱ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime ℱ τ) (s : ℝ≥0) : Measurable (postDriver U τ s) := by
  have hT : Measurable fun ω => (τ ω).untopA := hτ.measurable'.untopA
  exact (measurable_apply_time hU (hT.add_const s)).sub (measurable_apply_time hU hT)

theorem continuous_postDriver (hU : IsSLEDriverAdapted a b c U P ℱ) (τ : Ω → WithTop ℝ≥0)
    (ω : Ω) : Continuous fun s => postDriver U τ s ω := by
  unfold postDriver
  exact ((hU.cont ω).comp (continuous_const.add continuous_id)).sub continuous_const

/-- **Conditional form of the strong Markov property** (for the proof of Lemma 3.2). -/
theorem ae_mem_postDriver (hU : IsSLEDriverAdapted a b c U P ℱ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime ℱ τ) (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) {X : Ω → ℂ}
    (hX : Measurable[hτ.measurableSpace] X) {M : Set ((ℝ≥0 → ℂ) × ℂ)} (hM : MeasurableSet M)
    {Z : Set ℂ} (hZ : ∀ ξ ∈ Z, ∀ᵐ ω ∂P, ((fun t => U t ω), ξ) ∈ M) (hXZ : ∀ᵐ ω ∂P, X ω ∈ Z) :
    ∀ᵐ ω ∂P, ((fun s => postDriver U τ s ω), X ω) ∈ M := by
  have : IsProbabilityMeasure P := hU.toIsSLEDriver.isProbabilityMeasure
  obtain ⟨hVd, hind, -⟩ := External.strongMarkov_sleDriver hU τ hτ hfin
  have hVm : ∀ s, Measurable (postDriver U τ s) := measurable_postDriver hU hτ
  have hVpath : Measurable fun ω (s : ℝ≥0) => postDriver U τ s ω :=
    IsSLEDriver.measurable_path hVm
  have hXm : Measurable X := hX.mono hτ.measurableSpace_le le_rfl
  -- independence of the post-`τ` path and `X`
  have hindep : IndepFun (fun ω (s : ℝ≥0) => postDriver U τ s ω) X P := by
    have e : MeasurableSpace.comap (fun ω (s : ℝ≥0) => postDriver U τ s ω) MeasurableSpace.pi =
        ⨆ s : ℝ≥0, MeasurableSpace.comap
          (fun ω => U ((τ ω).untopA + s) ω - U (τ ω).untopA ω) inferInstance := by
      rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
      refine iSup_congr fun s => ?_
      rw [MeasurableSpace.comap_comp]
      rfl
    have hXle : MeasurableSpace.comap X inferInstance ≤ hτ.measurableSpace :=
      hX.comap_le
    exact indep_of_indep_of_le_right (e ▸ hind) hXle
  have hjoint : P.map (fun ω => ((fun s => postDriver U τ s ω), X ω)) =
      (P.map fun ω (s : ℝ≥0) => postDriver U τ s ω).prod (P.map X) :=
    (indepFun_iff_map_prod_eq_prod_map_map hVpath.aemeasurable hXm.aemeasurable).1 hindep
  have hUm : ∀ t, Measurable (U t) := fun t => hU.adapted.measurable
  rw [ae_iff]
  have hbad : MeasurableSet Mᶜ := hM.compl
  have hmeasPair : Measurable fun ω => ((fun s => postDriver U τ s ω), X ω) :=
    hVpath.prodMk hXm
  have h1 : P {ω | ¬ (((fun s => postDriver U τ s ω), X ω) ∈ M)} =
      (P.map fun ω => ((fun s => postDriver U τ s ω), X ω)) Mᶜ := by
    rw [Measure.map_apply hmeasPair hbad]
    rfl
  have hsec : ∀ ξ ∈ Z, (P.map fun ω (s : ℝ≥0) => postDriver U τ s ω)
      ((fun v => (v, ξ)) ⁻¹' Mᶜ) = 0 := by
    intro ξ hξ
    have hA : MeasurableSet ((fun v => (v, ξ)) ⁻¹' Mᶜ) := measurable_prodMk_right hbad
    rw [Measure.map_apply hVpath hA]
    have h2 := hVd.measure_path_preimage_eq hU.toIsSLEDriver hVm hUm hA
    refine h2.trans ?_
    have h3 := hZ ξ hξ
    rw [ae_iff] at h3
    simpa using h3
  rw [h1, hjoint, Measure.prod_apply_symm hbad,
    lintegral_map (measurable_measure_prodMk_right hbad) hXm]
  have hae : ∀ᵐ ω ∂P, (P.map fun ω (s : ℝ≥0) => postDriver U τ s ω)
      ((fun v => (v, X ω)) ⁻¹' Mᶜ) = 0 := by
    filter_upwards [hXZ] with ω hω using hsec _ hω
  rw [lintegral_congr_ae hae]
  simp

end ComplexSLE.Internal

end
