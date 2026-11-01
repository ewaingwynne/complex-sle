/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.AllZ
public import ComplexSLE.Internal.Phases.AllZExamples
public import ComplexSLE.Internal.Phases.EventMeasEvents
public import ComplexSLE.Internal.Phases.ErgodicConst
public import ComplexSLE.Internal.Phases.SwallowDistanceAE
public import ComplexSLE.Internal.Driver.BridgeAdapted

/-!
# Proposition 3.1: shared assembly (M7/C2)

The shared part of the proofs of Proposition 3.1(a) and (b) (paper.tex:L1265-1270, L1401-1418).

* `ae_prod_unit_of_ae_ae`: Fubini in the direction needed here. For an everywhere-continuous
  measurable driver `U'` and a measurable event family `E`, if for `ν`-a.e. `u` the event holds
  a.s. at `e^{iu}`, then it holds `P ⊗ ν`-a.s. on the product space `Ω × ℝ`.
* `ae_event_of_ae_ae_unit`: from the fibrewise statement for the adapted version of the driver
  given by the driver bridge (`IsSLEDriver.exists_adapted`) to the statement for every `z ≠ 0` and
  the original driver `U`, by Lemma 3.3 (`lemma_3_3`).
* `scaleInvariantEvents_absorbingTime_eq_top`, `futureDependentEvents_absorbingTime_eq_top`: the
  event `{T_z = ∞}` is the negation of `{T_z < ∞}` (`AllZExamples.lean`), hence scale invariant and
  future dependent;
* `ae_ae_absorbingTime_eq_top`, `ae_ae_absorbingTime_lt_top`: the fibrewise consequences of
  Lemma 3.4 (`not_tendsto_atBot_logFHat`, `tendsto_logFHat_div_of_integralI_neg`) and the
  almost sure forms of Lemma 3.6 and of the ODE comparison (`SwallowDistanceAE.lean`) at the unit
  points `z = e^{iu}`.

The results consume the externals of the Lemma 3.3, Lemma 3.4 and Lemma 3.6 layers, and the
EXTERNAL `markov_oneDim` as the hypothesis `hMO : MarkovOneDim`.
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Internal

open Polar

section Transfer

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {a b c : ℝ}

/-- **Fubini for the event at the random point.** For an adapted `SLE_Σ` driver `U'` and a
measurable event family `E`, if for `ν`-a.e. `u` the event `E (U' ·) e^{iu}` holds a.s., then it
holds `P ⊗ ν`-a.s. on `Ω × ℝ`. -/
theorem ae_prod_unit_of_ae_ae {ℱ : Filtration ℝ≥0 m} {U' : ℝ≥0 → Ω → ℂ}
    (hU' : IsSLEDriverAdapted a b c U' P ℱ) {E : (ℝ≥0 → ℂ) → ℂ → Prop}
    (hEm : MeasurableEvents E) {ν : Measure ℝ} [SFinite P] [SFinite ν]
    (h : ∀ᵐ u ∂ν, ∀ᵐ ω ∂P, E (fun t => U' t ω) (unitPt u)) :
    ∀ᵐ x ∂(P.prod ν), E (fun t => U' t x.1) (Complex.exp ((x.2 : ℂ) * Complex.I)) := by
  obtain ⟨M, hMm, hM⟩ := hEm
  have hUm : ∀ t, Measurable (U' t) := fun t => Measurable.mono (hU'.adapted t) (ℱ.le t) le_rfl
  have hmeas : Measurable fun x : Ω × ℝ => ((fun t => U' t x.1), unitPt x.2) :=
    Measurable.prodMk (measurable_pi_iff.2 fun t => (hUm t).comp measurable_fst)
      (continuous_unitPt.measurable.comp measurable_snd)
  have hS : MeasurableSet {x : Ω × ℝ |
      E (fun t => U' t x.1) (Complex.exp ((x.2 : ℂ) * Complex.I))} := by
    have e : {x : Ω × ℝ | E (fun t => U' t x.1) (Complex.exp ((x.2 : ℂ) * Complex.I))} =
        (fun x : Ω × ℝ => ((fun t => U' t x.1), unitPt x.2)) ⁻¹' M := by
      ext x
      exact hM _ _ (hU'.cont x.1)
    rw [e]
    exact hmeas hMm
  exact ae_prod_of_ae_ae_snd hS h

/-- **Assembly through Lemma 3.3.** Let `U` be an `SLE_Σ` driver, `p` an admissible density and
`E` a measurable, scale invariant and future dependent event family. If for the adapted version
`U'` of `U` (any adapted version) the event `E (U' ·) e^{iu}` holds a.s. for `ν`-a.e. `u`
(`ν = p 1_{[0,2π]} du`), then `E (U ·) z` holds a.s. for every `z ≠ 0`. -/
theorem ae_event_of_ae_ae_unit {U : ℝ≥0 → Ω → ℂ} (ha : 0 < a) (hb : 0 < b)
    (hc : c ^ 2 ≤ a * b) (hU : IsSLEDriver a b c U P) {p : ℝ → ℝ}
    (hp : IsAdmissibleDensity a b c p) {E : (ℝ≥0 → ℂ) → ℂ → Prop}
    (hEm : MeasurableEvents E) (hEs : ScaleInvariantEvents E) (hEf : FutureDependentEvents E)
    (h : ∀ (ℱ : Filtration ℝ≥0 m) (U' : ℝ≥0 → Ω → ℂ),
      IsSLEDriverAdapted a b c U' P ℱ →
        ∀ᵐ u ∂(admissibleMeasure p), ∀ᵐ ω ∂P, E (fun t => U' t ω) (unitPt u)) :
    ∀ z : ℂ, z ≠ 0 → ∀ᵐ ω ∂P, E (fun t => U t ω) z := by
  have hPprob : IsProbabilityMeasure P := hU.isProbabilityMeasure
  have : IsProbabilityMeasure (admissibleMeasure p) := isProbabilityMeasure_admissibleMeasure hp
  have : IsProbabilityMeasure (admissibleLaw p) := isProbabilityMeasure_admissibleLaw hp
  obtain ⟨ℱ, U', hUU', -, -, hU'⟩ := hU.exists_adapted
  have hprod := ae_prod_unit_of_ae_ae hU' hEm (h ℱ U' hU')
  refine lemma_3_3 ha hb hc hU hp hEm hEs hEf ?_
  have hae : ∀ᵐ x ∂(P.prod (admissibleLaw p) : Measure (Ω × ℝ)), ∀ t, U' t x.1 = U t x.1 :=
    (measurePreserving_fst (μ := P) (ν := admissibleLaw p)).quasiMeasurePreserving.ae hUU'
  -- `admissibleLaw p` and `admissibleMeasure p` are the same measure
  have hprod' : ∀ᵐ x ∂(P.prod (admissibleLaw p) : Measure (Ω × ℝ)),
      E (fun t => U' t x.1) (Complex.exp ((x.2 : ℂ) * Complex.I)) := hprod
  filter_upwards [hprod', hae] with x h1 h2
  have e : (fun t => U' t x.1) = fun t => U t x.1 := funext h2
  rw [e] at h1
  exact h1

end Transfer

section Events

theorem scaleInvariantEvents_absorbingTime_eq_top :
    ScaleInvariantEvents fun u z => absorbingTime u z = ⊤ := by
  intro u hu r hr z
  have h := scaleInvariantEvents_absorbingTime_lt_top u hu r hr z
  beta_reduce at h ⊢
  rw [← not_lt_top_iff, ← not_lt_top_iff]
  exact not_congr h

theorem futureDependentEvents_absorbingTime_eq_top :
    FutureDependentEvents fun u z => absorbingTime u z = ⊤ := by
  intro u hu s z hz
  have h := futureDependentEvents_absorbingTime_lt_top u hu s z hz
  beta_reduce at h ⊢
  rw [← not_lt_top_iff, ← not_lt_top_iff]
  exact not_congr h

end Events

section Fibre

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-- On the event `sigmaDom = [0, ∞)`, the process `log |f̂_s(z)|` of the polar layer is the
coordinate `logFHat` at `z = e^{iu}`. -/
theorem logFHat_eq_sigmaLogNorm (hU : IsSLEDriverAdapted a b c U P ℱ) {u : ℝ} {ω : Ω}
    (hω : sigmaDom (fun s => U s ω) (hU.cont ω) (unitPt u) = Ici 0) (s : ℝ≥0) :
    logFHat hU s (ω, u) = sigmaLogNorm hU (unitPt u) s ω := by
  have hs : (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) (unitPt u) := by
    rw [hω]; exact s.coe_nonneg
  simp only [logFHat, fHat_of_mem hU hs, sigmaLogNorm]

/-- **Proposition 3.1(a), fibrewise at the unit points.** If `(I) ≥ 0`, then for `ν`-a.e. `u`,
almost surely `T_{e^{iu}} = ∞`. (Lemma 3.4: `log |f̂_s| ↛ -∞`; Lemma 3.6: `T_z < ∞` forces
`log |f̂_s| → -∞`.) -/
theorem ae_ae_absorbingTime_eq_top [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (hI : 0 ≤ integralI a b c p) :
    ∀ᵐ u ∂(admissibleMeasure p), ∀ᵐ ω ∂P, absorbingTime (fun t => U t ω) (unitPt u) = ⊤ := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  have hfib := ae_ae_of_ae_prod_snd (not_tendsto_atBot_logFHat hMO hU ha hb hc hp hI)
  filter_upwards [hfib] with u hu
  have hz := unitPt_ne_zero u
  filter_upwards [hu, ae_tendsto_sigmaLogNorm_atBot hU ha hc hz,
    ae_sigmaDom_eq_Ici hU (unitPt u) ha hc hz] with ω h1 h2 h3
  by_contra hT
  refine h1 ?_
  exact (h2 (lt_top_iff_ne_top.2 hT)).congr fun s => (logFHat_eq_sigmaLogNorm hU h3 s).symm

/-- **Proposition 3.1(b), fibrewise at the unit points.** If `(I) < 0`, then for `ν`-a.e. `u`,
almost surely `T_{e^{iu}} < ∞`. (Lemma 3.4: `log |f̂_s| / s → (I) < 0`; the ODE comparison turns
this into `T_z < ∞`.) -/
theorem ae_ae_absorbingTime_lt_top [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (hI : integralI a b c p < 0) :
    ∀ᵐ u ∂(admissibleMeasure p), ∀ᵐ ω ∂P, absorbingTime (fun t => U t ω) (unitPt u) < ⊤ := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  have hfib := ae_ae_of_ae_prod_snd (tendsto_logFHat_div_of_integralI_neg hMO hU ha hb hc hp hI)
  filter_upwards [hfib] with u hu
  have hz := unitPt_ne_zero u
  have hα : 0 < -integralI a b c p := neg_pos.2 hI
  filter_upwards [hu, ae_absorbingTime_lt_top_of_tendsto_sigmaLogNorm_div hU ha hc hz hα,
    ae_sigmaDom_eq_Ici hU (unitPt u) ha hc hz] with ω h1 h2 h3
  refine h2 ?_
  rw [neg_neg]
  exact h1.congr fun s => by rw [logFHat_eq_sigmaLogNorm hU h3 s]

end Fibre

end ComplexSLE.Internal

end
