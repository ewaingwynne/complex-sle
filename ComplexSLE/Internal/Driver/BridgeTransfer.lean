/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsSLEDriverAdapted
public import ComplexSLE.Frozen.Defs.LeftHull
import ComplexSLE.Internal.Driver.BridgeAdapted
import ComplexSLE.Internal.Driver.BridgeProduct
import ComplexSLE.Internal.Driver.Transform

/-!
# Transfer of almost-sure statements along the product extension

Section 3 of the paper works on `Ω × Ω'` with the measure `P.prod ν` carrying the driver and the
random point `𝐳` independently (graph step `step:section3-product-extension`). The statements of the
roots are about the original driver `U` on `(Ω, P)`. This file proves

* `ae_prod_iff_ae_fst`: for a probability measure `ν`, `∀ᵐ x ∂P.prod ν, p x.1 ↔ ∀ᵐ ω ∂P, p ω`
  (`p` arbitrary: no measurability, as the roots read `a.s.` as `null complement`, ruling R9);
* `ae_prod_path_iff`: if `U'' t x = U t x.1` for a.e. `x`, then for every event `E` of paths,
  `∀ᵐ x ∂P.prod ν, E (U'' · x) ↔ ∀ᵐ ω ∂P, E (U · ω)`;
* its specializations to the hull objects of the driver: `ae_prod_absorbingTime_iff` (events of the
  function `z ↦ absorbingTime (U · ω) z`) and `ae_prod_leftHull_iff` (events of the family
  `t ↦ leftHull (U · ω) t`);
* `ae_prod_iff_ae_ae_path`: the Fubini form for events that also depend on the angle;
* `IsSLEDriver.exists_productExtension`: the bundled statement. For every `SLE_Σ` driver `U` on
  `(Ω, P)` and probability measure `ν` on `Ω'` there are a filtration `ℱ''` and a process `U''` on
  `Ω × Ω'` with `U'' = U ∘ fst` a.s., `IsSLEDriverAdapted a b c U'' (P.prod ν) ℱ''`, the angle
  `snd` is `ℱ'' 0`-measurable, has law `ν` and is independent of `U''`.
-/

@[expose] public section

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE

section Transfer

variable {Ω Ω' : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'} {P : Measure Ω}
  {ν : Measure Ω'} [IsProbabilityMeasure ν]

/-- Almost-sure statements about the first coordinate of a product with a probability measure. -/
theorem ae_prod_iff_ae_fst {p : Ω → Prop} :
    (∀ᵐ x ∂(P.prod ν), p x.1) ↔ ∀ᵐ ω ∂P, p ω := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  swap
  · exact (measurePreserving_fst (μ := P) (ν := ν)).quasiMeasurePreserving.ae h
  rw [ae_iff] at h ⊢
  have e : {x : Ω × Ω' | ¬p x.1} = {ω | ¬p ω} ×ˢ (univ : Set Ω') := by
    ext x
    simp
  rw [e, Measure.prod_prod] at h
  simpa using h

/-- **Transfer of path events.** If `U'' t x = U t x.1` for `P.prod ν`-a.e. `x` (for all `t`), then
for every event `E` of paths, `E (U'' · x)` holds a.s. on the product space iff `E (U · ω)` holds
a.s. on `(Ω, P)`. -/
theorem ae_prod_path_iff {U : ℝ≥0 → Ω → ℂ} {U'' : ℝ≥0 → Ω × Ω' → ℂ}
    (h : ∀ᵐ x ∂(P.prod ν), ∀ t, U'' t x = U t x.1) (E : (ℝ≥0 → ℂ) → Prop) :
    (∀ᵐ x ∂(P.prod ν), E fun t => U'' t x) ↔ ∀ᵐ ω ∂P, E fun t => U t ω := by
  rw [← ae_prod_iff_ae_fst (ν := ν) (p := fun ω => E fun t => U t ω)]
  refine Filter.eventually_congr ?_
  filter_upwards [h] with x hx
  have : (fun t => U'' t x) = fun t => U t x.1 := funext hx
  rw [this]

/-- **Transfer of events of the absorbing times.** For every property `E` of the function
`z ↦ T_z` of absorbing times: it holds a.s. for the lifted driver iff it holds a.s. for `U`. -/
theorem ae_prod_absorbingTime_iff {U : ℝ≥0 → Ω → ℂ} {U'' : ℝ≥0 → Ω × Ω' → ℂ}
    (h : ∀ᵐ x ∂(P.prod ν), ∀ t, U'' t x = U t x.1) (E : (ℂ → ℝ≥0∞) → Prop) :
    (∀ᵐ x ∂(P.prod ν), E fun z => absorbingTime (fun t => U'' t x) z) ↔
      ∀ᵐ ω ∂P, E fun z => absorbingTime (fun t => U t ω) z :=
  ae_prod_path_iff h fun γ => E fun z => absorbingTime γ z

/-- **Transfer of events of the left hulls.** For every property `E` of the family `t ↦ L_t` of left
hulls: it holds a.s. for the lifted driver iff it holds a.s. for `U`. -/
theorem ae_prod_leftHull_iff {U : ℝ≥0 → Ω → ℂ} {U'' : ℝ≥0 → Ω × Ω' → ℂ}
    (h : ∀ᵐ x ∂(P.prod ν), ∀ t, U'' t x = U t x.1) (E : (ℝ≥0 → Set ℂ) → Prop) :
    (∀ᵐ x ∂(P.prod ν), E fun t => leftHull (fun s => U'' s x) t) ↔
      ∀ᵐ ω ∂P, E fun t => leftHull (fun s => U s ω) t :=
  ae_prod_path_iff h fun γ => E fun t => leftHull γ t

/-- **Fubini form.** For an event `E` of the pair (path, angle) whose lifted version is a
measurable set of the product space, `E (U'' · x) x.2` holds a.s. on the product iff for a.e. `ω`,
`E (U · ω) u` holds for `ν`-a.e. `u`. -/
theorem ae_prod_iff_ae_ae_path {U : ℝ≥0 → Ω → ℂ} {U'' : ℝ≥0 → Ω × Ω' → ℂ}
    [SFinite P] (h : ∀ᵐ x ∂(P.prod ν), ∀ t, U'' t x = U t x.1) (E : (ℝ≥0 → ℂ) → Ω' → Prop)
    (hE : MeasurableSet {x : Ω × Ω' | E (fun t => U'' t x) x.2}) :
    (∀ᵐ x ∂(P.prod ν), E (fun t => U'' t x) x.2) ↔
      ∀ᵐ ω ∂P, ∀ᵐ u ∂ν, E (fun t => U t ω) u := by
  rw [Measure.ae_prod_iff_ae_ae hE]
  have h' : ∀ᵐ ω ∂P, ∀ᵐ u ∂ν, ∀ t, U'' t (ω, u) = U t ω := by
    have := Measure.ae_ae_of_ae_prod h
    exact this
  refine Filter.eventually_congr ?_
  filter_upwards [h'] with ω hω
  refine Filter.eventually_congr ?_
  filter_upwards [hω] with u hu
  have : (fun t => U'' t (ω, u)) = fun t => U t ω := funext hu
  rw [this]

end Transfer

variable {Ω Ω' : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'}

/-- **Bundled product extension (M7/A1, items 1-3).** For an `SLE_Σ` driver `U` on `(Ω, P)` and a
probability measure `ν` on `Ω'` there are a filtration `ℱ''` of `Ω × Ω'` and a process `U''` such
that

* `U'' t x = U t x.1` for `P.prod ν`-a.e. `x`, for all `t` simultaneously;
* `IsSLEDriverAdapted a b c U'' (P.prod ν) ℱ''` (every path continuous, adapted, increments
  independent of the past);
* `snd` is `ℱ'' 0`-measurable, has law `ν`, and is independent of the path of `U''`.

By `ae_prod_path_iff` (and its specializations) almost-sure statements about `U''` transfer to `U`.
-/
theorem IsSLEDriver.exists_productExtension {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ} {P : Measure Ω}
    (hU : IsSLEDriver a b c U P) (ν : Measure Ω') [IsProbabilityMeasure ν] :
    ∃ (ℱ'' : Filtration ℝ≥0 (m.prod m')) (U'' : ℝ≥0 → Ω × Ω' → ℂ),
      (∀ᵐ x ∂(P.prod ν), ∀ t, U'' t x = U t x.1) ∧
      IsSLEDriverAdapted a b c U'' (P.prod ν) ℱ'' ∧
      Measurable[ℱ'' 0] (Prod.snd : Ω × Ω' → Ω') ∧
      HasLaw (Prod.snd : Ω × Ω' → Ω') ν (P.prod ν) ∧
      IndepFun (Prod.snd : Ω × Ω' → Ω') (fun x (t : ℝ≥0) => U'' t x) (P.prod ν) := by
  obtain ⟨ℱ, U', hae, -, -, hU'⟩ := hU.exists_adapted
  have := hU.isProbabilityMeasure
  refine ⟨prodFiltration m' ℱ, fun t x => U' t x.1, ?_, hU'.prod ν,
    measurable_snd_prodFiltration_zero m' ℱ, hasLaw_snd_prod, hU'.indepFun_snd_path ν⟩
  have h := (measurePreserving_fst (μ := P) (ν := ν)).quasiMeasurePreserving.ae hae
  exact h

end ComplexSLE

end
