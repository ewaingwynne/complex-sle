/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.AllZDriverLaw
public import ComplexSLE.Internal.Phases.AllZMarkov
public import ComplexSLE.Internal.Loewner.Concatenation
public import ComplexSLE.Internal.Loewner.MapTransform
public import ComplexSLE.Internal.Driver.BridgeAdapted

/-!
# Event families for Lemma 3.2 (`lem-all-z`)

The hypotheses of Lemma 3.2 (paper.tex:L1294-1302) on a collection of events
`{𝓔(z)}_{z ∈ ℂ∖{0}}` of the `SLE_Σ` process, formalised as a predicate `E u z` on a (driver path,
point) pair, "pathwise for continuous drivers":

* `ScaleInvariantEvents E` (*scale invariance*): for every continuous driver `u`, `r > 0`,
  `E u z ↔ E (r u(·/r²)) (r z)` (the re-scaled Loewner chain `t ↦ r f_{t/r²}(·/r)` is the one
  driven by `r u(·/r²)`, `centeredLoewnerMap_scale`);
* `FutureDependentEvents E` (*future dependence*): for every continuous driver `u`, `s ≥ 0` and
  `z ∉ L_s` (i.e. `s < T_z`), `E u z ↔ E (u(· + s) - u s) (f_s z)` (the chain `f_{s,s+t}` of (2.3)
  is the one driven by `u(· + s) - u s`, `centeredLoewnerMap_add_eq`);
* `MeasurableEvents E` (*the events are events*): on continuous paths, `E` is the section of a
  jointly measurable set of (path, point) pairs for the product σ-algebra of `ℝ≥0 → ℂ`
  (equivalently the cylinder σ-algebra of `C(ℝ≥0, ℂ)`). This is the implicit measurability of the
  "events" of the source, needed so that a.s. statements transfer between processes with the same
  law (a non-measurable family can distinguish two drivers with the same path law).

The pathwise reading of scale invariance and future dependence is stronger than the source's
"almost surely"; both examples of the source ({T_z < ∞} and `lim dist(z, L_t) = 0`) satisfy it for
every continuous driver.

`mem_cone_of_direction`: if `ζ = ξ/|ξ|` satisfies "`E(·, ζ)` holds a.s." for a driver `U` (in the
measurable form), so does `ξ` (scale invariance and the equality of the law of `U` with that of the
Brownian-rescaled driver).
-/

@[expose] public section

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Internal

/-- **Scale invariance** of an event family (Lemma 3.2, paper.tex:L1297), pathwise for continuous
drivers. -/
def ScaleInvariantEvents (E : (ℝ≥0 → ℂ) → ℂ → Prop) : Prop :=
  ∀ u : ℝ≥0 → ℂ, Continuous u → ∀ r : ℝ≥0, 0 < r → ∀ z : ℂ,
    E u z ↔ E (fun s => (r : ℂ) * u (s / r ^ 2)) ((r : ℂ) * z)

/-- **Future dependence** of an event family (Lemma 3.2, paper.tex:L1298), pathwise for
continuous drivers: for `z ∉ L_s`, `E(z)` occurs iff `E(f_s(z))` occurs for the chain driven by
`u(· + s) - u s`. -/
def FutureDependentEvents (E : (ℝ≥0 → ℂ) → ℂ → Prop) : Prop :=
  ∀ (u : ℝ≥0 → ℂ) (hu : Continuous u) (s : ℝ≥0) (z : ℂ) (hz : z ∈ (leftHull u s)ᶜ),
    E u z ↔ E (fun r => u (r + s) - u s) (centeredLoewnerMap u hu s ⟨z, hz⟩)

/-- **Measurability** of an event family: on continuous paths, `E` is a section of a measurable
set of the product `(ℝ≥0 → ℂ) × ℂ`. -/
def MeasurableEvents (E : (ℝ≥0 → ℂ) → ℂ → Prop) : Prop :=
  ∃ M : Set ((ℝ≥0 → ℂ) × ℂ), MeasurableSet M ∧
    ∀ (u : ℝ≥0 → ℂ) (z : ℂ), Continuous u → (E u z ↔ (u, z) ∈ M)

/-- **Scale invariance of the almost-sure event.** Let `U` be an everywhere-continuous adapted
`SLE_Σ` driver and `M` a measurable set of (path, point) pairs on which `E` is a section. If
`ξ ≠ 0` and `E(·, ξ/|ξ|)` holds a.s. for `U`, then `E(·, ξ)` holds a.s. for `U`. -/
theorem mem_cone_of_direction {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 m} {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}
    (hU : IsSLEDriverAdapted a b c U P ℱ) {E : (ℝ≥0 → ℂ) → ℂ → Prop}
    (hEs : ScaleInvariantEvents E) {M : Set ((ℝ≥0 → ℂ) × ℂ)} (hM : MeasurableSet M)
    (hEM : ∀ (u : ℝ≥0 → ℂ) (z : ℂ), Continuous u → (E u z ↔ (u, z) ∈ M)) {ξ : ℂ}
    (hξ : ξ ≠ 0) (hdir : ∀ᵐ ω ∂P, ((fun t => U t ω), ξ / (‖ξ‖ : ℂ)) ∈ M) :
    ∀ᵐ ω ∂P, ((fun t => U t ω), ξ) ∈ M := by
  have hnorm : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  set r : ℝ≥0 := ‖ξ‖₊⁻¹ with hr
  have hr0 : 0 < r := by rw [hr]; exact inv_pos.2 (nnnorm_pos.2 hξ)
  have hrC : (r : ℂ) * ξ = ξ / (‖ξ‖ : ℂ) := by
    rw [hr]
    have : ((‖ξ‖₊⁻¹ : ℝ≥0) : ℂ) = (‖ξ‖ : ℂ)⁻¹ := by
      rw [show ((‖ξ‖₊⁻¹ : ℝ≥0) : ℂ) = (((‖ξ‖₊⁻¹ : ℝ≥0) : ℝ) : ℂ) from rfl, NNReal.coe_inv]
      simp
    rw [this, div_eq_inv_mul]
  have hUm : ∀ t, Measurable (U t) := fun t => hU.adapted.measurable
  set U' : ℝ≥0 → Ω → ℂ := fun s ω => (r : ℂ) * U (s / r ^ 2) ω with hU'
  have hscaled : IsSLEDriver a b c U' P := hU.toIsSLEDriver.scale r hr0
  have hU'm : ∀ t, Measurable (U' t) := fun t => measurable_const.mul (hUm _)
  have hsec : MeasurableSet ((fun v : ℝ≥0 → ℂ => (v, ξ / (‖ξ‖ : ℂ))) ⁻¹' Mᶜ) :=
    measurable_prodMk_right hM.compl
  have hlaw := hscaled.measure_path_preimage_eq hU.toIsSLEDriver hU'm hUm hsec
  have hnull : P {ω | (fun t => U t ω) ∈
      (fun v : ℝ≥0 → ℂ => (v, ξ / (‖ξ‖ : ℂ))) ⁻¹' Mᶜ} = 0 := by
    rw [ae_iff] at hdir
    exact hdir
  have hnull' : P {ω | (fun t => U' t ω) ∈
      (fun v : ℝ≥0 → ℂ => (v, ξ / (‖ξ‖ : ℂ))) ⁻¹' Mᶜ} = 0 := hlaw.trans hnull
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hnull'
  simp only [mem_ofPred_eq, mem_preimage, mem_compl_iff] at hω ⊢
  have hcont : Continuous fun t => U t ω := hU.cont ω
  have hcont' : Continuous fun t => U' t ω :=
    continuous_const.mul ((hU.cont ω).comp (continuous_id.div_const _))
  intro hmem'
  apply hω
  have h1 : E (fun t => U' t ω) (ξ / (‖ξ‖ : ℂ)) := (hEM _ _ hcont').2 hmem'
  rw [← hrC] at h1
  exact (hEM _ _ hcont).1 ((hEs _ hcont r hr0 ξ).2 h1)

end ComplexSLE.Internal

end
