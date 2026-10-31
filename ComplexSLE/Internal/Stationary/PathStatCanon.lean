/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Driver.BridgeAdapted
public import ComplexSLE.Internal.Phases.AllZDriverLaw

/-!
# The canonical path space of continuous drivers (M7/A4c)

The polar data `(θ̂, log |f̂|)` of a chain are functionals of the *continuous* driver path, which is
not a measurable subset of `ℝ≥0 → ℂ` for the product σ-algebra. To compare the polar data of two
drivers with the same path law (the driver `U` and the restarted driver `V` of the strong Markov
step) we therefore work on the canonical space

* `CPath = {v : ℝ≥0 → ℂ // Continuous v}`, with the trace of the product σ-algebra,

on which evaluation is jointly measurable in `(t, v)` (`CPath.measurable_eval_uncurry`), and the
operations used below are measurable:

* `CPath.ofDriver U hc : Ω → CPath`, the path of an everywhere-continuous process;
* `CPath.scale r : CPath → CPath`, `v ↦ r v(·/r²)`, jointly measurable in `(r, v)`;
* `CPath.neg : CPath → CPath`, `v ↦ -v`.

Results:

* `map_ofDriver_eq`: two `SLE_Σ` drivers with the same `(a, b, c)` (with everywhere continuous
  paths and measurable coordinates, on possibly different spaces) have the same law on `CPath`
  (from `IsSLEDriver.measure_path_preimage_eq`);
* `isSLEDriver_eval`, `exists_isSLEDriverAdapted_eval`: the canonical coordinate process on
  `(CPath, P.map (CPath.ofDriver U hc))` is an `SLE_Σ` driver, adapted to some filtration. Hence
  every measurability theorem proved for adapted drivers (`PolarContMeas.lean`, `AllZFHat.lean`)
  applies to the polar functionals on `CPath`;
* `map_scale_eq`, `map_neg_eq`: the law is invariant under Brownian scaling and under `v ↦ -v`.

No external input is used.
-/

@[expose] public section

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Internal

/-- The canonical path space: continuous drivers `ℝ≥0 → ℂ`, with the σ-algebra induced by the
product σ-algebra of `ℝ≥0 → ℂ`. -/
abbrev CPath : Type := {v : ℝ≥0 → ℂ // Continuous v}

namespace CPath

/-- Evaluation of a path at time `t`. -/
def eval (t : ℝ≥0) (v : CPath) : ℂ := v.1 t

theorem measurable_eval (t : ℝ≥0) : Measurable (CPath.eval t) :=
  (measurable_pi_apply t).comp measurable_subtype_coe

theorem measurable_eval_uncurry : Measurable (Function.uncurry CPath.eval) :=
  measurable_uncurry_of_continuous_of_measurable (fun v => v.2) CPath.measurable_eval

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The path of an everywhere continuous process, as an element of `CPath`. -/
def ofDriver (U : ℝ≥0 → Ω → ℂ) (hc : ∀ ω, Continuous fun t => U t ω) (ω : Ω) : CPath :=
  ⟨fun t => U t ω, hc ω⟩

theorem measurable_ofDriver {U : ℝ≥0 → Ω → ℂ} (hc : ∀ ω, Continuous fun t => U t ω)
    (hm : ∀ t, Measurable (U t)) : Measurable (ofDriver U hc) :=
  Measurable.subtype_mk (measurable_pi_iff.2 hm)

/-- Brownian scaling `v ↦ r v(·/r²)` on paths. -/
noncomputable def scale (r : ℝ≥0) (v : CPath) : CPath :=
  ⟨fun s => (r : ℂ) * v.1 (s / r ^ 2), continuous_const.mul (v.2.comp (continuous_id.div_const _))⟩

theorem measurable_scale : Measurable fun p : ℝ≥0 × CPath => CPath.scale p.1 p.2 := by
  refine Measurable.subtype_mk (measurable_pi_iff.2 fun s => ?_)
  have h1 : Measurable fun p : ℝ≥0 × CPath => ((p.1 : ℝ≥0) : ℂ) :=
    (Complex.measurable_ofReal.comp (measurable_coe_nnreal_real.comp measurable_fst))
  have h3 : Measurable fun p : ℝ≥0 × CPath => s / p.1 ^ 2 := by
    simp only [div_eq_mul_inv]
    exact measurable_const.mul ((measurable_fst.pow_const 2).inv)
  have h2 : Measurable fun p : ℝ≥0 × CPath => CPath.eval (s / p.1 ^ 2) p.2 :=
    CPath.measurable_eval_uncurry.comp (h3.prodMk measurable_snd)
  exact h1.mul h2

theorem measurable_scale_const (r : ℝ≥0) : Measurable (CPath.scale r) :=
  measurable_scale.comp (measurable_const.prodMk measurable_id)

/-- Negation `v ↦ -v` of paths. -/
def neg (v : CPath) : CPath := ⟨fun s => - v.1 s, v.2.neg⟩

theorem measurable_neg : Measurable CPath.neg :=
  Measurable.subtype_mk (measurable_pi_iff.2 fun s => (CPath.measurable_eval s).neg)

end CPath

section Laws

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ} {U' : ℝ≥0 → Ω' → ℂ}

/-- **Uniqueness of the law on `CPath`.** Two `SLE_Σ` drivers with the same `(a, b, c)`, with
everywhere continuous paths and measurable coordinates, have the same law on `CPath`. -/
theorem map_ofDriver_eq (hU : IsSLEDriver a b c U P) (hU' : IsSLEDriver a b c U' P')
    (hc : ∀ ω, Continuous fun t => U t ω) (hc' : ∀ ω, Continuous fun t => U' t ω)
    (hm : ∀ t, Measurable (U t)) (hm' : ∀ t, Measurable (U' t)) :
    P.map (CPath.ofDriver U hc) = P'.map (CPath.ofDriver U' hc') := by
  ext A hA
  obtain ⟨B, hB, rfl⟩ := hA
  rw [Measure.map_apply (CPath.measurable_ofDriver hc hm) ⟨B, hB, rfl⟩,
    Measure.map_apply (CPath.measurable_ofDriver hc' hm') ⟨B, hB, rfl⟩]
  exact hU.measure_path_preimage_eq hU' hm hm' hB

theorem iIndepFun_map_of_comp {ι : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {g : ∀ i, Ω' → β i} (hg : ∀ i, Measurable (g i)) {φ : Ω → Ω'} (hφ : Measurable φ)
    (h : iIndepFun (fun i => g i ∘ φ) P) : iIndepFun g (P.map φ) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro S sets hsets
  have hmeas : ∀ i ∈ S, MeasurableSet (g i ⁻¹' sets i) := fun i hi => hg i (hsets i hi)
  rw [Measure.map_apply hφ (Finset.measurableSet_biInter S hmeas)]
  have h1 := h S hsets
  have e1 : φ ⁻¹' (⋂ i ∈ S, g i ⁻¹' sets i) = ⋂ i ∈ S, (g i ∘ φ) ⁻¹' sets i := by
    ext x; simp
  rw [e1, h1]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Measure.map_apply hφ (hmeas i hi)]
  rfl

/-- **The canonical driver.** If `U` is an `SLE_Σ` driver with everywhere continuous paths and
measurable coordinates, the coordinate process `CPath.eval` on `(CPath, P.map (ofDriver U))` is
an `SLE_Σ` driver. -/
theorem isSLEDriver_eval (hU : IsSLEDriver a b c U P) (hc : ∀ ω, Continuous fun t => U t ω)
    (hm : ∀ t, Measurable (U t)) :
    IsSLEDriver a b c CPath.eval (P.map (CPath.ofDriver U hc)) := by
  have hι := CPath.measurable_ofDriver hc hm
  refine ⟨Eventually.of_forall fun v => v.2, ?_, ?_, ?_⟩
  · rw [ae_map_iff hι.aemeasurable (measurableSet_eq_fun (CPath.measurable_eval 0)
      measurable_const)]
    exact hU.zero
  · intro n t ht
    refine iIndepFun_map_of_comp (fun i => (CPath.measurable_eval _).sub (CPath.measurable_eval _))
      hι ?_
    exact hU.indepIncrements n t ht
  · intro s t hst
    have h := hU.law_increment s t hst
    refine ⟨((CPath.measurable_eval t).sub (CPath.measurable_eval s)).aemeasurable, ?_⟩
    have hg : Measurable fun v : CPath => CPath.eval t v - CPath.eval s v :=
      (CPath.measurable_eval t).sub (CPath.measurable_eval s)
    rw [Measure.map_map hg hι]
    exact h.map_eq

/-- The canonical driver on `CPath` is adapted to some filtration. -/
theorem exists_isSLEDriverAdapted_eval (hU : IsSLEDriver a b c U P)
    (hc : ∀ ω, Continuous fun t => U t ω) (hm : ∀ t, Measurable (U t)) :
    ∃ ℱc : Filtration ℝ≥0 (inferInstance : MeasurableSpace CPath),
      IsSLEDriverAdapted a b c CPath.eval (P.map (CPath.ofDriver U hc)) ℱc :=
  ⟨_, (isSLEDriver_eval hU hc hm).isAdapted_bridgeFiltration (fun v => v.2)
    CPath.measurable_eval⟩

/-- **Scaling invariance of the law on `CPath`.** -/
theorem map_scale_eq (hU : IsSLEDriver a b c U P) (hc : ∀ ω, Continuous fun t => U t ω)
    (hm : ∀ t, Measurable (U t)) {r : ℝ≥0} (hr : 0 < r) :
    (P.map (CPath.ofDriver U hc)).map (CPath.scale r) = P.map (CPath.ofDriver U hc) := by
  have hι := CPath.measurable_ofDriver hc hm
  rw [Measure.map_map (CPath.measurable_scale_const r) hι]
  have hsc := hU.scale r hr
  have hc' : ∀ ω, Continuous fun t => (r : ℂ) * U (t / r ^ 2) ω := fun ω =>
    continuous_const.mul ((hc ω).comp (continuous_id.div_const _))
  have hm' : ∀ t, Measurable fun ω => (r : ℂ) * U (t / r ^ 2) ω := fun t =>
    measurable_const.mul (hm _)
  exact map_ofDriver_eq hsc hU hc' hc hm' hm

/-- **Negation invariance of the law on `CPath`** (`-U =_d U`). -/
theorem map_neg_eq (hU : IsSLEDriver a b c U P) (hc : ∀ ω, Continuous fun t => U t ω)
    (hm : ∀ t, Measurable (U t)) :
    (P.map (CPath.ofDriver U hc)).map CPath.neg = P.map (CPath.ofDriver U hc) := by
  have hι := CPath.measurable_ofDriver hc hm
  rw [Measure.map_map CPath.measurable_neg hι]
  have hng := hU.neg
  have hc' : ∀ ω, Continuous fun t => - U t ω := fun ω => (hc ω).neg
  have hm' : ∀ t, Measurable fun ω => - U t ω := fun t => (hm t).neg
  exact map_ofDriver_eq hng hU hc' hc hm' hm

end Laws

end ComplexSLE.Internal

end
