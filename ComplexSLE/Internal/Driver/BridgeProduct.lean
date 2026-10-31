/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsSLEDriverAdapted
import ComplexSLE.Internal.Driver.Shift
import ComplexSLE.Internal.Driver.Transform
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Product extension of an adapted `SLE_Σ` driver

Section 3 of the paper samples a random point `𝐳` on the unit circle, independent of the driver
(paper.tex:L939, L1255; graph step `step:section3-product-extension`). Formally the driver `U` lives
on `(Ω, P)`, the point on `(Ω', ν)`, and everything is placed on `(Ω × Ω', P.prod ν)`.

For `hU : IsSLEDriverAdapted a b c U P ℱ` and a probability measure `ν` on a measurable space `Ω'`
(e.g. `Ω' = ℝ` for the angle `arg 𝐳`):

* `prodFiltration m' ℱ t = (ℱ t).comap fst ⊔ m'.comap snd`; the σ-algebra of `snd` is contained in
  `prodFiltration m' ℱ 0` (`comap_snd_le_prodFiltration`);
* `IsSLEDriverAdapted.prod`: the lift `(t, x) ↦ U t x.1` is
  `IsSLEDriverAdapted a b c _ (P.prod ν) (prodFiltration ℱ)`;
* `snd` has law `ν` (`hasLaw_snd_prod`) and is independent of the lifted driver, as a path
  (`IsSLEDriverAdapted.indepFun_snd_path`);
* events of the lifted path and of the original path have the same almost-sure behaviour
  (`ComplexSLE.Internal.BridgeTransfer`).

The independence of the increment `U t - U s` from `prodFiltration ℱ s` (which contains `σ(snd)`) is
the tri-independence of `σ(U t - U s)`, `ℱ s` and `σ(snd)` (`indep_sup_of_indep_of_indep`).
-/

@[expose] public section

open scoped NNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE

/-- If `A ⟂ B` and `(A ⊔ B) ⟂ C`, then `A ⟂ (B ⊔ C)`. -/
theorem indep_sup_of_indep_of_indep {Ω : Type*} {A B C : MeasurableSpace Ω}
    {m₀ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] (hA : A ≤ m₀)
    (hB : B ≤ m₀) (hC : C ≤ m₀) (hAB : Indep A B μ) (hABC : Indep (A ⊔ B) C μ) :
    Indep A (B ⊔ C) μ := by
  have hpi2 : IsPiSystem {s : Set Ω | ∃ b c, MeasurableSet[B] b ∧ MeasurableSet[C] c ∧
      s = b ∩ c} := by
    rintro _ ⟨b₁, c₁, hb₁, hc₁, rfl⟩ _ ⟨b₂, c₂, hb₂, hc₂, rfl⟩ _
    refine ⟨b₁ ∩ b₂, c₁ ∩ c₂, hb₁.inter hb₂, hc₁.inter hc₂, ?_⟩
    ext x
    simp only [mem_inter_iff]
    tauto
  have hgen : B ⊔ C = MeasurableSpace.generateFrom {s : Set Ω | ∃ b c, MeasurableSet[B] b ∧
      MeasurableSet[C] c ∧ s = b ∩ c} := by
    refine le_antisymm (sup_le (fun b hb => ?_) (fun c hc => ?_))
      (MeasurableSpace.generateFrom_le ?_)
    · exact MeasurableSpace.measurableSet_generateFrom ⟨b, univ, hb, @MeasurableSet.univ _ C,
        (inter_univ b).symm⟩
    · exact MeasurableSpace.measurableSet_generateFrom ⟨univ, c, @MeasurableSet.univ _ B, hc,
        (univ_inter c).symm⟩
    · rintro _ ⟨b, c, hb, hc, rfl⟩
      exact (le_sup_left (a := B) (b := C) _ hb).inter (le_sup_right (a := B) (b := C) _ hc)
  refine IndepSets.indep hA (sup_le hB hC) (@MeasurableSpace.isPiSystem_measurableSet Ω A) hpi2
    (@MeasurableSpace.generateFrom_measurableSet Ω A).symm hgen ?_
  rw [Indep_iff] at hAB hABC
  rw [IndepSets_iff]
  rintro s _ hs ⟨b, c, hb, hc, rfl⟩
  have hsb : MeasurableSet[A ⊔ B] (s ∩ b) :=
    (le_sup_left (a := A) (b := B) _ hs).inter (le_sup_right (a := A) (b := B) _ hb)
  have hb' : MeasurableSet[A ⊔ B] b := le_sup_right (a := A) (b := B) _ hb
  rw [← inter_assoc, hABC (s ∩ b) c hsb hc, hAB s b hs hb, hABC b c hb' hc]
  ring

/-- Sub-σ-algebras of the first factor, lifted along `fst`, stay independent under the product
measure. -/
theorem indep_comap_fst {Ω Ω' : Type*} {A B : MeasurableSpace Ω} {m : MeasurableSpace Ω}
    {m' : MeasurableSpace Ω'} {P : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure ν] (hA : A ≤ m) (hB : B ≤ m) (h : Indep A B P) :
    Indep (A.comap Prod.fst) (B.comap Prod.fst) (P.prod ν) := by
  rw [Indep_iff] at h ⊢
  rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  have hmp := measurePreserving_fst (μ := P) (ν := ν)
  have e : Prod.fst ⁻¹' s ∩ Prod.fst ⁻¹' t = (Prod.fst : Ω × Ω' → Ω) ⁻¹' (s ∩ t) := rfl
  rw [e, hmp.measure_preimage ((hA _ hs).inter (hB _ ht)).nullMeasurableSet,
    hmp.measure_preimage (hA _ hs).nullMeasurableSet,
    hmp.measure_preimage (hB _ ht).nullMeasurableSet]
  exact h s t hs ht

/-- The first and second coordinates of a product probability space are independent. -/
theorem indep_comap_fst_comap_snd {Ω Ω' : Type*} {m : MeasurableSpace Ω}
    {m' : MeasurableSpace Ω'} {P : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure ν] :
    Indep (m.comap Prod.fst) (m'.comap Prod.snd) (P.prod ν) :=
  indepFun_prod (μ := P) (ν := ν) (X := id) (Y := id) measurable_id measurable_id

/-- Independence of `A ≤ m` and `B ≤ m` on `Ω` lifts to the independence of `A ∘ fst` and
`B ∘ fst ⊔ C ∘ snd` on `(Ω × Ω', P.prod ν)`, for every `C ≤ m'`. -/
theorem indep_comap_fst_sup_comap_snd {Ω Ω' : Type*} {A B : MeasurableSpace Ω}
    {m : MeasurableSpace Ω} {C : MeasurableSpace Ω'} {m' : MeasurableSpace Ω'} {P : Measure Ω}
    {ν : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure ν] (hA : A ≤ m) (hB : B ≤ m)
    (h : Indep A B P) (hC : C ≤ m') :
    Indep (A.comap Prod.fst) (B.comap Prod.fst ⊔ C.comap Prod.snd) (P.prod ν) := by
  have hle : ∀ {X : MeasurableSpace Ω}, X ≤ m → X.comap Prod.fst ≤ m.prod m' :=
    fun hX => (MeasurableSpace.comap_mono hX).trans le_sup_left
  refine indep_sup_of_indep_of_indep (m₀ := m.prod m') (hle hA) (hle hB)
    ((MeasurableSpace.comap_mono hC).trans le_sup_right) (indep_comap_fst hA hB h) ?_
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left
    (indep_comap_fst_comap_snd (P := P) (ν := ν))
    (sup_le (MeasurableSpace.comap_mono hA) (MeasurableSpace.comap_mono hB)))
    (MeasurableSpace.comap_mono hC)

/-- Independence of a finite family lifts along `fst` to the product space. -/
theorem iIndepFun_comp_fst {Ω Ω' : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'}
    {P : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure ν] {ι : Type*} {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] {f : ∀ i, Ω → β i} (hf : ∀ i, AEMeasurable (f i) P)
    (h : iIndepFun f P) :
    iIndepFun (fun i (x : Ω × Ω') => f i x.1) (P.prod ν) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro S sets hsets
  have hmp := measurePreserving_fst (μ := P) (ν := ν)
  have hnm : ∀ i ∈ S, NullMeasurableSet (f i ⁻¹' sets i) P :=
    fun i hi => (hf i).nullMeasurableSet_preimage (hsets i hi)
  have e : (⋂ i ∈ S, (fun x : Ω × Ω' => f i x.1) ⁻¹' sets i) =
      (Prod.fst : Ω × Ω' → Ω) ⁻¹' (⋂ i ∈ S, f i ⁻¹' sets i) := by
    ext x
    simp
  rw [e, hmp.measure_preimage (Finset.nullMeasurableSet_biInter S hnm), h S hsets]
  refine Finset.prod_congr rfl fun i hi => ?_
  exact (hmp.measure_preimage (hnm i hi)).symm

variable {Ω Ω' : Type*} {m : MeasurableSpace Ω}

/-- The product filtration `ℱ'' t = (ℱ t).comap fst ⊔ m'.comap snd`: the filtration `ℱ` lifted to
`Ω × Ω'`, with the whole σ-algebra of the second factor present from time `0`. -/
def prodFiltration (m' : MeasurableSpace Ω') (ℱ : Filtration ℝ≥0 m) :
    Filtration ℝ≥0 (m.prod m') where
  seq t := (ℱ t).comap Prod.fst ⊔ m'.comap Prod.snd
  mono' _ _ hst := sup_le_sup_right (MeasurableSpace.comap_mono (ℱ.mono hst)) _
  le' t := sup_le_sup_right (MeasurableSpace.comap_mono (ℱ.le t)) _

theorem prodFiltration_apply (m' : MeasurableSpace Ω') (ℱ : Filtration ℝ≥0 m) (t : ℝ≥0) :
    prodFiltration m' ℱ t = (ℱ t).comap Prod.fst ⊔ m'.comap Prod.snd := rfl

/-- The σ-algebra of the second coordinate is contained in `prodFiltration ℱ 0`. -/
theorem comap_snd_le_prodFiltration (m' : MeasurableSpace Ω') (ℱ : Filtration ℝ≥0 m) (t : ℝ≥0) :
    m'.comap Prod.snd ≤ prodFiltration m' ℱ t := le_sup_right

/-- `snd` is `prodFiltration ℱ 0`-measurable (the random angle is known at time `0`). -/
theorem measurable_snd_prodFiltration_zero (m' : MeasurableSpace Ω') (ℱ : Filtration ℝ≥0 m) :
    Measurable[prodFiltration m' ℱ 0] (Prod.snd : Ω × Ω' → Ω') :=
  (comap_measurable Prod.snd).mono (comap_snd_le_prodFiltration m' ℱ 0) le_rfl

/-- The lift `U t x = U t x.1` of a driver on `Ω` to `Ω × Ω'`. -/
theorem IsSLEDriver.prod {m' : MeasurableSpace Ω'} {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ} {P : Measure Ω}
    (hU : IsSLEDriver a b c U P) (ν : Measure Ω') [IsProbabilityMeasure ν] :
    IsSLEDriver a b c (fun t (x : Ω × Ω') => U t x.1) (P.prod ν) := by
  have := hU.isProbabilityMeasure
  have hmp := measurePreserving_fst (μ := P) (ν := ν)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hmp.quasiMeasurePreserving.ae hU.cont
  · exact hmp.quasiMeasurePreserving.ae hU.zero
  · intro n s hs
    exact iIndepFun_comp_fst (fun i => (hU.aemeasurable _).sub (hU.aemeasurable _))
      (hU.indepIncrements n s hs)
  · intro s t hst
    exact (hU.law_increment s t hst).fun_comp hmp.hasLaw

/-- **Product extension (step 2 of the driver bridge).** If `U` is an `ℱ`-adapted `SLE_Σ` driver
on `(Ω, P)` and `ν` is a probability measure on `Ω'`, then the lift `(t, x) ↦ U t x.1` is an
adapted `SLE_Σ` driver on `(Ω × Ω', P.prod ν)` for `prodFiltration ℱ`, a filtration whose time-zero
σ-algebra contains `σ(snd)`. -/
theorem IsSLEDriverAdapted.prod {m' : MeasurableSpace Ω'} {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} (hU : IsSLEDriverAdapted a b c U P ℱ)
    (ν : Measure Ω') [IsProbabilityMeasure ν] :
    IsSLEDriverAdapted a b c (fun t (x : Ω × Ω') => U t x.1) (P.prod ν)
      (prodFiltration m' ℱ) := by
  have := hU.toIsSLEDriver.isProbabilityMeasure
  have hmeas : ∀ t, Measurable (U t) := fun t => (hU.adapted t).mono (ℱ.le t) le_rfl
  refine ⟨hU.toIsSLEDriver.prod ν, fun x => hU.cont x.1, fun t => ?_, fun s t hst => ?_⟩
  · have h1 : Measurable[(ℱ t).comap Prod.fst] fun x : Ω × Ω' => U t x.1 :=
      (hU.adapted t).comp (comap_measurable Prod.fst)
    exact h1.mono le_sup_left le_rfl
  · have hA : MeasurableSpace.comap (fun ω => U t ω - U s ω) inferInstance ≤ m :=
      measurable_iff_comap_le.1 ((hmeas t).sub (hmeas s))
    have e : MeasurableSpace.comap (fun x : Ω × Ω' => U t x.1 - U s x.1) inferInstance =
        (MeasurableSpace.comap (fun ω => U t ω - U s ω) inferInstance).comap Prod.fst := by
      rw [MeasurableSpace.comap_comp]
      rfl
    rw [e, prodFiltration_apply]
    exact indep_comap_fst_sup_comap_snd hA (ℱ.le s) (hU.indep_increment s t hst) le_rfl

/-- The second coordinate of the product space has law `ν`. -/
theorem hasLaw_snd_prod {Ω Ω' : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'}
    {P : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure ν] :
    HasLaw (Prod.snd : Ω × Ω' → Ω') ν (P.prod ν) :=
  (measurePreserving_snd (μ := P) (ν := ν)).hasLaw

/-- **Independence of the random angle from the driver.** The second coordinate `snd` of the
product space is independent of the lifted driver, as a path `x ↦ (t ↦ U t x.1)`. -/
theorem IsSLEDriverAdapted.indepFun_snd_path {m' : MeasurableSpace Ω'} {a b c : ℝ}
    {U : ℝ≥0 → Ω → ℂ} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ν : Measure Ω') [IsProbabilityMeasure ν] :
    IndepFun (Prod.snd : Ω × Ω' → Ω') (fun (x : Ω × Ω') (t : ℝ≥0) => U t x.1) (P.prod ν) := by
  have := hU.toIsSLEDriver.isProbabilityMeasure
  have hmeas : ∀ t, Measurable (U t) := fun t => (hU.adapted t).mono (ℱ.le t) le_rfl
  exact (indepFun_prod (μ := P) (ν := ν) (X := fun ω (t : ℝ≥0) => U t ω) (Y := id)
    (measurable_pi_iff.2 hmeas) measurable_id).symm

end ComplexSLE

end
