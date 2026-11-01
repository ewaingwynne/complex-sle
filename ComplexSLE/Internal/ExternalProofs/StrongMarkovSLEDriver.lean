/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsSLEDriverAdapted
public import ComplexSLE.Infrastructure.Stochastic.StrongMarkovAeFinite
public import ComplexSLE.Infrastructure.Stochastic.StrongMarkovTransfer

/-!
# Strong Markov property of the SLE_Σ driver (proof of the external input)

A complete proof of the exact statement of `ComplexSLE.External.strongMarkov_sleDriver`
(E3, Revuz–Yor III.3.7); this module deliberately does not import `ComplexSLE.External.*`, the
statement is a verbatim copy.

Route (all helpers are in `ComplexSLE.Infrastructure.Stochastic.StrongMarkov*`).

1. `StrongMarkovFuture`: independence of the single increments `U t - U s` from `ℱ s` gives, by
   induction over finitely many times and a π-system argument, that the whole restarted path
   `s ↦ U (t + s) - U t` is independent of `ℱ t` and has the law of `U - U 0`, for every
   deterministic `t`.
2. `StrongMarkovCore`: dyadic approximation `T_m ↓ T` from above, path continuity and bounded
   continuous test functions give, for a finite stopping time `T` and `A ∈ ℱ_T`, that the law of the
   restarted path under `P|_A` is `P A •` the law of `U - U 0`.
3. `StrongMarkovAeFinite`: truncation `τ ∧ n` on `{τ ≤ n}` for an a.s. finite `τ`
   (`untopA` sends `⊤` to a junk value only on a null set).
4. `StrongMarkovTransfer` and this file: the law of the restarted path is the law of `U - U 0`, so
   `IsSLEDriver` is inherited (`U 0 = 0` is not needed: `V 0 = 0` identically), the restarted path
   is independent of `ℱ_τ`, and for the filtration `𝒢 s = ℱ_{τ + s}` the restarted process is
   adapted (progressive measurability of `U`, `τ ≤ τ + s`) with independent increments (step 3
   applied to the stopping time `τ + s`, whose σ-algebra is `𝒢 s` by hypothesis).
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open ComplexSLE.Infrastructure.StrongMarkov

namespace ComplexSLE.Internal.ExternalProofs

namespace StrongMarkovSLEDriverAux

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- An `SLE_Σ` driver adapted to `ℱ` has the simple Markov property at deterministic times. -/
theorem simpleMarkov [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ) :
    SimpleMarkov U P ℱ :=
  SimpleMarkov.of_increments hU.adapted hU.indep_increment fun s t r hst => by
    have h1 := (hU.toIsSLEDriver.law_increment (s + r) (t + r) (by gcongr)).map_eq
    have h2 := (hU.toIsSLEDriver.law_increment s t hst).map_eq
    have h3 : (((t + r : ℝ≥0) : ℝ) - ((s + r : ℝ≥0) : ℝ)) = (t : ℝ) - s := by push_cast; ring
    rw [h3] at h1
    rw [h1, h2]

/-- If the law of the restarted path at `T` is the law of `U - U 0` (as measures on `ℝ≥0 → ℂ`),
then the restarted process is an `SLE_Σ` driver. -/
theorem isSLEDriver_smShift [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ)
    {T : Ω → ℝ≥0} (hT : Measurable T)
    (hlaw : P.map (smPath U T) = P.map (smPath U (fun _ => 0))) :
    IsSLEDriver a b c (smShift U T) P := by
  have hUm : ∀ t, Measurable (U t) := measurable_of_adapted hU.adapted
  have hV : ∀ s, Measurable (smShift U T s) := measurable_smShift hU.cont hUm hT
  have hW : ∀ s, Measurable (smShift U (fun _ => 0) s) :=
    measurable_smShift hU.cont hUm measurable_const
  have hpath : P.map (fun ω t => smShift U T t ω) =
      P.map (fun ω t => smShift U (fun _ => 0) t ω) := hlaw
  have hincr : ∀ s t : ℝ≥0, (fun ω => smShift U (fun _ => 0) t ω - smShift U (fun _ => 0) s ω) =
      fun ω => U t ω - U s ω := by
    intro s t; funext ω; simp [smShift]
  refine ⟨Eventually.of_forall fun ω => ?_, Eventually.of_forall fun ω => by simp [smShift], ?_,
    fun s t hst => ?_⟩
  · exact ((hU.cont ω).comp (continuous_const.add continuous_id)).sub continuous_const
  · refine hasIndepIncrements_of_map_path_eq hV hW hpath ?_
    intro n t ht
    have := hU.toIsSLEDriver.indepIncrements n t ht
    convert this using 3 with i ω
    exact congrFun (hincr _ _) ω
  · refine ⟨((hV t).sub (hV s)).aemeasurable, ?_⟩
    rw [map_sub_eq_of_map_path_eq hV hW hpath s t, hincr s t]
    exact (hU.toIsSLEDriver.law_increment s t hst).map_eq

/-- `τ + s` is a stopping time for `ℝ≥0`-indexed filtrations. -/
theorem isStoppingTime_add_const_nnreal {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    (s : ℝ≥0) : IsStoppingTime ℱ fun ω => τ ω + (s : WithTop ℝ≥0) := by
  intro t
  by_cases hst : s ≤ t
  · have : {ω | τ ω + (s : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} =
        {ω | τ ω ≤ ((t - s : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [mem_ofPred_eq]
      induction h : τ ω with
      | top => simp only [top_add, top_le_iff, WithTop.coe_ne_top]
      | coe v =>
        rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
        exact (le_tsub_iff_right hst).symm
    rw [this]
    exact ℱ.mono tsub_le_self _ (hτ (t - s))
  · have : {ω | τ ω + (s : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le (by exact_mod_cast not_le.1 hst) le_add_self
    rw [this]
    exact @MeasurableSet.empty _ (ℱ t)

/-- `untopA` commutes with adding a finite time away from `⊤`. -/
theorem untopA_add_coe {x : WithTop ℝ≥0} (hx : x ≠ ⊤) (s : ℝ≥0) :
    (x + (s : WithTop ℝ≥0)).untopA = x.untopA + s := by
  obtain ⟨v, rfl⟩ := WithTop.ne_top_iff_exists.1 hx
  rw [← WithTop.coe_add]
  rfl

end StrongMarkovSLEDriverAux

open StrongMarkovSLEDriverAux

/-- **Strong Markov property of the planar driver (E3).** Same statement as
`ComplexSLE.External.strongMarkov_sleDriver`, proved. -/
theorem strongMarkov_sleDriver {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ≥0 ‹_›} {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}
    (hU : IsSLEDriverAdapted a b c U P ℱ) (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime ℱ τ)
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IsSLEDriver a b c (fun s ω => U ((τ ω).untopA + s) ω - U (τ ω).untopA ω) P ∧
    Indep (⨆ s : ℝ≥0, MeasurableSpace.comap
        (fun ω => U ((τ ω).untopA + s) ω - U (τ ω).untopA ω) inferInstance)
      hτ.measurableSpace P ∧
    ∀ 𝒢 : Filtration ℝ≥0 ‹_›,
      (∀ (s : ℝ≥0) (A : Set Ω), MeasurableSet[𝒢 s] A ↔
        MeasurableSet[⨆ t, ℱ t] A ∧ ∀ t : ℝ≥0, MeasurableSet[ℱ t] (A ∩ {ω | τ ω + s ≤ t})) →
      IsSLEDriverAdapted a b c (fun s ω => U ((τ ω).untopA + s) ω - U (τ ω).untopA ω) P 𝒢 := by
  have hUm : ∀ t, Measurable (U t) := measurable_of_adapted hU.adapted
  have hMk : SimpleMarkov U P ℱ := simpleMarkov hU
  have hTm : Measurable fun ω => (τ ω).untopA := hτ.measurable'.untopA
  have hlaw : P.map (smPath U fun ω => (τ ω).untopA) = P.map (smPath U fun _ => 0) :=
    map_smPath_aeFinite hU.cont hUm hMk hτ hfin
  have hdrv : IsSLEDriver a b c (fun s ω => U ((τ ω).untopA + s) ω - U (τ ω).untopA ω) P :=
    isSLEDriver_smShift hU hTm hlaw
  refine ⟨hdrv, ?_, ?_⟩
  · have h := indep_smPath_aeFinite hU.cont hUm hMk hτ hfin
    have hgen : (⨆ s : ℝ≥0, MeasurableSpace.comap
        (fun ω => U ((τ ω).untopA + s) ω - U (τ ω).untopA ω) inferInstance) =
        MeasurableSpace.comap (smPath U fun ω => (τ ω).untopA) MeasurableSpace.pi := by
      rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
      simp_rw [MeasurableSpace.comap_comp]
      rfl
    rw [hgen]
    exact h.symm
  · intro 𝒢 h𝒢
    have hτs : ∀ s : ℝ≥0, IsStoppingTime ℱ fun ω => τ ω + (s : WithTop ℝ≥0) := fun s =>
      isStoppingTime_add_const_nnreal hτ s
    have h𝒢eq : ∀ s : ℝ≥0, 𝒢 s = (hτs s).measurableSpace := fun s => by
      ext A; exact (h𝒢 s A).trans ((hτs s).measurableSet A).symm
    have hprog : IsStronglyProgressive ℱ U :=
      hU.adapted.stronglyAdapted.isStronglyProgressive_of_continuous hU.cont
    refine ⟨hdrv, fun ω =>
      ((hU.cont ω).comp (continuous_const.add continuous_id)).sub continuous_const, ?_, ?_⟩
    · intro s B hB
      refine (h𝒢 s _).2 ⟨?_, fun t => ?_⟩
      · have hUm' : ∀ t, Measurable[⨆ t, ℱ t] (U t) := fun t =>
          (hU.adapted t).mono (le_iSup ℱ t) le_rfl
        have hTm' : Measurable[⨆ t, ℱ t] fun ω => (τ ω).untopA := hτ.measurable_iSup.untopA
        exact (measurable_smShift (mΩ := ⨆ t, ℱ t) hU.cont hUm' hTm' s) hB
      · have hSV1 : Measurable[(hτs s).measurableSpace]
            (stoppedValue U fun ω => τ ω + (s : WithTop ℝ≥0)) :=
          measurable_stoppedValue hprog (hτs s)
        have hSV0 : Measurable[hτ.measurableSpace] (stoppedValue U τ) :=
          measurable_stoppedValue hprog hτ
        have hle : hτ.measurableSpace ≤ (hτs s).measurableSpace :=
          hτ.measurableSpace_mono (hτs s) fun ω => le_self_add
        have hW : Measurable[(hτs s).measurableSpace] (fun ω =>
            stoppedValue U (fun ω => τ ω + (s : WithTop ℝ≥0)) ω - stoppedValue U τ ω) :=
          hSV1.fun_sub (hSV0.mono hle le_rfl)
        have hset : (fun ω => U ((τ ω).untopA + s) ω - U (τ ω).untopA ω) ⁻¹' B ∩
            {ω | τ ω + (s : WithTop ℝ≥0) ≤ t} =
            (fun ω => stoppedValue U (fun ω => τ ω + (s : WithTop ℝ≥0)) ω -
              stoppedValue U τ ω) ⁻¹' B ∩ {ω | τ ω + (s : WithTop ℝ≥0) ≤ t} := by
          ext ω
          simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, and_congr_left_iff]
          intro hω
          have hne : τ ω ≠ ⊤ := fun h => by
            simp only [h, top_add, top_le_iff, WithTop.coe_ne_top] at hω
          simp only [stoppedValue, untopA_add_coe hne s]
        rw [hset]
        exact (hW hB).2 t
    · intro s t hst
      have hτsfin : ∀ᵐ ω ∂P, τ ω + (s : WithTop ℝ≥0) ≠ ⊤ :=
        hfin.mono fun ω h => WithTop.add_ne_top.2 ⟨h, WithTop.coe_ne_top⟩
      have hI := (indep_smPath_aeFinite hU.cont hUm hMk (hτs s) hτsfin).symm
      rw [← h𝒢eq s] at hI
      refine indep_comap_of_ae_eq_comp (g := fun x : ℝ≥0 → ℂ => x (t - s))
        (measurable_pi_apply _) ?_ hI
      filter_upwards [hfin] with ω hω
      simp only [Function.comp_apply, smPath, smShift]
      rw [untopA_add_coe hω s, add_assoc, add_tsub_cancel_of_le hst]
      ring

end ComplexSLE.Internal.ExternalProofs

end
