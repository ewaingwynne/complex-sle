/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Stochastic.StrongMarkovFuture
public import ComplexSLE.Infrastructure.Stochastic.ContinuousOptionalStopping
public import Mathlib.Probability.Process.Stopping

import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Strong Markov property, step 2: finite stopping times

Source-independent probability. No external input is used; only Mathlib.

Let `U : ℝ≥0 → Ω → E` have every path continuous, every `U t` measurable, and satisfy the
simple Markov property at deterministic times in the form `SimpleMarkov U P ℱ`: for each `t`, the
restarted path `smPath U (fun _ => t)` is independent of `ℱ t` and has the law of
`smPath U (fun _ => 0)` (this follows from independence of single increments from `ℱ`, see
`SimpleMarkov.of_increments`). For an `ℝ≥0`-valued stopping time `T` and `A ∈ ℱ_T` we prove

* `map_restrict_smPath_eq`: `(P|_A).map (smPath U T) = P A • P.map (smPath U (fun _ => 0))`;
* `indep_comap_of_map_restrict_eq`: a law identity of this form for every `A` of a σ-algebra gives
  independence of that σ-algebra from the process.

Proof (as in `QuantumZipper.StrongMarkov.setIntegral_dyadicTime`, leobon12/lean-formalizations
@31e7483, here for `E`-valued processes and a general filtration): approximate `T` from above
by `T_m = ⌈2^m T⌉ / 2^m`, which takes countably many values `d_k`; on `{T_m = d_k} ∩ A ∈ ℱ (d_k)`
the simple Markov property at the deterministic time `d_k` applies. Path continuity and bounded
continuous test functions of finitely many restarted coordinates (`setIntegral_bcf`) give the
limit `m → ∞`, then uniqueness of finite measures on cylinders.
-/

public section

open scoped NNReal ENNReal Topology BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Infrastructure.StrongMarkov

/-- If `m₁ ⟂ m₂`, `S ∈ m₁` and `g` is `m₂`-measurable, then `∫_S g = P S ∫ g`. -/
theorem setIntegral_eq_of_indep {Ω : Type*} {m₁ m₂ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hind : Indep m₁ m₂ P) (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ)
    {S : Set Ω} (hS : MeasurableSet[m₁] S) {g : Ω → ℝ} (hg : Measurable[m₂] g) :
    ∫ ω in S, g ω ∂P = P.real S * ∫ ω, g ω ∂P := by
  have hSm : MeasurableSet[mΩ] S := h₁ _ hS
  have hf1 : Measurable[m₁] (S.indicator (1 : Ω → ℝ)) :=
    (@measurable_one ℝ Ω _ m₁ _).indicator hS
  have hfg : IndepFun (S.indicator (1 : Ω → ℝ)) g P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hind hf1.comap_le) hg.comap_le
  have hmul := hfg.integral_mul_eq_mul_integral (hf1.mono h₁ le_rfl).aestronglyMeasurable
    (hg.mono h₂ le_rfl).aestronglyMeasurable
  have h1 : ∫ ω in S, g ω ∂P = ∫ ω, S.indicator (1 : Ω → ℝ) ω * g ω ∂P := by
    rw [← integral_indicator hSm]
    congr 1
    ext ω
    by_cases h : ω ∈ S <;> simp [h]
  rw [h1]
  simp only [Pi.mul_apply] at hmul
  rw [hmul, integral_indicator_one hSm]

/-- If the law of `f` under `P|_A` is `P A • μ` for every `A` of a σ-algebra `m₁`, then `f` is
independent of `m₁`. -/
theorem indep_comap_of_map_restrict_eq {Ω β : Type*} {m₁ : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [mβ : MeasurableSpace β] {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → β} (hf : Measurable f) {μ : Measure β}
    (h : ∀ A, MeasurableSet[m₁] A → (P.restrict A).map f = P A • μ) :
    Indep m₁ (MeasurableSpace.comap f mβ) P := by
  rw [Indep_iff]
  rintro t1 t2 ht1 ⟨S, hS, rfl⟩
  have h1 := congrArg (fun ν : Measure β => ν S) (h t1 ht1)
  have h2 := congrArg (fun ν : Measure β => ν S) (h Set.univ (@MeasurableSet.univ _ m₁))
  simp only [Measure.map_apply hf hS, Measure.smul_apply, smul_eq_mul, Measure.restrict_univ,
    measure_univ, one_mul] at h1 h2
  rw [Measure.restrict_apply (hf hS)] at h1
  rw [Set.inter_comm, h1, h2]


variable {Ω E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {U : ℝ≥0 → Ω → E}

/-- The simple Markov property at deterministic times: for every `t`, the restarted path
`s ↦ U (t + s) - U t` is independent of `ℱ t` and has the law of the restarted path at `0`. -/
structure SimpleMarkov (U : ℝ≥0 → Ω → E) (P : Measure Ω) (ℱ : Filtration ℝ≥0 mΩ) : Prop where
  indep : ∀ t : ℝ≥0,
    Indep (ℱ t) (MeasurableSpace.comap (smPath U (fun _ => t)) MeasurableSpace.pi) P
  law : ∀ t : ℝ≥0, P.map (smPath U (fun _ => t)) = P.map (smPath U (fun _ => 0))

theorem SimpleMarkov.of_increments [IsProbabilityMeasure P] (hU : Adapted ℱ U)
    (hind : ∀ s t : ℝ≥0, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => U t ω - U s ω) inferInstance) (ℱ s) P)
    (hinc : ∀ s t r : ℝ≥0, s ≤ t →
      P.map (fun ω => U (t + r) ω - U (s + r) ω) = P.map (fun ω => U t ω - U s ω)) :
    SimpleMarkov U P ℱ :=
  ⟨indep_smPath_const hU hind hinc, map_smPath_const_eq hU hind hinc⟩

/-! ### Measurability of restarted paths -/

omit [SecondCountableTopology E] in
/-- `ω ↦ U (T ω) ω` is measurable for a measurable random time `T`. -/
theorem measurable_randomTime_eval (hUc : ∀ ω, Continuous fun t => U t ω)
    (hUm : ∀ t, Measurable (U t)) {T : Ω → ℝ≥0} (hT : Measurable T) :
    Measurable (fun ω => U (T ω) ω) :=
  (measurable_uncurry_of_continuous_of_measurable hUc hUm).comp (hT.prodMk measurable_id)

/-- The restarted process is measurable at every time. -/
theorem measurable_smShift (hUc : ∀ ω, Continuous fun t => U t ω)
    (hUm : ∀ t, Measurable (U t)) {T : Ω → ℝ≥0} (hT : Measurable T) (s : ℝ≥0) :
    Measurable (smShift U T s) :=
  (measurable_randomTime_eval hUc hUm (hT.add_const s)).sub (measurable_randomTime_eval hUc hUm hT)

/-- The restarted path is a measurable map into `ℝ≥0 → E`. -/
theorem measurable_smPath (hUc : ∀ ω, Continuous fun t => U t ω)
    (hUm : ∀ t, Measurable (U t)) {T : Ω → ℝ≥0} (hT : Measurable T) :
    Measurable (smPath U T) :=
  measurable_pi_iff.2 fun s => measurable_smShift hUc hUm hT s

/-- A finite stopping time is measurable. -/
theorem measurable_of_isStoppingTime {T : Ω → ℝ≥0}
    (hT : IsStoppingTime ℱ fun ω => (T ω : WithTop ℝ≥0)) : Measurable T :=
  measurable_of_Iic fun u => ℱ.le u _ (measurableSet_nnreal_le hT u)

/-! ### The discrete step -/

/-- The deterministic-time Markov identity for integrals of functionals of finitely many
restarted coordinates. -/
theorem integral_smPath_const [IsProbabilityMeasure P] (hUm : ∀ t, Measurable (U t))
    (hM : SimpleMarkov U P ℱ) (t : ℝ≥0) (I : Finset ℝ≥0) {F : (I → E) → ℝ} (hF : Measurable F) :
    ∫ ω, F (I.restrict (smPath U (fun _ => t) ω)) ∂P =
      ∫ x, F (I.restrict x) ∂(P.map (smPath U (fun _ => 0))) := by
  rw [← hM.law t]
  exact (integral_map (measurable_smPath_const hUm t).aemeasurable
    (hF.comp (Finset.measurable_restrict I)).aestronglyMeasurable).symm

/-- **The discrete step**: the strong Markov identity holds at the dyadic approximations
`T_m = ⌈2^m T⌉ / 2^m`. -/
theorem setIntegral_dyadicTime [IsProbabilityMeasure P] (hUc : ∀ ω, Continuous fun t => U t ω)
    (hUm : ∀ t, Measurable (U t)) (hM : SimpleMarkov U P ℱ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime ℱ fun ω => (T ω : WithTop ℝ≥0)) {A : Set Ω}
    (hA : MeasurableSet[hT.measurableSpace] A) (m : ℕ) (I : Finset ℝ≥0)
    {F : (I → E) → ℝ} (hF : Measurable F) {C : ℝ} (hFC : ∀ x, |F x| ≤ C) :
    ∫ ω in A, F (I.restrict (smPath U (fun ω => dyadicCeil m (T ω)) ω)) ∂P =
      P.real A * ∫ x, F (I.restrict x) ∂(P.map (smPath U (fun _ => 0))) := by
  set c := ∫ x, F (I.restrict x) ∂(P.map (smPath U (fun _ => 0))) with hc
  set Tm : Ω → ℝ≥0 := fun ω => dyadicCeil m (T ω) with hTmdef
  have hTm : IsStoppingTime ℱ fun ω => (Tm ω : WithTop ℝ≥0) := isStoppingTime_dyadicCeil hT m
  have hTmm : Measurable Tm := measurable_of_isStoppingTime hTm
  have hAm : MeasurableSet A := hT.measurableSpace_le _ hA
  -- `Tm` has countable range; decompose `A` along its values
  have : Countable (Set.range Tm) := (countable_range_dyadicCeil T m).to_subtype
  set B : Set.range Tm → Set Ω := fun r => A ∩ {ω | Tm ω = r} with hB
  have hBF : ∀ r : Set.range Tm, MeasurableSet[ℱ (r : ℝ≥0)] (B r) := by
    intro r
    have h1 := hA.2 (r : ℝ≥0)
    have h3 := hTm.measurableSet_eq (r : ℝ≥0)
    have : B r = (A ∩ {ω | (T ω : WithTop ℝ≥0) ≤ (r : ℝ≥0)}) ∩
        {ω | (Tm ω : WithTop ℝ≥0) = (r : ℝ≥0)} := by
      ext ω
      simp only [hB, Set.mem_inter_iff, Set.mem_ofPred_eq, WithTop.coe_le_coe, WithTop.coe_inj]
      constructor
      · rintro ⟨hω, h⟩
        exact ⟨⟨hω, h ▸ le_dyadicCeil m (T ω)⟩, h⟩
      · rintro ⟨⟨hω, -⟩, h⟩
        exact ⟨hω, h⟩
    rw [this]
    exact h1.inter h3
  have hBm : ∀ r : Set.range Tm, MeasurableSet (B r) := fun r => ℱ.le _ _ (hBF r)
  have hdisj : Pairwise (Function.onFun Disjoint B) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun ω hi hj => hij (Subtype.ext ?_)
    exact hi.2.symm.trans hj.2
  have hU : A = ⋃ r, B r := by
    ext ω
    simp only [hB, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨⟨Tm ω, ω, rfl⟩, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  set f : Ω → ℝ := fun ω => F (I.restrict (smPath U Tm ω)) with hf
  have hfm : Measurable f :=
    (hF.comp (Finset.measurable_restrict I)).comp (measurable_smPath hUc hUm hTmm)
  have hfi : IntegrableOn f (⋃ r, B r) P :=
    Integrable.of_bound hfm.aestronglyMeasurable C
      (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hFC _)
  have hci : IntegrableOn (fun _ : Ω => c) (⋃ r, B r) P := integrable_const c
  have hstep : ∀ r : Set.range Tm, ∫ ω in B r, f ω ∂P = ∫ ω in B r, c ∂P := by
    intro r
    have hcongr : ∫ ω in B r, f ω ∂P =
        ∫ ω in B r, F (I.restrict (smPath U (fun _ => (r : ℝ≥0)) ω)) ∂P := by
      refine setIntegral_congr_fun (hBm r) fun ω hω => ?_
      simp only [hf]
      have : smPath U Tm ω = smPath U (fun _ => (r : ℝ≥0)) ω := by
        have h' : Tm ω = r := hω.2
        funext s; simp only [smPath, smShift, h']
      rw [this]
    have hgm : Measurable[MeasurableSpace.comap (smPath U (fun _ => (r : ℝ≥0)))
        MeasurableSpace.pi] (fun ω => F (I.restrict (smPath U (fun _ => (r : ℝ≥0)) ω))) :=
      (hF.comp (Finset.measurable_restrict I)).comp
        (comap_measurable (smPath U (fun _ => (r : ℝ≥0))))
    have hle : MeasurableSpace.comap (smPath U (fun _ => (r : ℝ≥0))) MeasurableSpace.pi ≤ mΩ :=
      (measurable_smPath_const hUm (r : ℝ≥0)).comap_le
    rw [hcongr, setIntegral_eq_of_indep (hM.indep (r : ℝ≥0)) (ℱ.le _) hle (hBF r) hgm,
      setIntegral_const, smul_eq_mul, integral_smPath_const hUm hM (r : ℝ≥0) I hF]
  calc ∫ ω in A, f ω ∂P = ∫ ω in ⋃ r, B r, f ω ∂P := by rw [← hU]
    _ = ∑' r, ∫ ω in B r, f ω ∂P := integral_iUnion hBm hdisj hfi
    _ = ∑' r, ∫ ω in B r, c ∂P := by simp_rw [hstep]
    _ = ∫ ω in ⋃ r, B r, c ∂P := (integral_iUnion hBm hdisj hci).symm
    _ = P.real A * c := by rw [← hU, setIntegral_const, smul_eq_mul]

/-! ### The limit step -/

/-- **The limit step**: the strong Markov identity at `T` for bounded continuous test functions. -/
theorem setIntegral_bcf [IsProbabilityMeasure P] (hUc : ∀ ω, Continuous fun t => U t ω)
    (hUm : ∀ t, Measurable (U t)) (hM : SimpleMarkov U P ℱ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime ℱ fun ω => (T ω : WithTop ℝ≥0)) {A : Set Ω}
    (hA : MeasurableSet[hT.measurableSpace] A) (I : Finset ℝ≥0) (F : (I → E) →ᵇ ℝ) :
    ∫ ω in A, F (I.restrict (smPath U T ω)) ∂P =
      P.real A * ∫ x, F (I.restrict x) ∂(P.map (smPath U (fun _ => 0))) := by
  have hFC : ∀ x, |F x| ≤ ‖F‖ := fun x => by
    rw [← Real.norm_eq_abs]; exact F.norm_coe_le_norm x
  have hlim : Tendsto (fun m => ∫ ω in A,
      F (I.restrict (smPath U (fun ω => dyadicCeil m (T ω)) ω)) ∂P)
      atTop (𝓝 (∫ ω in A, F (I.restrict (smPath U T ω)) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ‖F‖) (fun m => ?_)
      (integrable_const _) (fun m => ae_of_all _ fun ω => F.norm_coe_le_norm _)
      (ae_of_all _ fun ω => ?_)
    · exact ((F.continuous.measurable.comp (Finset.measurable_restrict I)).comp
        (measurable_smPath hUc hUm (measurable_of_isStoppingTime
          (isStoppingTime_dyadicCeil hT m)))).aestronglyMeasurable
    · refine (F.continuous.tendsto _).comp (tendsto_pi_nhds.2 fun i => ?_)
      have hTm : Tendsto (fun m => dyadicCeil m (T ω)) atTop (𝓝 (T ω)) :=
        tendsto_dyadicCeil (T ω)
      exact (((hUc ω).tendsto _).comp (hTm.add_const _)).sub (((hUc ω).tendsto _).comp hTm)
  have hconst : (fun m => ∫ ω in A,
      F (I.restrict (smPath U (fun ω => dyadicCeil m (T ω)) ω)) ∂P) =
      fun _ => P.real A * ∫ x, F (I.restrict x) ∂(P.map (smPath U (fun _ => 0))) := by
    funext m
    exact setIntegral_dyadicTime hUc hUm hM hT hA m I F.continuous.measurable hFC
  rw [hconst] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- Finite-dimensional form: the law of `(U (T + s) - U T)_{s ∈ I}` under `P|_A` is
`P A • (law of (U s - U 0)_{s ∈ I})`. -/
theorem map_restrict_finite_eq [IsProbabilityMeasure P] (hUc : ∀ ω, Continuous fun t => U t ω)
    (hUm : ∀ t, Measurable (U t)) (hM : SimpleMarkov U P ℱ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime ℱ fun ω => (T ω : WithTop ℝ≥0)) {A : Set Ω}
    (hA : MeasurableSet[hT.measurableSpace] A) (I : Finset ℝ≥0) :
    (P.restrict A).map (fun ω => I.restrict (smPath U T ω)) =
      P A • (P.map (smPath U (fun _ => 0))).map I.restrict := by
  have hgm : Measurable (fun ω => I.restrict (smPath U T ω)) :=
    (Finset.measurable_restrict I).comp
      (measurable_smPath hUc hUm (measurable_of_isStoppingTime hT))
  have hm0 : Measurable (I.restrict : (ℝ≥0 → E) → (I → E)) := Finset.measurable_restrict I
  have : IsFiniteMeasure (P A • (P.map (smPath U (fun _ => 0))).map I.restrict) :=
    ⟨by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top (measure_lt_top _ _) (measure_lt_top _ _)⟩
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun F => ?_
  rw [integral_map hgm.aemeasurable F.continuous.aestronglyMeasurable, integral_smul_measure,
    integral_map hm0.aemeasurable F.continuous.aestronglyMeasurable,
    setIntegral_bcf hUc hUm hM hT hA I F, smul_eq_mul, measureReal_def]

/-- **Strong Markov property at a finite stopping time, law form**: for `A ∈ ℱ_T`, the law
of the restarted path under `P|_A` is `P A` times the law of `U - U 0`. -/
theorem map_restrict_smPath_eq [IsProbabilityMeasure P] (hUc : ∀ ω, Continuous fun t => U t ω)
    (hUm : ∀ t, Measurable (U t)) (hM : SimpleMarkov U P ℱ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime ℱ fun ω => (T ω : WithTop ℝ≥0)) {A : Set Ω}
    (hA : MeasurableSet[hT.measurableSpace] A) :
    (P.restrict A).map (smPath U T) = P A • P.map (smPath U (fun _ => 0)) := by
  have hsm := measurable_smPath hUc hUm (measurable_of_isStoppingTime hT)
  have hs0 := measurable_smPath_const hUm 0
  have hrm : ∀ I : Finset ℝ≥0, Measurable (fun ω => I.restrict (smPath U T ω)) := fun I =>
    (Finset.measurable_restrict I).comp hsm
  refine ext_of_generate_finite (measurableCylinders fun _ : ℝ≥0 => E)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders (fun s hs => ?_) ?_
  · obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders s).1 hs
    have hsM := MeasurableSet.cylinder (α := fun _ : ℝ≥0 => E) I hS
    have h1 := congrArg (fun μ : Measure (I → E) => μ S)
      (map_restrict_finite_eq hUc hUm hM hT hA I)
    simp only [Measure.smul_apply, smul_eq_mul] at h1
    rw [Measure.map_apply (hrm I) hS,
      Measure.map_apply (Finset.measurable_restrict I) hS] at h1
    rw [Measure.map_apply hsm hsM, Measure.smul_apply, smul_eq_mul]
    exact h1
  · rw [Measure.map_apply hsm MeasurableSet.univ, Measure.smul_apply,
      Measure.map_apply hs0 MeasurableSet.univ]
    simp

end ComplexSLE.Infrastructure.StrongMarkov

end
