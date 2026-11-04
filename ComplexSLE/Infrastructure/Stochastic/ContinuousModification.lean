/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsDiffusionSolution
public import ComplexSLE.Frozen.Defs.IsContLocalMartingale
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.Stopping

/-!
# Continuous versions of continuous local martingales and diffusion solutions

`ComplexSLE.IsContLocalMartingale` and `ComplexSLE.IsDiffusionSolution` only ask for *almost sure*
path continuity. Many arguments (optional stopping, `IsSLEDriverAdapted`, …) need *every* path to
be continuous. Redefining a process on a null set `N` keeps it indistinguishable, but destroys
adaptedness unless the null set is in the σ-algebras of the filtration. So the continuous version
lives on the completed filtration
`𝒢 t = ℱ t ⊔ σ(measurable P-null sets)`.

Main results (all external-free):

* `IsContLocalMartingale.of_modification`: a process equal to a continuous local martingale `Y`
  off a null set `N ∈ 𝒢 0`, and equal to a measurable function of time on `N`, is a continuous
  local martingale for any filtration `𝒢` between `ℱ` and the completion.
* `IsContLocalMartingale.exists_continuous_version`: an everywhere-continuous indistinguishable
  version, a continuous local martingale for the completed filtration.
* `IsDiffusionSolution.exists_continuous_version`: the same for solutions of the martingale
  problem: `X' = X` off a measurable null set `N` and `X' = 0` on `N`, and
  `IsDiffusionSolution 𝒢 α β X' P`. Since `X' = 0` on `N`, the integrals `∫₀ᵗ α (X' s) ds`
  equal `t α(0)` there, so the two local martingales of `IsDiffusionSolution` are modified on
  `N` only by the deterministic functions `-t α(0)` and `t² α(0)² - t β(0)²`.

The completion is necessary in general: without null sets in `ℱ₀`, no adapted modification need
exist. If `ℱ` already contains the measurable null sets in `ℱ 0`, take `𝒢 = ℱ`.
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Infrastructure

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω}

/-- A set in `m₁ ⊔ σ(null sets)` agrees a.e. with a set of `m₁`. -/
theorem exists_ae_eq_of_measurableSet_sup {m₁ : MeasurableSpace Ω} {A : Set Ω}
    (hA : MeasurableSet[m₁ ⊔
      MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet[m] N ∧ P N = 0}] A) :
    ∃ A₀, MeasurableSet[m₁] A₀ ∧ A =ᵐ[P] A₀ := by
  let C : MeasurableSpace Ω :=
    { MeasurableSet' := fun A => ∃ A₀, MeasurableSet[m₁] A₀ ∧ A =ᵐ[P] A₀
      measurableSet_empty := ⟨∅, @MeasurableSet.empty _ m₁, Filter.EventuallyEq.rfl⟩
      measurableSet_compl := fun A ⟨A₀, h₁, h₂⟩ =>
        ⟨A₀ᶜ, @MeasurableSet.compl _ _ m₁ h₁, h₂.compl⟩
      measurableSet_iUnion := fun f hf => by
        choose g hg1 hg2 using hf
        exact ⟨⋃ i, g i, @MeasurableSet.iUnion _ _ m₁ _ _ hg1,
          Filter.EventuallyEqSet.countable_iUnion hg2⟩ }
  have hle : m₁ ⊔ MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet[m] N ∧ P N = 0} ≤ C :=
    sup_le (fun A hA => ⟨A, hA, Filter.EventuallyEq.rfl⟩)
      (MeasurableSpace.generateFrom_le fun N hN =>
        ⟨∅, @MeasurableSet.empty _ m₁, ae_eq_empty.2 hN.2⟩)
  exact hle _ hA

/-- **Martingale transfer to the completed filtration.** If `Z` is an `ℱ`-martingale and `Z'` is
`𝒢`-adapted with `Z' t = Z t` a.e. for each `t`, where `𝒢 t ≤ ℱ t ⊔ σ(null sets)`, then `Z'` is a
`𝒢`-martingale. -/
theorem martingale_of_ae_eq_of_le_sup_null [IsFiniteMeasure P] {ι : Type*} [Preorder ι]
    {ℱ 𝒢 : Filtration ι m}
    (h𝒢 : ∀ t, 𝒢 t ≤
      ℱ t ⊔ MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet[m] N ∧ P N = 0})
    {Z Z' : ι → Ω → ℝ} (hZ : Martingale Z ℱ P) (hZ' : StronglyAdapted 𝒢 Z')
    (hae : ∀ t, Z' t =ᵐ[P] Z t) : Martingale Z' 𝒢 P := by
  have hint : ∀ t, Integrable (Z' t) P := fun t => (hZ.integrable t).congr (hae t).symm
  refine ⟨hZ', fun i j hij => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝒢.le i) (hint j)
    (fun A _ _ => (hint i).integrableOn) (fun A hA _ => ?_)
    (hZ' i).aestronglyMeasurable).symm
  obtain ⟨A₀, hA₀, hAA₀⟩ := exists_ae_eq_of_measurableSet_sup (h𝒢 i _ hA)
  have hA₀m : MeasurableSet[m] A₀ := ℱ.le i _ hA₀
  have e1 : ∫ ω in A₀, Z' i ω ∂P = ∫ ω in A₀, Z i ω ∂P :=
    setIntegral_congr_ae hA₀m (by filter_upwards [hae i] with ω h _ using h)
  have e2 : ∫ ω in A₀, Z' j ω ∂P = ∫ ω in A₀, Z j ω ∂P :=
    setIntegral_congr_ae hA₀m (by filter_upwards [hae j] with ω h _ using h)
  rw [setIntegral_congr_set hAA₀, setIntegral_congr_set hAA₀, e1, e2]
  exact hZ.setIntegral_eq hij hA₀

section Progressive

variable {ℱ 𝒢 : Filtration ℝ≥0 m}

/-- A progressive process stays progressive for a larger filtration when multiplied by the
indicator of a `𝒢 0`-measurable set. -/
theorem isStronglyProgressive_indicator {Y : ℝ≥0 → Ω → ℝ} (hY : IsStronglyProgressive ℱ Y)
    (hℱ𝒢 : ∀ t, ℱ t ≤ 𝒢 t) {N : Set Ω} (hN : MeasurableSet[𝒢 0] N) :
    IsStronglyProgressive 𝒢 fun t ω => N.indicator (Y t) ω := fun i => by
  have hNi : MeasurableSet[𝒢 i] N := 𝒢.mono zero_le _ hN
  have hprod : (Subtype.instMeasurableSpace : MeasurableSpace (Set.Iic i)).prod (ℱ i) ≤
      (Subtype.instMeasurableSpace : MeasurableSpace (Set.Iic i)).prod (𝒢 i) :=
    sup_le_sup (MeasurableSpace.comap_mono le_rfl) (MeasurableSpace.comap_mono (hℱ𝒢 i))
  have h1 : StronglyMeasurable[Subtype.instMeasurableSpace.prod (𝒢 i)]
      fun p : Set.Iic i × Ω => Y p.1 p.2 := (hY i).mono hprod
  have h2 : MeasurableSet[Subtype.instMeasurableSpace.prod (𝒢 i)] {p : Set.Iic i × Ω | p.2 ∈ N} :=
    @measurable_snd (Set.Iic i) Ω Subtype.instMeasurableSpace (𝒢 i) _ hNi
  exact h1.indicator h2

/-- Deterministic functions of time, supported on a `𝒢 0`-measurable set, are progressive. -/
theorem isStronglyProgressive_indicator_const {c : ℝ≥0 → ℝ} (hc : Measurable c) {N : Set Ω}
    (hN : MeasurableSet[𝒢 0] N) :
    IsStronglyProgressive 𝒢 fun t ω => N.indicator (fun _ => c t) ω := fun i => by
  have hNi : MeasurableSet[𝒢 i] N := 𝒢.mono zero_le _ hN
  have hfst : @Measurable _ _ (Subtype.instMeasurableSpace.prod (𝒢 i)) _
      (fun p : Set.Iic i × Ω => p.1) := @measurable_fst _ _ Subtype.instMeasurableSpace (𝒢 i)
  have hmeas : Measurable[Subtype.instMeasurableSpace.prod (𝒢 i)]
      fun p : Set.Iic i × Ω => c p.1 := hc.comp (measurable_subtype_coe.comp hfst)
  have h1 : StronglyMeasurable[Subtype.instMeasurableSpace.prod (𝒢 i)]
      fun p : Set.Iic i × Ω => c p.1 := hmeas.stronglyMeasurable
  have h2 : MeasurableSet[Subtype.instMeasurableSpace.prod (𝒢 i)] {p : Set.Iic i × Ω | p.2 ∈ N} :=
    @measurable_snd (Set.Iic i) Ω Subtype.instMeasurableSpace (𝒢 i) _ hNi
  exact h1.indicator h2

end Progressive

end ComplexSLE.Infrastructure

namespace ComplexSLE

open Infrastructure

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {ℱ 𝒢 : Filtration ℝ≥0 m}

/-- **Modification on a null set.** Let `𝒢` be a filtration between `ℱ` and
`ℱ ⊔ σ(null sets)`, `N` a `𝒢 0`-measurable `P`-null set, `Y` an `ℱ`-continuous local martingale
and `Y'` a process agreeing with `Y` off `N` and with a measurable deterministic function of time
`c` on `N`. Then `Y'` is a continuous local martingale for `𝒢`. -/
theorem IsContLocalMartingale.of_modification
    (hℱ𝒢 : ∀ t, ℱ t ≤ 𝒢 t)
    (h𝒢 : ∀ t, 𝒢 t ≤
      ℱ t ⊔ MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet[m] N ∧ P N = 0})
    {N : Set Ω} (hN : MeasurableSet[𝒢 0] N) (hN0 : P N = 0)
    {Y Y' : ℝ≥0 → Ω → ℝ} (hY : IsContLocalMartingale ℱ Y P)
    {c : ℝ≥0 → ℝ} (hc : Measurable c)
    (hYY' : ∀ ω ∉ N, ∀ t, Y' t ω = Y t ω) (hYc : ∀ ω ∈ N, ∀ t, Y' t ω = c t) :
    IsContLocalMartingale 𝒢 Y' P := by
  obtain ⟨hprog, hcont, τ, hτ, hτev, hmart⟩ := hY
  have hY'eq : Y' = fun t ω => Nᶜ.indicator (Y t) ω + N.indicator (fun _ => c t) ω := by
    funext t ω
    by_cases hω : ω ∈ N
    · simp [hω, hYc ω hω t]
    · simp [hω, hYY' ω hω t]
  have hprog' : IsStronglyProgressive 𝒢 Y' := by
    rw [hY'eq]
    exact (isStronglyProgressive_indicator hprog hℱ𝒢 hN.compl).add
      (isStronglyProgressive_indicator_const hc hN)
  have hae : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  have hτ' : ∀ n, IsStoppingTime 𝒢 (τ n) := fun n t => hℱ𝒢 t _ (hτ n t)
  refine ⟨hprog', ?_, τ, hτ', hτev, fun n => ?_⟩
  · filter_upwards [hae, hcont] with ω hω h
    have : (fun t => Y' t ω) = fun t => Y t ω := funext (hYY' ω hω)
    rwa [this]
  · refine martingale_of_ae_eq_of_le_sup_null h𝒢 (hmart n)
      (hprog'.stronglyAdapted_stoppedProcess (hτ' n)) fun t => ?_
    filter_upwards [hae] with ω hω
    simp only [stoppedProcess, hYY' ω hω]

omit [IsFiniteMeasure P] in
/-- A measurable `P`-null set outside which all paths of `X` are continuous. -/
theorem exists_null_measurableSet_continuous {X : ℝ≥0 → Ω → ℝ}
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => X t ω) :
    ∃ N : Set Ω, MeasurableSet[m] N ∧ P N = 0 ∧ ∀ ω ∉ N, Continuous fun t => X t ω := by
  obtain ⟨N, hSN, hNmeas, hN0⟩ := exists_measurable_superset_of_null
    (μ := P) (s := {ω | ¬ Continuous fun t => X t ω}) (ae_iff.1 hcont)
  exact ⟨N, hNmeas, hN0, fun ω hω => by_contra fun h => hω (hSN h)⟩

/-- **Continuous version of a continuous local martingale.** There is `Y'` indistinguishable from
`Y`, with *every* path continuous, that is a continuous local martingale for the completed
filtration `𝒢 t = ℱ t ⊔ σ(null sets)`. -/
theorem IsContLocalMartingale.exists_continuous_version {Y : ℝ≥0 → Ω → ℝ}
    (hY : IsContLocalMartingale ℱ Y P) (𝒢 : Filtration ℝ≥0 m)
    (h𝒢 : ∀ t, 𝒢 t =
      ℱ t ⊔ MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet[m] N ∧ P N = 0}) :
    ∃ Y' : ℝ≥0 → Ω → ℝ, (∀ᵐ ω ∂P, ∀ t, Y' t ω = Y t ω) ∧ (∀ ω, Continuous fun t => Y' t ω) ∧
      IsContLocalMartingale 𝒢 Y' P := by
  obtain ⟨N, hNmeas, hN0, hNcont⟩ := exists_null_measurableSet_continuous hY.2.1
  have hℱ𝒢 : ∀ t, ℱ t ≤ 𝒢 t := fun t => by rw [h𝒢]; exact le_sup_left
  have hN𝒢 : MeasurableSet[𝒢 0] N := by
    rw [h𝒢]
    exact (le_sup_right : _ ≤ ℱ 0 ⊔ MeasurableSpace.generateFrom
      {N : Set Ω | MeasurableSet[m] N ∧ P N = 0}) _
      (MeasurableSpace.measurableSet_generateFrom ⟨hNmeas, hN0⟩)
  have hout : ∀ ω, ω ∉ N → ∀ t, Nᶜ.indicator (Y t) ω = Y t ω := fun ω hω t => by simp [hω]
  have hin : ∀ ω, ω ∈ N → ∀ t, Nᶜ.indicator (Y t) ω = 0 := fun ω hω t => by simp [hω]
  refine ⟨fun t ω => Nᶜ.indicator (Y t) ω, ?_, fun ω => ?_, ?_⟩
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω t using hout ω hω t
  · by_cases hω : ω ∈ N
    · simp only [hin ω hω]; exact continuous_const
    · have : (fun t => Nᶜ.indicator (Y t) ω) = fun t => Y t ω := funext (hout ω hω)
      rw [this]; exact hNcont ω hω
  · exact IsContLocalMartingale.of_modification hℱ𝒢 (fun t => (h𝒢 t).le) hN𝒢 hN0 hY
      (c := fun _ => 0) measurable_const hout hin

/-- `pathIntegral` only depends on the path of `ω`. -/
theorem pathIntegral_congr {Ω : Type*} {ξ ξ' : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (h : ∀ s, ξ s ω = ξ' s ω) (t : ℝ≥0) : pathIntegral ξ t ω = pathIntegral ξ' t ω := by
  simp only [pathIntegral, h]

/-- On a path that vanishes identically, `∫₀ᵗ g (X_s) ds = t * g 0`. -/
theorem pathIntegral_of_eq_zero {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (h : ∀ s, X s ω = 0)
    (g : ℝ → ℝ) (t : ℝ≥0) : pathIntegral (fun s ω => g (X s ω)) t ω = t * g 0 := by
  simp [pathIntegral, h]

/-- **Continuity transfer for diffusion solutions.** If `X` solves the martingale problem
(`IsDiffusionSolution ℱ α β X P`, a.s. continuous paths), then there is `X'` indistinguishable from
`X`, with *every* path continuous, solving it for the completed filtration
`𝒢 t = ℱ t ⊔ σ(measurable P-null sets)`. -/
theorem IsDiffusionSolution.exists_continuous_version {α β : ℝ → ℝ} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsDiffusionSolution ℱ α β X P) (𝒢 : Filtration ℝ≥0 m)
    (h𝒢 : ∀ t, 𝒢 t =
      ℱ t ⊔ MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet[m] N ∧ P N = 0}) :
    ∃ X' : ℝ≥0 → Ω → ℝ, (∀ᵐ ω ∂P, ∀ t, X' t ω = X t ω) ∧ (∀ ω, Continuous fun t => X' t ω) ∧
      IsDiffusionSolution 𝒢 α β X' P := by
  obtain ⟨hprog, hcont, hM1, hM2⟩ := hX
  obtain ⟨N, hNmeas, hN0, hNcont⟩ := exists_null_measurableSet_continuous hcont
  have hℱ𝒢 : ∀ t, ℱ t ≤ 𝒢 t := fun t => by rw [h𝒢]; exact le_sup_left
  have hN𝒢 : MeasurableSet[𝒢 0] N := by
    rw [h𝒢]
    exact (le_sup_right : _ ≤ ℱ 0 ⊔ MeasurableSpace.generateFrom
      {N : Set Ω | MeasurableSet[m] N ∧ P N = 0}) _
      (MeasurableSpace.measurableSet_generateFrom ⟨hNmeas, hN0⟩)
  set X' : ℝ≥0 → Ω → ℝ := fun t ω => Nᶜ.indicator (X t) ω with hX'
  have hX'out : ∀ ω, ω ∉ N → ∀ t, X' t ω = X t ω := fun ω hω t => by simp [hX', hω]
  have hX'in : ∀ ω, ω ∈ N → ∀ t, X' t ω = 0 := fun ω hω t => by simp [hX', hω]
  have hcontall : ∀ ω, Continuous fun t => X' t ω := by
    intro ω
    by_cases hω : ω ∈ N
    · simp only [hX'in ω hω]; exact continuous_const
    · have : (fun t => X' t ω) = fun t => X t ω := funext (hX'out ω hω)
      rw [this]; exact hNcont ω hω
  have hprog' : IsStronglyProgressive 𝒢 X' := isStronglyProgressive_indicator hprog hℱ𝒢 hN𝒢.compl
  have hmod : ∀ (g : ℝ → ℝ), ∀ ω, ω ∉ N → ∀ t,
      pathIntegral (fun s ω => g (X' s ω)) t ω = pathIntegral (fun s ω => g (X s ω)) t ω :=
    fun g ω hω t => pathIntegral_congr (fun s => by rw [hX'out ω hω s]) t
  refine ⟨X', ?_, hcontall, hprog', ae_of_all _ hcontall, ?_, ?_⟩
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω t using hX'out ω hω t
  · refine IsContLocalMartingale.of_modification hℱ𝒢 (fun t => (h𝒢 t).le) hN𝒢 hN0 hM1
      (c := fun t => -((t : ℝ) * α 0)) (by fun_prop) ?_ ?_
    · intro ω hω t
      simp only [hX'out ω hω, hmod α ω hω]
    · intro ω hω t
      simp only [hX'in ω hω, pathIntegral_of_eq_zero (hX'in ω hω) α]
      ring
  · refine IsContLocalMartingale.of_modification hℱ𝒢 (fun t => (h𝒢 t).le) hN𝒢 hN0 hM2
      (c := fun t => (-((t : ℝ) * α 0)) ^ 2 - (t : ℝ) * β 0 ^ 2) (by fun_prop) ?_ ?_
    · intro ω hω t
      simp only [hX'out ω hω, hmod α ω hω, hmod (fun x => β x ^ 2) ω hω]
    · intro ω hω t
      simp only [hX'in ω hω, pathIntegral_of_eq_zero (hX'in ω hω) α,
        pathIntegral_of_eq_zero (hX'in ω hω) (fun x => β x ^ 2)]
      ring

end ComplexSLE
