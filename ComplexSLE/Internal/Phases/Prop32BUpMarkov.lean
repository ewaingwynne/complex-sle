/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.AllZ
public import ComplexSLE.Internal.Phases.EventMeasEvents

/-!
# The quantitative strong Markov step for the upgrade of Proposition 3.2(b) (M7/E5)

Source: paper.tex:L1796-1816. Let `U` be an adapted `SLE_Σ` driver, `E` an event family
(`MeasurableEvents`, `ScaleInvariantEvents`, `FutureDependentEvents`) and

  `q E P U ξ = P(E(U, ξ))`.

* `measure_inter_postDriver`: for an a.s. finite stopping time `τ`, an `ℱ_τ`-measurable random
  point `X`, an event `A ∈ ℱ_τ` and a measurable set `M` of (path, point) pairs,
  `P(A ∩ {(V, X) ∈ M}) = ∫_A P_U(M_X) dP`, where `V = U_{τ+·} - U_τ` is the post-`τ` driver
  (the quantitative form of `ae_mem_postDriver`, from the independence of `V` and `ℱ_τ` and the
  equality of the law of `V` with that of `U`: classical input `strongMarkov_sleDriver`).
* `q_mul`, `q_eq_unit`: scale invariance `q(rξ) = q(ξ)`, `q(ξ) = q(ξ/|ξ|)` (law of the rescaled
  driver `r U(·/r²)`).
* `measure_inter_event_eq_lintegral`: at the σ-time `σ_z(s)` (`τ = sigmaTop hU z s`, `X = f̂_s(z)`),
  `P(A ∩ E(U, z)) = ∫_A q(f̂_s(z)) dP` for `A ∈ 𝒢_s = ℱ_{σ_z(s)}` (future dependence at `σ_z(s)`).

Uses the classical input `strongMarkov_sleDriver` (proved in-project).
-/

public section

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Internal

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- `q E P U ξ = P(E(U, ξ))`, the probability of the event at the point `ξ`. -/
@[expose] noncomputable def evProb (E : (ℝ≥0 → ℂ) → ℂ → Prop) (P : Measure Ω)
    (U : ℝ≥0 → Ω → ℂ) (ξ : ℂ) : ℝ≥0∞ :=
  P {ω | E (fun t => U t ω) ξ}

/-- **Quantitative conditional form of the strong Markov property.** For an adapted `SLE_Σ`
driver `U`, an a.s. finite stopping time `τ`, an `ℱ_τ`-measurable random point `X`, `A ∈ ℱ_τ` and
a measurable set `M ⊆ (ℝ≥0 → ℂ) × ℂ`:
`P(A ∩ {(V, X) ∈ M}) = ∫_A P{(U, X ω) ∈ M} dP(ω)`. -/
theorem measure_inter_postDriver (hU : IsSLEDriverAdapted a b c U P ℱ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime ℱ τ) (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) {X : Ω → ℂ}
    (hX : Measurable[hτ.measurableSpace] X) {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    {M : Set ((ℝ≥0 → ℂ) × ℂ)} (hM : MeasurableSet M) :
    P (A ∩ {ω | ((fun s => postDriver U τ s ω), X ω) ∈ M}) =
      ∫⁻ ω in A, P {ω' | ((fun t => U t ω'), X ω) ∈ M} ∂P := by
  have : IsProbabilityMeasure P := hU.toIsSLEDriver.isProbabilityMeasure
  obtain ⟨hVd, hind, -⟩ := External.strongMarkov_sleDriver hU τ hτ hfin
  have hVm : ∀ s, Measurable (postDriver U τ s) := measurable_postDriver hU hτ
  have hVpath : Measurable fun ω (s : ℝ≥0) => postDriver U τ s ω :=
    IsSLEDriver.measurable_path hVm
  have hUm : ∀ t, Measurable (U t) := fun t => hU.adapted.measurable
  have hXm : Measurable X := hX.mono hτ.measurableSpace_le le_rfl
  have hAm : MeasurableSet A := hτ.measurableSpace_le _ hA
  -- the pair `Y = (X, 1_A)` is `ℱ_τ`-measurable
  set Y : Ω → ℂ × ℝ := fun ω => (X ω, A.indicator (fun _ => (1 : ℝ)) ω) with hY
  have hYτ : Measurable[hτ.measurableSpace] Y :=
    hX.prodMk (measurable_const.indicator hA)
  have hYm : Measurable Y := hYτ.mono hτ.measurableSpace_le le_rfl
  -- independence of the post-`τ` path and `Y`
  have hindep : IndepFun (fun ω (s : ℝ≥0) => postDriver U τ s ω) Y P := by
    have e : MeasurableSpace.comap (fun ω (s : ℝ≥0) => postDriver U τ s ω) MeasurableSpace.pi =
        ⨆ s : ℝ≥0, MeasurableSpace.comap
          (fun ω => U ((τ ω).untopA + s) ω - U (τ ω).untopA ω) inferInstance := by
      rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
      refine iSup_congr fun s => ?_
      rw [MeasurableSpace.comap_comp]
      rfl
    exact indep_of_indep_of_le_right (e ▸ hind) hYτ.comap_le
  have hjoint : P.map (fun ω => ((fun s => postDriver U τ s ω), Y ω)) =
      (P.map fun ω (s : ℝ≥0) => postDriver U τ s ω).prod (P.map Y) :=
    (indepFun_iff_map_prod_eq_prod_map_map hVpath.aemeasurable hYm.aemeasurable).1 hindep
  -- the set `M'` encoding `A ∩ {(V, X) ∈ M}`
  set M' : Set ((ℝ≥0 → ℂ) × (ℂ × ℝ)) := {p | p.2.2 = 1 ∧ (p.1, p.2.1) ∈ M} with hM'
  have hM'm : MeasurableSet M' :=
    (measurableSet_eq_fun measurable_snd.snd measurable_const).inter
      (measurable_fst.prodMk measurable_snd.fst hM)
  have hset : A ∩ {ω | ((fun s => postDriver U τ s ω), X ω) ∈ M} =
      {ω | ((fun s => postDriver U τ s ω), Y ω) ∈ M'} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, hM', hY]
    by_cases hω : ω ∈ A
    · simp [hω]
    · simp [hω]
  have hmeasPair : Measurable fun ω => ((fun s => postDriver U τ s ω), Y ω) :=
    hVpath.prodMk hYm
  -- the law of the post-`τ` path on sections
  have hsec : ∀ ξ : ℂ, (P.map fun ω (s : ℝ≥0) => postDriver U τ s ω)
      ((fun v => (v, ξ)) ⁻¹' M) = P {ω' | ((fun t => U t ω'), ξ) ∈ M} := by
    intro ξ
    have hA' : MeasurableSet ((fun v : ℝ≥0 → ℂ => (v, ξ)) ⁻¹' M) := measurable_prodMk_right hM
    rw [Measure.map_apply hVpath hA']
    exact hVd.measure_path_preimage_eq hU.toIsSLEDriver hVm hUm hA'
  have h1 : P {ω | ((fun s => postDriver U τ s ω), Y ω) ∈ M'} =
      (P.map fun ω => ((fun s => postDriver U τ s ω), Y ω)) M' :=
    (Measure.map_apply hmeasPair hM'm).symm
  rw [hset, h1, hjoint, Measure.prod_apply_symm hM'm,
    lintegral_map (measurable_measure_prodMk_right hM'm) hYm, ← lintegral_indicator hAm]
  refine lintegral_congr fun ω => ?_
  by_cases hω : ω ∈ A
  · have : (fun v : ℝ≥0 → ℂ => (v, Y ω)) ⁻¹' M' = (fun v => (v, X ω)) ⁻¹' M := by
      ext v
      simp [hM', hY, hω]
    rw [this, hsec, Set.indicator_of_mem hω]
  · have : (fun v : ℝ≥0 → ℂ => (v, Y ω)) ⁻¹' M' = ∅ := by
      ext v
      simp [hM', hY, hω]
    rw [this, Set.indicator_of_notMem hω]
    simp

/-! ### Scale invariance of `q` -/

/-- **`q` is invariant under scaling the point.** -/
theorem evProb_mul (hU : IsSLEDriverAdapted a b c U P ℱ) {E : (ℝ≥0 → ℂ) → ℂ → Prop}
    (hEs : ScaleInvariantEvents E) {M : Set ((ℝ≥0 → ℂ) × ℂ)} (hM : MeasurableSet M)
    (hEM : ∀ (u : ℝ≥0 → ℂ) (z : ℂ), Continuous u → (E u z ↔ (u, z) ∈ M)) {r : ℝ≥0}
    (hr : 0 < r) (ξ : ℂ) : evProb E P U ((r : ℂ) * ξ) = evProb E P U ξ := by
  have hUm : ∀ t, Measurable (U t) := fun t => hU.adapted.measurable
  set U' : ℝ≥0 → Ω → ℂ := fun s ω => (r : ℂ) * U (s / r ^ 2) ω with hU'
  have hscaled : IsSLEDriver a b c U' P := hU.toIsSLEDriver.scale r hr
  have hU'm : ∀ t, Measurable (U' t) := fun t => measurable_const.mul (hUm _)
  have hsec : MeasurableSet ((fun v : ℝ≥0 → ℂ => (v, (r : ℂ) * ξ)) ⁻¹' M) :=
    measurable_prodMk_right hM
  have hlaw := hscaled.measure_path_preimage_eq hU.toIsSLEDriver hU'm hUm hsec
  have hcont' : ∀ ω, Continuous fun t => U' t ω := fun ω =>
    continuous_const.mul ((hU.cont ω).comp (continuous_id.div_const _))
  unfold evProb
  have e1 : {ω | E (fun t => U t ω) ξ} = {ω | E (fun t => U' t ω) ((r : ℂ) * ξ)} := by
    ext ω
    exact hEs _ (hU.cont ω) r hr ξ
  have e2 : {ω | E (fun t => U' t ω) ((r : ℂ) * ξ)} =
      {ω | (fun t => U' t ω) ∈ (fun v : ℝ≥0 → ℂ => (v, (r : ℂ) * ξ)) ⁻¹' M} := by
    ext ω
    exact hEM _ _ (hcont' ω)
  have e3 : {ω | E (fun t => U t ω) ((r : ℂ) * ξ)} =
      {ω | (fun t => U t ω) ∈ (fun v : ℝ≥0 → ℂ => (v, (r : ℂ) * ξ)) ⁻¹' M} := by
    ext ω
    exact hEM _ _ (hU.cont ω)
  rw [e1, e2, e3, ← hlaw]

/-- **`q(ξ) = q(ξ/|ξ|)`** for `ξ ≠ 0`. -/
theorem evProb_eq_unit (hU : IsSLEDriverAdapted a b c U P ℱ) {E : (ℝ≥0 → ℂ) → ℂ → Prop}
    (hEs : ScaleInvariantEvents E) {M : Set ((ℝ≥0 → ℂ) × ℂ)} (hM : MeasurableSet M)
    (hEM : ∀ (u : ℝ≥0 → ℂ) (z : ℂ), Continuous u → (E u z ↔ (u, z) ∈ M)) {ξ : ℂ}
    (hξ : ξ ≠ 0) : evProb E P U ξ = evProb E P U (ξ / (‖ξ‖ : ℂ)) := by
  set r : ℝ≥0 := ‖ξ‖₊⁻¹ with hr
  have hr0 : 0 < r := by rw [hr]; exact inv_pos.2 (nnnorm_pos.2 hξ)
  have hrC : (r : ℂ) * ξ = ξ / (‖ξ‖ : ℂ) := by
    rw [hr]
    have : ((‖ξ‖₊⁻¹ : ℝ≥0) : ℂ) = (‖ξ‖ : ℂ)⁻¹ := by
      rw [show ((‖ξ‖₊⁻¹ : ℝ≥0) : ℂ) = (((‖ξ‖₊⁻¹ : ℝ≥0) : ℝ) : ℂ) from rfl, NNReal.coe_inv]
      simp
    rw [this, div_eq_inv_mul]
  rw [← hrC, evProb_mul hU hEs hM hEM hr0]

/-! ### The Markov step at the σ-time `σ_z(s)` -/

open Polar

/-- **Future dependence at the σ-time.** For `z ≠ 0` and `s ≥ 0`, almost surely
`E(U, z) ↔ E(V, f̂_s(z))`, where `V` is the post-`σ_z(s)` driver. -/
theorem ae_event_iff_postDriver [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ)
    (ha : 0 < a) (hc : c ^ 2 ≤ a * b) {E : (ℝ≥0 → ℂ) → ℂ → Prop}
    (hEf : FutureDependentEvents E) {z : ℂ} (hz : z ≠ 0) (s : ℝ≥0) :
    ∀ᵐ ω ∂P, (E (fun t => U t ω) z ↔
      E (fun r => postDriver U (sigmaTop hU z s) r ω) (fHat hU z s ω)) := by
  filter_upwards [ae_thetaHat_eq_and_continuous hU ha hc hz] with ω hgω
  set τ : Ω → WithTop ℝ≥0 := sigmaTop hU z s with hτdef
  have hmem := hgω.1 s
  have hlife := sigmaTime_mem_lifeSet (hU.cont ω) hmem
  set σ := sigmaTime (fun t => U t ω) (hU.cont ω) z s with hσ
  have hσ0 : 0 ≤ σ := sigmaTime_nonneg (hU.cont ω) hmem
  have hτω : τ ω = ((σ.toNNReal : ℝ≥0) : WithTop ℝ≥0) := sigmaTop_of_mem hU hmem
  have hs : (τ ω).untopA = σ.toNNReal := by rw [hτω]; rfl
  set s' : ℝ≥0 := σ.toNNReal with hsdef
  have hsσ : (s' : ℝ) = σ := Real.coe_toNNReal σ hσ0
  have hz' : z ∈ (leftHull (fun t => U t ω) s')ᶜ := by
    rw [← coe_mem_lifeSet_iff, hsσ]; exact hlife
  have hfut := hEf (fun t => U t ω) (hU.cont ω) s' z hz'
  have hcl : centeredLoewnerMap (fun t => U t ω) (hU.cont ω) s' ⟨z, hz'⟩ = fHat hU z s ω := by
    rw [centeredLoewnerMap_eq_fPath (hU.cont ω) s' hz', fHat_of_mem hU hmem, hsσ]
  have hpath : (fun r => (fun t => U t ω) (r + s') - (fun t => U t ω) s') =
      fun r => postDriver U τ r ω := by
    funext r
    simp only [postDriver, hs, add_comm r]
  rw [hcl, hpath] at hfut
  exact hfut

/-- **The Markov step at the σ-time `σ_z(s)`.** For `A ∈ 𝒢_s = ℱ_{σ_z(s)}`,
`P(A ∩ E(U, z)) = ∫_A q(f̂_s(z)) dP`. -/
theorem measure_inter_event_eq_lintegral [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hc : c ^ 2 ≤ a * b)
    {E : (ℝ≥0 → ℂ) → ℂ → Prop} (hEf : FutureDependentEvents E) {M : Set ((ℝ≥0 → ℂ) × ℂ)}
    (hM : MeasurableSet M) (hEM : ∀ (u : ℝ≥0 → ℂ) (z : ℂ), Continuous u → (E u z ↔ (u, z) ∈ M))
    {z : ℂ} (hz : z ≠ 0) (s : ℝ≥0) {A : Set Ω} (hA : MeasurableSet[sigmaFiltration hU z s] A) :
    P (A ∩ {ω | E (fun t => U t ω) z}) = ∫⁻ ω in A, evProb E P U (fHat hU z s ω) ∂P := by
  have hτ := isStoppingTime_sigmaTop hU z s
  have hgood := ae_thetaHat_eq_and_continuous hU ha hc hz
  have hfin : ∀ᵐ ω ∂P, sigmaTop hU z s ω ≠ ⊤ := by
    filter_upwards [hgood] with ω hω
    rw [sigmaTop_of_mem hU (hω.1 s)]
    exact WithTop.coe_ne_top
  have hX : Measurable[hτ.measurableSpace] (fHat hU z s) := measurable_fHat hU s
  have hmain := measure_inter_postDriver hU hτ hfin hX hA hM
  have hiff := ae_event_iff_postDriver hU ha hc hEf hz s
  have hae : (A ∩ {ω | E (fun t => U t ω) z} : Set Ω) =ᵐ[P]
      (A ∩ {ω | ((fun r => postDriver U (sigmaTop hU z s) r ω), fHat hU z s ω) ∈ M} : Set Ω) := by
    filter_upwards [hiff] with ω h
    refine propext (and_congr_right fun _ => ?_)
    exact (h.trans (hEM _ _ (continuous_postDriver hU _ ω)))
  rw [measure_congr hae, hmain]
  refine lintegral_congr fun ω => ?_
  unfold evProb
  congr 1
  ext ω'
  exact (hEM _ _ (hU.cont ω')).symm

end ComplexSLE.Internal

end
