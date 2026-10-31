/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.ErgodicMean
public import ComplexSLE.Internal.Recurrence.Renewal
public import ComplexSLE.Internal.Recurrence.Recurrence2
public import ComplexSLE.Internal.Recurrence.StatBridge
public import ComplexSLE.Internal.Stationary.SLEStat
public import ComplexSLE.Internal.Driver.BridgeAdapted
public import ComplexSLE.Infrastructure.Stochastic.ContinuousModification

/-!
# Recurrence of `e^{2iθ̂}` on the product space (M7/A5b, part A)

On `(Ω × ℝ, P ⊗ ν)`, `ν = p(u) 1_{[0,2π]}(u) du`, with the random point `𝐳 = e^{iu}`, the polar
angle `θ̂_t(e^{iu})` is recurrent to the lattice `πℤ`:

* `ae_recurrent_unit`: for `ν`-a.e. `u`, almost surely, for every `s` there is `t ≥ s` with
  `e^{2iθ̂_t(e^{iu})} = 1` (Lemma 2.16, both signs of `c`).

The stationarity input `hstat` of the renewal argument (`ae_frequently_mem_latticeSet`) is only
available on the product (one-time stationarity of `θ̂ mod π`,
`map_addCircle_thetaHat_prod_eq`), not for a single starting point. The renewal argument uses only
adaptedness, continuity of the paths and the two inputs `hstat`, `hren`, so it is run on the
product with the product filtration

  `ℋ_s = {A | A measurable, every fibre A_u ∈ 𝒢^u_s}`,   `𝒢^u = sigmaFiltration (e^{iu})`
  (`prodFiltration`),

and `hren` is the fibrewise statement of `sle_markov_transport` integrated over `u` (Fubini):

* `ae_frequently_prod`: abstract product renewal lemma;
* `ae_recurrent_prod_core`: the case of fibre diffusion solutions of `(µ, β)` with `c ≥ 0`;
* `thetaHatC`: the everywhere continuous version of `θ̂` (zero off the good set);
* `ae_recurrent_prod_of_null`: recurrence on the product for a filtration containing the null sets
  in time `0` (so that the fibre filtrations `𝒢^u` do too), for the version `thetaHatC`;
  `ae_recurrent_unit` completes the filtration (`nullFiltration`) and applies Fubini.

The reflection `θ ↦ -θ`, `c ↦ -c` handles `c ≤ 0` as in `sle_recurrence_nonpos`.

Consumes `ito_formula`, `timeChange_isContLocalMartingale`, `hormander_oneDim` (through the polar
and stationarity layers) and the EXTERNAL `markov_oneDim` (R29) as the explicit hypothesis
`hMO : MarkovOneDim`.
-/

@[expose] public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal

open Polar

/-! ### The product filtration -/

section ProdFiltration

variable {Ω : Type} {m : MeasurableSpace Ω}

/-- The product filtration `ℋ_s = {A | A measurable and every fibre `A_u ∈ 𝒢 u s`}` on `Ω × ℝ`
built from a family of filtrations `𝒢 u` of `Ω`. -/
def prodFiltration (𝒢 : ℝ → Filtration ℝ≥0 m) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × ℝ)) where
  seq s :=
    { MeasurableSet' := fun A => MeasurableSet A ∧
        ∀ u : ℝ, MeasurableSet[𝒢 u s] ((fun ω => (ω, u)) ⁻¹' A)
      measurableSet_empty := ⟨MeasurableSet.empty, fun u => by
        rw [Set.preimage_empty]; exact @MeasurableSet.empty _ (𝒢 u s)⟩
      measurableSet_compl := fun A hA => ⟨hA.1.compl, fun u => by
        rw [Set.preimage_compl]; exact @MeasurableSet.compl _ _ (𝒢 u s) (hA.2 u)⟩
      measurableSet_iUnion := fun f hf => ⟨MeasurableSet.iUnion fun i => (hf i).1, fun u => by
        rw [Set.preimage_iUnion]
        exact @MeasurableSet.iUnion _ _ (𝒢 u s) _ _ fun i => (hf i).2 u⟩ }
  mono' := fun _ _ hst _ hA => ⟨hA.1, fun u => (𝒢 u).mono hst _ (hA.2 u)⟩
  le' := fun _ _ hA => hA.1

theorem measurableSet_prodFiltration_iff {𝒢 : ℝ → Filtration ℝ≥0 m} {s : ℝ≥0} {A : Set (Ω × ℝ)} :
    MeasurableSet[prodFiltration 𝒢 s] A ↔
      MeasurableSet A ∧ ∀ u : ℝ, MeasurableSet[𝒢 u s] ((fun ω => (ω, u)) ⁻¹' A) := Iff.rfl

theorem measurable_prodFiltration {𝒢 : ℝ → Filtration ℝ≥0 m} {s : ℝ≥0} {f : Ω × ℝ → ℝ}
    (hf : Measurable f) (hfib : ∀ u : ℝ, Measurable[𝒢 u s] fun ω => f (ω, u)) :
    Measurable[prodFiltration 𝒢 s] f :=
  fun _ hB => ⟨hf hB, fun u => hfib u hB⟩

end ProdFiltration

/-! ### The abstract renewal argument on the product -/

section ProdRenewal

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ν : Measure ℝ} [IsProbabilityMeasure ν]

/-- **Renewal on the product.** Let `𝒢 u` be filtrations of `Ω` and `Z` a process on `Ω × ℝ` with
everywhere continuous paths, `Z_t(·, u)` being `𝒢 u t`-measurable. Assume the stationarity input
`hstat` on `(Ω × ℝ, P ⊗ ν)` and the fibrewise conditional hitting bound `hren` (for every `u`, every
`A ∈ 𝒢 u s`). Then `P ⊗ ν`-a.s. `Z` visits `x + πℤ` at arbitrarily large times. -/
theorem ae_frequently_prod (𝒢 : ℝ → Filtration ℝ≥0 m) (Z : ℝ≥0 → Ω × ℝ → ℝ)
    (hZm : ∀ t, Measurable (Z t)) (hZc : ∀ q, Continuous fun t => Z t q)
    (hZad : ∀ u t, Measurable[𝒢 u t] fun ω => Z t (ω, u)) (x : ℝ)
    (hstat : ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ≥0,
      (P.prod ν).real {q | Z t q ∉ ComplexSLE.Recurrence.goodSet x ε} ≤ η)
    (hren : ∀ ε : ℝ, 0 < ε → ∃ (T : ℝ≥0) (δ : ℝ), 0 < T ∧ 0 < δ ∧
      ∀ (u : ℝ) (s : ℝ≥0) (A : Set Ω), MeasurableSet[𝒢 u s] A →
        δ * P.real (A ∩ {ω | Z s (ω, u) ∈ ComplexSLE.Recurrence.goodSet x ε}) ≤
          P.real (A ∩ {ω | Z s (ω, u) ∈ ComplexSLE.Recurrence.goodSet x ε} ∩
            {ω | ∃ t ≤ T, Z (s + t) (ω, u) ∈ ComplexSLE.Recurrence.latticeSet x})) :
    ∀ᵐ q ∂(P.prod ν), ∀ s : ℝ≥0, ∃ t : ℝ≥0, s ≤ t ∧
      Z t q ∈ ComplexSLE.Recurrence.latticeSet x := by
  have hadapt : StronglyAdapted (prodFiltration 𝒢) Z := fun t =>
    (measurable_prodFiltration (hZm t) fun u => hZad u t).stronglyMeasurable
  refine ComplexSLE.Recurrence.ae_frequently_mem_latticeSet (ℱ := prodFiltration 𝒢) hadapt hZc
    hstat ?_
  intro ε hε
  obtain ⟨T, δ, hT, hδ, h⟩ := hren ε hε
  refine ⟨T, δ, hT, hδ, fun s A hA => ?_⟩
  have hGm : MeasurableSet {q : Ω × ℝ | Z s q ∈ ComplexSLE.Recurrence.goodSet x ε} :=
    hZm s (ComplexSLE.Recurrence.measurableSet_goodSet x ε)
  have hWm : MeasurableSet {q : Ω × ℝ |
      ∃ t ≤ T, Z (s + t) q ∈ ComplexSLE.Recurrence.latticeSet x} :=
    (prodFiltration 𝒢).le _ _ (ComplexSLE.Recurrence.measurableSet_window hadapt hZc s T)
  have hAm : MeasurableSet A := hA.1
  refine ComplexSLE.Recurrence.real_mul_measureReal_le hδ.le ?_
  rw [Measure.prod_apply_symm (hAm.inter hGm), Measure.prod_apply_symm ((hAm.inter hGm).inter hWm),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun u => ?_
  exact ComplexSLE.Recurrence.ofReal_mul_measure_le hδ.le (h u s _ (hA.2 u))

end ProdRenewal

/-! ### The case of fibre diffusion solutions with `c ≥ 0` -/

section Core

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ν : Measure ℝ} [IsProbabilityMeasure ν] {a b c : ℝ} {β : ℝ → ℝ}

/-- **Recurrence on the product, `c ≥ 0`.** If for every `u` the fibre `Z_·(·, u)` solves the
`θ̂`-SDE (martingale form) for the filtration `𝒢 u`, all paths of `Z` are continuous and the
stationarity input `hstat` holds on `(Ω × ℝ, P ⊗ ν)`, then `P ⊗ ν`-a.s. `Z` visits `x + πℤ` at
arbitrarily large times. -/
theorem ae_recurrent_prod_core (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b) (hc0 : 0 ≤ c)
    (hβc : Continuous β) (hβ2 : ∀ v, β v ^ 2 = 2 * diffusionD a b c v)
    (𝒢 : ℝ → Filtration ℝ≥0 m) (Z : ℝ≥0 → Ω × ℝ → ℝ) (hZm : ∀ t, Measurable (Z t))
    (hZc : ∀ q, Continuous fun t => Z t q)
    (hsol : ∀ u, IsDiffusionSolution (𝒢 u) (mu a b c) β (fun t ω => Z t (ω, u)) P) (x : ℝ)
    (hstat : ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ≥0,
      (P.prod ν).real {q | Z t q ∉ ComplexSLE.Recurrence.goodSet x ε} ≤ η) :
    ∀ᵐ q ∂(P.prod ν), ∀ s : ℝ≥0, ∃ t : ℝ≥0, s ≤ t ∧
      Z t q ∈ ComplexSLE.Recurrence.latticeSet x := by
  refine ae_frequently_prod 𝒢 Z hZm hZc
    (fun u t => ((hsol u).1.stronglyAdapted t).measurable) x hstat ?_
  intro ε hε
  have hε' : 0 < min ε π := lt_min hε Real.pi_pos
  obtain ⟨T, δ, hT, hδ, h245⟩ := ComplexSLE.Recurrence.sle_angle_hit_unif ha hb hc hc0 hβc hβ2 x
    hε' (min_le_right _ _)
  refine ⟨T, δ, hT, hδ, fun u s A hA => ?_⟩
  have hsub : ComplexSLE.Recurrence.goodSet x ε ⊆ ComplexSLE.Recurrence.goodSet x (min ε π) :=
    ComplexSLE.Recurrence.goodSet_subset_goodSet (min_le_left ε π)
  have hXs : Measurable[𝒢 u s] fun ω => Z s (ω, u) := ((hsol u).1.stronglyAdapted s).measurable
  have hA' : MeasurableSet[𝒢 u s]
      (A ∩ {ω | Z s (ω, u) ∈ ComplexSLE.Recurrence.goodSet x ε}) :=
    hA.inter (hXs (ComplexSLE.Recurrence.measurableSet_goodSet x ε))
  have := ComplexSLE.Recurrence.sle_markov_transport (continuous_mu a b c) hβc
    (mu_periodic a b c) (sq_periodic_of_sq_eq_two_mul_diffusionD hβ2) (hsol u)
    (fun ω => hZc (ω, u)) x hε' hδ h245 s _ hA'
  have e1 : A ∩ {ω | Z s (ω, u) ∈ ComplexSLE.Recurrence.goodSet x ε} ∩
      {ω | Z s (ω, u) ∈ ComplexSLE.Recurrence.goodSet x (min ε π)} =
      A ∩ {ω | Z s (ω, u) ∈ ComplexSLE.Recurrence.goodSet x ε} := by
    rw [inter_eq_left]
    rintro ω ⟨-, h⟩
    exact hsub h
  rwa [e1] at this

end Core


/-! ### Modification on a null set (diffusion solutions) -/

section Modification

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {ℱ : Filtration ℝ≥0 m} {α β : ℝ → ℝ} {X : ℝ≥0 → Ω → ℝ}

/-- **Zeroing a diffusion solution off a measurable conull `ℱ 0`-set.** If `S ∈ ℱ 0` is conull and
all paths of `X` in `S` are continuous, then `1_S X` solves the same martingale problem for the
same filtration, with every path continuous. (The explicit-null-set form of
`IsDiffusionSolution.exists_continuous_version`, for a filtration already containing the null sets
in `ℱ 0`.) -/
theorem isDiffusionSolution_indicator_of_conull (hX : IsDiffusionSolution ℱ α β X P) {S : Set Ω}
    (hS : MeasurableSet[ℱ 0] S) (hS0 : P Sᶜ = 0)
    (hcont : ∀ ω ∈ S, Continuous fun t => X t ω) :
    IsDiffusionSolution ℱ α β (fun t ω => S.indicator (X t) ω) P := by
  obtain ⟨hprog, -, hM1, hM2⟩ := hX
  have hN : MeasurableSet[ℱ 0] Sᶜ := hS.compl
  have hh : ∀ t, ℱ t ≤ ℱ t ⊔ MeasurableSpace.generateFrom
      {N : Set Ω | MeasurableSet[m] N ∧ P N = 0} := fun t => le_sup_left
  have hout : ∀ ω, ω ∈ S → ∀ t, S.indicator (X t) ω = X t ω := fun ω hω t => by simp [hω]
  have hin : ∀ ω, ω ∉ S → ∀ t, S.indicator (X t) ω = 0 := fun ω hω t => by simp [hω]
  have hcontall : ∀ ω, Continuous fun t => S.indicator (X t) ω := by
    intro ω
    by_cases hω : ω ∈ S
    · have : (fun t => S.indicator (X t) ω) = fun t => X t ω := funext (hout ω hω)
      rw [this]; exact hcont ω hω
    · simp only [hin ω hω]; exact continuous_const
  have hprog' : IsStronglyProgressive ℱ fun t ω => S.indicator (X t) ω :=
    Infrastructure.isStronglyProgressive_indicator hprog (fun _ => le_rfl) hS
  have hmod : ∀ (g : ℝ → ℝ), ∀ ω, ω ∈ S → ∀ t,
      pathIntegral (fun s ω => g (S.indicator (X s) ω)) t ω =
        pathIntegral (fun s ω => g (X s ω)) t ω :=
    fun g ω hω t => pathIntegral_congr (fun s => by rw [hout ω hω s]) t
  refine ⟨hprog', ae_of_all _ hcontall, ?_, ?_⟩
  · refine IsContLocalMartingale.of_modification (fun t => le_rfl) hh hN hS0 hM1
      (c := fun t => -((t : ℝ) * α 0)) (by fun_prop) ?_ ?_
    · intro ω hω t
      have hω' : ω ∈ S := by simpa using hω
      simp only [hout ω hω', hmod α ω hω']
    · intro ω hω t
      have hω' : ω ∉ S := by simpa using hω
      simp only [hin ω hω', pathIntegral_of_eq_zero (hin ω hω') α]
      ring
  · refine IsContLocalMartingale.of_modification (fun t => le_rfl) hh hN hS0 hM2
      (c := fun t => (-((t : ℝ) * α 0)) ^ 2 - (t : ℝ) * β 0 ^ 2) (by fun_prop) ?_ ?_
    · intro ω hω t
      have hω' : ω ∈ S := by simpa using hω
      simp only [hout ω hω', hmod α ω hω', hmod (fun x => β x ^ 2) ω hω']
    · intro ω hω t
      have hω' : ω ∉ S := by simpa using hω
      simp only [hin ω hω', pathIntegral_of_eq_zero (hin ω hω') α,
        pathIntegral_of_eq_zero (hin ω hω') (fun x => β x ^ 2)]
      ring

end Modification

/-! ### The everywhere continuous version of `θ̂` on the product -/

section Version

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-- The everywhere continuous version of `(t, (ω, u)) ↦ θ̂_t(e^{iu})(ω)`: it is `θ̂` on `goodSet hU`
(the conull set on which `sigmaDom = [0, ∞)`) and `0` elsewhere. -/
noncomputable def thetaHatC (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) (q : Ω × ℝ) : ℝ :=
  (goodSet hU).indicator (fun q : Ω × ℝ => thetaHat hU (unitPt q.2) t q.1) q

theorem measurable_thetaHatC (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) :
    Measurable (thetaHatC hU t) :=
  (measurable_thetaHat_unit hU t).indicator (measurableSet_goodSet hU)

theorem thetaHatC_of_mem (hU : IsSLEDriverAdapted a b c U P ℱ) {q : Ω × ℝ} (hq : q ∈ goodSet hU)
    (t : ℝ≥0) : thetaHatC hU t q = thetaHat hU (unitPt q.2) t q.1 :=
  Set.indicator_of_mem hq _

theorem thetaHatC_of_notMem (hU : IsSLEDriverAdapted a b c U P ℱ) {q : Ω × ℝ}
    (hq : q ∉ goodSet hU) (t : ℝ≥0) : thetaHatC hU t q = 0 :=
  Set.indicator_of_notMem hq _

theorem continuous_thetaHatC (hU : IsSLEDriverAdapted a b c U P ℱ) (q : Ω × ℝ) :
    Continuous fun t => thetaHatC hU t q := by
  by_cases hq : q ∈ goodSet hU
  · have := continuous_thetaHat_of_forall_mem hU (z := unitPt q.2) (ω := q.1)
      (mem_sigmaDom_of_mem_goodSet hU hq)
    have e : (fun t => thetaHatC hU t q) = fun t => thetaHat hU (unitPt q.2) t q.1 :=
      funext fun t => thetaHatC_of_mem hU hq t
    rw [e]; exact this
  · have e : (fun t => thetaHatC hU t q) = fun _ => (0 : ℝ) :=
      funext fun t => thetaHatC_of_notMem hU hq t
    rw [e]; exact continuous_const

theorem ae_thetaHatC_eq [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ)
    (ha : 0 < a) (hc : c ^ 2 ≤ a * b) {ν : Measure ℝ} [SFinite ν] :
    ∀ᵐ q ∂(P.prod ν), ∀ t, thetaHatC hU t q = thetaHat hU (unitPt q.2) t q.1 := by
  filter_upwards [ae_mem_goodSet hU ha hc (ν := ν)] with q hq t using thetaHatC_of_mem hU hq t

/-- For every `u`, almost surely `(ω, u)` lies in `goodSet hU`. -/
theorem ae_fibre_mem_goodSet [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ)
    (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (u : ℝ) : ∀ᵐ ω ∂P, (ω, u) ∈ goodSet hU := by
  filter_upwards [ae_sigmaDom_eq_Ici hU (unitPt u) ha hc (unitPt_ne_zero u)] with ω hω
  refine mem_iInter.2 fun n => ?_
  change (n : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) (unitPt u)
  rw [hω]; exact Nat.cast_nonneg n

/-- If the null sets lie in `ℱ 0`, they lie in `𝒢_0 = ℱ_{σ_z(0)}`. -/
theorem measurableSet_sigmaFiltration_zero_of_null
    (hnull : ∀ N : Set Ω, MeasurableSet N → P N = 0 → MeasurableSet[ℱ 0] N)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) {N : Set Ω} (hN : MeasurableSet N)
    (hN0 : P N = 0) : MeasurableSet[sigmaFiltration hU z 0] N := by
  have hN' : MeasurableSet[ℱ 0] N := hnull N hN hN0
  refine ⟨(le_iSup (fun t => ℱ t) 0) _ hN', fun i => ?_⟩
  exact (ℱ.mono (zero_le : (0 : ℝ≥0) ≤ i) _ hN').inter (isStoppingTime_sigmaTop hU z 0 i)

/-- **The fibre solution.** Assume the null sets lie in `ℱ 0`. For every `u`, the everywhere
continuous version `ω ↦ thetaHatC hU t (ω, u)` of `θ̂_t(e^{iu})` solves the martingale problem
of `(µ, β)` for the σ-time filtration `sigmaFiltration hU e^{iu}`. -/
theorem isDiffusionSolution_thetaHatC_fibre [IsProbabilityMeasure P]
    (hnull : ∀ N : Set Ω, MeasurableSet N → P N = 0 → MeasurableSet[ℱ 0] N)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {β : ℝ → ℝ} (hβsq : ∀ u, β u ^ 2 = 2 * diffusionD a b c u) (u : ℝ) :
    IsDiffusionSolution (sigmaFiltration hU (unitPt u)) (mu a b c) β
      (fun t ω => thetaHatC hU t (ω, u)) P := by
  have hsol := isDiffusionSolution_thetaHat_of_sq hU ha hb hc hβsq u
  set S : Set Ω := (fun ω => (ω, u)) ⁻¹' goodSet hU with hSdef
  have hSm : MeasurableSet S := measurable_prodMk_right (measurableSet_goodSet hU)
  have hS0 : P Sᶜ = 0 := ae_iff.1 (ae_fibre_mem_goodSet hU ha hc u)
  have hS : MeasurableSet[sigmaFiltration hU (unitPt u) 0] S := by
    have := measurableSet_sigmaFiltration_zero_of_null hnull hU (unitPt u) hSm.compl hS0
    simpa using this.compl
  have hcont : ∀ ω ∈ S, Continuous fun t => thetaHat hU (unitPt u) t ω := fun ω hω =>
    continuous_thetaHat_of_forall_mem hU (mem_sigmaDom_of_mem_goodSet hU (q := (ω, u)) hω)
  have h := isDiffusionSolution_indicator_of_conull hsol hS hS0 hcont
  have e : (fun t ω => S.indicator (thetaHat hU (unitPt u) t) ω) =
      fun t ω => thetaHatC hU t (ω, u) := by
    funext t ω
    by_cases hω : (ω, u) ∈ goodSet hU
    · rw [Set.indicator_of_mem (show ω ∈ S from hω), thetaHatC_of_mem hU hω]
    · rw [Set.indicator_of_notMem (show ω ∉ S from hω), thetaHatC_of_notMem hU hω]
  rw [e] at h
  exact h

end Version

/-! ### Recurrence of `e^{2iθ̂}` on the product space -/

section Main

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-- **Recurrence of `θ̂` on the product (null sets in `ℱ 0`).** `P ⊗ ν`-a.s., for every `s` there is
`t ≥ s` with `θ̂_t(e^{iu}) ∈ πℤ` (for the everywhere continuous version `thetaHatC`). -/
theorem ae_recurrent_prod_of_null [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hnull : ∀ N : Set Ω, MeasurableSet N → P N = 0 → MeasurableSet[ℱ 0] N)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) :
    ∀ᵐ q ∂(P.prod (admissibleMeasure p)), ∀ s : ℝ≥0, ∃ t : ℝ≥0, s ≤ t ∧
      thetaHatC hU t q ∈ ComplexSLE.Recurrence.latticeSet 0 := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  obtain ⟨β, hβ, hβsq, -⟩ := exists_beta ha hb hc
  have hβc : Continuous β := hβ.continuous
  have hsol : ∀ u : ℝ, IsDiffusionSolution (sigmaFiltration hU (unitPt u)) (mu a b c) β
      (fun t ω => thetaHatC hU t (ω, u)) P :=
    fun u => isDiffusionSolution_thetaHatC_fibre hnull hU ha hb hc hβsq u
  -- the law of `θ̂ mod π` is time independent, with no atoms
  have hlaw : ∀ t : ℝ≥0, (P.prod (admissibleMeasure p)).map
      (fun q : Ω × ℝ => ((thetaHatC hU t q : ℝ) : AddCircle π)) =
      (admissibleMeasure p).map ((↑) : ℝ → AddCircle π) := fun t => by
    rw [← map_addCircle_thetaHat_prod_eq_of_markovOneDim hMO hU ha hb hc hp t]
    refine Measure.map_congr ?_
    filter_upwards [ae_thetaHatC_eq hU ha hc (ν := admissibleMeasure p)] with q hq
    rw [hq t]
  have hac : (admissibleMeasure p).map (fun u : ℝ => u) ≪ volume := by
    rw [Measure.map_id']
    exact (withDensity_absolutelyContinuous _ _).trans Measure.restrict_le_self.absolutelyContinuous
  have : NullSingletonClass ((admissibleMeasure p).map ((↑) : ℝ → AddCircle π)) :=
    ComplexSLE.Recurrence.nullSingletonClass_map_addCircle_of_absolutelyContinuous
      (X₀ := fun u : ℝ => u) measurable_id hac
  have hXm := measurable_thetaHatC hU
  rcases le_total 0 c with hc0 | hc0
  · exact ae_recurrent_prod_core ha hb hc hc0 hβc hβsq (fun u => sigmaFiltration hU (unitPt u))
      (thetaHatC hU) hXm (continuous_thetaHatC hU) hsol 0
      (ComplexSLE.Recurrence.hstat_of_map_eq hXm hlaw 0)
  · -- reflection `θ ↦ -θ`, `c ↦ -c`
    have hc' : (-c) ^ 2 ≤ a * b := by rwa [neg_sq]
    have hβ2' : ∀ v, (fun w => β (-w)) v ^ 2 = 2 * diffusionD a b (-c) v := fun v => by
      simp only [diffusionD_neg_c, hβsq]
    have hsol' : ∀ u : ℝ, IsDiffusionSolution (sigmaFiltration hU (unitPt u)) (mu a b (-c))
        (fun w => β (-w)) (fun t ω => -thetaHatC hU t (ω, u)) P := fun u => by
      have := ComplexSLE.Recurrence.isDiffusionSolution_neg (hsol u)
      have e : (fun v => -mu a b c (-v)) = mu a b (-c) :=
        funext fun v => (mu_neg_c a b c v).symm
      rwa [e] at this
    have hstat' := ComplexSLE.Recurrence.hstat_neg_of_map_eq hXm hlaw 0
    rw [neg_zero] at hstat'
    have h := ae_recurrent_prod_core ha hb hc' (neg_nonneg.2 hc0) (hβc.comp continuous_neg) hβ2'
      (fun u => sigmaFiltration hU (unitPt u)) (fun t q => -thetaHatC hU t q)
      (fun t => (hXm t).neg) (fun q => (continuous_thetaHatC hU q).neg) hsol' 0 hstat'
    filter_upwards [h] with q hq s
    obtain ⟨t, hst, ht⟩ := hq s
    refine ⟨t, hst, ?_⟩
    rw [ComplexSLE.Recurrence.mem_latticeSet_iff] at ht ⊢
    obtain ⟨n, hn⟩ := ht
    exact ⟨-n, by push_cast; linarith⟩

/-- `θ̂` does not depend on the filtration of the adapted driver. -/
theorem thetaHat_congr_filtration {𝒢 : Filtration ℝ≥0 m} (hU : IsSLEDriverAdapted a b c U P ℱ)
    (hU' : IsSLEDriverAdapted a b c U P 𝒢) (z : ℂ) (s : ℝ≥0) (ω : Ω) :
    thetaHat hU' z s ω = thetaHat hU z s ω := by
  rw [thetaHat_eq_thetaC hU, thetaHat_eq_thetaC hU']

/-- The filtration `ℱ t ⊔ σ(measurable `P`-null sets)` (the completed filtration; it contains the
null sets in time `0`). -/
def nullFiltration (ℱ : Filtration ℝ≥0 m) (P : Measure Ω) : Filtration ℝ≥0 m where
  seq t := ℱ t ⊔ MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet[m] N ∧ P N = 0}
  mono' _ _ hst := sup_le_sup_right (ℱ.mono hst) _
  le' t := sup_le (ℱ.le t) (MeasurableSpace.generateFrom_le fun _ hN => hN.1)

/-- **Recurrence of `e^{2iθ̂}` on the product space (A5b, part A; Lemma 2.16 for the random point
`𝐳 = e^{iu}`).** Under `hMO : MarkovOneDim`: for `ν`-a.e. `u`, almost surely, for every `s` there
is `t ≥ s` with `e^{2iθ̂_t(e^{iu})} = 1`. -/
theorem ae_recurrent_unit [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) :
    ∀ᵐ u ∂(admissibleMeasure p), ∀ᵐ ω ∂P, ∀ s : ℝ≥0, ∃ t : ℝ≥0, s ≤ t ∧
      Complex.exp (2 * Complex.I * (thetaHat hU (unitPt u) t ω : ℂ)) = 1 := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  -- complete the filtration, so that the null sets lie in time `0`
  have hnull : ∀ N : Set Ω, MeasurableSet N → P N = 0 →
      MeasurableSet[nullFiltration ℱ P 0] N := fun N hN hN0 =>
    (le_sup_right : _ ≤ ℱ 0 ⊔ MeasurableSpace.generateFrom
      {N : Set Ω | MeasurableSet[m] N ∧ P N = 0}) _
      (MeasurableSpace.measurableSet_generateFrom ⟨hN, hN0⟩)
  have hU' : IsSLEDriverAdapted a b c U P (nullFiltration ℱ P) :=
    hU.of_le_sup_null (fun t => le_sup_left) (fun t => le_rfl)
  have h := ae_recurrent_prod_of_null hMO hnull hU' ha hb hc hp
  have h2 : ∀ᵐ q ∂(P.prod (admissibleMeasure p)), ∀ s : ℝ≥0, ∃ t : ℝ≥0, s ≤ t ∧
      Complex.exp (2 * Complex.I * (thetaHat hU (unitPt q.2) t q.1 : ℂ)) = 1 := by
    filter_upwards [h, ae_thetaHatC_eq hU' ha hc (ν := admissibleMeasure p)] with q hq heq s
    obtain ⟨t, hst, ht⟩ := hq s
    refine ⟨t, hst, ?_⟩
    rw [heq t, ComplexSLE.Recurrence.mem_latticeSet_iff_exp,
      thetaHat_congr_filtration hU hU'] at ht
    simpa using ht
  exact ae_ae_of_ae_prod_snd h2

end Main


end ComplexSLE.Internal

end
