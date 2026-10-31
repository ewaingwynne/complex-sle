/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsSLEDriver
import ComplexSLE.Internal.Driver.Shift
import ComplexSLE.Internal.Driver.Transform

/-!
# Everywhere-continuous measurable versions of an `SLE_Σ` driver

`IsSLEDriver a b c U P` only asks for *almost sure* path continuity and does not even make the
coordinates `U t` measurable (only `P`-a.e. equal to a measurable function). This file produces,
for any such driver, an indistinguishable version `U'` with every path continuous, `U' 0 = 0`
everywhere, every coordinate `U' t` measurable, and again an `SLE_Σ` driver (the modification is
the identity off a measurable `P`-null set `N` and `0` on `N`).

* `IsSLEDriver.congr_ae`: an `SLE_Σ` driver stays an `SLE_Σ` driver after an a.s.-indistinguishable
  modification (no measurability needed).
* `IsSLEDriver.exists_measurable_version`: the version described above, together with the null
  set `N`.

This is step 1 of the driver bridge (`M7/A1`): the version feeds the natural filtration in
`ComplexSLE.Internal.BridgeAdapted`.
-/

public section

open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.IsSLEDriver

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- **Indistinguishable modification.** If `U` is an `SLE_Σ` driver and `U'` agrees with `U`
simultaneously for all times outside a `P`-null set, then `U'` is an `SLE_Σ` driver. -/
theorem congr_ae (hU : IsSLEDriver a b c U P) {U' : ℝ≥0 → Ω → ℂ}
    (h : ∀ᵐ ω ∂P, ∀ t, U' t ω = U t ω) : IsSLEDriver a b c U' P := by
  have h1 : ∀ t, U' t =ᵐ[P] U t := fun t => by filter_upwards [h] with ω hω using hω t
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hU.cont, h] with ω hω hω'
    have : (fun t => U' t ω) = fun t => U t ω := funext hω'
    rwa [this]
  · filter_upwards [hU.zero, h] with ω hω hω'
    rw [hω' 0]
    exact hω
  · intro n s hs
    refine (iIndepFun_congr (fun i => ?_)).1 (hU.indepIncrements n s hs)
    exact ((h1 (s i.succ)).symm.sub (h1 (s i.castSucc)).symm)
  · intro s t hst
    refine (hU.law_increment s t hst).congr ?_
    exact (h1 t).sub (h1 s)

/-- **Everywhere-continuous measurable version.** For an `SLE_Σ` driver `U` there are a measurable
`P`-null set `N` and a process `U'` which equals `U` off `N` and `0` on `N`, such that every path
of `U'` is continuous, `U' 0 = 0` everywhere, every `U' t` is measurable, and `U'` is an
`SLE_Σ` driver. -/
theorem exists_measurable_version (hU : IsSLEDriver a b c U P) :
    ∃ (N : Set Ω) (U' : ℝ≥0 → Ω → ℂ), MeasurableSet N ∧ P N = 0 ∧
      (∀ ω ∉ N, ∀ t, U' t ω = U t ω) ∧ (∀ ω ∈ N, ∀ t, U' t ω = 0) ∧
      (∀ ω, Continuous fun t => U' t ω) ∧ (∀ ω, U' 0 ω = 0) ∧ (∀ t, Measurable (U' t)) ∧
      IsSLEDriver a b c U' P := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ → ℝ≥0, DenseRange d := TopologicalSpace.exists_dense_seq ℝ≥0
  have hmk : ∀ n, AEMeasurable (U (d n)) P := fun n => hU.aemeasurable _
  set V : ℕ → Ω → ℂ := fun n => (hmk n).mk (U (d n)) with hVdef
  have hV : ∀ n, Measurable (V n) := fun n => (hmk n).measurable_mk
  have hVae : ∀ n, U (d n) =ᵐ[P] V n := fun n => (hmk n).ae_eq_mk
  have hgood : ∀ᵐ ω ∂P, (Continuous fun t => U t ω) ∧ U 0 ω = 0 ∧ ∀ n, U (d n) ω = V n ω := by
    filter_upwards [hU.cont, hU.zero, ae_all_iff.2 hVae] with ω h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hgoodN : ∀ ω ∉ N, (Continuous fun t => U t ω) ∧ U 0 ω = 0 ∧ ∀ n, U (d n) ω = V n ω :=
    fun ω hω => by_contra fun h => hω (hsub h)
  set U' : ℝ≥0 → Ω → ℂ := fun t ω => Nᶜ.indicator (U t) ω with hU'
  have hout : ∀ ω ∉ N, ∀ t, U' t ω = U t ω := fun ω hω t => by simp [hU', hω]
  have hin : ∀ ω ∈ N, ∀ t, U' t ω = 0 := fun ω hω t => by simp [hU', hω]
  have hcont : ∀ ω, Continuous fun t => U' t ω := fun ω => by
    by_cases hω : ω ∈ N
    · simp only [hin ω hω]
      exact continuous_const
    · have : (fun t => U' t ω) = fun t => U t ω := funext (hout ω hω)
      rw [this]
      exact (hgoodN ω hω).1
  have hmeas : ∀ t, Measurable (U' t) := by
    intro t
    have ht : t ∈ closure (Set.range d) := by rw [hd.closure_range]; exact mem_univ t
    obtain ⟨x, hxr, hxt⟩ := mem_closure_iff_seq_limit.1 ht
    choose k hk using hxr
    refine measurable_of_tendsto_metrizable (f := fun j => Nᶜ.indicator (V (k j)))
      (fun j => (hV (k j)).indicator hNm.compl) (tendsto_pi_nhds.2 fun ω => ?_)
    by_cases hω : ω ∈ N
    · simp only [hin ω hω, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hω)]
      exact tendsto_const_nhds
    · have hω' : ω ∈ Nᶜ := hω
      simp only [Set.indicator_of_mem hω', hout ω hω]
      have h1 : Tendsto (fun j => U (d (k j)) ω) atTop (𝓝 (U t ω)) := by
        have h2 := ((hgoodN ω hω).1.tendsto t).comp hxt
        have h3 : (fun j => U (d (k j)) ω) = (fun t => U t ω) ∘ x := by
          funext j
          simp only [Function.comp_apply, hk j]
        rwa [h3]
      refine h1.congr fun j => ?_
      exact (hgoodN ω hω).2.2 (k j)
  have hae : ∀ᵐ ω ∂P, ∀ t, U' t ω = U t ω := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω t using hout ω hω t
  refine ⟨N, U', hNm, hN0, hout, hin, hcont, fun ω => ?_, hmeas, hU.congr_ae hae⟩
  by_cases hω : ω ∈ N
  · exact hin ω hω 0
  · rw [hout ω hω 0]
    exact (hgoodN ω hω).2.1

end ComplexSLE.IsSLEDriver

end
