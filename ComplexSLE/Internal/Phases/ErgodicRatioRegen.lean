/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.ErgodicConstStop
public import ComplexSLE.Internal.Phases.ErgodicConstFibre

/-!
# Regeneration data remembering the σ-time past (M7/D2)

`nonempty_regenDatum_le` is `nonempty_regenDatum` (`ErgodicConstStop.lean`) with the additional
conclusion `𝒢_k ≤ ℱ_S`, `𝒢_k = sigmaFiltration hU z k`: the regeneration time `S = hitTime` is
at or after `σ_z(k)` (`sigmaFiltration_le_hitTime`). It is used to show that the Birkhoff limit
of `∫₀ⁿ cos 2θ̂` (`ErgodicRatioConst.lean`) is a.s. constant: the past functionals `C_n` of the
σ-time process are `ℱ_S`-measurable weights for `S` the level-`n` regeneration time.
-/

@[expose] public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal

open Polar

section Datum

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

variable (hU : IsSLEDriverAdapted a b c U P ℱ) {z : ℂ}

/-- **The regeneration datum with σ-time past** (`ErgodicConstRegen.lean`) at level `k`, for
`z ≠ 0` such that `e^{2iθ̂(z)}` is a.s. recurrent to `1` (and null sets in `ℱ 0`): the datum of
`nonempty_regenDatum` (same construction, `S = hitTime`), together with the inclusion of the
σ-time σ-algebra `𝒢_k = ℱ_{σ_z(k)}` into `ℱ_S`. This is what makes every `𝒢_k`-measurable
past functional (e.g. `∫₀ᵏ cos 2θ̂`) an `ℱ_S`-measurable weight. -/
theorem nonempty_regenDatum_le [IsProbabilityMeasure P]
    (hnull : ∀ N : Set Ω, MeasurableSet N → P N = 0 → MeasurableSet[ℱ 0] N)
    (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0)
    (hrec : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, ∃ t : ℝ≥0, s ≤ t ∧
      Complex.exp (2 * Complex.I * (thetaHat hU z t ω : ℂ)) = 1) (k : ℕ) :
    ∃ D : RegenDatum hU z k, sigmaFiltration hU z (k : ℝ≥0) ≤ D.hS.measurableSpace := by
  classical
  have hgood : ∀ᵐ ω ∂P, sigmaDom (fun r => U r ω) (hU.cont ω) z = Ici 0 ∧
      (hitSet hU z k ω).Nonempty := by
    filter_upwards [ae_sigmaDom_eq_Ici hU z ha hc hz, hrec] with ω h1 h2
    exact ⟨h1, hitSet_nonempty_of_recurrent hU h1 h2 k⟩
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hNgood : ∀ ω, ω ∉ N → sigmaDom (fun r => U r ω) (hU.cont ω) z = Ici 0 ∧
      (hitSet hU z k ω).Nonempty := fun ω hω => by
    by_contra h; exact hω (hNsub h)
  have hae : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  set S : Ω → WithTop ℝ≥0 := hitTime hU z k with hSdef
  have hS : IsStoppingTime ℱ S := isStoppingTime_hitTime hU k
  set τ : Ω → ℝ≥0 := fun ω => if ω ∈ N then 0 else
    (clock (fun r => U r ω) (hU.cont ω) z (((S ω).untopA : ℝ≥0) : ℝ)).toNNReal with hτdef
  -- pathwise facts off `N`
  have hpath : ∀ ω, ω ∉ N → ∃ t : ℝ≥0, S ω = (t : WithTop ℝ≥0) ∧ t ∈ hitSet hU z k ω ∧
      (τ ω : ℝ) = clock (fun r => U r ω) (hU.cont ω) z (t : ℝ) := by
    intro ω hω
    obtain ⟨t, ht, hteq⟩ := exists_hitTime_eq_coe hU (hNgood ω hω).2
    refine ⟨t, hteq, ht, ?_⟩
    have hSω : S ω = (t : WithTop ℝ≥0) := hteq
    have hteq' : ((S ω).untopA : ℝ≥0) = t := by rw [hSω]; rfl
    simp only [hτdef, hω, ite_false, hteq']
    exact Real.coe_toNNReal _ (clock_nonneg (hU.cont ω) ht.2.1)
  have hτ0 : ∀ ω, ω ∈ N → τ ω = 0 := fun ω hω => by simp [hτdef, hω]
  refine ⟨⟨S, hS, ?_, τ, ?_, ?_, ?_, ?_, ?_, ?_⟩, sigmaFiltration_le_hitTime hU le_rfl⟩
  · -- hfin
    filter_upwards [hae] with ω hω
    obtain ⟨t, ht, -⟩ := hpath ω hω
    rw [ht]; exact WithTop.coe_ne_top
  · -- hX
    have hNS : MeasurableSet[hS.measurableSpace] N := by
      rw [hS.measurableSet]
      have h0 := hnull N hNm hN0
      refine ⟨(le_iSup (fun t => ℱ t) 0) _ h0, fun i => ?_⟩
      exact (ℱ.mono (zero_le : (0 : ℝ≥0) ≤ i) _ h0).inter (hS i)
    have hX₀ : Measurable[hS.measurableSpace]
        (fun ω => (‖fHat hU z (0 : ℝ≥0) ω‖₊, thetaHat hU z (0 : ℝ≥0) ω)) := by
      have hle : sigmaFiltration hU z (0 : ℝ≥0) ≤ hS.measurableSpace :=
        sigmaFiltration_le_hitTime hU (by simp)
      have h1 := (measurable_fHat hU (z := z) (0 : ℝ≥0)).mono hle le_rfl
      have h2 := (((isStronglyProgressive_thetaHat hU (z := z)).stronglyAdapted
        (0 : ℝ≥0)).measurable).mono hle le_rfl
      exact (measurable_nnnorm.comp h1).prodMk h2
    have hX' : Measurable[hS.measurableSpace] (fun ω =>
        (‖stoppedValue (centeredOrZero U hU.cont z) S ω‖₊, stoppedValue (argOrZero hU z) S ω)) := by
      have h1 := measurable_stoppedValue
        (isStronglyProgressive_centeredOrZero hU.cont hU.adapted z) hS
      have h2 := measurable_stoppedValue (isStronglyProgressive_argOrZero hU z) hS
      exact (measurable_nnnorm.comp h1).prodMk h2
    have heq : (fun ω => (‖fHat hU z (τ ω) ω‖₊, thetaHat hU z (τ ω) ω)) = fun ω =>
        if ω ∈ N then (‖fHat hU z (0 : ℝ≥0) ω‖₊, thetaHat hU z (0 : ℝ≥0) ω) else
          (‖stoppedValue (centeredOrZero U hU.cont z) S ω‖₊,
            stoppedValue (argOrZero hU z) S ω) := by
      funext ω
      by_cases hω : ω ∈ N
      · simp only [hω, ite_true, hτ0 ω hω]
      · simp only [hω, ite_false]
        obtain ⟨t, hSt, ht, hτt⟩ := hpath ω hω
        obtain ⟨-, h2, h3, -⟩ := hitSet_sigma_facts hU (hNgood ω hω).1 ht hτt
        have hSt' : S ω = (t : WithTop ℝ≥0) := hSt
        have hl := ht.2.1
        have e1 : stoppedValue (centeredOrZero U hU.cont z) S ω =
            fPath (fun r => U r ω) (hU.cont ω) z (t : ℝ) := by
          simp only [stoppedValue, hSt']; exact centeredOrZero_eq hU.cont z hl
        have e2 : stoppedValue (argOrZero hU z) S ω =
            argPath (fun r => U r ω) (hU.cont ω) z (t : ℝ) := by
          simp only [stoppedValue, hSt']; exact argOrZero_eq hU z hl
        rw [e1, e2, h2, h3]
    rw [heq]
    let _ : MeasurableSpace Ω := hS.measurableSpace
    exact Measurable.ite hNS hX₀ hX'
  · -- hpos
    filter_upwards [hae] with ω hω
    obtain ⟨t, -, ht, hτt⟩ := hpath ω hω
    obtain ⟨-, -, hf, -⟩ := hitSet_sigma_facts hU (hNgood ω hω).1 ht hτt
    rw [hf]
    exact nnnorm_pos.2 (fPath_ne_zero (hU.cont ω) ht.2.1)
  · -- hobs
    filter_upwards [hae] with ω hω
    obtain ⟨t, hSt, ht, hτt⟩ := hpath ω hω
    have hall := (hNgood ω hω).1
    obtain ⟨h1, -, -, -⟩ := hitSet_sigma_facts hU hall ht hτt
    have e := pathObsAt_eq_obsC hU (z := z) (s := τ ω) (ω := ω) hall
    have hpp : postPath hU (sigmaTop hU z (τ ω)) ω = postPath hU S ω := by
      apply Subtype.ext
      funext s'
      have hSt' : S ω = (t : WithTop ℝ≥0) := hSt
      simp only [postPath, CPath.ofDriver, postDriver, h1, hSt']
    rw [e, hpp]
  · -- hstate
    filter_upwards [hae] with ω hω
    obtain ⟨t, -, ht, hτt⟩ := hpath ω hω
    obtain ⟨-, h2, -, -⟩ := hitSet_sigma_facts hU (hNgood ω hω).1 ht hτt
    rw [h2]
    have := (ComplexSLE.Recurrence.mem_latticeSet_iff_exp).1 ht.2.2
    simpa using this
  · -- hk
    filter_upwards [hae] with ω hω
    obtain ⟨t, -, ht, hτt⟩ := hpath ω hω
    exact (hitSet_sigma_facts hU (hNgood ω hω).1 ht hτt).2.2.2
  · -- hpast
    intro n hn
    have hle : sigmaFiltration hU z (n : ℝ≥0) ≤ hS.measurableSpace :=
      sigmaFiltration_le_hitTime hU (by exact_mod_cast hn)
    have h := (measurable_fHat hU (z := z) (n : ℝ≥0)).mono hle le_rfl
    exact Real.measurable_log.comp (measurable_norm.comp h)

end Datum

end ComplexSLE.Internal

end
