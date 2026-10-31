/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Disconnect.Thm110ALsc
public import ComplexSLE.Internal.Phases.Prop32BUpHit
public import ComplexSLE.Internal.Phases.ErgodicConstRec
public import ComplexSLE.Internal.Recurrence.SLE

/-!
# Theorem 1.10(a), upgrade step: the restart inequality and `Λ = ℝ` (M8/T5b)

Source: paper.tex:L2199-2217 with the correction R27 (ERRATA.md).

* `RestartImpliesEvents E`: the one-sided form of future dependence, for `z ∉ L_s`,
  `E(u(· + s) - u s, f_s(z)) → E(u, z)`. `Disc` has it (`disc_of_disc_restart`), but not the
  converse (`restartImpliesEvents_disc`).
* `lintegral_evProb_fHat_le`: the Markov step at the σ-time `σ_z(s)` as an inequality,
  `∫_A q(f̂_s(z)) dP ≤ P(A ∩ E(U, z))` for `A ∈ 𝒢_s = ℱ_{σ_z(s)}`
  (`measure_inter_postDriver` and the a.s. implication `ae_postDriver_imp_event`).
* `evProb_disc_unit_pos` (R27, as `evProb_unit_pos` of Prop32BUpHit): if `Λ ≠ ∅` then `Λ = ℝ`.
  By periodicity choose `θ* ∈ Λ` below (`c ≥ 0`) or above (`c ≤ 0`) the starting point of
  `θ̂(e^{iu})`; the hitting lemma (`sle_hits_lower`, `sle_hits_upper`) gives that `θ̂` hits `θ*`
  with positive probability; `Λ` is open (lower semicontinuity of `q`), so `θ̂_s ∈ Λ` for some
  rational `s` with positive probability, and the Markov inequality at `σ_z(s)` gives
  `q(e^{iu}) ≥ ∫ q(f̂_s) dP > 0`.
* `evProb_disc_pos`: `q(z) > 0` for every `z ≠ 0` (scale invariance).

Consumes the EXTERNALs `strongMarkov_sleDriver` and (through the polar and recurrence layers)
`ito_formula`, `timeChange_isContLocalMartingale`, `hormander_oneDim`.
-/

public section

open scoped NNReal ENNReal Topology Real
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Internal

open Polar

/-- The one-sided future dependence of an event family: for `z ∉ L_s`, the event for the restarted
driver at `f_s(z)` implies the event for the driver at `z`. -/
def RestartImpliesEvents (E : (ℝ≥0 → ℂ) → ℂ → Prop) : Prop :=
  ∀ (u : ℝ≥0 → ℂ) (hu : Continuous u) (s : ℝ≥0) (z : ℂ) (hz : z ∈ (leftHull u s)ᶜ),
    E (fun r => u (r + s) - u s) (centeredLoewnerMap u hu s ⟨z, hz⟩) → E u z

theorem restartImpliesEvents_disc : RestartImpliesEvents Disc :=
  fun _ hu s z hz h => disc_of_disc_restart hu s z hz h

section Markov

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- **Restart implication at the σ-time.** For `z ≠ 0` and `s ≥ 0`, almost surely
`E(V, f̂_s(z)) → E(U, z)`, where `V` is the post-`σ_z(s)` driver. -/
theorem ae_postDriver_imp_event [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ)
    (ha : 0 < a) (hc : c ^ 2 ≤ a * b) {E : (ℝ≥0 → ℂ) → ℂ → Prop}
    (hEr : RestartImpliesEvents E) {z : ℂ} (hz : z ≠ 0) (s : ℝ≥0) :
    ∀ᵐ ω ∂P, E (fun r => postDriver U (sigmaTop hU z s) r ω) (fHat hU z s ω) →
      E (fun t => U t ω) z := by
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
  have hfut := hEr (fun t => U t ω) (hU.cont ω) s' z hz'
  have hcl : centeredLoewnerMap (fun t => U t ω) (hU.cont ω) s' ⟨z, hz'⟩ = fHat hU z s ω := by
    rw [centeredLoewnerMap_eq_fPath (hU.cont ω) s' hz', fHat_of_mem hU hmem, hsσ]
  have hpath : (fun r => (fun t => U t ω) (r + s') - (fun t => U t ω) s') =
      fun r => postDriver U τ r ω := by
    funext r
    simp only [postDriver, hs, add_comm r]
  rw [hcl, hpath] at hfut
  exact hfut

/-- **The Markov step at the σ-time `σ_z(s)`, as an inequality.** For `A ∈ 𝒢_s = ℱ_{σ_z(s)}`,
`∫_A q(f̂_s(z)) dP ≤ P(A ∩ E(U, z))`. -/
theorem lintegral_evProb_fHat_le [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hc : c ^ 2 ≤ a * b)
    {E : (ℝ≥0 → ℂ) → ℂ → Prop} (hEr : RestartImpliesEvents E) {M : Set ((ℝ≥0 → ℂ) × ℂ)}
    (hM : MeasurableSet M) (hEM : ∀ (u : ℝ≥0 → ℂ) (z : ℂ), Continuous u → (E u z ↔ (u, z) ∈ M))
    {z : ℂ} (hz : z ≠ 0) (s : ℝ≥0) {A : Set Ω} (hA : MeasurableSet[sigmaFiltration hU z s] A) :
    ∫⁻ ω in A, evProb E P U (fHat hU z s ω) ∂P ≤ P (A ∩ {ω | E (fun t => U t ω) z}) := by
  have hτ := isStoppingTime_sigmaTop hU z s
  have hgood := ae_thetaHat_eq_and_continuous hU ha hc hz
  have hfin : ∀ᵐ ω ∂P, sigmaTop hU z s ω ≠ ⊤ := by
    filter_upwards [hgood] with ω hω
    rw [sigmaTop_of_mem hU (hω.1 s)]
    exact WithTop.coe_ne_top
  have hX : Measurable[hτ.measurableSpace] (fHat hU z s) := measurable_fHat hU s
  have hmain := measure_inter_postDriver hU hτ hfin hX hA hM
  have himp := ae_postDriver_imp_event hU ha hc hEr hz s
  have hae : (A ∩ {ω | ((fun r => postDriver U (sigmaTop hU z s) r ω), fHat hU z s ω) ∈ M} :
      Set Ω) ≤ᵐ[P] (A ∩ {ω | E (fun t => U t ω) z} : Set Ω) := by
    filter_upwards [himp] with ω h hω
    refine ⟨hω.1, h ?_⟩
    exact (hEM _ _ (continuous_postDriver hU _ ω)).2 hω.2
  refine le_trans (le_of_eq ?_) (measure_mono_ae hae)
  rw [hmain]
  refine lintegral_congr fun ω => ?_
  unfold evProb
  congr 1
  ext ω'
  exact hEM _ _ (hU.cont ω')

end Markov

section Hit

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- **R27 + fixed-time Markov inequality: `Λ ≠ ∅` implies `Λ = ℝ`** (paper.tex:L2205-2210,
corrected as in `evProb_unit_pos`). If `q(e^{iu₀}) > 0` for some `u₀`, then `q(e^{iu}) > 0` for
every `u`, for `q(ξ) = P(Disc(U, ξ))`. The null sets are assumed to lie in `ℱ 0`. -/
theorem evProb_disc_unit_pos [IsProbabilityMeasure P]
    (hnull : ∀ N : Set Ω, MeasurableSet N → P N = 0 → MeasurableSet[ℱ 0] N)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (hΛ : ∃ u₀ : ℝ, 0 < evProb Disc P U (unitPt u₀)) (u : ℝ) :
    0 < evProb Disc P U (unitPt u) := by
  set q : ℂ → ℝ≥0∞ := evProb Disc P U with hq
  set Λ : Set ℝ := {u | 0 < q (unitPt u)} with hΛdef
  have hΛopen : IsOpen Λ := isOpen_evProb_disc_unit_pos hU
  obtain ⟨u₀, hu₀⟩ := hΛ
  have hu₀Λ : u₀ ∈ Λ := hu₀
  -- the diffusion `θ̂(e^{iu})`, started at `y`
  obtain ⟨β, hβ, hβsq, -⟩ := exists_beta ha hb hc
  have hβc : Continuous β := hβ.continuous
  have hsol := isDiffusionSolution_thetaHatC_fibre hnull hU ha hb hc hβsq u
  set X : ℝ≥0 → Ω → ℝ := fun t ω => thetaHatC hU t (ω, u) with hX
  have hXc : ∀ ω, Continuous fun t => X t ω := fun ω => continuous_thetaHatC hU (ω, u)
  set y : ℝ := argInit (fun _ => (0 : ℂ)) continuous_const (unitPt u) with hy
  have h0 : ∀ᵐ ω ∂P, X 0 ω = y := by
    filter_upwards [ae_fibre_mem_goodSet hU ha hc u,
      thetaHat_zero_ae hU ha hc (unitPt_ne_zero u)] with ω hg h0
    rw [hX]
    simp only
    rw [thetaHatC_of_mem hU hg 0]
    exact h0
  -- a level `θ* ∈ Λ` that `θ̂` hits with positive probability
  have hhit : ∃ θ ∈ Λ, 0 < P.real {ω | ∃ t : ℝ≥0, X t ω = θ} := by
    rcases le_total 0 c with hc0 | hc0
    · obtain ⟨k, hk⟩ := exists_nat_gt ((u₀ - y) / (2 * π))
      have hθ : u₀ - 2 * π * k < y := by
        have h2π : 0 < 2 * π := by positivity
        rw [div_lt_iff₀ h2π] at hk
        nlinarith
      have hθΛ : u₀ - 2 * π * k ∈ Λ := by
        change 0 < q (unitPt (u₀ - 2 * π * k))
        rw [unitPt_sub_two_pi_nat_mul]; exact hu₀
      obtain ⟨T, δ, -, hδ, h⟩ := ComplexSLE.Recurrence.sle_hits_lower ha hb hc hc0 hβc hβsq hθ
      refine ⟨_, hθΛ, lt_of_lt_of_le hδ ((h Ω P _ X hsol hXc ?_).trans (measureReal_mono ?_))⟩
      · filter_upwards [h0] with ω hω
        rw [hω]; exact ⟨hθ.le, le_rfl⟩
      · rintro ω ⟨t, -, ht⟩
        exact ⟨t, ht⟩
    · obtain ⟨k, hk⟩ := exists_nat_gt ((y - u₀) / (2 * π))
      have hθ : y < u₀ + 2 * π * k := by
        have h2π : 0 < 2 * π := by positivity
        rw [div_lt_iff₀ h2π] at hk
        nlinarith
      have hθΛ : u₀ + 2 * π * k ∈ Λ := by
        change 0 < q (unitPt (u₀ + 2 * π * k))
        rw [unitPt_add_two_pi_nat_mul]; exact hu₀
      obtain ⟨T, δ, -, hδ, h⟩ := ComplexSLE.Recurrence.sle_hits_upper ha hb hc hc0 hβc hβsq hθ
      refine ⟨_, hθΛ, lt_of_lt_of_le hδ ((h Ω P _ X hsol hXc ?_).trans (measureReal_mono ?_))⟩
      · filter_upwards [h0] with ω hω
        rw [hω]; exact ⟨le_rfl, hθ.le⟩
      · rintro ω ⟨t, -, ht⟩
        exact ⟨t, ht⟩
  obtain ⟨θ, hθΛ, hθpos⟩ := hhit
  have hPH : P {ω | ∃ t : ℝ≥0, X t ω = θ} ≠ 0 := by
    intro h
    simp [Measure.real, h] at hθpos
  -- at a rational time `s`, `θ̂_s ∈ Λ` with positive probability
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hsub : {ω | ∃ t : ℝ≥0, X t ω = θ} ⊆ ⋃ s ∈ D, {ω | X s ω ∈ Λ} := by
    rintro ω ⟨t, ht⟩
    have hopen : IsOpen ((fun s => X s ω) ⁻¹' Λ) := hΛopen.preimage (hXc ω)
    obtain ⟨s, hsD, hs⟩ := hDd.exists_mem_open hopen ⟨t, by simp only [mem_preimage, ht]; exact hθΛ⟩
    exact mem_biUnion hsD hs
  have hex : ∃ s ∈ D, P {ω | X s ω ∈ Λ} ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hPH (measure_mono_null hsub ?_)
    exact (measure_biUnion_null_iff hDc).2 hcon
  obtain ⟨s, -, hs⟩ := hex
  -- the Markov inequality at `σ_z(s)`
  obtain ⟨M, hMm, hM⟩ := measurableEvents_disc
  have hmark := lintegral_evProb_fHat_le hU ha hc restartImpliesEvents_disc hMm hM
    (unitPt_ne_zero u) s MeasurableSet.univ
  rw [Set.univ_inter, Measure.restrict_univ] at hmark
  have hfm : Measurable fun ω => q (fHat hU (unitPt u) s ω) := by
    have hfH : Measurable (fHat hU (unitPt u) s) :=
      (measurable_fHat hU s).mono ((sigmaFiltration hU (unitPt u)).le s) le_rfl
    exact (measurable_evProb hU hMm hM).comp hfH
  have hqz : ∫⁻ ω, q (fHat hU (unitPt u) s ω) ∂P ≤ q (unitPt u) := hmark
  refine lt_of_lt_of_le ?_ hqz
  rw [pos_iff_ne_zero, Ne, lintegral_eq_zero_iff hfm]
  intro hzero
  apply hs
  have hgood := ae_thetaHat_eq_and_continuous hU (z := unitPt u) ha hc (unitPt_ne_zero u)
  have hae : ∀ᵐ ω ∂P, ω ∈ {ω | X s ω ∈ Λ} → False := by
    filter_upwards [hzero, hgood, ae_fibre_mem_goodSet hU ha hc u] with ω h1 h2 h3 hω
    have hmem := h2.1 s
    have hlife := sigmaTime_mem_lifeSet (hU.cont ω) hmem
    have hne := fPath_ne_zero (hU.cont ω) hlife
    have hexp := exp_argPath_mul_I (hU.cont ω) hlife
    have hXs : X s ω = thetaHat hU (unitPt u) s ω := thetaHatC_of_mem hU h3 s
    have hω' : 0 < q (unitPt (thetaHat hU (unitPt u) s ω)) := by
      have : thetaHat hU (unitPt u) s ω ∈ Λ := by rw [← hXs]; exact hω
      exact this
    have hq1 : q (fHat hU (unitPt u) s ω) = q (unitPt (thetaHat hU (unitPt u) s ω)) := by
      rw [fHat_of_mem hU hmem, thetaHat_of_mem hU hmem, hq]
      have e1 := evProb_eq_unit hU scaleInvariantEvents_disc hMm hM hne
      rw [e1, ← hexp]
      rfl
    have : q (fHat hU (unitPt u) s ω) = 0 := h1
    rw [hq1] at this
    exact absurd hω' (by rw [this]; exact lt_irrefl _)
  refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hae)
  exact fun h => h hω

theorem div_norm_eq_unitPt_arg {z : ℂ} (hz : z ≠ 0) : z / (‖z‖ : ℂ) = unitPt (Complex.arg z) := by
  unfold unitPt
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  rw [div_eq_iff hn, mul_comm]
  exact (Complex.norm_mul_exp_arg_mul_I z).symm

/-- **`Λ ≠ ∅` from `q(z₀) > 0`** (scale invariance): if `P(Disc(U, z₀)) > 0` for some `z₀ ≠ 0`,
then `P(Disc(U, e^{iu₀})) > 0` for some `u₀`. -/
theorem exists_evProb_disc_unit_pos (hU : IsSLEDriverAdapted a b c U P ℱ) {z : ℂ} (hz : z ≠ 0)
    (h : 0 < evProb Disc P U z) : ∃ u₀ : ℝ, 0 < evProb Disc P U (unitPt u₀) := by
  obtain ⟨M, hMm, hM⟩ := measurableEvents_disc
  refine ⟨Complex.arg z, ?_⟩
  rw [← div_norm_eq_unitPt_arg hz, ← evProb_eq_unit hU scaleInvariantEvents_disc hMm hM hz]
  exact h

/-- **`q(z) > 0` for every `z ≠ 0`** (scale invariance). -/
theorem evProb_disc_pos [IsProbabilityMeasure P]
    (hnull : ∀ N : Set Ω, MeasurableSet N → P N = 0 → MeasurableSet[ℱ 0] N)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (hΛ : ∃ u₀ : ℝ, 0 < evProb Disc P U (unitPt u₀)) {z : ℂ} (hz : z ≠ 0) :
    0 < evProb Disc P U z := by
  obtain ⟨M, hMm, hM⟩ := measurableEvents_disc
  rw [evProb_eq_unit hU scaleInvariantEvents_disc hMm hM hz, div_norm_eq_unitPt_arg hz]
  exact evProb_disc_unit_pos hnull hU ha hb hc hΛ _

end Hit

end ComplexSLE.Internal

end
