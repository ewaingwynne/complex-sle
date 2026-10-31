/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.Prop32BUpEvents
public import ComplexSLE.Internal.Phases.Prop32BUpMarkov
public import ComplexSLE.Internal.Phases.ErgodicConstRec
public import ComplexSLE.Internal.Recurrence.SLE

/-!
# Proposition 3.2(b): `q(z) > 0` for every `z ≠ 0` (M7/E5, steps 1-4 of the upgrade)

Source: paper.tex:L1786-1810 with the approved correction ERRATA.md R27 (hitting lemma replaces
Girsanov). Let `U` be an adapted `SLE_Σ` driver and `q(ξ) = P(StaysAway(U, ξ))`.

* `exists_ball_lt_evProb_staysAway` (**Koebe ball**, L1806-1810): if `q(z) > 0` there is `δ > 0`
  with `q(w) > q(z)/2` for `‖w - z‖ < δ`. (`P(StaysAway z) = sup_n P(StaysAwayBy 1/(n+1) z)` since
  `T_z > 0` a.s.; and `StaysAwayBy r z` implies `StaysAway w` for `w ∈ B(z, r/16)`,
  `staysAway_of_staysAwayBy`.)
* `isOpen_evProb_unit_pos`: `Λ = {u | q(e^{iu}) > 0}` is open.
* `exists_evProb_unit_pos`: from the hypothesis `P ⊗ ν (StaysAway at the random point) > 0`, `Λ`
  is nonempty (Fubini).
* `evProb_unit_pos` (**R27**, L1796-1803): if `Λ ≠ ∅` then `Λ = ℝ`. By periodicity choose
  `θ* ∈ Λ` below (`c ≥ 0`) or above (`c ≤ 0`) the starting point `y` of `θ̂(e^{iu})`. The
  hitting lemma (`sle_hits_lower`, `sle_hits_upper`) gives that the everywhere continuous version of
  `θ̂` hits `θ*` with positive probability. As `Λ` is open, `θ̂_s ∈ Λ` for some rational `s` with
  positive probability, and the Markov step at `σ_z(s)` (`measure_inter_event_eq_lintegral`)
  gives `q(e^{iu}) = ∫ q(f̂_s) dP > 0`. (This uses a *fixed* σ-time instead of the hitting time;
  openness of `Λ` is what makes this possible.)
* `evProb_pos`: `q(z) > 0` for all `z ≠ 0` (scale invariance).

Consumes the EXTERNALs `strongMarkov_sleDriver`, `koebe_quarter` and (through the polar layer)
`ito_formula`, `timeChange_isContLocalMartingale`.
-/

public section

open scoped NNReal ENNReal Topology Real
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Internal

open Polar

section Prelim

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- `ξ ↦ P(E(U, ξ))` is measurable. -/
theorem measurable_evProb (hU : IsSLEDriverAdapted a b c U P ℱ) [SFinite P]
    {E : (ℝ≥0 → ℂ) → ℂ → Prop} {M : Set ((ℝ≥0 → ℂ) × ℂ)} (hM : MeasurableSet M)
    (hEM : ∀ (u : ℝ≥0 → ℂ) (z : ℂ), Continuous u → (E u z ↔ (u, z) ∈ M)) :
    Measurable (evProb E P U) := by
  have hUm : ∀ t, Measurable (U t) := fun t => Measurable.mono (hU.adapted t) (ℱ.le t) le_rfl
  have hpair : Measurable fun p : ℂ × Ω => ((fun t => U t p.2), p.1) :=
    (measurable_pi_iff.2 fun t => (hUm t).comp measurable_snd).prodMk measurable_fst
  have hS : MeasurableSet {p : ℂ × Ω | ((fun t => U t p.2), p.1) ∈ M} := hpair hM
  have h := measurable_measure_prodMk_left (ν := P) hS
  convert h using 2 with ξ
  unfold evProb
  congr 1
  ext ω
  exact hEM _ _ (hU.cont ω)

end Prelim

section Ball

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- **The Koebe ball** (paper.tex:L1806-1810). If `q(z) = P(StaysAway(U, z)) > 0` there is `δ > 0`
with `q(z)/2 < q(w)` for all `w` with `‖w - z‖ < δ`. -/
theorem exists_ball_lt_evProb_staysAway [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hc : c ^ 2 ≤ a * b) {z : ℂ}
    (hz : z ≠ 0) (hq : 0 < evProb StaysAway P U z) :
    ∃ δ > 0, ∀ w : ℂ, ‖w - z‖ < δ → evProb StaysAway P U z / 2 < evProb StaysAway P U w := by
  have hT0 : ∀ᵐ ω ∂P, 0 < absorbingTime (fun t => U t ω) z := by
    filter_upwards [ae_sigmaDom_eq_Ici hU z ha hc hz] with ω hω
    exact pos_absorbingTime_of_mem_sigmaDom (hU.cont ω) (by rw [hω]; exact Set.mem_Ici.2 le_rfl)
  set S : ℕ → Set Ω := fun n => {ω | StaysAwayBy (1 / ((n : ℝ) + 1)) (fun t => U t ω) z} with hS
  have hmono : Monotone S := fun m n hmn ω hω => staysAwayBy_one_div_mono hmn hω
  have hle : evProb StaysAway P U z ≤ P (⋃ n, S n) := by
    unfold evProb
    refine measure_mono_ae ?_
    filter_upwards [hT0] with ω h0 hω
    obtain ⟨n, hn⟩ := exists_staysAwayBy hω h0
    exact mem_iUnion.2 ⟨n, hn⟩
  rw [hmono.measure_iUnion] at hle
  have hqtop : evProb StaysAway P U z ≠ ⊤ := measure_ne_top _ _
  have hlt : evProb StaysAway P U z / 2 < ⨆ n, P (S n) :=
    lt_of_lt_of_le (ENNReal.half_lt_self hq.ne' hqtop) hle
  obtain ⟨n, hn⟩ := lt_iSup_iff.1 hlt
  refine ⟨(1 / ((n : ℝ) + 1)) / 16, by positivity, fun w hw => ?_⟩
  refine lt_of_lt_of_le hn (measure_mono fun ω hω => ?_)
  exact staysAway_of_staysAwayBy (hU.cont ω) hω hw

/-- `Λ = {u | q(e^{iu}) > 0}` is open. -/
theorem isOpen_evProb_unit_pos [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ)
    (ha : 0 < a) (hc : c ^ 2 ≤ a * b) :
    IsOpen {u : ℝ | 0 < evProb StaysAway P U (unitPt u)} := by
  rw [isOpen_iff_mem_nhds]
  intro u hu
  obtain ⟨δ, hδ, h⟩ := exists_ball_lt_evProb_staysAway hU ha hc (unitPt_ne_zero u) hu
  have hev : ∀ᶠ u' in 𝓝 u, unitPt u' ∈ Metric.ball (unitPt u) δ :=
    (continuous_unitPt.tendsto u).eventually (Metric.ball_mem_nhds _ hδ)
  filter_upwards [hev] with u' hu'
  have h1 := h (unitPt u') (by simpa [dist_eq_norm] using hu')
  exact lt_trans (ENNReal.half_pos hu.ne') h1

/-- **`Λ ≠ ∅`** (paper.tex:L1796, Fubini): if the event holds at the random point `𝐳 = e^{iu}` with
positive probability, then `q(e^{iu}) > 0` for some `u`. -/
theorem exists_evProb_unit_pos [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ)
    {ν : Measure ℝ} [SFinite ν]
    (hconv : 0 < (P.prod ν)
      {x : Ω × ℝ | StaysAway (fun t => U t x.1) (unitPt x.2)}) :
    ∃ u : ℝ, 0 < evProb StaysAway P U (unitPt u) := by
  by_contra hcon
  push Not at hcon
  have hzero : ∀ u : ℝ, evProb StaysAway P U (unitPt u) = 0 := fun u =>
    le_antisymm (hcon u) bot_le
  obtain ⟨M, hMm, hM⟩ := measurableEvents_staysAway
  have hUm : ∀ t, Measurable (U t) := fun t => Measurable.mono (hU.adapted t) (ℱ.le t) le_rfl
  have hmeas : Measurable fun x : Ω × ℝ => ((fun t => U t x.1), unitPt x.2) :=
    Measurable.prodMk (measurable_pi_iff.2 fun t => (hUm t).comp measurable_fst)
      (continuous_unitPt.measurable.comp measurable_snd)
  have hS : MeasurableSet {x : Ω × ℝ | StaysAway (fun t => U t x.1) (unitPt x.2)} := by
    have e : {x : Ω × ℝ | StaysAway (fun t => U t x.1) (unitPt x.2)} =
        (fun x : Ω × ℝ => ((fun t => U t x.1), unitPt x.2)) ⁻¹' M := by
      ext x
      exact hM _ _ (hU.cont x.1)
    rw [e]
    exact hmeas hMm
  rw [Measure.prod_apply_symm hS] at hconv
  have : ∫⁻ u, P ((fun x : Ω => (x, u)) ⁻¹'
      {x : Ω × ℝ | StaysAway (fun t => U t x.1) (unitPt x.2)}) ∂ν = 0 :=
    (lintegral_congr fun u => hzero u).trans lintegral_zero
  exact absurd hconv (by rw [this]; exact lt_irrefl _)

end Ball

section Hit

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

theorem unitPt_add_two_pi_nat_mul (v : ℝ) (k : ℕ) : unitPt (v + 2 * π * k) = unitPt v := by
  unfold unitPt
  have : (((v + 2 * π * k : ℝ)) : ℂ) * Complex.I =
      (v : ℂ) * Complex.I + (k : ℂ) * (2 * π * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

theorem unitPt_sub_two_pi_nat_mul (v : ℝ) (k : ℕ) : unitPt (v - 2 * π * k) = unitPt v := by
  have := unitPt_add_two_pi_nat_mul (v - 2 * π * k) k
  rw [sub_add_cancel] at this
  exact this.symm

/-- **R27 + fixed-time Markov: `Λ ≠ ∅` implies `Λ = ℝ`** (paper.tex:L1796-1803, corrected). If
`q(e^{iu₀}) > 0` for some `u₀`, then `q(e^{iu}) > 0` for every `u`. The null sets are assumed to lie
in `ℱ 0`. -/
theorem evProb_unit_pos [IsProbabilityMeasure P]
    (hnull : ∀ N : Set Ω, MeasurableSet N → P N = 0 → MeasurableSet[ℱ 0] N)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (hΛ : ∃ u₀ : ℝ, 0 < evProb StaysAway P U (unitPt u₀)) (u : ℝ) :
    0 < evProb StaysAway P U (unitPt u) := by
  set q : ℂ → ℝ≥0∞ := evProb StaysAway P U with hq
  set Λ : Set ℝ := {u | 0 < q (unitPt u)} with hΛdef
  have hΛopen : IsOpen Λ := isOpen_evProb_unit_pos hU ha hc
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
  -- the Markov step at `σ_z(s)`
  obtain ⟨M, hMm, hM⟩ := measurableEvents_staysAway
  have hmark := measure_inter_event_eq_lintegral hU ha hc futureDependentEvents_staysAway hMm hM
    (unitPt_ne_zero u) s MeasurableSet.univ
  rw [Set.univ_inter, Measure.restrict_univ] at hmark
  have hfm : Measurable fun ω => q (fHat hU (unitPt u) s ω) := by
    have hfH : Measurable (fHat hU (unitPt u) s) :=
      (measurable_fHat hU s).mono ((sigmaFiltration hU (unitPt u)).le s) le_rfl
    exact (measurable_evProb hU hMm hM).comp hfH
  have hqz : q (unitPt u) = ∫⁻ ω, q (fHat hU (unitPt u) s ω) ∂P := hmark
  rw [hqz, pos_iff_ne_zero, Ne, lintegral_eq_zero_iff hfm]
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
      have e1 := evProb_eq_unit hU scaleInvariantEvents_staysAway hMm hM hne
      rw [e1, ← hexp]
      rfl
    have : q (fHat hU (unitPt u) s ω) = 0 := h1
    rw [hq1] at this
    exact absurd hω' (by rw [this]; exact lt_irrefl _)
  refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hae)
  exact fun h => h hω

/-- **`q(z) > 0` for every `z ≠ 0`** (scale invariance). -/
theorem evProb_pos [IsProbabilityMeasure P]
    (hnull : ∀ N : Set Ω, MeasurableSet N → P N = 0 → MeasurableSet[ℱ 0] N)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (hΛ : ∃ u₀ : ℝ, 0 < evProb StaysAway P U (unitPt u₀)) {z : ℂ} (hz : z ≠ 0) :
    0 < evProb StaysAway P U z := by
  obtain ⟨M, hMm, hM⟩ := measurableEvents_staysAway
  rw [evProb_eq_unit hU scaleInvariantEvents_staysAway hMm hM hz]
  have : z / (‖z‖ : ℂ) = unitPt (Complex.arg z) := by
    unfold unitPt
    have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
    rw [div_eq_iff hn, mul_comm]
    exact (Complex.norm_mul_exp_arg_mul_I z).symm
  rw [this]
  exact evProb_unit_pos hnull hU ha hb hc hΛ _

end Hit

section LowerBound

open Metric

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- **Koebe balls and compactness** (paper.tex:L1808-1810): if `q(z) > 0` for every `z ≠ 0`, then
`q ≥ q_* > 0` on `ℂ ∖ {0}`. -/
theorem exists_lowerBound [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ)
    (ha : 0 < a) (hc : c ^ 2 ≤ a * b)
    (hpos : ∀ z : ℂ, z ≠ 0 → 0 < evProb StaysAway P U z) :
    ∃ qs : ℝ, 0 < qs ∧ ∀ ξ : ℂ, ξ ≠ 0 → ENNReal.ofReal qs ≤ evProb StaysAway P U ξ := by
  obtain ⟨M, hMm, hM⟩ := measurableEvents_staysAway
  have hball : ∀ z : ℂ, z ≠ 0 → ∃ δ > 0, ∀ w : ℂ, ‖w - z‖ < δ →
      evProb StaysAway P U z / 2 < evProb StaysAway P U w := fun z hz =>
    exists_ball_lt_evProb_staysAway hU ha hc hz (hpos z hz)
  choose! δ hδ0 hδ using hball
  have hsph : ∀ z ∈ sphere (0 : ℂ) 1, z ≠ 0 := fun z hz h => by
    rw [mem_sphere_zero_iff_norm, h, norm_zero] at hz
    exact zero_ne_one hz
  obtain ⟨t, htS, hcov⟩ := (isCompact_sphere (0 : ℂ) 1).elim_nhds_subcover
    (fun z => ball z (δ z)) (fun z hz => ball_mem_nhds z (hδ0 z (hsph z hz)))
  set qm : ℝ≥0∞ := t.inf fun z => evProb StaysAway P U z / 2 with hqm
  have hqm0 : 0 < qm := by
    rw [hqm, Finset.lt_inf_iff ENNReal.zero_lt_top]
    exact fun z hz => ENNReal.half_pos (hpos z (hsph z (htS z hz))).ne'
  have hqmS : ∀ ξ ∈ sphere (0 : ℂ) 1, qm ≤ evProb StaysAway P U ξ := by
    intro ξ hξ
    obtain ⟨z, hz, hξz⟩ := mem_iUnion₂.1 (hcov hξ)
    have h1 : qm ≤ evProb StaysAway P U z / 2 :=
      Finset.inf_le (f := fun z => evProb StaysAway P U z / 2) hz
    have h2 := hδ z (hsph z (htS z hz)) ξ (by rwa [mem_ball, dist_eq_norm] at hξz)
    exact h1.trans h2.le
  have hone : (1 : ℂ) ∈ sphere (0 : ℂ) 1 := by simp
  have hqmtop : qm ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top _ _) (hqmS 1 hone)
  refine ⟨qm.toReal, ENNReal.toReal_pos hqm0.ne' hqmtop, fun ξ hξ => ?_⟩
  rw [ENNReal.ofReal_toReal hqmtop, evProb_eq_unit hU scaleInvariantEvents_staysAway hMm hM hξ]
  refine hqmS _ ?_
  rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, norm_norm,
    div_self (norm_ne_zero_iff.2 hξ)]

end LowerBound

end ComplexSLE.Internal

end
