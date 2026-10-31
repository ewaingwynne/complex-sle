/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsHittingPhase
public import ComplexSLE.Frozen.Proposition_3_1_B
public import ComplexSLE.Frozen.Lemma_2_13_Exists
public import ComplexSLE.External.DambisDubinsSchwarz
public import ComplexSLE.Infrastructure.Stochastic.BrownianOscillation
public import ComplexSLE.Internal.Driver.BridgeAdapted
public import ComplexSLE.Internal.Phases.C0Integrals
public import ComplexSLE.Internal.Phases.KoebeHitSigma
public import ComplexSLE.Internal.Polar.PolarDerivSigma

/-!
# The boundary case `c = 0`, `a - b = 8` (Lemma 3.12, `lem-c0-bdy`) (M7/F2b)

Source: paper.tex:L1910-1930. For `c = 0` and `a - b = 8` the `SLE_Σ` driver is in the hitting
phase (`lemma_3_12`).

Proof (fixed `z ≠ 0`):

* `T_z < ∞` a.s. is the sealed anchor `proposition_3_1_b` with `(I) < 0`, which holds because
  `a - b = 8 > 4` (`integralI_c0_neg_iff`, for the admissible density `exists_admissibleDensity`).
* Closure clause, for the adapted version `U'` of the driver (`IsSLEDriver.exists_adapted`): for
  `c = 0`, `a - b = 8` the drift density `ν(θ̂) + 2 cos 2θ̂` of `log(|f̂'|/|f̂|)` vanishes
  identically (`ratioDriftHat_eq_zero`), so `sigmaLogRatio_s = -log|f_0(z)| - M_s` with
  `M = sigmaLogMart` (`sigmaLogRatio_eq_neg`, paper.tex:L1917-1920), where `log|f_0(z)| = log|z|`
  (`log_norm_fPath_zero`). `M` is a continuous local martingale for the σ-time filtration with
  `M² - A` a continuous local martingale, `A = M² - sigmaLogMartSq`; a.s. `A_s = ∫₀ˢ Γ̂` with
  `Γ̂ = a cos² θ̂ + b sin² θ̂ ≥ min a b > 0` (`logBracketHat_ge`), so `A` is continuous,
  nondecreasing, `A_0 = 0` and `A_s → ∞` (`ae_sigmaLogBracket_props`). The EXTERNAL
  `dambis_dubins_schwarz` writes `M_s = β_{A_s}` for a Brownian motion `β`, hence
  `liminf M = -∞` (`ae_forall_exists_le_of_timeChange`), i.e. `limsup sigmaLogRatio = +∞`
  (paper.tex:L1921-1925). The Koebe hitting bound `mem_closure_iUnion_leftHull_of_ratio_unbounded`
  (paper.tex:L1460-1466, `eqn-hit-koebe`) then gives `z ∈ closure (⋃_{t < T_z} L_t)`
  (`ae_mem_closure_c0_bdy`).
* The adapted version agrees with `U` a.s., which transfers the closure clause back to `U`.

`lemma_3_12` is `PROVED_REL{dambis_dubins_schwarz, koebe_quarter, …}`: it consumes the EXTERNAL
inputs through the sealed anchor `proposition_3_1_b`, `KoebeHitSigma` and
`dambis_dubins_schwarz`.
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Internal

open Polar

section Fibre

variable {Ω : Type} [m : MeasurableSpace Ω] {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- **The drift vanishes** (`c = 0`, `a - b = 8`, paper.tex:L1916-1917): `ν(·) + 2 cos 2· ≡ 0`,
so `ratioDriftHat ≡ 0`. -/
theorem ratioDriftHat_eq_zero (hU : IsSLEDriverAdapted a b 0 U P ℱ) (z : ℂ) (hab : a - b = 8)
    (ω : Ω) (v : ℝ) : ratioDriftHat hU z ω v = 0 := by
  simp only [ratioDriftHat, nuHat, cosTwoHat, nu]
  have h : (2 - a / 2 + b / 2) = -2 := by linarith
  rw [h]
  ring

/-- `log |f_0(z)| = log |z|` for a driver with `U 0 = 0`. -/
theorem log_norm_fPath_zero (hU : IsSLEDriverAdapted a b 0 U P ℱ) (z : ℂ) {ω : Ω}
    (h0 : U 0 ω = 0) :
    Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z 0‖ = Real.log ‖z‖ := by
  rw [fPath_zero, h0, sub_zero]

/-- **(eqn-sde-ratio) for `c = 0`, `a - b = 8`** (paper.tex:L1917-1920), on `sigmaDom`:
`log(|f̂'_s|/|f̂_s|) = -log|f_0(z)| - M_s`, `M = sigmaLogMart`. -/
theorem sigmaLogRatio_eq_neg (hU : IsSLEDriverAdapted a b 0 U P ℱ) {z : ℂ} (hab : a - b = 8)
    {s : ℝ≥0} {ω : Ω} (hs : (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z) :
    sigmaLogRatio hU z s ω =
      -Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z 0‖ - sigmaLogMart hU z s ω := by
  rw [sigmaLogRatio_eq hU hs]
  simp [ratioDriftHat_eq_zero hU z hab]

/-- The bracket density is bounded below: `Γ̂ = a cos² θ̂ + b sin² θ̂ ≥ min a b` (`c = 0`). -/
theorem logBracketHat_ge (hU : IsSLEDriverAdapted a b 0 U P ℱ) (z : ℂ) (ω : Ω) (v : ℝ) :
    min a b ≤ logBracketHat hU z ω v := by
  simp only [logBracketHat, logBracketFn]
  set θ := argPath (fun r => U r ω) (hU.cont ω) z (sigmaTime (fun r => U r ω) (hU.cont ω) z v)
  have h1 := Real.sin_sq_add_cos_sq θ
  have h2 : min a b ≤ a := min_le_left _ _
  have h3 : min a b ≤ b := min_le_right _ _
  have hc := sq_nonneg (Real.cos θ)
  have hs := sq_nonneg (Real.sin θ)
  have h4 : min a b * (Real.sin θ ^ 2 + Real.cos θ ^ 2) = min a b := by rw [h1, mul_one]
  nlinarith [mul_nonneg (sub_nonneg.2 h2) hc, mul_nonneg (sub_nonneg.2 h3) hs]

/-- The bracket process `M² - (M² - ∫₀ˢ Γ̂)` of `sigmaLogMart`, defined as
`M² - sigmaLogMartSq` so that it is progressively measurable. -/
@[expose] noncomputable def sigmaLogBracket (hU : IsSLEDriverAdapted a b 0 U P ℱ) (z : ℂ)
    (s : ℝ≥0) (ω : Ω) : ℝ :=
  sigmaLogMart hU z s ω ^ 2 - sigmaLogMartSq hU z s ω

/-- On `sigmaDom`, `sigmaLogBracket_s = ∫₀ˢ Γ̂`. -/
theorem sigmaLogBracket_eq (hU : IsSLEDriverAdapted a b 0 U P ℱ) {z : ℂ} {s : ℝ≥0} {ω : Ω}
    (hs : (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z) :
    sigmaLogBracket hU z s ω = ∫ v in (0 : ℝ)..(s : ℝ), logBracketHat hU z ω v := by
  rw [sigmaLogBracket, sigmaLogMartSq_eq hU z hs]
  ring

/-- `sigmaLogBracket` is a continuous nondecreasing process, started at `0`, with
`sigmaLogBracket_s ≥ min a b · s` (a.s.). -/
theorem ae_sigmaLogBracket_props [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b 0 U P ℱ) {z : ℂ} (ha : 0 < a) (hb : 0 < b) (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, Continuous (fun t => sigmaLogBracket hU z t ω) ∧
      Monotone (fun t => sigmaLogBracket hU z t ω) ∧ sigmaLogBracket hU z 0 ω = 0 ∧
      ∀ s : ℝ≥0, min a b * (s : ℝ) ≤ sigmaLogBracket hU z s ω := by
  have hc : (0 : ℝ) ^ 2 ≤ a * b := by rw [zero_pow two_ne_zero]; exact (mul_pos ha hb).le
  have hNm := isContLocalMartingale_sigmaLogMart hU ha hc hz
  have hNsqm := isContLocalMartingale_sigmaLogMartSq hU ha hc hz
  filter_upwards [hNm.2.1, hNsqm.2.1, ae_sigmaDom_eq_Ici hU z ha hc hz] with ω h1 h2 hω
  have hmem : ∀ s : ℝ≥0, (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z := fun s => by
    rw [hω]; exact s.coe_nonneg
  have hint : ∀ s : ℝ≥0, IntervalIntegrable (logBracketHat hU z ω) volume 0 (s : ℝ) := fun s =>
    intervalIntegrable_comp_argPath_sigmaTime (hU.cont ω) (continuous_logBracketFn a b 0)
      (hmem s)
  have hpos : min a b > 0 := lt_min ha hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (h1.pow 2).sub h2
  · intro s t hst
    change sigmaLogBracket hU z s ω ≤ sigmaLogBracket hU z t ω
    rw [sigmaLogBracket_eq hU (hmem s), sigmaLogBracket_eq hU (hmem t)]
    refine intervalIntegral.integral_mono_interval le_rfl s.coe_nonneg
      (NNReal.coe_le_coe.2 hst) ?_ (hint t)
    exact Filter.Eventually.of_forall fun v => hpos.le.trans (logBracketHat_ge hU z ω v)
  · rw [sigmaLogBracket_eq hU (hmem 0)]
    simp
  · intro s
    rw [sigmaLogBracket_eq hU (hmem s)]
    have : ∫ v in (0 : ℝ)..(s : ℝ), min a b = min a b * (s : ℝ) := by
      simp [mul_comm]
    rw [← this]
    refine intervalIntegral.integral_mono_on s.coe_nonneg intervalIntegrable_const (hint s) ?_
    intro v _
    exact logBracketHat_ge hU z ω v

/-- **`log(|f̂'|/|f̂|)` is unbounded above** (`c = 0`, `a - b = 8`, paper.tex:L1921-1925): for an
adapted driver, a.s. `limsup_{s → ∞} sigmaLogRatio_s = +∞`, in the form
`∀ K, ∃ s, K ≤ sigmaLogRatio_s`. Uses the EXTERNAL `dambis_dubins_schwarz`. -/
theorem ae_sigmaLogRatio_unbounded [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b 0 U P ℱ) {z : ℂ} (ha : 0 < a) (hb : 0 < b) (hab : a - b = 8)
    (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, ∀ K : ℝ, ∃ s : ℝ≥0, K ≤ sigmaLogRatio hU z s ω := by
  have hc : (0 : ℝ) ^ 2 ≤ a * b := by rw [zero_pow two_ne_zero]; exact (mul_pos ha hb).le
  have hNm := isContLocalMartingale_sigmaLogMart hU ha hc hz
  have hNsqm := isContLocalMartingale_sigmaLogMartSq hU ha hc hz
  have hdom := ae_sigmaDom_eq_Ici hU z ha hc hz
  have hAprops := ae_sigmaLogBracket_props hU ha hb hz
  -- `M_0 = 0`
  have hN0 : ∀ᵐ ω ∂P, sigmaLogMart hU z 0 ω = 0 := by
    filter_upwards [hdom] with ω hω
    have h0 : (0 : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z := by
      rw [hω]; exact Set.mem_Ici.2 le_rfl
    have hT := zero_mem_lifeSet_iff.2 (pos_absorbingTime_of_mem_sigmaDom (hU.cont ω) h0)
    rw [sigmaLogMart, ite_eq_left (by simpa using h0)]
    simp [sigmaTime_zero (hU.cont ω) hT]
  -- the bracket process is progressively measurable and `M² - A` is a local martingale
  have hAprog : IsStronglyProgressive (sigmaFiltration hU z) (sigmaLogBracket hU z) :=
    fun i => ((hNm.1 i).pow 2).sub (hNsqm.1 i)
  have hAmart : IsContLocalMartingale (sigmaFiltration hU z)
      (fun t ω => sigmaLogMart hU z t ω ^ 2 - sigmaLogBracket hU z t ω) P := by
    have : (fun t ω => sigmaLogMart hU z t ω ^ 2 - sigmaLogBracket hU z t ω) =
        sigmaLogMartSq hU z := by
      funext t ω
      simp [sigmaLogBracket]
    rw [this]
    exact hNsqm
  have hAc : ∀ᵐ ω ∂P, Continuous (fun t => sigmaLogBracket hU z t ω) ∧
      Monotone (fun t => sigmaLogBracket hU z t ω) ∧ sigmaLogBracket hU z 0 ω = 0 := by
    filter_upwards [hAprops] with ω h using ⟨h.1, h.2.1, h.2.2.1⟩
  have hAtop : ∀ᵐ ω ∂P, Tendsto (fun t => sigmaLogBracket hU z t ω) atTop atTop := by
    filter_upwards [hAprops] with ω h
    have hpos : 0 < min a b := lt_min ha hb
    refine tendsto_atTop_mono (fun s => (h.2.2.2 s)) ?_
    exact (Filter.Tendsto.const_mul_atTop hpos (NNReal.tendsto_coe_atTop.2 tendsto_id))
  obtain ⟨β, hβ, hMβ⟩ := External.dambis_dubins_schwarz (sigmaFiltration hU z)
    (sigmaLogMart hU z) (sigmaLogBracket hU z) hNm hN0 hAprog hAc hAmart hAtop
  have hosc := Infrastructure.ae_forall_exists_le_of_timeChange hβ hMβ
    (by filter_upwards [hAc] with ω h using h.1) hAtop
  filter_upwards [hosc, hdom] with ω h1 hω K
  obtain ⟨t, -, ht⟩ := h1 (K + Real.log ‖fPath (fun r => U r ω) (hU.cont ω) z 0‖) 0
  refine ⟨t, ?_⟩
  have hts : (t : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z := by rw [hω]; exact t.coe_nonneg
  rw [sigmaLogRatio_eq_neg hU hab hts]
  linarith

/-- **Closure clause of the hitting phase for `c = 0`, `a - b = 8`** (paper.tex:L1921-1927): for an
adapted driver and `z ≠ 0`, a.s. `z ∈ closure (⋃_{t < T_z} L_t)`. -/
theorem ae_mem_closure_c0_bdy [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b 0 U P ℱ)
    {z : ℂ} (ha : 0 < a) (hb : 0 < b) (hab : a - b = 8) (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, z ∈ closure (⋃ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < absorbingTime (fun r => U r ω) z),
      leftHull (fun r => U r ω) t) := by
  have hc : (0 : ℝ) ^ 2 ≤ a * b := by rw [zero_pow two_ne_zero]; exact (mul_pos ha hb).le
  filter_upwards [ae_sigmaLogRatio_unbounded hU ha hb hab hz, ae_sigmaDom_eq_Ici hU z ha hc hz]
    with ω h hω
  refine mem_closure_iUnion_leftHull_of_ratio_unbounded (hU.cont ω) fun K => ?_
  obtain ⟨s, hs⟩ := h K
  exact ⟨(s : ℝ), by rw [hω]; exact s.coe_nonneg, hs⟩

end Fibre

section Main

/-- **Lemma 3.12** (`lem-c0-bdy`, paper.tex:L1910-1930): for `c = 0` and `a - b = 8`, the
`SLE_Σ` driver is in the hitting phase. `PROVED_REL` to the externals consumed by the sealed
anchor `proposition_3_1_b`, by `KoebeHitSigma` and by `dambis_dubins_schwarz`. -/
theorem lemma_3_12 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a - b = 8) :
    IsHittingPhase a b 0 := by
  intro Ω _ P _ U hU z hz
  have hc : (0 : ℝ) ^ 2 ≤ a * b := by rw [zero_pow two_ne_zero]; exact (mul_pos ha hb).le
  obtain ⟨p, hp⟩ := exists_admissibleDensity a b 0 ha hb hc
  have hI : integralI a b 0 p < 0 := (integralI_c0_neg_iff ha hb hp).2 (by linarith)
  have hfin := proposition_3_1_b a b 0 ha hb hc p hp hI Ω P U hU z hz
  obtain ⟨ℱ, U', hUU', -, -, hU'⟩ := hU.exists_adapted
  have hcl := ae_mem_closure_c0_bdy hU' ha hb hab hz
  filter_upwards [hfin, hUU', hcl] with ω h1 h2 h3
  have e : (fun t => U' t ω) = fun t => U t ω := funext h2
  rw [e] at h3
  exact ⟨h1, h3⟩

end Main

end ComplexSLE.Internal

end
