/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.ErgodicBirkhoff
public import ComplexSLE.Internal.Phases.ErgodicConstRec
public import ComplexSLE.Internal.Phases.ErgodicConstStop
public import ComplexSLE.Internal.Phases.ErgodicConstFibre
public import ComplexSLE.Internal.Phases.ErgodicConstRecur

/-!
# Lemma 3.3, second half: the Birkhoff limit is a.s. constant (M7/A5b)

On `(Ω × ℝ, P ⊗ ν)`, `ν = p(u) 1_{[0,2π]}(u) du`, `Y_s = log |f̂_s(e^{iu})|` (`logFHat`),
`(I) = integralI a b c p`. Under `hMO : MarkovOneDim` (the EXTERNAL `markov_oneDim` (R29)):

* `birkhoff_logFHat_const`: `P ⊗ ν`-a.s. `Y_s / s → (I)` as `s → ∞` in `ℝ≥0`.
  Proof (paper.tex:L1361-1372, `step:sde-limit-deterministic`, `step:sde-regeneration`): the
  Birkhoff limit `L` of `exists_birkhoff_logFHat_ae`; for `ν`-a.e. `u`, by the recurrence of
  `e^{2iθ̂}` to `1` on the product (`ae_recurrent_unit`) the regeneration times
  `S_k = hitTime` (`ErgodicConstStop.lean`) are a.s. finite `ℱ`-stopping times, at which the strong
  Markov property and the reflection symmetry (`obsKernel` is a function of `e^{2iβ}` only) show
  that `L` is independent of `ℱ_{S_k} ∋ Y_n` (`n ≤ k`) with a law not depending on `u`
  (`fibre_law_and_const`), hence a.s. constant `κ`, the same for all `u`; and `κ = ∫ L = (I)`.
* `recurrent_logFHat`: if `(I) = 0`, a.s. for every `ε > 0` there are arbitrarily large `s` with
  `|Y_s| < ε` (EXTERNAL `recurrence_stationary`).
* `not_tendsto_atBot_logFHat` (Prop 3.1(a) shape): if `(I) ≥ 0`, a.s. `Y_s ↛ -∞`.
* `tendsto_logFHat_div_of_integralI_neg`, `tendsto_atBot_logFHat` (Prop 3.1(b) shape): if
  `(I) < 0`, a.s. `Y_s / s → (I)` and `Y_s → -∞`.

Consumes the EXTERNALs `strongMarkov_sleDriver`, `birkhoff_stationary`, `recurrence_stationary`
and, through the polar and stationarity layers, `ito_formula`, `hormander_oneDim`,
`timeChange_isContLocalMartingale`; the EXTERNAL `markov_oneDim` (R29) is the hypothesis
`hMO : MarkovOneDim`.
-/

@[expose] public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal

open Polar

section Main

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-- **Lemma 3.3: the Birkhoff limit is a.s. constant, equal to `(I)`.** Under
`hMO : MarkovOneDim`: `P ⊗ ν`-a.s., `log |f̂_s(e^{iu})| / s → (I)` as `s → ∞` along `ℝ≥0`. -/
theorem birkhoff_logFHat_const [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) :
    ∀ᵐ q ∂(P.prod (admissibleMeasure p)),
      Tendsto (fun s : ℝ≥0 => logFHat hU s q / s) atTop (𝓝 (integralI a b c p)) := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  -- complete the filtration so that the null sets lie in time `0`
  have hnull : ∀ N : Set Ω, MeasurableSet N → P N = 0 →
      MeasurableSet[nullFiltration ℱ P 0] N := fun N hN hN0 =>
    (le_sup_right : _ ≤ ℱ 0 ⊔ MeasurableSpace.generateFrom
      {N : Set Ω | MeasurableSet[m] N ∧ P N = 0}) _
      (MeasurableSpace.measurableSet_generateFrom ⟨hN, hN0⟩)
  have hU' : IsSLEDriverAdapted a b c U P (nullFiltration ℱ P) :=
    hU.of_le_sup_null (fun t => le_sup_left) (fun t => le_rfl)
  -- the Birkhoff limit, with a measurable representative
  obtain ⟨L, hLint, hLmean, -, hLreal⟩ := exists_birkhoff_logFHat_ae hMO hU ha hb hc hp
  set L' : Ω × ℝ → ℝ := hLint.1.mk L with hL'
  have hL'm : Measurable L' := hLint.1.stronglyMeasurable_mk.measurable
  have hLL' : L =ᵐ[P.prod (admissibleMeasure p)] L' := hLint.1.ae_eq_mk
  have hLreal' : ∀ᵐ q ∂(P.prod (admissibleMeasure p)),
      Tendsto (fun s : ℝ≥0 => logFHat hU s q / s) atTop (𝓝 (L' q)) := by
    filter_upwards [hLreal, hLL'] with q h1 h2
    rwa [← h2]
  -- the constant on each good fibre
  set κ : ℝ := ∫ x, x ∂((driverLaw hU').map (fun w : CPath => limFunctional (obsC (w, 0))))
    with hκ
  have hfib : ∀ᵐ u ∂(admissibleMeasure p), ∀ᵐ ω ∂P, L' (ω, u) = κ := by
    filter_upwards [ae_ae_of_ae_prod_snd hLreal', ae_recurrent_unit hMO hU ha hb hc hp] with u
      h1 h2
    have hz := unitPt_ne_zero u
    have hrec' : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, ∃ t : ℝ≥0, s ≤ t ∧
        Complex.exp (2 * Complex.I * (thetaHat hU' (unitPt u) t ω : ℂ)) = 1 := by
      filter_upwards [h2] with ω hω s
      obtain ⟨t, hst, ht⟩ := hω s
      refine ⟨t, hst, ?_⟩
      rwa [thetaHat_congr_filtration hU hU']
    have D : ∀ k : ℕ, RegenDatum hU' (unitPt u) k := fun k =>
      (nonempty_regenDatum hU' hnull ha hc hz hrec' k).some
    have hlim : ∀ᵐ ω ∂P, Tendsto (fun s : ℝ≥0 =>
        Real.log ‖fHat hU' (unitPt u) s ω‖ / (s : ℝ)) atTop (𝓝 (L' (ω, u))) := h1
    have hLm : Measurable fun ω => L' (ω, u) := hL'm.comp measurable_prodMk_right
    obtain ⟨hlaw, c₀, hc₀⟩ := fibre_law_and_const hU' ha hc D hLm hlim
    -- `κ = ∫ L'(·, u) = c₀`
    have h3 : ∫ ω, L' (ω, u) ∂P = κ := by
      rw [hκ, ← hlaw]
      exact (integral_map (f := fun x : ℝ => x) hLm.aemeasurable
        measurable_id.aestronglyMeasurable).symm
    have h4 : ∫ ω, L' (ω, u) ∂P = c₀ := by
      rw [integral_congr_ae hc₀]; simp
    filter_upwards [hc₀] with ω hω
    rw [hω, ← h4, h3]
  -- the product statement
  have hS : MeasurableSet {q : Ω × ℝ | L' q = κ} := measurableSet_eq_fun hL'm measurable_const
  have hprod : ∀ᵐ q ∂(P.prod (admissibleMeasure p)), L' q = κ := ae_prod_of_ae_ae_snd hS hfib
  -- `κ = (I)`
  have hκI : κ = integralI a b c p := by
    rw [← hLmean, integral_congr_ae hLL', integral_congr_ae hprod]
    simp
  filter_upwards [hLreal', hprod] with q h1 h2
  rwa [h2, hκI] at h1

/-- **Recurrence of `log |f̂|` when `(I) = 0`** (Lemma 3.3, last clause): under `hMO` and
`(I) = 0`, `P ⊗ ν`-a.s. for every `ε > 0` there are arbitrarily large `s` with
`|log |f̂_s(e^{iu})|| < ε`. -/
theorem recurrent_logFHat [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (hI : integralI a b c p = 0) :
    ∀ᵐ q ∂(P.prod (admissibleMeasure p)), ∀ ε : ℝ, 0 < ε → ∀ S : ℝ≥0,
      ∃ s : ℝ≥0, S ≤ s ∧ |logFHat hU s q| < ε :=
  recurrent_logFHat_of_integralI_eq_zero hMO hU ha hb hc hp hI
    (birkhoff_logFHat_const hMO hU ha hb hc hp)

/-- **Prop 3.1(a) shape.** If `(I) ≥ 0`, then `P ⊗ ν`-a.s. `log |f̂_s(e^{iu})| ↛ -∞`. -/
theorem not_tendsto_atBot_logFHat [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (hI : 0 ≤ integralI a b c p) :
    ∀ᵐ q ∂(P.prod (admissibleMeasure p)),
      ¬ Tendsto (fun s : ℝ≥0 => logFHat hU s q) atTop atBot :=
  not_tendsto_atBot_logFHat_of_integralI_nonneg hMO hU ha hb hc hp hI
    (birkhoff_logFHat_const hMO hU ha hb hc hp)

/-- **Prop 3.1(b) shape.** If `(I) < 0`, then `P ⊗ ν`-a.s. `log |f̂_s(e^{iu})| / s → (I)`. -/
theorem tendsto_logFHat_div_of_integralI_neg [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (_hI : integralI a b c p < 0) :
    ∀ᵐ q ∂(P.prod (admissibleMeasure p)),
      Tendsto (fun s : ℝ≥0 => logFHat hU s q / s) atTop (𝓝 (integralI a b c p)) :=
  birkhoff_logFHat_const hMO hU ha hb hc hp

/-- **Prop 3.1(b) shape.** If `(I) < 0`, then `P ⊗ ν`-a.s. `log |f̂_s(e^{iu})| → -∞`. -/
theorem tendsto_atBot_logFHat [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (hI : integralI a b c p < 0) :
    ∀ᵐ q ∂(P.prod (admissibleMeasure p)),
      Tendsto (fun s : ℝ≥0 => logFHat hU s q) atTop atBot :=
  tendsto_atBot_logFHat_of_integralI_neg hU hI (birkhoff_logFHat_const hMO hU ha hb hc hp)

end Main

end ComplexSLE.Internal

end
