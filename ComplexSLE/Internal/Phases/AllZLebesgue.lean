/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.AllZPositivity
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The law of `arg 𝐳` and its null sets (Lemma 3.2, first step)

Section 3 of the paper samples `𝐳` on the unit circle with `arg 𝐳` having density
`p(u) 1_{[0,2π]}(u)` (paper.tex:L939, L1255). For an admissible density `p`:

* `admissibleLaw p`: the measure `p(u) 1_{[0,2π]}(u) du` on `ℝ`;
  `isProbabilityMeasure_admissibleLaw` (it has total mass `∫₀^{2π} p = 1`);
* `restrict_absolutelyContinuous_admissibleLaw`: for `a, b > 0`, `c² ≤ ab`, Lebesgue measure on
  `[0, 2π]` is absolutely continuous with respect to `admissibleLaw p` (Part 1 of
  `lem-all-z`: `p > 0` a.e., `IsAdmissibleDensity.ae_pos`);
  so a property that holds `admissibleLaw p`-a.e. holds Lebesgue-a.e. on `[0, 2π]`;
* `ae_volume_of_ae_restrict_Icc`: a `2π`-periodic property that holds a.e. on `[0, 2π]` holds
  Lebesgue-a.e. on `ℝ`;
* `ae_ae_of_ae_prod_snd`: Fubini in the order needed here (no measurability): an a.s. statement on
  a product space `Ω × ℝ` gives, for `ν`-a.e. `u`, an a.s. statement on `Ω`.
-/

public section

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set Real intervalIntegral

namespace ComplexSLE.Internal

/-- The law `p(u) 1_{[0,2π]}(u) du` of `arg 𝐳` (paper.tex:L939, L1255). -/
@[expose] noncomputable def admissibleLaw (p : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Icc 0 (2 * π))).withDensity fun u => ENNReal.ofReal (p u)

variable {a b c : ℝ} {p : ℝ → ℝ}

theorem isProbabilityMeasure_admissibleLaw (hp : IsAdmissibleDensity a b c p) :
    IsProbabilityMeasure (admissibleLaw p) := by
  refine ⟨?_⟩
  rw [admissibleLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hp.1.integrableOn_Icc
      (Eventually.of_forall hp.2.1), integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity), hp.2.2.2.1, ENNReal.ofReal_one]

/-- **Lebesgue measure on `[0, 2π]` is absolutely continuous with respect to the law of `arg 𝐳`**
(`p > 0` almost everywhere, Part 1 of `lem-all-z`). -/
theorem restrict_absolutelyContinuous_admissibleLaw (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (hp : IsAdmissibleDensity a b c p) :
    volume.restrict (Icc 0 (2 * π)) ≪ admissibleLaw p := by
  refine withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp
    hp.1.measurable).aemeasurable ?_
  have h := IsAdmissibleDensity.ae_pos ha hb hc hp
  filter_upwards [ae_restrict_of_ae h] with u hu
  exact (ENNReal.ofReal_pos.2 hu).ne'

theorem ae_volume_restrict_of_ae_admissibleLaw (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (hp : IsAdmissibleDensity a b c p) {q : ℝ → Prop} (h : ∀ᵐ u ∂(admissibleLaw p), q u) :
    ∀ᵐ u ∂(volume.restrict (Icc 0 (2 * π))), q u :=
  restrict_absolutelyContinuous_admissibleLaw ha hb hc hp h

/-- A `2π`-periodic property that holds Lebesgue-a.e. on `[0, 2π]` holds Lebesgue-a.e. on `ℝ`. -/
theorem ae_volume_of_ae_restrict_Icc {q : ℝ → Prop} (hq : Function.Periodic q (2 * π))
    (h : ∀ᵐ u ∂(volume.restrict (Icc 0 (2 * π))), q u) : ∀ᵐ u ∂(volume : Measure ℝ), q u := by
  rw [ae_restrict_iff' measurableSet_Icc] at h
  have hn : ∀ n : ℤ, ∀ᵐ u ∂(volume : Measure ℝ), u - n * (2 * π) ∈ Icc 0 (2 * π) → q u := by
    intro n
    have hmp := measurePreserving_sub_right (volume : Measure ℝ) ((n : ℝ) * (2 * π))
    filter_upwards [hmp.quasiMeasurePreserving.ae h] with u hu hu'
    have := hu hu'
    rwa [hq.sub_int_mul_eq n] at this
  filter_upwards [ae_all_iff.2 hn] with u hu
  have hπ : 0 < 2 * π := by positivity
  have h1 : ((⌊u / (2 * π)⌋ : ℤ) : ℝ) ≤ u / (2 * π) := Int.floor_le _
  have h2 : u / (2 * π) < ⌊u / (2 * π)⌋ + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hπ] at h1
  rw [div_lt_iff₀ hπ] at h2
  exact hu ⌊u / (2 * π)⌋ ⟨by linarith, by linarith⟩

/-- **Fubini, in the order used for `lem-all-z`.** If a statement holds almost everywhere on
`Ω × ℝ` (`P.prod ν`), then for `ν`-a.e. `u` it holds almost surely in `ω`. No measurability of the
statement is needed. -/
theorem ae_ae_of_ae_prod_snd {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    {ν : Measure ℝ} [SFinite ν] {q : Ω × ℝ → Prop} (h : ∀ᵐ x ∂(P.prod ν), q x) :
    ∀ᵐ u ∂ν, ∀ᵐ ω ∂P, q (ω, u) := by
  have h' : ∀ᵐ y ∂(ν.prod P), q y.swap :=
    (Measure.measurePreserving_swap (μ := ν) (ν := P)).quasiMeasurePreserving.ae h
  exact Measure.ae_ae_of_ae_prod h'

end ComplexSLE.Internal

end
