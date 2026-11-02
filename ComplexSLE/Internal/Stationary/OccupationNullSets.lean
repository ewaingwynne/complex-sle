/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Algebra.Order.Interval.Set.Group

/-!
# From periodic test functions to Lebesgue-null sets (M10-R5a)

Let `ρ` be a finite measure on `ℝ`, `w ≥ 0` a bounded continuous weight and `K ≥ 0` with

  `∫ ψ w dρ ≤ K ∫₀^π ψ`  for every continuous `π`-periodic `ψ ≥ 0`.        (★)

Then `∫ N.indicator w dρ = 0` for every Lebesgue-null measurable `N`, hence
`ρ (N ∩ {w ≠ 0}) = 0` (`measure_inter_ne_zero_eq_zero`). The proof of the implication:

1. for an open `π`-periodic `O` with nonempty complement, `ψₙ = min 1 (n · dist(·, Oᶜ)) ↑ 1_O` are
   continuous and `π`-periodic, so (★) and dominated convergence give
   `∫ O.indicator w dρ ≤ K · Leb(O ∩ (0, π])` (`integral_indicator_le_of_isOpen`);
2. a null `N` is contained in an open `O'` of arbitrarily small measure, and the periodization
   `⋃_{n ∈ ℤ} (O' - nπ)` is open, `π`-periodic, contains `N`, and has
   `Leb(· ∩ (0, π]) ≤ Leb(O')` (`volume_periodize_inter_Ioc_le`).
-/

public section

open Real Set MeasureTheory Function Filter
open scoped Topology ENNReal

namespace ComplexSLE.Internal

/-! ### The periodization of a set -/

/-- The union of all translates of `O` by multiples of `π`. -/
@[expose] noncomputable def periodize (O : Set ℝ) : Set ℝ := ⋃ n : ℤ, (fun x => x + n * π) ⁻¹' O

theorem subset_periodize (O : Set ℝ) : O ⊆ periodize O := fun x hx =>
  mem_iUnion.2 ⟨0, by simpa using hx⟩

theorem isOpen_periodize {O : Set ℝ} (hO : IsOpen O) : IsOpen (periodize O) :=
  isOpen_iUnion fun n => hO.preimage (by fun_prop)

theorem add_pi_mem_periodize_iff (O : Set ℝ) (x : ℝ) : x + π ∈ periodize O ↔ x ∈ periodize O := by
  simp only [periodize, mem_iUnion, mem_preimage]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    have e : x + ((n + 1 : ℤ) : ℝ) * π = x + π + n * π := by push_cast; ring
    rwa [e]
  · rintro ⟨n, hn⟩
    refine ⟨n - 1, ?_⟩
    have e : x + π + ((n - 1 : ℤ) : ℝ) * π = x + n * π := by push_cast; ring
    rwa [e]

theorem volume_periodize_inter_Ioc_le {O : Set ℝ} (hO : MeasurableSet O) :
    volume (periodize O ∩ Ioc 0 π) ≤ volume O := by
  have h1 : periodize O ∩ Ioc 0 π = ⋃ n : ℤ, ((fun x => x + n * π) ⁻¹' O) ∩ Ioc 0 π := by
    unfold periodize; rw [iUnion_inter]
  have h2 : ∀ n : ℤ, volume (((fun x => x + n * π) ⁻¹' O) ∩ Ioc 0 π) =
      volume (O ∩ Ioc (n * π) ((n + 1) * π)) := by
    intro n
    have : ((fun x => x + n * π) ⁻¹' O) ∩ Ioc 0 π =
        (fun x => x + n * π) ⁻¹' (O ∩ Ioc (n * π) ((n + 1) * π)) := by
      rw [preimage_inter, preimage_add_const_Ioc]
      congr 2 <;> ring
    rw [this, measure_preimage_add_right]
  have hdisj : Pairwise (Disjoint on fun n : ℤ => O ∩ Ioc (n * π) ((n + 1) * π)) := by
    have := Set.pairwise_disjoint_Ioc_add_zsmul (0 : ℝ) π
    simp only [zero_add, zsmul_eq_mul, Int.cast_add, Int.cast_one] at this
    intro m n hmn
    exact (this hmn).mono inter_subset_right inter_subset_right
  calc volume (periodize O ∩ Ioc 0 π)
      ≤ ∑' n : ℤ, volume (((fun x => x + n * π) ⁻¹' O) ∩ Ioc 0 π) := by
        rw [h1]; exact measure_iUnion_le _
    _ = ∑' n : ℤ, volume (O ∩ Ioc (n * π) ((n + 1) * π)) := by simp only [h2]
    _ = volume (⋃ n : ℤ, O ∩ Ioc (n * π) ((n + 1) * π)) :=
        (measure_iUnion hdisj fun n => hO.inter measurableSet_Ioc).symm
    _ ≤ volume O := measure_mono (iUnion_subset fun n => inter_subset_left)

/-- An open `O'` of small measure has a `π`-periodic open hull of small measure per period. -/
theorem exists_isOpen_periodic_of_volume_lt {O : Set ℝ} (hO : IsOpen O)
    (hlt : volume O < ENNReal.ofReal π) :
    IsOpen (periodize O) ∧ (periodize O)ᶜ.Nonempty ∧
      volume (periodize O ∩ Ioc 0 π) ≤ volume O := by
  have hle := volume_periodize_inter_Ioc_le hO.measurableSet
  refine ⟨isOpen_periodize hO, ?_, hle⟩
  by_contra hne
  rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hne
  rw [hne, univ_inter, Real.volume_Ioc, sub_zero] at hle
  exact absurd (hle.trans_lt hlt) (lt_irrefl _)

/-! ### Open periodic sets -/

section Open

variable {ρ : Measure ℝ} {w : ℝ → ℝ} {K : ℝ}

/-- A translation-invariant set has translation-invariant distance function. -/
theorem infDist_add_le {S : Set ℝ} (d : ℝ) (hS : ∀ y ∈ S, y + d ∈ S) (hne : S.Nonempty) (x : ℝ) :
    Metric.infDist (x + d) S ≤ Metric.infDist x S := by
  refine (Metric.le_infDist hne).2 fun y hy => ?_
  calc Metric.infDist (x + d) S ≤ dist (x + d) (y + d) := Metric.infDist_le_dist_of_mem (hS y hy)
    _ = dist x y := dist_add_right x y d

theorem infDist_add_pi {O : Set ℝ} (hper : ∀ x, x + π ∈ O ↔ x ∈ O) (hne : Oᶜ.Nonempty) (x : ℝ) :
    Metric.infDist (x + π) Oᶜ = Metric.infDist x Oᶜ := by
  have h1 : ∀ y ∈ Oᶜ, y + π ∈ Oᶜ := fun y hy h => hy ((hper y).1 h)
  have h2 : ∀ y ∈ Oᶜ, y + (-π) ∈ Oᶜ := fun y hy h => hy (by
    have := (hper (y + -π)).2 h
    rwa [neg_add_cancel_right] at this)
  refine le_antisymm (infDist_add_le π h1 hne x) ?_
  have := infDist_add_le (-π) h2 hne (x + π)
  rwa [add_neg_cancel_right] at this

/-- The continuous approximants `min 1 (n · dist(x, Oᶜ)) ↑ 1_O`. -/
@[expose] noncomputable def approxIndicator (O : Set ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  min 1 (n * Metric.infDist x Oᶜ)

theorem continuous_approxIndicator (O : Set ℝ) (n : ℕ) : Continuous (approxIndicator O n) :=
  continuous_const.min (continuous_const.mul (Metric.continuous_infDist_pt _))

theorem approxIndicator_nonneg (O : Set ℝ) (n : ℕ) (x : ℝ) : 0 ≤ approxIndicator O n x :=
  le_min zero_le_one (mul_nonneg n.cast_nonneg Metric.infDist_nonneg)

theorem approxIndicator_le_one (O : Set ℝ) (n : ℕ) (x : ℝ) : approxIndicator O n x ≤ 1 :=
  min_le_left _ _

theorem periodic_approxIndicator {O : Set ℝ} (hper : ∀ x, x + π ∈ O ↔ x ∈ O) (hne : Oᶜ.Nonempty)
    (n : ℕ) : Periodic (approxIndicator O n) π := fun x => by
  simp only [approxIndicator, infDist_add_pi hper hne x]

theorem approxIndicator_le_indicator (O : Set ℝ) (n : ℕ) (x : ℝ) :
    approxIndicator O n x ≤ O.indicator (1 : ℝ → ℝ) x := by
  by_cases hx : x ∈ O
  · simpa [hx] using approxIndicator_le_one O n x
  · have : Metric.infDist x Oᶜ = 0 := Metric.infDist_zero_of_mem hx
    simp [approxIndicator, hx, this]

theorem tendsto_approxIndicator {O : Set ℝ} (hO : IsOpen O) (hne : Oᶜ.Nonempty) (x : ℝ) :
    Tendsto (fun n => approxIndicator O n x) atTop (𝓝 (O.indicator (1 : ℝ → ℝ) x)) := by
  by_cases hx : x ∈ O
  · have hd : 0 < Metric.infDist x Oᶜ :=
      (hO.isClosed_compl.notMem_iff_infDist_pos hne).1 (by simpa using hx)
    simp only [hx, indicator_of_mem, Pi.one_apply]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈(Metric.infDist x Oᶜ)⁻¹⌉₊] with n hn
    have : 1 ≤ (n : ℝ) * Metric.infDist x Oᶜ := by
      have h1 : (Metric.infDist x Oᶜ)⁻¹ ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
      calc (1 : ℝ) = (Metric.infDist x Oᶜ)⁻¹ * Metric.infDist x Oᶜ := (inv_mul_cancel₀ hd.ne').symm
        _ ≤ n * Metric.infDist x Oᶜ := mul_le_mul_of_nonneg_right h1 hd.le
    simp [approxIndicator, this]
  · have : Metric.infDist x Oᶜ = 0 := Metric.infDist_zero_of_mem hx
    simp [approxIndicator, hx, this]

theorem integral_indicator_one_Ioc {O : Set ℝ} (hO : MeasurableSet O) :
    ∫ s in (0 : ℝ)..π, O.indicator (1 : ℝ → ℝ) s = (volume (O ∩ Ioc 0 π)).toReal := by
  rw [intervalIntegral.integral_of_le pi_pos.le, integral_indicator_one hO, Measure.real,
    Measure.restrict_apply hO]

theorem integrable_indicator_of_bounded {ρ : Measure ℝ} [IsFiniteMeasure ρ] {w : ℝ → ℝ}
    (hw : Continuous w) {B : ℝ} (hwB : ∀ x, |w x| ≤ B) {O : Set ℝ} (hO : MeasurableSet O) :
    Integrable (O.indicator w) ρ :=
  (integrable_const B).mono' ((hw.measurable.indicator hO).aestronglyMeasurable)
    (Eventually.of_forall fun x => by
      by_cases hx : x ∈ O
      · simpa [hx, Real.norm_eq_abs] using hwB x
      · simp only [indicator_of_notMem hx, norm_zero]
        exact (abs_nonneg _).trans (hwB x))

variable (hρ : IsFiniteMeasure ρ)

include hρ in
/-- **Open periodic sets.** If `(★)` holds, `∫ 1_O w dρ ≤ K Leb(O ∩ (0, π])` for an open
`π`-periodic `O` with nonempty complement. -/
theorem integral_indicator_le_of_isOpen (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x) {B : ℝ}
    (hwB : ∀ x, w x ≤ B) (hK0 : 0 ≤ K)
    (hK : ∀ ψ : ℝ → ℝ, Continuous ψ → Periodic ψ π → (∀ x, 0 ≤ ψ x) →
      ∫ x, ψ x * w x ∂ρ ≤ K * ∫ s in (0 : ℝ)..π, ψ s)
    {O : Set ℝ} (hO : IsOpen O) (hper : ∀ x, x + π ∈ O ↔ x ∈ O) (hne : Oᶜ.Nonempty) :
    ∫ x, O.indicator w x ∂ρ ≤ K * (volume (O ∩ Ioc 0 π)).toReal := by
  have hB0 : 0 ≤ B := (hw0 0).trans (hwB 0)
  have hlim : Tendsto (fun n : ℕ => ∫ x, approxIndicator O n x * w x ∂ρ) atTop
      (𝓝 (∫ x, O.indicator w x ∂ρ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => B) (fun n => ?_)
      (integrable_const B) (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · exact ((continuous_approxIndicator O n).mul hw).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (approxIndicator_nonneg O n x),
        abs_of_nonneg (hw0 x)]
      calc approxIndicator O n x * w x ≤ 1 * B :=
            mul_le_mul (approxIndicator_le_one O n x) (hwB x) (hw0 x) zero_le_one
        _ = B := one_mul B
    · have := (tendsto_approxIndicator hO hne x).mul_const (w x)
      convert this using 2
      by_cases hx : x ∈ O <;> simp [hx]
  refine le_of_tendsto' hlim fun n => ?_
  refine (hK _ (continuous_approxIndicator O n) (periodic_approxIndicator hper hne n)
    (approxIndicator_nonneg O n)).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hK0
  rw [← integral_indicator_one_Ioc hO.measurableSet]
  refine intervalIntegral.integral_mono_on pi_pos.le
    ((continuous_approxIndicator O n).intervalIntegrable _ _) ?_ fun x _ =>
    approxIndicator_le_indicator O n x
  exact (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
    ((measurable_const.indicator hO.measurableSet).aestronglyMeasurable)
    (Eventually.of_forall fun x => by
      by_cases hx : x ∈ O <;> simp [hx])

include hρ in
/-- **Null sets.** If `(★)` holds, `∫ 1_N w dρ = 0` for a Lebesgue-null measurable `N`. -/
theorem integral_indicator_eq_zero_of_null (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x) {B : ℝ}
    (hwB : ∀ x, w x ≤ B) (hK0 : 0 ≤ K)
    (hK : ∀ ψ : ℝ → ℝ, Continuous ψ → Periodic ψ π → (∀ x, 0 ≤ ψ x) →
      ∫ x, ψ x * w x ∂ρ ≤ K * ∫ s in (0 : ℝ)..π, ψ s)
    {N : Set ℝ} (hN : MeasurableSet N) (hN0 : volume N = 0) :
    ∫ x, N.indicator w x ∂ρ = 0 := by
  have hbd : ∀ x, |w x| ≤ B := fun x => by rw [abs_of_nonneg (hw0 x)]; exact hwB x
  have key : ∀ ε : ℝ, 0 < ε → ε ≤ π → ∫ x, N.indicator w x ∂ρ ≤ K * ε := by
    intro ε hε hεπ
    obtain ⟨O, hNO, hO, hOε⟩ := Set.exists_isOpen_lt_of_lt N (ENNReal.ofReal ε)
      (by rw [hN0]; simpa using hε)
    obtain ⟨hÔ, hne, hle⟩ := exists_isOpen_periodic_of_volume_lt hO
      (hOε.trans_le (ENNReal.ofReal_le_ofReal hεπ))
    have hmono : ∫ x, N.indicator w x ∂ρ ≤ ∫ x, (periodize O).indicator w x ∂ρ :=
      integral_mono (integrable_indicator_of_bounded hw hbd hN)
        (integrable_indicator_of_bounded hw hbd hÔ.measurableSet) fun x =>
        indicator_le_indicator_of_subset (hNO.trans (subset_periodize O)) hw0 x
    refine hmono.trans ((integral_indicator_le_of_isOpen hρ hw hw0 hwB hK0 hK hÔ
      (add_pi_mem_periodize_iff O) hne).trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ hK0
    calc (volume (periodize O ∩ Ioc 0 π)).toReal ≤ (volume O).toReal :=
          ENNReal.toReal_mono (hOε.trans_le le_top).ne hle
      _ ≤ ε := (ENNReal.toReal_lt_of_lt_ofReal hOε).le
  have h0 : 0 ≤ ∫ x, N.indicator w x ∂ρ :=
    integral_nonneg fun x => indicator_nonneg (fun x _ => hw0 x) x
  refine le_antisymm ?_ h0
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hK1 : 0 < K + 1 := by linarith
  have := key (min π (δ / (K + 1))) (lt_min pi_pos (by positivity)) (min_le_left _ _)
  have h2 : K * min π (δ / (K + 1)) ≤ δ := by
    calc K * min π (δ / (K + 1)) ≤ K * (δ / (K + 1)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hK0
      _ ≤ δ := by
          rw [← mul_div_assoc, div_le_iff₀ hK1]
          nlinarith
  linarith

include hρ in
/-- **Occupation of null sets.** Under `(★)`, `ρ (N ∩ {w ≠ 0}) = 0` for every Lebesgue-null `N`. -/
theorem measure_inter_ne_zero_eq_zero (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x) {B : ℝ}
    (hwB : ∀ x, w x ≤ B) (hK0 : 0 ≤ K)
    (hK : ∀ ψ : ℝ → ℝ, Continuous ψ → Periodic ψ π → (∀ x, 0 ≤ ψ x) →
      ∫ x, ψ x * w x ∂ρ ≤ K * ∫ s in (0 : ℝ)..π, ψ s)
    {N : Set ℝ} (hN : volume N = 0) : ρ (N ∩ {x | w x ≠ 0}) = 0 := by
  have hbd : ∀ x, |w x| ≤ B := fun x => by rw [abs_of_nonneg (hw0 x)]; exact hwB x
  set N₁ := toMeasurable volume N with hN₁
  have h1 : MeasurableSet N₁ := measurableSet_toMeasurable _ _
  have h2 : volume N₁ = 0 := by rw [hN₁, measure_toMeasurable]; exact hN
  have h3 := integral_indicator_eq_zero_of_null hρ hw hw0 hwB hK0 hK h1 h2
  have h4 : N₁.indicator w =ᵐ[ρ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => indicator_nonneg (fun x _ => hw0 x) x)
      (integrable_indicator_of_bounded hw hbd h1)).1 h3
  rw [Filter.EventuallyEq, ae_iff] at h4
  refine measure_mono_null (fun x hx => ?_) h4
  have hxN : x ∈ N₁ := subset_toMeasurable _ _ hx.1
  simp only [mem_ofPred_eq, indicator_of_mem hxN, Pi.zero_apply]
  exact hx.2

end Open

end ComplexSLE.Internal

end
