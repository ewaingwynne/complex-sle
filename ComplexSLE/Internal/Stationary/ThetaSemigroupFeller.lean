/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.ThetaSemigroup

/-!
# The semigroup of `θ̂` (M10-R3): the Feller property and continuity in time

* `continuous_thetaSemigroup` (Feller): for continuous `π`-periodic `f`, `Q_t f` is continuous.
  For a.e. `ω` (`U 0 = 0`, `σ_{e^{iu₀}}` defined on `[0, ∞)`), the map
  `u ↦ f(θ̂_t(e^{iu}))` is continuous at `u₀`: near `u₀` it equals
  `f((θ̂_t - θ̂_0)(e^{iu}) + u)` (`θ̂_0(e^{iu}) ≡ u` mod `2π`, `f` `2π`-periodic), and
  `(θ̂_t - θ̂_0)(e^{iu})` is continuous in `u` (`continuousAt_argPath_sub_initial`).
  Then dominated convergence.
* `continuous_thetaSemigroup_time`: for continuous bounded `f`, `t ↦ Q_t f(u)` is continuous
  (a.s. path continuity of `θ̂`, then dominated convergence).
-/

public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter Function

namespace ComplexSLE.Internal

open Polar

section Deterministic

variable {V : ℝ≥0 → ℂ}

/-- For a driver with `V 0 = 0`, `θ_0(e^{iu}) ≡ u` mod `2π`. -/
theorem exists_argPath_zero_unit (hV : Continuous V) (h0 : V 0 = 0) {u : ℝ}
    (hz : (0 : ℝ) ∈ lifeSet V (unitPt u)) :
    ∃ n : ℤ, argPath V hV (unitPt u) 0 = u + n * (2 * π) := by
  have hexp := exp_argPath_mul_I hV hz
  rw [fPath_zero, h0, sub_zero, norm_unitPt, Complex.ofReal_one, div_one] at hexp
  have hexp' : Complex.exp ((argPath V hV (unitPt u) 0 : ℂ) * Complex.I) =
      Complex.exp ((u : ℂ) * Complex.I) := hexp
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 hexp'
  refine ⟨n, ?_⟩
  have hπ : (2 * (π : ℂ) * Complex.I) = ((2 * π : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hπ] at hn
  have := congrArg Complex.im hn
  simpa using this

/-- **The Feller step**: `u ↦ f(θ_{σ_{e^{iu}}(s)}(e^{iu}))` is continuous at `u₀` when `V 0 = 0`,
`s ∈ sigmaDom` at `e^{iu₀}`, and `f` is continuous and `π`-periodic. -/
theorem continuousAt_comp_argPath_sigmaTime_unit (hV : Continuous V) (h0 : V 0 = 0) {f : ℝ → ℝ}
    (hf : Continuous f) (hper : Periodic f π) {s : ℝ} {u₀ : ℝ}
    (hs : s ∈ sigmaDom V hV (unitPt u₀)) :
    ContinuousAt (fun u => f (argPath V hV (unitPt u) (sigmaTime V hV (unitPt u) s))) u₀ := by
  have hΔ : ContinuousAt (fun u : ℝ => argPath V hV (unitPt u) (sigmaTime V hV (unitPt u) s) -
      argPath V hV (unitPt u) 0) u₀ :=
    (continuousAt_argPath_sub_initial hV hs).comp (f := unitPt) continuous_unitPt.continuousAt
  have hcont : ContinuousAt (fun u : ℝ => f ((argPath V hV (unitPt u)
      (sigmaTime V hV (unitPt u) s) - argPath V hV (unitPt u) 0) + u)) u₀ :=
    hf.continuousAt.comp (hΔ.add continuousAt_id)
  refine hcont.congr ?_
  filter_upwards [(isOpen_sigmaDom_unit hV s).mem_nhds hs] with u hu
  have hu' : s ∈ sigmaDom V hV (unitPt u) := hu
  obtain ⟨n, hn⟩ := exists_argPath_zero_unit hV h0 (ne_driver_zero_of_mem_sigmaDomSet hu')
  calc f ((argPath V hV (unitPt u) (sigmaTime V hV (unitPt u) s) -
          argPath V hV (unitPt u) 0) + u)
      = f (((argPath V hV (unitPt u) (sigmaTime V hV (unitPt u) s) -
          argPath V hV (unitPt u) 0) + u) + ((2 * n : ℤ) : ℝ) * π) :=
        ((hper.int_mul _) _).symm
    _ = f (argPath V hV (unitPt u) (sigmaTime V hV (unitPt u) s)) := by
        congr 1
        rw [hn]; push_cast; ring

end Deterministic

section Process

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-- A continuous periodic function is bounded. -/
theorem exists_abs_le_of_periodic {f : ℝ → ℝ} (hf : Continuous f) (hper : Periodic f π) :
    ∃ C, ∀ v, |f v| ≤ C := by
  obtain ⟨C, hC⟩ := (hper.isBounded_of_continuous Real.pi_ne_zero hf).exists_norm_le
  exact ⟨C, fun v => by simpa [Real.norm_eq_abs] using hC (f v) ⟨v, rfl⟩⟩

/-- Pathwise Feller: `u ↦ f(θ̂_t(e^{iu})(ω))` is continuous at `u₀` when `U 0 ω = 0` and
`t ∈ sigmaDom` at `e^{iu₀}`. -/
theorem continuousAt_comp_thetaHat_unit (hU : IsSLEDriverAdapted a b c U P ℱ) {f : ℝ → ℝ}
    (hf : Continuous f) (hper : Periodic f π) {t : ℝ≥0} {ω : Ω} (h0 : U 0 ω = 0) {u₀ : ℝ}
    (ht : (t : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) (unitPt u₀)) :
    ContinuousAt (fun u => f (thetaHat hU (unitPt u) t ω)) u₀ := by
  refine (continuousAt_comp_argPath_sigmaTime_unit (hU.cont ω) h0 hf hper ht).congr ?_
  filter_upwards [(isOpen_sigmaDom_unit (hU.cont ω) (t : ℝ)).mem_nhds ht] with u hu
  have hu' : (t : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) (unitPt u) := hu
  simp only [thetaHat_of_mem hU hu']

variable [IsProbabilityMeasure P]

/-- **Feller property**: for continuous `π`-periodic `f`, `Q_t f` is continuous. -/
theorem continuous_thetaSemigroup (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a)
    (hc : c ^ 2 ≤ a * b) (t : ℝ≥0) {f : ℝ → ℝ} (hf : Continuous f) (hper : Periodic f π) :
    Continuous (thetaSemigroup hU t f) := by
  obtain ⟨C, hC⟩ := exists_abs_le_of_periodic hf hper
  refine continuous_iff_continuousAt.2 fun u₀ => ?_
  refine continuousAt_of_dominated (bound := fun _ => C) ?_ ?_ (integrable_const _) ?_
  · exact Eventually.of_forall fun u =>
      (hf.measurable.comp (measurable_thetaHat hU (unitPt u) t)).aestronglyMeasurable
  · exact Eventually.of_forall fun u => Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using hC _
  · filter_upwards [ae_thetaHat_eq_and_continuous hU ha hc (unitPt_ne_zero u₀),
      hU.toIsSLEDriver.zero] with ω hω h0
    exact continuousAt_comp_thetaHat_unit hU hf hper h0 (hω.1 t)

/-- **Continuity in time**: for continuous bounded `f`, `t ↦ Q_t f(u)` is continuous. -/
theorem continuous_thetaSemigroup_time (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a)
    (hc : c ^ 2 ≤ a * b) {f : ℝ → ℝ} (hf : Continuous f) (hb : ∃ C, ∀ v, |f v| ≤ C) (u : ℝ) :
    Continuous fun t : ℝ≥0 => thetaSemigroup hU t f u := by
  obtain ⟨C, hC⟩ := hb
  refine continuous_of_dominated (bound := fun _ => C) ?_ ?_ (integrable_const _) ?_
  · exact fun t =>
      (hf.measurable.comp (measurable_thetaHat hU (unitPt u) t)).aestronglyMeasurable
  · exact fun t => Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hC _
  · filter_upwards [ae_thetaHat_eq_and_continuous hU ha hc (unitPt_ne_zero u)] with ω hω
    exact hf.comp hω.2

end Process

end ComplexSLE.Internal

end
