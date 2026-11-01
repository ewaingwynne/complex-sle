/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Ito.QuadraticVariation
public import ComplexSLE.Infrastructure.Ito.L2Limit

/-!
# The Taylor remainder of the discretized Itô expansion vanishes in `L¹`

`|remSum m| ≤ epsSeq m · incrSq m` where `epsSeq m = ½ max_k modulus(‖ΔX_k‖)` is bounded, measurable
and tends to `0` pathwise (uniform continuity of the path and of `D²F`) and `incrSq m = ∑ₖ ‖ΔX_k‖²`
is bounded in `L²` uniformly in `m` (`QuadraticVariation.lean`). By
`tendsto_integral_abs_of_le_mul`,
`E|remSum m| → 0` (`BoundedSetting.tendsto_integral_abs_remSum`).
-/

@[expose] public section

open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Infrastructure.Ito

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {n : ℕ} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m0}
  {X A : ℝ≥0 → Ω → (Fin n → ℝ)} {Q : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ} {C : ℝ}
  {F : (Fin n → ℝ) → ℝ}

section Rem

theorem range_succ_nonempty (m : ℕ) : (Finset.range (m + 1)).Nonempty :=
  ⟨0, Finset.mem_range.2 (Nat.succ_pos m)⟩

/-- `½ max_k modulus F ‖ΔX_k‖` along the `(m + 1)`-piece partition. -/
noncomputable def epsSeq (F : (Fin n → ℝ) → ℝ) (X : ℝ≥0 → Ω → (Fin n → ℝ)) (s t : ℝ≥0) (m : ℕ)
    (ω : Ω) : ℝ :=
  (1 / 2) * (Finset.range (m + 1)).sup' (range_succ_nonempty _)
    (fun k => modulus F ‖X (pt s t m (k + 1)) ω - X (pt s t m k) ω‖)

theorem epsSeq_nonneg (s t : ℝ≥0) (m : ℕ) (ω : Ω) : 0 ≤ epsSeq F X s t m ω :=
  mul_nonneg (by norm_num) ((modulus_nonneg F _).trans
    (Finset.le_sup' (fun k => modulus F ‖X (pt s t m (k + 1)) ω - X (pt s t m k) ω‖)
      (Finset.mem_range.2 (Nat.succ_pos m))))

theorem epsSeq_le {L : ℝ} (hB : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ L) (s t : ℝ≥0) (m : ℕ) (ω : Ω) :
    epsSeq F X s t m ω ≤ L := by
  unfold epsSeq
  have := Finset.sup'_le (s := Finset.range (m + 1)) (range_succ_nonempty _)
    (f := fun k => modulus F ‖X (pt s t m (k + 1)) ω - X (pt s t m k) ω‖) (a := 2 * L)
    (fun k _ => modulus_le hB _)
  linarith

theorem abs_remSum_le {L : ℝ} (hF : ContDiff ℝ 2 F) (hB : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ L)
    (s t : ℝ≥0) (m : ℕ) (ω : Ω) :
    |remSum F X s t m ω| ≤ epsSeq F X s t m ω * incrSq X s t m ω := by
  unfold remSum incrSq
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  refine (abs_taylorRem_le hF hB _ _).trans ?_
  have h1 : modulus F ‖X (pt s t m (k + 1)) ω - X (pt s t m k) ω‖ ≤
      (Finset.range (m + 1)).sup' (range_succ_nonempty _)
        (fun k => modulus F ‖X (pt s t m (k + 1)) ω - X (pt s t m k) ω‖) :=
    Finset.le_sup' (fun k => modulus F ‖X (pt s t m (k + 1)) ω - X (pt s t m k) ω‖) hk
  unfold epsSeq
  have h2 := sq_nonneg ‖X (pt s t m (k + 1)) ω - X (pt s t m k) ω‖
  nlinarith

theorem tendsto_epsSeq (huc : UniformContinuous (iteratedFDeriv ℝ 2 F)) {ω : Ω}
    (hX : Continuous fun t => X t ω) (s t : ℝ≥0) (hst : s ≤ t) :
    Tendsto (fun m => epsSeq F X s t m ω) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => Filter.Eventually.of_forall fun m =>
    lt_of_lt_of_le ha (epsSeq_nonneg s t m ω), fun a ha => ?_⟩
  obtain ⟨δ, hδ, hδF⟩ := exists_modulus_le huc (half_pos ha)
  have hcont : Continuous fun u : ℝ => X u.toNNReal ω := hX.comp continuous_real_toNNReal
  filter_upwards [eventually_dist_ptR_succ_le hcont.continuousOn (NNReal.coe_le_coe.2 hst) hδ]
    with m hm
  have : (Finset.range (m + 1)).sup' (range_succ_nonempty _)
      (fun k => modulus F ‖X (pt s t m (k + 1)) ω - X (pt s t m k) ω‖) ≤ a / 2 := by
    refine Finset.sup'_le _ _ fun k hk => hδF _ ?_
    have := hm k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
    rwa [dist_eq_norm] at this
  unfold epsSeq
  linarith

theorem measurable_epsSeq {L : ℝ} (hB : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ L)
    (hX : ∀ u, Measurable (X u)) (s t : ℝ≥0) (m : ℕ) : Measurable (epsSeq F X s t m) := by
  unfold epsSeq
  refine Measurable.const_mul ?_ _
  have hmono : Measurable (modulus F) := (modulus_mono hB).measurable
  have := Finset.measurable_sup' (s := Finset.range (m + 1)) (range_succ_nonempty m)
    (f := fun k ω => modulus F ‖X (pt s t m (k + 1)) ω - X (pt s t m k) ω‖)
    (fun k _ => hmono.comp (((hX _).sub (hX _)).norm))
  convert this using 1
  ext ω
  simp [Finset.sup'_apply]

theorem measurable_remSum (hF : ContDiff ℝ 2 F) (hX : ∀ u, Measurable (X u)) (s t : ℝ≥0) (m : ℕ) :
    Measurable (remSum F X s t m) := by
  unfold remSum taylorRem
  refine Finset.measurable_sum _ fun k _ => ?_
  have hXv := hX (pt s t m (k + 1))
  have hXu := hX (pt s t m k)
  have hFm : Measurable F := hF.continuous.measurable
  have hg : ∀ i, Measurable (gF F i) := fun i => (continuous_gF hF i).measurable
  have hH : ∀ i j, Measurable (HF F i j) := fun i j => (continuous_HF hF i j).measurable
  refine ((((hFm.comp hXv).sub (hFm.comp hXu)).sub (Finset.measurable_sum _ fun i _ => ?_)).sub
    (Measurable.const_mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _
      fun j _ => ?_) _))
  · exact (((measurable_pi_apply i).comp hXv).sub ((measurable_pi_apply i).comp hXu)).mul
      ((hg i).comp hXu)
  · exact ((((measurable_pi_apply i).comp hXv).sub ((measurable_pi_apply i).comp hXu)).mul
      (((measurable_pi_apply j).comp hXv).sub ((measurable_pi_apply j).comp hXu))).mul
      ((hH i j).comp hXu)

theorem BoundedSetting.aebdd_remSum [IsProbabilityMeasure P]
    (h : BoundedSetting ℱ P X A Q C) (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) : AEBdd P (remSum F X s t m) := by
  obtain ⟨-, -, L, -, -, -, hB⟩ := exists_bounds hF hFc
  obtain ⟨-, b, hb⟩ := (h.aebdd_incrSq hst m)
  refine ⟨(measurable_remSum hF h.measurable_X s t m).aestronglyMeasurable, L * b, ?_⟩
  filter_upwards [hb] with ω hω
  refine (abs_remSum_le hF hB s t m ω).trans ?_
  exact mul_le_mul (epsSeq_le (X := X) hB s t m ω) ((le_abs_self _).trans hω)
    (incrSq_nonneg s t m ω)
    ((epsSeq_nonneg (F := F) (X := X) s t m ω).trans (epsSeq_le (X := X) hB s t m ω))

/-- **The Taylor remainders vanish in `L¹`.** -/
theorem BoundedSetting.tendsto_integral_abs_remSum [IsProbabilityMeasure P]
    (h : BoundedSetting ℱ P X A Q C) (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    {s t : ℝ≥0} (hst : s ≤ t) :
    Tendsto (fun m => ∫ ω, |remSum F X s t m ω| ∂P) atTop (𝓝 0) := by
  obtain ⟨-, -, L, -, -, -, hB⟩ := exists_bounds hF hFc
  have huc := uniformContinuous_iteratedFDeriv_two hF hFc
  have hXm : ∀ u, Measurable (X u) := h.measurable_X
  refine tendsto_integral_abs_of_le_mul (e := fun m => epsSeq F X s t m)
    (S := fun m => incrSq X s t m) (B := L) (K := incrSqBound n C) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun m => (measurable_epsSeq hB hXm s t m).aestronglyMeasurable
  · exact fun m => Filter.Eventually.of_forall fun ω => epsSeq_nonneg (F := F) (X := X) s t m ω
  · exact fun m => Filter.Eventually.of_forall fun ω => epsSeq_le (X := X) hB s t m ω
  · exact Filter.Eventually.of_forall fun ω => tendsto_epsSeq huc (h.cont_X ω) s t hst
  · exact fun m => (h.aebdd_incrSq hst m).sq.integrable
  · exact fun m => h.integral_sq_incrSq_le hst m
  · exact fun m => (h.aebdd_remSum hF hFc hst m).integrable
  · exact fun m => Filter.Eventually.of_forall fun ω => by
      rw [abs_of_nonneg (incrSq_nonneg (X := X) s t m ω)]
      exact abs_remSum_le hF hB s t m ω

end Rem

end ComplexSLE.Infrastructure.Ito

end
