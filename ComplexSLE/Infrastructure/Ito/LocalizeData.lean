/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Ito.Bounded
public import ComplexSLE.Infrastructure.Stochastic.ProgressiveTools

/-!
# Stopped and frozen data for the localisation of Itô's formula

Let `T` be a finite stopping time, `U` a measurable set, `x₀` a point. From the data `(X, A, Q)` of
Itô's formula we build

* `frozenStop U x₀ T X`: `X_{t ∧ T}` on `{X₀ ∈ U}` and the constant `x₀` elsewhere (the event
  `{X₀ ∈ U}` is `ℱ 0`-measurable, so this is progressive);
* `stopSmul T A`: the density `A_s 1_{s ≤ T}` (progressive).

If `T = 0` on `{X₀ ∉ U}`, the martingale parts, the brackets and the Itô process of the new data are
the stopped processes of the old ones (`Mp_frozenStop`, `Np_frozenStop`,
`itoProcess_frozenStop`), for *every* `ω`.
-/

@[expose] public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Infrastructure.Ito

section Algebra

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}

/-- The indicator `1_{s ≤ T}` of the stochastic interval `[0, T]`. -/
noncomputable def stopInd (T : Ω → ℝ≥0) (s : ℝ≥0) (ω : Ω) : ℝ := if s ≤ T ω then 1 else 0

theorem isStronglyProgressive_stopInd {T : Ω → ℝ≥0}
    (hT : IsStoppingTime ℱ fun ω => (T ω : WithTop ℝ≥0)) :
    IsStronglyProgressive ℱ (stopInd T) :=
  isStronglyProgressive_indicator_le_nnreal hT

/-- The density `A_s 1_{s ≤ T}`. -/
noncomputable def stopSmul {E : Type*} [AddCommMonoid E] [Module ℝ E] (T : Ω → ℝ≥0)
    (A : ℝ≥0 → Ω → E) (s : ℝ≥0) (ω : Ω) : E := stopInd T s ω • A s ω

theorem isStronglyProgressive_stopSmul {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {T : Ω → ℝ≥0}
    (hT : IsStoppingTime ℱ fun ω => (T ω : WithTop ℝ≥0)) {A : ℝ≥0 → Ω → E}
    (hA : IsStronglyProgressive ℱ A) : IsStronglyProgressive ℱ (stopSmul T A) :=
  fun i => ((isStronglyProgressive_stopInd hT) i).smul (hA i)

/-- `∫₀ᵗ ξ_s 1_{s ≤ T} ds = ∫₀^{t ∧ T} ξ_s ds`. -/
theorem pathIntegral_ite_le (ξ : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    pathIntegral (fun s ω => if s ≤ T ω then ξ s ω else 0) t ω =
      pathIntegral ξ (min t (T ω)) ω := by
  unfold pathIntegral
  rw [intervalIntegral.integral_of_le t.coe_nonneg,
    intervalIntegral.integral_of_le (NNReal.coe_nonneg _)]
  have h : (fun s : ℝ => if s.toNNReal ≤ T ω then ξ s.toNNReal ω else 0) =
      (Iic ((T ω : ℝ≥0) : ℝ)).indicator fun s : ℝ => ξ s.toNNReal ω := by
    funext s
    simp only [indicator, mem_Iic, Real.toNNReal_le_iff_le_coe]
  rw [h, setIntegral_indicator measurableSet_Iic]
  congr 1
  ext s
  simp

theorem min_zero_left' (x : ℝ≥0) : min 0 x = 0 := min_eq_left zero_le

theorem pathIntegral_zero (ξ : ℝ≥0 → Ω → ℝ) (ω : Ω) : pathIntegral ξ 0 ω = 0 := by
  simp [pathIntegral]

theorem stopSmul_vec_apply {d : ℕ} (T : Ω → ℝ≥0) (A : ℝ≥0 → Ω → (Fin d → ℝ)) (s : ℝ≥0) (ω : Ω)
    (i : Fin d) : stopSmul T A s ω i = if s ≤ T ω then A s ω i else 0 := by
  by_cases h : s ≤ T ω <;> simp [stopSmul, stopInd, h]

theorem stopSmul_matrix_apply {d : ℕ} (T : Ω → ℝ≥0) (Q : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ)
    (s : ℝ≥0) (ω : Ω) (i j : Fin d) :
    stopSmul T Q s ω i j = if s ≤ T ω then Q s ω i j else 0 := by
  by_cases h : s ≤ T ω <;> simp [stopSmul, stopInd, h]

/-- The stopped process `X_{t ∧ T}` of a progressive process at a finite stopping time `T`. -/
theorem isStronglyProgressive_min_stop {E : Type*} [TopologicalSpace E] {T : Ω → ℝ≥0}
    (hT : IsStoppingTime ℱ fun ω => (T ω : WithTop ℝ≥0)) {X : ℝ≥0 → Ω → E}
    (hX : IsStronglyProgressive ℱ X) :
    IsStronglyProgressive ℱ fun t ω => X (min t (T ω)) ω := by
  have := hX.stoppedProcess hT
  have e : stoppedProcess X (fun ω => (T ω : WithTop ℝ≥0)) =
      fun t ω => X (min t (T ω)) ω := by
    funext t ω
    simp only [stoppedProcess]
    rw [← WithTop.coe_min]
    rfl
  rwa [e] at this

open scoped Classical in
/-- `X_{t ∧ T}` on `{X₀ ∈ U}` and the constant `x₀` elsewhere. -/
noncomputable def frozenStop {E : Type*} (U : Set E) (x₀ : E) (T : Ω → ℝ≥0) (X : ℝ≥0 → Ω → E)
    (t : ℝ≥0) (ω : Ω) : E := if X 0 ω ∈ U then X (min t (T ω)) ω else x₀

theorem isStronglyProgressive_frozenStop {d : ℕ} {U : Set (Fin d → ℝ)} (hU : MeasurableSet U)
    (x₀ : Fin d → ℝ) {T : Ω → ℝ≥0} (hT : IsStoppingTime ℱ fun ω => (T ω : WithTop ℝ≥0))
    {X : ℝ≥0 → Ω → (Fin d → ℝ)} (hX : IsStronglyProgressive ℱ X) :
    IsStronglyProgressive ℱ (frozenStop U x₀ T X) := by
  intro i
  have hXT := isStronglyProgressive_min_stop hT hX
  have h0 : MeasurableSet[ℱ i] {ω | X 0 ω ∈ U} :=
    ((hX.stronglyAdapted 0).measurable.mono (ℱ.mono zero_le) le_rfl) hU
  have hset : MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ i)]
      {p : Iic i × Ω | X 0 p.2 ∈ U} :=
    @measurable_snd (Iic i) Ω Subtype.instMeasurableSpace (ℱ i) _ h0
  exact StronglyMeasurable.ite hset (hXT i) stronglyMeasurable_const

end Algebra

section Identities

variable {Ω : Type*} {d : ℕ} {U : Set (Fin d → ℝ)} {x₀ : Fin d → ℝ} {T : Ω → ℝ≥0}
  {X A : ℝ≥0 → Ω → (Fin d → ℝ)} {Q : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ}

/-- The martingale part of the frozen data is the stopped martingale part. -/
theorem Mp_frozenStop (hT0 : ∀ ω, X 0 ω ∉ U → T ω = 0) (i : Fin d) (t : ℝ≥0) (ω : Ω) :
    Mp (frozenStop U x₀ T X) (stopSmul T A) i t ω = Mp X A i (min t (T ω)) ω := by
  have hp : pathIntegral (fun s ω => stopSmul T A s ω i) t ω =
      pathIntegral (fun s ω => A s ω i) (min t (T ω)) ω := by
    rw [← pathIntegral_ite_le]
    simp only [stopSmul_vec_apply]
  by_cases hG : X 0 ω ∈ U
  · simp only [Mp, frozenStop, hG, ite_true, min_zero_left', hp]
  · have h0 := hT0 ω hG
    simp only [Mp, frozenStop, hG, ite_false, hp, h0, min_zero, pathIntegral_zero]
    ring

/-- The bracket of the frozen data is the stopped bracket. -/
theorem Np_frozenStop (hT0 : ∀ ω, X 0 ω ∉ U → T ω = 0) (i j : Fin d) (t : ℝ≥0) (ω : Ω) :
    Np (frozenStop U x₀ T X) (stopSmul T A) (stopSmul T Q) i j t ω =
      Np X A Q i j (min t (T ω)) ω := by
  have hp : pathIntegral (fun s ω => stopSmul T Q s ω i j) t ω =
      pathIntegral (fun s ω => Q s ω i j) (min t (T ω)) ω := by
    rw [← pathIntegral_ite_le]
    simp only [stopSmul_matrix_apply]
  simp only [Np, Mp_frozenStop hT0, hp]

/-- The Itô process `F(X_t) - F(X_0) - ∫₀ᵗ (∑ ∂ᵢF Aⁱ + ½ ∑ ∂ᵢⱼF Qⁱʲ)`. -/
noncomputable def itoProc (F : (Fin d → ℝ) → ℝ) (X A : ℝ≥0 → Ω → (Fin d → ℝ))
    (Q : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  F (X t ω) - F (X 0 ω) - pathIntegral (itoDrift F X A Q) t ω

theorem pathIntegral_itoDrift_frozenStop {F : (Fin d → ℝ) → ℝ}
    (hT0 : ∀ ω, X 0 ω ∉ U → T ω = 0) (t : ℝ≥0) (ω : Ω) :
    pathIntegral (itoDrift F (frozenStop U x₀ T X) (stopSmul T A) (stopSmul T Q)) t ω =
      pathIntegral (itoDrift F X A Q) (min t (T ω)) ω := by
  rw [← pathIntegral_ite_le]
  unfold pathIntegral
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun s hs => ?_)
  rw [Set.uIoc_of_le t.coe_nonneg] at hs
  by_cases hle : s.toNNReal ≤ T ω
  · have hG : X 0 ω ∈ U := by
      by_contra h
      have h0 := hT0 ω h
      have : 0 < s.toNNReal := Real.toNNReal_pos.2 hs.1
      rw [h0] at hle
      exact absurd hle (not_le.2 this)
    simp only [itoDrift, stopSmul_vec_apply, stopSmul_matrix_apply, frozenStop, hG, hle,
      ite_true, min_eq_left hle]
  · simp only [itoDrift, stopSmul_vec_apply, stopSmul_matrix_apply, hle, ite_false, mul_zero,
      Finset.sum_const_zero, add_zero, mul_zero]

/-- The Itô process of the frozen data is the stopped Itô process of the original data. -/
theorem itoProc_frozenStop {F : (Fin d → ℝ) → ℝ} (hT0 : ∀ ω, X 0 ω ∉ U → T ω = 0) (t : ℝ≥0)
    (ω : Ω) :
    itoProc F (frozenStop U x₀ T X) (stopSmul T A) (stopSmul T Q) t ω =
      itoProc F X A Q (min t (T ω)) ω := by
  unfold itoProc
  rw [pathIntegral_itoDrift_frozenStop hT0]
  by_cases hG : X 0 ω ∈ U
  · simp only [frozenStop, hG, ite_true, min_zero_left']
  · have h0 := hT0 ω hG
    simp only [frozenStop, hG, ite_false, h0, min_zero, sub_self]

/-- Interval integrability is inherited by the stopped density. -/
theorem intervalIntegrable_stopSmul_vec {A : ℝ≥0 → Ω → (Fin d → ℝ)} {ω : Ω} {i : Fin d}
    {t : ℝ≥0} (h : IntervalIntegrable (fun s : ℝ => A s.toNNReal ω i) volume 0 t) :
    IntervalIntegrable (fun s : ℝ => stopSmul T A s.toNNReal ω i) volume 0 t := by
  have e : (fun s : ℝ => stopSmul T A s.toNNReal ω i) =
      (Iic ((T ω : ℝ≥0) : ℝ)).indicator fun s : ℝ => A s.toNNReal ω i := by
    funext s
    simp only [stopSmul_vec_apply, indicator, mem_Iic, Real.toNNReal_le_iff_le_coe]
  rw [e, intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg] at *
  exact h.indicator measurableSet_Iic

theorem intervalIntegrable_stopSmul_matrix {Q : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ} {ω : Ω}
    {i j : Fin d} {t : ℝ≥0}
    (h : IntervalIntegrable (fun s : ℝ => Q s.toNNReal ω i j) volume 0 t) :
    IntervalIntegrable (fun s : ℝ => stopSmul T Q s.toNNReal ω i j) volume 0 t := by
  have e : (fun s : ℝ => stopSmul T Q s.toNNReal ω i j) =
      (Iic ((T ω : ℝ≥0) : ℝ)).indicator fun s : ℝ => Q s.toNNReal ω i j := by
    funext s
    simp only [stopSmul_matrix_apply, indicator, mem_Iic, Real.toNNReal_le_iff_le_coe]
  rw [e, intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg] at *
  exact h.indicator measurableSet_Iic

/-- The total variation of the stopped density is bounded by the bound of the original one. -/
theorem abs_integral_stopSmul_vec_le {A : ℝ≥0 → Ω → (Fin d → ℝ)} {ω : Ω} {C₀ : ℝ}
    (h : ∀ (i : Fin d) (t : ℝ≥0), ∫ s in (0 : ℝ)..(t : ℝ), |A s.toNNReal ω i| ≤ C₀)
    (i : Fin d) (t : ℝ≥0) :
    ∫ s in (0 : ℝ)..(t : ℝ), |stopSmul T A s.toNNReal ω i| ≤ C₀ := by
  have e := pathIntegral_ite_le (fun s ω => |A s ω i|) T t ω
  have e2 : (fun s ω => if s ≤ T ω then |A s ω i| else 0) =
      fun s ω => |stopSmul T A s ω i| := by
    funext s ω
    by_cases hs : s ≤ T ω <;> simp [stopSmul_vec_apply, hs]
  rw [e2] at e
  exact e.trans_le (h i (min t (T ω)))

theorem abs_integral_stopSmul_matrix_le {Q : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ} {ω : Ω}
    {C₀ : ℝ}
    (h : ∀ (i j : Fin d) (t : ℝ≥0), ∫ s in (0 : ℝ)..(t : ℝ), |Q s.toNNReal ω i j| ≤ C₀)
    (i j : Fin d) (t : ℝ≥0) :
    ∫ s in (0 : ℝ)..(t : ℝ), |stopSmul T Q s.toNNReal ω i j| ≤ C₀ := by
  have e := pathIntegral_ite_le (fun s ω => |Q s ω i j|) T t ω
  have e2 : (fun s ω => if s ≤ T ω then |Q s ω i j| else 0) =
      fun s ω => |stopSmul T Q s ω i j| := by
    funext s ω
    by_cases hs : s ≤ T ω <;> simp [stopSmul_matrix_apply, hs]
  rw [e2] at e
  exact e.trans_le (h i j (min t (T ω)))

end Identities

end ComplexSLE.Infrastructure.Ito

end
