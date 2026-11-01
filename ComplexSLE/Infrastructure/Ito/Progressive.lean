/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.PathIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Probability.Process.Adapted
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Path integrals of progressive processes

Source-independent tools for the bounded core of Itô's formula (`ComplexSLE.Infrastructure.Ito`).

* `isStronglyProgressive_pathIntegral`: the path integral `t ↦ ∫₀ᵗ ξ_s ds` of a progressively
  measurable process is progressively measurable (Fubini on `[0, i] × Ω × [0, i]`); no integrability
  or continuity is needed. (Adapted from the proof of the same fact in
  `ComplexSLE.Internal.Polar.PolarThetaBrIto`, which imports an external input.)
* `isStronglyProgressive_comp_measurable`, `isStronglyProgressive_apply`,
  `isStronglyProgressive_matrix_apply`: closure properties of progressive processes.
* `continuous_pathIntegral`: path integrals of locally integrable paths are continuous in the
  upper limit; `pathIntegral_sub_eq`: increments are integrals over the increment interval.
-/

@[expose] public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Infrastructure.Ito

section Progressive

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}

/-- **The path integral of a progressive process is progressive** (no integrability needed). -/
theorem isStronglyProgressive_pathIntegral {ξ : ℝ≥0 → Ω → ℝ} (hξ : IsStronglyProgressive ℱ ξ) :
    IsStronglyProgressive ℱ fun t ω => pathIntegral ξ t ω := by
  intro i
  let mI : MeasurableSpace (Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
  let mR : MeasurableSpace ℝ := inferInstance
  -- the integrand on `([0, i] × Ω) × ℝ`
  let F : (Iic i × Ω) × ℝ → ℝ := fun q =>
    {q : (Iic i × Ω) × ℝ | 0 < q.2 ∧ q.2 ≤ ((q.1.1 : ℝ≥0) : ℝ)}.indicator
      (fun q => ξ (min (Real.toNNReal q.2) i) q.1.2) q
  have hφ : Measurable[mI.prod mR, mI] fun q : (Iic i × Ω) × ℝ =>
      ((⟨min (Real.toNNReal q.2) i, mem_Iic.2 (min_le_right _ _)⟩ : Iic i), q.1.2) := by
    refine Measurable.prodMk ?_ ?_
    · refine Measurable.subtype_mk ?_
      exact (measurable_real_toNNReal.comp (@measurable_snd _ _ mI mR)).min measurable_const
    · exact (@measurable_snd _ _ Subtype.instMeasurableSpace (ℱ i)).comp
        (@measurable_fst _ _ mI mR)
  have hF : StronglyMeasurable[mI.prod mR] F := by
    refine StronglyMeasurable.indicator ((hξ i).comp_measurable hφ) ?_
    have h1 : Measurable[mI.prod mR] fun q : (Iic i × Ω) × ℝ => q.2 :=
      @measurable_snd _ _ mI mR
    have h2 : Measurable[mI.prod mR] fun q : (Iic i × Ω) × ℝ => ((q.1.1 : ℝ≥0) : ℝ) :=
      (measurable_subtype_coe.comp
        (@measurable_fst _ _ Subtype.instMeasurableSpace (ℱ i))).comp
          (@measurable_fst _ _ mI mR) |>.coe_nnreal_real
    exact (measurableSet_lt measurable_const h1).inter (measurableSet_le h1 h2)
  have key := @StronglyMeasurable.integral_prod_right' (Iic i × Ω) ℝ ℝ mI mR volume _ _ _ F hF
  have e : (fun p : Iic i × Ω => pathIntegral ξ (p.1 : ℝ≥0) p.2) = fun p => ∫ y, F (p, y) := by
    funext p
    simp only [pathIntegral]
    rw [intervalIntegral.integral_of_le (p.1 : ℝ≥0).coe_nonneg,
      ← integral_indicator measurableSet_Ioc]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    by_cases h1 : 0 < s ∧ s ≤ ((p.1 : ℝ≥0) : ℝ)
    · have : Real.toNNReal s ≤ i := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ h1.1.le]
        exact h1.2.trans (NNReal.coe_le_coe.2 p.1.2)
      simp only [F, indicator, mem_Ioc, mem_ofPred_eq, h1, and_self, ite_true, min_eq_left this]
    · simp only [F, indicator, mem_Ioc, mem_ofPred_eq, h1, ite_false]
  rw [e]; exact key

/-- A measurable function of a progressive `ℝⁿ`-valued process is progressive. -/
theorem isStronglyProgressive_comp_measurable {n : ℕ} {X : ℝ≥0 → Ω → (Fin n → ℝ)}
    (hX : IsStronglyProgressive ℱ X) {g : (Fin n → ℝ) → ℝ} (hg : Measurable g) :
    IsStronglyProgressive ℱ fun t ω => g (X t ω) := fun i => by
  let _ : MeasurableSpace (Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
  exact (hg.comp (hX i).measurable).stronglyMeasurable

/-- The coordinates of a progressive vector process are progressive. -/
theorem isStronglyProgressive_apply {n : ℕ} {A : ℝ≥0 → Ω → (Fin n → ℝ)}
    (hA : IsStronglyProgressive ℱ A) (i : Fin n) : IsStronglyProgressive ℱ fun t ω => A t ω i :=
  fun j => (continuous_apply i).comp_stronglyMeasurable (hA j)

/-- The entries of a progressive matrix process are progressive. -/
theorem isStronglyProgressive_matrix_apply {n : ℕ}
    {Q : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ} (hQ : IsStronglyProgressive ℱ Q)
    (i j : Fin n) : IsStronglyProgressive ℱ fun t ω => Q t ω i j :=
  fun k => (continuous_id.matrix_elem i j).comp_stronglyMeasurable (hQ k)

end Progressive

section PathIntegral

variable {Ω : Type*}

/-- A path integral with an integrand that is interval integrable on every `[0, t]` is a
continuous function of the upper limit. -/
theorem continuous_pathIntegral {ξ : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hξ : ∀ t : ℝ≥0, IntervalIntegrable (fun s : ℝ => ξ s.toNNReal ω) volume 0 t) :
    Continuous fun t : ℝ≥0 => pathIntegral ξ t ω := by
  have h0 : ∀ b : ℝ, IntervalIntegrable (fun s : ℝ => ξ s.toNNReal ω) volume 0 b := by
    intro b
    rcases le_or_gt 0 b with hb | hb
    · have := hξ b.toNNReal
      rwa [Real.coe_toNNReal _ hb] at this
    · refine IntervalIntegrable.symm ?_
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le]
      exact (integrableOn_const (C := ξ 0 ω) measure_Ioc_lt_top.ne).congr_fun (fun s hs => by
        have : s.toNNReal = 0 := Real.toNNReal_of_nonpos hs.2
        simp [this]) measurableSet_Ioc
  have hall : ∀ a b : ℝ, IntervalIntegrable (fun s : ℝ => ξ s.toNNReal ω) volume a b :=
    fun a b => (h0 a).symm.trans (h0 b)
  exact (intervalIntegral.continuous_primitive hall 0).comp NNReal.continuous_coe

/-- Increments of a path integral. -/
theorem pathIntegral_sub_eq {ξ : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hξ : ∀ t : ℝ≥0, IntervalIntegrable (fun s : ℝ => ξ s.toNNReal ω) volume 0 t) (u v : ℝ≥0) :
    pathIntegral ξ v ω - pathIntegral ξ u ω = ∫ x in (u : ℝ)..(v : ℝ), ξ x.toNNReal ω :=
  intervalIntegral.integral_interval_sub_left (hξ v) (hξ u)

/-- `|∫₀ᵗ ξ| ≤ ∫₀ᵗ |ξ|`. -/
theorem abs_pathIntegral_le {ξ : ℝ≥0 → Ω → ℝ} {ω : Ω} (t : ℝ≥0) :
    |pathIntegral ξ t ω| ≤ ∫ x in (0 : ℝ)..(t : ℝ), |ξ x.toNNReal ω| :=
  intervalIntegral.abs_integral_le_integral_abs t.coe_nonneg

end PathIntegral

end ComplexSLE.Infrastructure.Ito

end
