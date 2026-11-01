/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Ito.Setting
public import ComplexSLE.Infrastructure.Ito.WPart
public import Mathlib.Algebra.Order.Chebyshev

/-!
# `L²` bound for the sum of squared increments

For the martingale part `Mⁱ` of a `BoundedSetting`, the quadratic variation sums
`qvSum i s t m = ∑ₖ (ΔMⁱ_k)²` satisfy `qvSum = M_t² - M_s² - 2 ∑ₖ M_k ΔM_k` (`qvSum_eq`), hence
`E[qvSum²] ≤ 18 C⁴` uniformly in the partition (`BoundedSetting.integral_sq_qvSum_le`, from the
`L²` bound for martingale transforms). Pathwise `∑ₖ ‖ΔX_k‖² ≤ ∑ᵢ (2 qvSum + 2C²)`
(`incrSq_le`), so `E[(∑ₖ ‖ΔX_k‖²)²] ≤ incrSqBound n C` uniformly in `m`
(`BoundedSetting.integral_sq_incrSq_le`). The sums themselves are not pathwise bounded uniformly
in `m`; only `L²` control is available, which is what the Taylor remainder estimate uses.
-/

@[expose] public section

open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Infrastructure.Ito

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {n : ℕ} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m0}
  {X A : ℝ≥0 → Ω → (Fin n → ℝ)} {Q : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ} {C : ℝ}

section QV

variable (X A) in
/-- The quadratic variation sum of `Mⁱ` along the `(m + 1)`-piece partition of `[s, t]`. -/
noncomputable def qvSum (i : Fin n) (s t : ℝ≥0) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (m + 1),
    (Mp X A i (pt s t m (k + 1)) ω - Mp X A i (pt s t m k) ω) ^ 2

/-- `∑ (ΔM)² = M_t² - M_s² - 2 ∑ M_k ΔM_k`. -/
theorem qvSum_eq {s t : ℝ≥0} (i : Fin n) (m : ℕ) (ω : Ω) :
    qvSum X A i s t m ω = Mp X A i t ω ^ 2 - Mp X A i s ω ^ 2 -
      2 * transform (Mp X A i) (pt s t m) (fun k ω => Mp X A i (pt s t m k) ω) (m + 1) ω := by
  unfold qvSum transform
  have h1 : ∀ k ∈ Finset.range (m + 1),
      (Mp X A i (pt s t m (k + 1)) ω - Mp X A i (pt s t m k) ω) ^ 2 =
        (Mp X A i (pt s t m (k + 1)) ω ^ 2 - Mp X A i (pt s t m k) ω ^ 2) -
          2 * (Mp X A i (pt s t m k) ω *
            (Mp X A i (pt s t m (k + 1)) ω - Mp X A i (pt s t m k) ω)) :=
    fun k _ => by ring
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_range_sub (fun k => Mp X A i (pt s t m k) ω ^ 2), pt_last, pt_zero]

theorem BoundedSetting.integral_sq_qvSum_le [IsProbabilityMeasure P]
    (h : BoundedSetting ℱ P X A Q C) (i : Fin n) {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) :
    ∫ ω, qvSum X A i s t m ω ^ 2 ∂P ≤ 18 * C ^ 4 := by
  have hbd := h.bd_M
  have hC := h.C_nonneg
  set T : Ω → ℝ := transform (Mp X A i) (pt s t m) (fun k ω => Mp X A i (pt s t m k) ω) (m + 1)
    with hT
  have hTint : ∫ ω, T ω ^ 2 ∂P ≤ C ^ 2 * C ^ 2 :=
    integral_sq_transform_le (h.mart_M i) (pt_mono hst m)
      (fun k => (h.mart_M i).stronglyMeasurable (pt s t m k)) (L := C) (K := C)
      (fun k => by filter_upwards [hbd] with ω hω using hω i _)
      (fun k => by filter_upwards [hbd] with ω hω using hω i _) (m + 1)
  have hTb : AEBdd P T := (sum_transform_aux (h.mart_M i) (pt_mono hst m)
      (fun k => (h.mart_M i).stronglyMeasurable (pt s t m k)) (L := C) (K := C)
      (fun k => by filter_upwards [hbd] with ω hω using hω i _)
      (fun k => by filter_upwards [hbd] with ω hω using hω i _) (m + 1)).2.1
  have hMt : AEBdd P (Mp X A i t) := AEBdd.of_stronglyMeasurable ((h.mart_M i).stronglyMeasurable t)
    (by filter_upwards [hbd] with ω hω using hω i t)
  have hMs : AEBdd P (Mp X A i s) := AEBdd.of_stronglyMeasurable ((h.mart_M i).stronglyMeasurable s)
    (by filter_upwards [hbd] with ω hω using hω i s)
  have hqv : AEBdd P (fun ω => qvSum X A i s t m ω) := by
    have : (fun ω => qvSum X A i s t m ω) = fun ω => Mp X A i t ω ^ 2 - Mp X A i s ω ^ 2 -
        2 * T ω := funext fun ω => qvSum_eq i m ω
    rw [this]
    exact (hMt.sq.sub hMs.sq).sub (hTb.const_mul 2)
  have hpt : ∀ᵐ ω ∂P, qvSum X A i s t m ω ^ 2 ≤
      3 * (C ^ 4 + C ^ 4 + 4 * T ω ^ 2) := by
    filter_upwards [hbd] with ω hω
    rw [qvSum_eq i m ω]
    have h1 : Mp X A i t ω ^ 2 ≤ C ^ 2 := by
      have := sq_le_sq' (abs_le.1 (hω i t)).1 (abs_le.1 (hω i t)).2
      simpa using this
    have h2 : Mp X A i s ω ^ 2 ≤ C ^ 2 := by
      have := sq_le_sq' (abs_le.1 (hω i s)).1 (abs_le.1 (hω i s)).2
      simpa using this
    have h3 : 0 ≤ Mp X A i t ω ^ 2 := sq_nonneg _
    have h4 : 0 ≤ Mp X A i s ω ^ 2 := sq_nonneg _
    nlinarith [sq_nonneg (Mp X A i t ω ^ 2 + Mp X A i s ω ^ 2 - 2 * T ω),
      sq_nonneg (Mp X A i t ω ^ 2 - Mp X A i s ω ^ 2 + 2 * T ω),
      sq_nonneg (Mp X A i t ω ^ 2 + Mp X A i s ω ^ 2), mul_nonneg h3 h4,
      mul_self_nonneg (Mp X A i t ω ^ 2 - Mp X A i s ω ^ 2),
      mul_self_nonneg (Mp X A i t ω ^ 2 - Mp X A i s ω ^ 2 - 2 * T ω),
      mul_self_nonneg (Mp X A i t ω ^ 2 - 2 * T ω), mul_self_nonneg (Mp X A i s ω ^ 2 + 2 * T ω)]
  calc ∫ ω, qvSum X A i s t m ω ^ 2 ∂P ≤ ∫ ω, 3 * (C ^ 4 + C ^ 4 + 4 * T ω ^ 2) ∂P :=
        integral_mono_ae hqv.sq.integrable
          ((((AEBdd.const _).add (AEBdd.const _)).add ((hTb.sq).const_mul 4)).const_mul 3
            ).integrable hpt
    _ = 3 * (C ^ 4 + C ^ 4 + 4 * ∫ ω, T ω ^ 2 ∂P) := by
        have e : ∫ ω, (C ^ 4 + C ^ 4 + 4 * T ω ^ 2) ∂P = C ^ 4 + C ^ 4 + 4 * ∫ ω, T ω ^ 2 ∂P := by
          rw [integral_add (f := fun _ => C ^ 4 + C ^ 4) (g := fun ω => 4 * T ω ^ 2)
            (integrable_const _) (hTb.sq.const_mul 4).integrable, integral_const_mul]
          simp
        rw [integral_const_mul, e]
    _ ≤ 18 * C ^ 4 := by nlinarith [pow_nonneg hC 4]

theorem norm_sq_le_sum_sq (x : Fin n → ℝ) : ‖x‖ ^ 2 ≤ ∑ i, x i ^ 2 := by
  have h0 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hle : ‖x‖ ≤ Real.sqrt (∑ i, x i ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun i => x i ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  calc ‖x‖ ^ 2 ≤ Real.sqrt (∑ i, x i ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = ∑ i, x i ^ 2 := Real.sq_sqrt h0

theorem sum_sq_le_sq_sum_abs (x : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range N, x k ^ 2 ≤ (∑ k ∈ Finset.range N, |x k|) ^ 2 := by
  set S : ℝ := ∑ k ∈ Finset.range N, |x k| with hS
  calc ∑ k ∈ Finset.range N, x k ^ 2 ≤ ∑ k ∈ Finset.range N, |x k| * S := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [← sq_abs, sq]
        exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun k => |x k|)
          (fun j _ => abs_nonneg _) hk) (abs_nonneg _)
    _ = S ^ 2 := by rw [← Finset.sum_mul, sq]

variable (X) in
/-- `∑ₖ ‖X_{tₖ₊₁} - X_{tₖ}‖²` along the `(m + 1)`-piece partition of `[s, t]`. -/
noncomputable def incrSq (s t : ℝ≥0) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), ‖X (pt s t m (k + 1)) ω - X (pt s t m k) ω‖ ^ 2

theorem incrSq_nonneg (s t : ℝ≥0) (m : ℕ) (ω : Ω) : 0 ≤ incrSq X s t m ω :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Pathwise: `∑ ‖ΔX‖² ≤ ∑ᵢ (2 ∑ (ΔMⁱ)² + 2 C²)`. -/
theorem incrSq_le {ω : Ω}
    (hA : ∀ i (t : ℝ≥0), IntervalIntegrable (fun s : ℝ => A s.toNNReal ω i) volume 0 t)
    (hAC : ∀ i (t : ℝ≥0), ∫ s in (0 : ℝ)..(t : ℝ), |A s.toNNReal ω i| ≤ C)
    {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) :
    incrSq X s t m ω ≤ ∑ i, (2 * qvSum X A i s t m ω + 2 * C ^ 2) := by
  unfold incrSq
  have hk : ∀ k ∈ Finset.range (m + 1),
      ‖X (pt s t m (k + 1)) ω - X (pt s t m k) ω‖ ^ 2 ≤ ∑ i,
        (2 * (Mp X A i (pt s t m (k + 1)) ω - Mp X A i (pt s t m k) ω) ^ 2 +
          2 * (pathIntegral (fun s ω => A s ω i) (pt s t m (k + 1)) ω -
            pathIntegral (fun s ω => A s ω i) (pt s t m k) ω) ^ 2) := by
    intro k _
    refine (norm_sq_le_sum_sq _).trans (Finset.sum_le_sum fun i _ => ?_)
    have e : (X (pt s t m (k + 1)) ω - X (pt s t m k) ω) i =
        (Mp X A i (pt s t m (k + 1)) ω - Mp X A i (pt s t m k) ω) +
          (pathIntegral (fun s ω => A s ω i) (pt s t m (k + 1)) ω -
            pathIntegral (fun s ω => A s ω i) (pt s t m k) ω) := by
      simp only [Pi.sub_apply, Mp]; ring
    rw [e]
    nlinarith [sq_nonneg ((Mp X A i (pt s t m (k + 1)) ω - Mp X A i (pt s t m k) ω) -
          (pathIntegral (fun s ω => A s ω i) (pt s t m (k + 1)) ω -
            pathIntegral (fun s ω => A s ω i) (pt s t m k) ω))]
  refine (Finset.sum_le_sum hk).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  unfold qvSum
  refine add_le_add le_rfl ?_
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hdD : ∀ k ∈ Finset.range (m + 1),
      pathIntegral (fun s ω => A s ω i) (pt s t m (k + 1)) ω -
        pathIntegral (fun s ω => A s ω i) (pt s t m k) ω =
      pieceInt (fun u => A u.toNNReal ω i) (s : ℝ) (t : ℝ) m k := by
    intro k hk
    have hk' : k + 1 ≤ m + 1 := Nat.succ_le_succ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
    rw [pathIntegral_sub_eq (hA i)]
    simp only [pieceInt, coe_pt hst m hk', coe_pt hst m ((Nat.le_succ k).trans hk')]
  have hint : IntervalIntegrable (fun u : ℝ => A u.toNNReal ω i) volume (s : ℝ) (t : ℝ) :=
    intervalIntegrable_toNNReal_mono (hA i t) hst le_rfl
  have hsum : ∑ k ∈ Finset.range (m + 1), |pieceInt (fun u => A u.toNNReal ω i) (s : ℝ) (t : ℝ) m k|
      ≤ C := (sum_abs_integral_ptR_le (NNReal.coe_le_coe.2 hst) hint m).trans
    ((integral_abs_le_of_le (hA i t) hst).trans (hAC i t))
  rw [Finset.sum_congr rfl fun k hk => by rw [hdD k hk]]
  refine (sum_sq_le_sq_sum_abs (fun k => pieceInt (fun u => A u.toNNReal ω i) (s : ℝ) (t : ℝ) m k)
    (m + 1)).trans ?_
  have h0 : 0 ≤ ∑ k ∈ Finset.range (m + 1),
      |pieceInt (fun u => A u.toNNReal ω i) (s : ℝ) (t : ℝ) m k| :=
    Finset.sum_nonneg fun k _ => abs_nonneg _
  nlinarith

theorem BoundedSetting.aebdd_qvSum [IsProbabilityMeasure P] (h : BoundedSetting ℱ P X A Q C)
    (i : Fin n) {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) : AEBdd P (qvSum X A i s t m) := by
  have hbd := h.bd_M
  have hTb : AEBdd P (transform (Mp X A i) (pt s t m) (fun k ω => Mp X A i (pt s t m k) ω)
      (m + 1)) := (sum_transform_aux (h.mart_M i) (pt_mono hst m)
      (fun k => (h.mart_M i).stronglyMeasurable (pt s t m k)) (L := C) (K := C)
      (fun k => by filter_upwards [hbd] with ω hω using hω i _)
      (fun k => by filter_upwards [hbd] with ω hω using hω i _) (m + 1)).2.1
  have hMt : AEBdd P (Mp X A i t) := AEBdd.of_stronglyMeasurable ((h.mart_M i).stronglyMeasurable t)
    (by filter_upwards [hbd] with ω hω using hω i t)
  have hMs : AEBdd P (Mp X A i s) := AEBdd.of_stronglyMeasurable ((h.mart_M i).stronglyMeasurable s)
    (by filter_upwards [hbd] with ω hω using hω i s)
  have : qvSum X A i s t m = fun ω => Mp X A i t ω ^ 2 - Mp X A i s ω ^ 2 -
      2 * transform (Mp X A i) (pt s t m) (fun k ω => Mp X A i (pt s t m k) ω) (m + 1) ω :=
    funext fun ω => qvSum_eq i m ω
  rw [this]
  exact (hMt.sq.sub hMs.sq).sub (hTb.const_mul 2)

theorem BoundedSetting.aebdd_incrSq [IsProbabilityMeasure P] (h : BoundedSetting ℱ P X A Q C)
    {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) : AEBdd P (incrSq X s t m) := by
  have hmeas : AEStronglyMeasurable (incrSq X s t m) P := by
    refine Measurable.aestronglyMeasurable ?_
    unfold incrSq
    exact Finset.measurable_sum _ fun k _ =>
      (((h.measurable_X _).sub (h.measurable_X _)).norm).pow_const 2
  have hV : AEBdd P (fun ω => ∑ i, (2 * qvSum X A i s t m ω + 2 * C ^ 2)) :=
    AEBdd.finset_sum _ fun i _ => ((h.aebdd_qvSum i hst m).const_mul 2).add (AEBdd.const _)
  obtain ⟨-, b, hb⟩ := hV
  refine ⟨hmeas, b, ?_⟩
  filter_upwards [hb, h.int_A, h.abs_A] with ω h1 h2 h3
  rw [abs_of_nonneg (incrSq_nonneg (X := X) _ _ _ _)]
  exact (incrSq_le h2 h3 hst m).trans ((le_abs_self _).trans h1)

/-- The constant bounding the `L²` norm of the sum of squared increments. -/
noncomputable def incrSqBound (n : ℕ) (C : ℝ) : ℝ := n * (n * (8 * (18 * C ^ 4) + 8 * C ^ 4))

theorem BoundedSetting.integral_sq_incrSq_le [IsProbabilityMeasure P]
    (h : BoundedSetting ℱ P X A Q C) {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) :
    ∫ ω, incrSq X s t m ω ^ 2 ∂P ≤ incrSqBound n C := by
  have hqv := fun i => h.aebdd_qvSum i hst m
  have hpt : ∀ᵐ ω ∂P, incrSq X s t m ω ^ 2 ≤
      n * ∑ i, (8 * qvSum X A i s t m ω ^ 2 + 8 * C ^ 4) := by
    filter_upwards [h.int_A, h.abs_A] with ω h2 h3
    have h1 := incrSq_le (X := X) h2 h3 hst m
    have h0 := incrSq_nonneg (X := X) s t m ω
    have hsq : incrSq X s t m ω ^ 2 ≤ (∑ i, (2 * qvSum X A i s t m ω + 2 * C ^ 2)) ^ 2 :=
      pow_le_pow_left₀ h0 h1 2
    refine hsq.trans ?_
    refine (sq_sum_le_card_mul_sum_sq (s := Finset.univ)).trans ?_
    simp only [Finset.card_univ, Fintype.card_fin]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (Nat.cast_nonneg _)
    nlinarith [sq_nonneg (2 * qvSum X A i s t m ω - 2 * C ^ 2)]
  have hR : AEBdd P (fun ω => (n : ℝ) * ∑ i, (8 * qvSum X A i s t m ω ^ 2 + 8 * C ^ 4)) :=
    ((AEBdd.finset_sum _ fun i _ => ((hqv i).sq.const_mul 8).add (AEBdd.const _))).const_mul _
  calc ∫ ω, incrSq X s t m ω ^ 2 ∂P
      ≤ ∫ ω, (n : ℝ) * ∑ i, (8 * qvSum X A i s t m ω ^ 2 + 8 * C ^ 4) ∂P :=
        integral_mono_ae (h.aebdd_incrSq hst m).sq.integrable hR.integrable hpt
    _ = n * ∑ i, (8 * ∫ ω, qvSum X A i s t m ω ^ 2 ∂P + 8 * C ^ 4) := by
        rw [integral_const_mul, integral_finsetSum _ fun i _ =>
          (((hqv i).sq.const_mul 8).add (AEBdd.const _)).integrable]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_add ((hqv i).sq.const_mul 8).integrable (integrable_const _),
          integral_const_mul]
        simp
    _ ≤ n * ∑ _i : Fin n, (8 * (18 * C ^ 4) + 8 * C ^ 4) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (Nat.cast_nonneg _)
        have := h.integral_sq_qvSum_le i hst m
        linarith
    _ = incrSqBound n C := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          incrSqBound]

end QV

end ComplexSLE.Infrastructure.Ito

end
