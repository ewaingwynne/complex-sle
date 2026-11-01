/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Piecewise linear interpolation of a path on a fine grid

Source-independent real analysis. For `φ : ℝ≥0 → ℂ` and integers `M, K ≥ 1`, `interpSeq φ M K j` is
the sum of the first `j` steps `K⁻¹ (φ ((J + 1) / M) - φ (J / M))`, `J = i / K`: the piecewise
linear interpolation of `φ` on the coarse grid `(J / M)`, sampled on the fine grid `j / (M K)`.

* `interpSeq_succ_sub_mem`: the steps lie in any real subspace containing all values of `φ`;
* `norm_interpSeq_succ_sub_le`: the steps have norm at most `δ' / K` if `φ` oscillates by at most
  `δ'` over intervals of length `1 / M`;
* `norm_interpSeq_sub_le`: the sequence stays within `2 δ'` of `φ` on each fine step.

These give a target with drift of order the mesh, as required by the chaining argument for the
support theorem.
-/

@[expose] public section

open Finset
open scoped NNReal

namespace ComplexSLE.Infrastructure.Support

/-- Increment of `φ` over the `J`-th coarse interval `[J / M, (J + 1) / M]`. -/
noncomputable def coarseInc (φ : ℝ≥0 → ℂ) (M J : ℕ) : ℂ :=
  φ (((J + 1 : ℕ) : ℝ≥0) / M) - φ ((J : ℝ≥0) / M)

/-- The piecewise linear interpolation sequence: each coarse interval is split into `K` equal
steps. -/
noncomputable def interpSeq (φ : ℝ≥0 → ℂ) (M K : ℕ) (j : ℕ) : ℂ :=
  ∑ i ∈ range j, ((K : ℝ)⁻¹ : ℝ) • coarseInc φ M (i / K)

theorem interpSeq_zero (φ : ℝ≥0 → ℂ) (M K : ℕ) : interpSeq φ M K 0 = 0 := by
  simp [interpSeq]

theorem interpSeq_succ_sub (φ : ℝ≥0 → ℂ) (M K j : ℕ) :
    interpSeq φ M K (j + 1) - interpSeq φ M K j = ((K : ℝ)⁻¹ : ℝ) • coarseInc φ M (j / K) := by
  simp [interpSeq, Finset.sum_range_succ]

theorem interpSeq_block (φ : ℝ≥0 → ℂ) (M : ℕ) {K : ℕ} (hK : 0 < K) (J r : ℕ) (hr : r ≤ K) :
    interpSeq φ M K (J * K + r) =
      interpSeq φ M K (J * K) + ((r : ℝ) / K) • coarseInc φ M J := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hrK : r < K := by omega
    have h1 := interpSeq_succ_sub φ M K (J * K + r)
    have h2 : (J * K + r) / K = J := by
      rw [Nat.mul_comm, Nat.mul_add_div hK, Nat.div_eq_of_lt hrK, add_zero]
    rw [h2] at h1
    have h3 : J * K + (r + 1) = J * K + r + 1 := by ring
    rw [h3, show interpSeq φ M K (J * K + r + 1) = interpSeq φ M K (J * K + r) +
      ((K : ℝ)⁻¹ : ℝ) • coarseInc φ M J by rw [← h1]; ring, ih (by omega)]
    rw [add_assoc, ← add_smul]
    congr 2
    push_cast
    field_simp

theorem interpSeq_start (φ : ℝ≥0 → ℂ) (hφ0 : φ 0 = 0) (M : ℕ) {K : ℕ} (hK : 0 < K) (J : ℕ) :
    interpSeq φ M K (J * K) = φ ((J : ℝ≥0) / M) := by
  induction J with
  | zero => simp [interpSeq_zero, hφ0]
  | succ J ih =>
    have := interpSeq_block φ M hK J K le_rfl
    rw [show (J + 1) * K = J * K + K by ring, this, ih]
    have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
    rw [div_self hK', one_smul, coarseInc]
    push_cast
    ring

theorem interpSeq_succ_sub_mem {R : Submodule ℝ ℂ} {φ : ℝ≥0 → ℂ} (hφR : ∀ t, φ t ∈ R) (M K j : ℕ) :
    interpSeq φ M K (j + 1) - interpSeq φ M K j ∈ R := by
  rw [interpSeq_succ_sub]
  exact R.smul_mem _ (R.sub_mem (hφR _) (hφR _))

theorem norm_coarseInc_le {φ : ℝ≥0 → ℂ} {M : ℕ} {δ' : ℝ}
    (hmod : ∀ s s' : ℝ≥0, s ≤ s' + (M : ℝ≥0)⁻¹ → s' ≤ s + (M : ℝ≥0)⁻¹ → ‖φ s - φ s'‖ ≤ δ')
    (J : ℕ) : ‖coarseInc φ M J‖ ≤ δ' := by
  refine hmod _ _ ?_ ?_
  · push_cast
    rw [add_div, one_div]
  · refine le_trans ?_ le_self_add
    push_cast
    gcongr
    exact le_self_add

theorem norm_interpSeq_succ_sub_le {φ : ℝ≥0 → ℂ} {M : ℕ} {δ' : ℝ}
    (hmod : ∀ s s' : ℝ≥0, s ≤ s' + (M : ℝ≥0)⁻¹ → s' ≤ s + (M : ℝ≥0)⁻¹ → ‖φ s - φ s'‖ ≤ δ')
    (K j : ℕ) : ‖interpSeq φ M K (j + 1) - interpSeq φ M K j‖ ≤ δ' / K := by
  rw [interpSeq_succ_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [div_eq_inv_mul]
  gcongr
  exact norm_coarseInc_le hmod _

/-- The interpolation sequence stays close to the function on each grid step. -/
theorem norm_interpSeq_sub_le (φ : ℝ≥0 → ℂ) (hφ0 : φ 0 = 0) {M : ℕ} (hM : 0 < M) {K : ℕ}
    (hK : 0 < K) {δ' : ℝ}
    (hmod : ∀ s s' : ℝ≥0, s ≤ s' + (M : ℝ≥0)⁻¹ → s' ≤ s + (M : ℝ≥0)⁻¹ → ‖φ s - φ s'‖ ≤ δ')
    (j : ℕ) (t : ℝ≥0) (ht1 : (j : ℝ≥0) / ((M : ℝ≥0) * K) ≤ t)
    (ht2 : t ≤ ((j : ℝ≥0) + 1) / ((M : ℝ≥0) * K)) :
    ‖interpSeq φ M K j - φ t‖ ≤ 2 * δ' := by
  set J := j / K with hJ
  set r := j % K with hr
  have hrK : r < K := Nat.mod_lt _ hK
  have hjeq : j = J * K + r := (Nat.div_add_mod' j K).symm
  have hψ : interpSeq φ M K j = φ ((J : ℝ≥0) / M) + ((r : ℝ) / K) • coarseInc φ M J := by
    rw [hjeq, interpSeq_block φ M hK J r hrK.le, interpSeq_start φ hφ0 M hK]
  have h1 : ‖interpSeq φ M K j - φ ((J : ℝ≥0) / M)‖ ≤ δ' := by
    rw [hψ, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (r : ℝ) / K * ‖coarseInc φ M J‖ ≤ 1 * δ' := by
          refine mul_le_mul ?_ (norm_coarseInc_le hmod J) (norm_nonneg _) zero_le_one
          rw [div_le_one (by exact_mod_cast hK)]; exact_mod_cast hrK.le
      _ = δ' := one_mul _
  have hMK : (0 : ℝ) < (M : ℝ) * K := by positivity
  have h2 : ‖φ ((J : ℝ≥0) / M) - φ t‖ ≤ δ' := by
    refine hmod _ _ ?_ ?_
    · refine le_trans ?_ (le_trans ht1 le_self_add)
      rw [← NNReal.coe_le_coe]
      push_cast
      rw [div_le_div_iff₀ (by exact_mod_cast hM) hMK]
      have : (J : ℝ) * K ≤ j := by exact_mod_cast (by rw [hjeq]; omega : J * K ≤ j)
      nlinarith
    · refine ht2.trans ?_
      rw [← NNReal.coe_le_coe]
      push_cast
      have hM' : (0 : ℝ) < M := by exact_mod_cast hM
      have : (j : ℝ) + 1 ≤ J * K + K := by
        exact_mod_cast (by rw [hjeq]; omega : j + 1 ≤ J * K + K)
      rw [← one_div, div_add_div _ _ hM'.ne' hM'.ne', div_le_div_iff₀ hMK (by positivity)]
      nlinarith [mul_pos hM' hM']
  calc ‖interpSeq φ M K j - φ t‖ = ‖(interpSeq φ M K j - φ ((J : ℝ≥0) / M)) +
        (φ ((J : ℝ≥0) / M) - φ t)‖ := by ring_nf
    _ ≤ _ := norm_add_le _ _
    _ ≤ δ' + δ' := add_le_add h1 h2
    _ = 2 * δ' := by ring

end ComplexSLE.Infrastructure.Support

end
