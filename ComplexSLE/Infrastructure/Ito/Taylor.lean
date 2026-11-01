/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.LinearAlgebra.Pi

/-!
# Second-order Taylor bound with a modulus of continuity

Deterministic analysis for the bounded core of Itô's formula (`ComplexSLE.Infrastructure.Ito`).

For `F : E → ℝ` of class `C²` with `‖D²F‖ ≤ B`:

* `exists_taylor_two`: `F (x + h) = F x + DF(x) h + ½ D²F(x + ξ h)[h, h]` for some `ξ ∈ [0, 1]`
  (Lagrange remainder of `τ ↦ F (x + τ h)`);
* `modulus F r = sup {‖D²F y - D²F x‖ : ‖y - x‖ ≤ r}`: nonnegative, bounded by `2B`, monotone, and
  `≤ ε` for small `r` when `D²F` is uniformly continuous (`exists_modulus_le`);
* `abs_taylor_remainder_le`: `|F (x + h) - F x - DF(x) h - ½ D²F(x)[h, h]| ≤ ½ modulus F ‖h‖ ‖h‖²`;
* `abs_taylor_remainder_le_coord`: the same in the coordinates `Pi.single i 1` of `ℝⁿ`.
-/

@[expose] public section

open scoped Topology
open Set

namespace ComplexSLE.Infrastructure.Ito

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_taylor_two {F : E → ℝ} (hF : ContDiff ℝ 2 F) (x h : E) :
    ∃ ξ : ℝ, 0 ≤ ξ ∧ ξ ≤ 1 ∧
      F (x + h) = F x + fderiv ℝ F x h +
        (1 / 2) * iteratedFDeriv ℝ 2 F (x + ξ • h) ![h, h] := by
  set ℓ : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ h with hℓ
  have hℓa : ∀ τ, ℓ τ = τ • h := fun τ => rfl
  set f : E → ℝ := fun y => F (x + y) with hf
  have hfc : ContDiff ℝ 2 f := hF.comp (contDiff_const.add contDiff_id)
  set g : ℝ → ℝ := fun τ => F (x + τ • h) with hg
  have hgf : g = f ∘ ℓ := rfl
  have hgc : ContDiff ℝ 2 g := hfc.comp ℓ.contDiff
  obtain ⟨ξ, hξ, hξeq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (f := g) (x := 1)
    (x₀ := 0) (n := 1) (by norm_num) (by exact_mod_cast hgc.contDiffOn)
  refine ⟨ξ, ?_, ?_, ?_⟩
  · simpa using hξ.1.le
  · simpa using hξ.2.le
  · have h1 : taylorWithinEval g 1 (uIcc (0 : ℝ) 1) 0 1 = F x + fderiv ℝ F x h := by
      have hd : HasDerivAt g (fderiv ℝ F x h) 0 := by
        have h2 : HasDerivAt (fun τ : ℝ => x + τ • h) h 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add x
        have h3 : HasFDerivAt F (fderiv ℝ F x) (x + (0 : ℝ) • h) := by
          simpa using (hF.differentiable (by norm_num) x).hasFDerivAt
        exact h3.comp_hasDerivAt (0 : ℝ) h2
      have hu : UniqueDiffWithinAt ℝ (uIcc (0 : ℝ) 1) 0 :=
        uniqueDiffOn_uIcc (by norm_num) 0 (by simp)
      rw [taylor_within_apply]
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
        iteratedDerivWithin_zero, iteratedDerivWithin_one, hd.differentiableAt.derivWithin hu,
        hd.deriv]
      simp [hg]
    have h2 : iteratedDeriv (1 + 1) g ξ =
        iteratedFDeriv ℝ 2 F (x + ξ • h) ![h, h] := by
      rw [iteratedDeriv_eq_iteratedFDeriv, hgf]
      rw [ℓ.iteratedFDeriv_comp_right hfc ξ (i := 2) (by norm_cast)]
      simp only [hf, iteratedFDeriv_comp_add_left,
        ContinuousMultilinearMap.compContinuousLinearMap_apply]
      have e : (fun _ : Fin 2 => ℓ 1) = ![h, h] := by
        funext i; fin_cases i <;> simp [hℓa]
      rw [e, hℓa]
    rw [h1, h2] at hξeq
    have h3 : g 1 = F (x + h) := by simp [hg]
    rw [h3] at hξeq
    norm_num [Nat.factorial] at hξeq
    linarith


/-! ### The modulus of continuity of the second derivative -/

/-- The modulus of continuity of `D²F`: `sup {‖D²F y - D²F x‖ : ‖y - x‖ ≤ r}`. -/
noncomputable def modulus (F : E → ℝ) (r : ℝ) : ℝ :=
  sSup ((fun p : E × E => ‖iteratedFDeriv ℝ 2 F p.1 - iteratedFDeriv ℝ 2 F p.2‖) ''
    {p | ‖p.1 - p.2‖ ≤ r})

section Modulus

variable {F : E → ℝ} {B : ℝ}

theorem bddAbove_modulus (hB : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ B) (r : ℝ) :
    BddAbove ((fun p : E × E => ‖iteratedFDeriv ℝ 2 F p.1 - iteratedFDeriv ℝ 2 F p.2‖) ''
      {p | ‖p.1 - p.2‖ ≤ r}) := by
  refine ⟨2 * B, ?_⟩
  rintro _ ⟨p, -, rfl⟩
  calc ‖iteratedFDeriv ℝ 2 F p.1 - iteratedFDeriv ℝ 2 F p.2‖
      ≤ ‖iteratedFDeriv ℝ 2 F p.1‖ + ‖iteratedFDeriv ℝ 2 F p.2‖ := norm_sub_le _ _
    _ ≤ 2 * B := by linarith [hB p.1, hB p.2]

theorem norm_sub_le_modulus (hB : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ B) {x y : E} {r : ℝ}
    (hxy : ‖x - y‖ ≤ r) :
    ‖iteratedFDeriv ℝ 2 F x - iteratedFDeriv ℝ 2 F y‖ ≤ modulus F r :=
  le_csSup (bddAbove_modulus hB r) ⟨(x, y), hxy, rfl⟩

theorem modulus_nonneg (F : E → ℝ) (r : ℝ) : 0 ≤ modulus F r :=
  Real.sSup_nonneg (by rintro _ ⟨p, -, rfl⟩; exact norm_nonneg _)

theorem modulus_le (hB : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ B) (r : ℝ) :
    modulus F r ≤ 2 * B := by
  by_cases hne : ({p : E × E | ‖p.1 - p.2‖ ≤ r}).Nonempty
  · refine csSup_le (hne.image _) ?_
    rintro _ ⟨p, -, rfl⟩
    calc ‖iteratedFDeriv ℝ 2 F p.1 - iteratedFDeriv ℝ 2 F p.2‖
        ≤ ‖iteratedFDeriv ℝ 2 F p.1‖ + ‖iteratedFDeriv ℝ 2 F p.2‖ := norm_sub_le _ _
      _ ≤ 2 * B := by linarith [hB p.1, hB p.2]
  · have : ({p : E × E | ‖p.1 - p.2‖ ≤ r}) = ∅ := Set.not_nonempty_iff_eq_empty.1 hne
    simp only [modulus, this, Set.image_empty, Real.sSup_empty]
    linarith [(norm_nonneg _).trans (hB 0)]

theorem modulus_mono (hB : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ B) : Monotone (modulus F) := by
  intro r r' hrr
  by_cases hne : ({p : E × E | ‖p.1 - p.2‖ ≤ r}).Nonempty
  · refine csSup_le_csSup (bddAbove_modulus hB r') (hne.image _) ?_
    exact Set.image_mono fun p hp => le_trans hp hrr
  · have : ({p : E × E | ‖p.1 - p.2‖ ≤ r}) = ∅ := Set.not_nonempty_iff_eq_empty.1 hne
    simp only [modulus, this, Set.image_empty, Real.sSup_empty]
    exact modulus_nonneg F r'

/-- Uniform continuity of `D²F` makes the modulus small for small radii. -/
theorem exists_modulus_le
    (huc : UniformContinuous (iteratedFDeriv ℝ 2 F)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ r, r ≤ δ → modulus F r ≤ ε := by
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuous_iff.1 huc (ε / 2) (half_pos hε)
  refine ⟨δ / 2, half_pos hδ, fun r hr => ?_⟩
  by_cases hne : ({p : E × E | ‖p.1 - p.2‖ ≤ r}).Nonempty
  · refine csSup_le (hne.image _) ?_
    rintro _ ⟨p, hp, rfl⟩
    have hd : dist p.1 p.2 < δ := by
      rw [dist_eq_norm]; linarith [hp.out]
    have := h hd
    rw [dist_eq_norm] at this
    simp only
    linarith
  · have : ({p : E × E | ‖p.1 - p.2‖ ≤ r}) = ∅ := Set.not_nonempty_iff_eq_empty.1 hne
    simp only [modulus, this, Set.image_empty, Real.sSup_empty]
    exact hε.le

end Modulus

/-- **Second-order Taylor bound** with the modulus of continuity of `D²F`. -/
theorem abs_taylor_remainder_le {F : E → ℝ} {B : ℝ} (hF : ContDiff ℝ 2 F)
    (hB : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ B) (x h : E) :
    |F (x + h) - F x - fderiv ℝ F x h - (1 / 2) * iteratedFDeriv ℝ 2 F x ![h, h]| ≤
      (1 / 2) * modulus F ‖h‖ * ‖h‖ ^ 2 := by
  obtain ⟨ξ, hξ0, hξ1, hξ⟩ := exists_taylor_two hF x h
  have hnorm : ‖(x + ξ • h) - x‖ ≤ ‖h‖ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hξ0]
    exact mul_le_of_le_one_left (norm_nonneg _) hξ1
  have h1 := norm_sub_le_modulus hB hnorm
  have h2 : |(iteratedFDeriv ℝ 2 F (x + ξ • h) - iteratedFDeriv ℝ 2 F x) ![h, h]| ≤
      modulus F ‖h‖ * ‖h‖ ^ 2 := by
    have := (iteratedFDeriv ℝ 2 F (x + ξ • h) - iteratedFDeriv ℝ 2 F x).le_opNorm ![h, h]
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [sq]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have e : F (x + h) - F x - fderiv ℝ F x h - (1 / 2) * iteratedFDeriv ℝ 2 F x ![h, h] =
      (1 / 2) * ((iteratedFDeriv ℝ 2 F (x + ξ • h) - iteratedFDeriv ℝ 2 F x) ![h, h]) := by
    rw [hξ]; simp only [sub_apply]; ring
  rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  nlinarith

/-! ### Coordinates in `ℝⁿ` -/

section Coordinates

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]

theorem apply_eq_sum_single (L : (Fin n → ℝ) →L[ℝ] M) (h : Fin n → ℝ) :
    L h = ∑ i, h i • L (Pi.single i 1) := by
  have := LinearMap.pi_apply_eq_sum_univ (L : (Fin n → ℝ) →ₗ[ℝ] M) h
  rw [ContinuousLinearMap.coe_coe] at this
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

theorem fderiv_apply_eq_sum (F : (Fin n → ℝ) → ℝ) (x h : Fin n → ℝ) :
    fderiv ℝ F x h = ∑ i, h i * fderiv ℝ F x (Pi.single i 1) :=
  apply_eq_sum_single (M := ℝ) (fderiv ℝ F x) h

theorem iteratedFDeriv_two_apply_eq_sum (F : (Fin n → ℝ) → ℝ) (y h : Fin n → ℝ) :
    iteratedFDeriv ℝ 2 F y ![h, h] =
      ∑ i, ∑ j, h i * h j * iteratedFDeriv ℝ 2 F y ![Pi.single i 1, Pi.single j 1] := by
  have key : ∀ u v : Fin n → ℝ, iteratedFDeriv ℝ 2 F y ![u, v] =
      ∑ i, ∑ j, u i * v j * iteratedFDeriv ℝ 2 F y ![Pi.single i 1, Pi.single j 1] := by
    intro u v
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [apply_eq_sum_single (M := (Fin n → ℝ) →L[ℝ] ℝ) (fderiv ℝ (fderiv ℝ F) y) u,
      sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_apply, apply_eq_sum_single (M := ℝ) _ v, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [smul_eq_mul]
    ring
  exact key h h

/-- Second-order Taylor bound in coordinates. -/
theorem abs_taylor_remainder_le_coord {F : (Fin n → ℝ) → ℝ} {B : ℝ} (hF : ContDiff ℝ 2 F)
    (hB : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ B) (x h : Fin n → ℝ) :
    |F (x + h) - F x - ∑ i, h i * fderiv ℝ F x (Pi.single i 1) -
        (1 / 2) * ∑ i, ∑ j, h i * h j * iteratedFDeriv ℝ 2 F x ![Pi.single i 1, Pi.single j 1]| ≤
      (1 / 2) * modulus F ‖h‖ * ‖h‖ ^ 2 := by
  have := abs_taylor_remainder_le hF hB x h
  rwa [fderiv_apply_eq_sum, iteratedFDeriv_two_apply_eq_sum] at this

end Coordinates

end ComplexSLE.Infrastructure.Ito

end
