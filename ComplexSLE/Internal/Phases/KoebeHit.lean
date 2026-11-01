/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.PolarDeriv
public import ComplexSLE.Internal.Loewner.Injective
public import ComplexSLE.Internal.Hull.Basic
public import ComplexSLE.Frozen.Defs.RightHull
public import ComplexSLE.Internal.Phases.KoebeChainInv
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The Koebe hitting bound (3.13) and `0 ∈ R_t` (M7/D1, `eqn-hit-koebe`, deterministic)

Source: paper.tex:L1460-1466 (`eqn-hit-koebe`), dependency-graph node `step:zero-in-right-hull`
(`SOURCE_GAP`). For a continuous driver `U` and `t ≥ 0`:

* `zero_mem_rightHull`: `0 ∈ R_t = ℂ ∖ f_t(ℂ ∖ L_t)`, because `f_t(w) = g_t(w) - U_t ≠ 0` for
  `w ∉ L_t` (`loewnerMap_ne_driver`);
* `norm_derivPath_mul_infDist_le` (**Koebe hitting bound**): if `d = dist(z, L_t) > 0` then

  `|f_t'(z)| · d ≤ koebeK |f_t(z)|`   (`koebeK = 48`).

  Proof: `f_t` is holomorphic (`differentiableOn_solPath_initial`) and injective
  (`centeredLoewnerMap_injective`) on the disc `B(z, d) ⊆ ℂ ∖ L_t`, with `f_t'(z) = derivPath`
  (`hasDerivAt_fPath_initial`). The Koebe covering theorem
  (`QuantumZipper.CA.Koebe.ball_subset_image_koebe`, constant `1/koebeK = 1/48` in place of the
  sharp `1/4`) applied to `F(ζ) = f_t(z + d ζ)` shows that the image of the unit disc contains
  `B(F 0, |F'(0)| / koebeK) = B(f_t(z), d |f_t'(z)| / koebeK)`, while `0` is not in it
  (`0 ∈ R_t`), hence `d |f_t'(z)| / koebeK ≤ |f_t(z)|`.

The bound is stated for `f_t'(z) = derivPath U hU z t` and, equivalently, for the complex
derivative `deriv (fun w => fPath U hU w t) z` of `w ↦ f_t(w) = g_t(w) - U_t`
(`norm_deriv_fPath_mul_infDist_le`).
-/

public section

open scoped NNReal ENNReal
open Set Metric

namespace ComplexSLE.Internal

variable {U : ℝ≥0 → ℂ}

/-- **`0 ∈ R_t`** (`step:zero-in-right-hull`): for every continuous driver and every `t ≥ 0`, `0`
lies in the right hull `R_t = ℂ ∖ f_t(ℂ ∖ L_t)`; i.e. `f_t(w) = g_t(w) - U_t ≠ 0` for `w ∉ L_t`. -/
theorem zero_mem_rightHull (hU : Continuous U) (t : ℝ≥0) : (0 : ℂ) ∈ rightHull U hU t := by
  rintro ⟨z, hz⟩
  refine loewnerMap_ne_driver hU t z (sub_eq_zero.1 ?_)
  simpa [centeredLoewnerMap] using hz

end ComplexSLE.Internal

namespace ComplexSLE.Internal.Polar

variable {U : ℝ≥0 → ℂ}

/-- The centered map `w ↦ f_t(w)` never takes the value `0` on `ℂ ∖ L_t` (`0 ∈ R_t`),
in the form `fPath U hU w t ≠ 0` for `w ∉ L_t`. -/
theorem fPath_coe_ne_zero (hU : Continuous U) {w : ℂ} {t : ℝ≥0} (hw : w ∈ (leftHull U t)ᶜ) :
    fPath U hU w t ≠ 0 :=
  fPath_ne_zero hU (coe_mem_lifeSet_iff.2 hw)

/-- The disc `B(z, dist(z, L_t))` does not meet `L_t`. -/
theorem ball_infDist_subset_compl_leftHull (z : ℂ) (t : ℝ≥0) :
    ball z (infDist z (leftHull U t)) ⊆ (leftHull U t)ᶜ := by
  intro w hw hwL
  have h1 := infDist_le_dist_of_mem (x := z) hwL
  rw [mem_ball, dist_comm] at hw
  exact absurd hw (not_lt.2 h1)

/-- **The Koebe hitting bound (3.13)** (paper.tex:L1460-1466, `eqn-hit-koebe`): for `t ≥ 0` and
`z` with `d = dist(z, L_t) > 0` (so `z ∉ L_t`),

  `|f_t'(z)| · dist(z, L_t) ≤ koebeK |f_t(z)|`   (`koebeK = 48`, see `KoebeChain.koebeK`),

where `f_t'(z) = derivPath U hU z t` is the derivative of `w ↦ f_t(w)` at `z`. The paper's constant
`4` (sharp Koebe `1/4`) is replaced by the universal constant `koebeK = 48`. -/
theorem norm_derivPath_mul_infDist_le (hU : Continuous U) {z : ℂ} {t : ℝ≥0}
    (hd : 0 < infDist z (leftHull U t)) :
    ‖derivPath U hU z t‖ * infDist z (leftHull U t) ≤ KoebeChain.koebeK * ‖fPath U hU z t‖ := by
  set d : ℝ := infDist z (leftHull U t) with hdd
  have hball : ball z d ⊆ (leftHull U t)ᶜ := ball_infDist_subset_compl_leftHull z t
  -- the affine parametrisation of the disc `B(z, d)` by the unit disc
  have hmaps : ∀ ζ ∈ ball (0 : ℂ) 1, z + (d : ℂ) * ζ ∈ (leftHull U t)ᶜ := by
    intro ζ hζ
    refine hball ?_
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hd.le]
    have : ‖ζ‖ < 1 := by simpa using hζ
    nlinarith
  set F : ℂ → ℂ := fun ζ => fPath U hU (z + (d : ℂ) * ζ) t with hF
  have hderiv : ∀ ζ ∈ ball (0 : ℂ) 1,
      HasDerivAt F (derivPath U hU (z + (d : ℂ) * ζ) t * (d : ℂ)) ζ := by
    intro ζ hζ
    have h1 := hasDerivAt_fPath_initial hU (coe_mem_lifeSet_iff.2 (hmaps ζ hζ))
    have h2 : HasDerivAt (fun ζ : ℂ => z + (d : ℂ) * ζ) (d : ℂ) ζ := by
      simpa using ((hasDerivAt_id ζ).const_mul (d : ℂ)).const_add z
    exact h1.comp ζ h2
  have hdiff : DifferentiableOn ℂ F (ball (0 : ℂ) 1) := fun ζ hζ =>
    (hderiv ζ hζ).differentiableAt.differentiableWithinAt
  have hd0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.ne'
  have hinj : InjOn F (ball (0 : ℂ) 1) := by
    intro ζ₁ h₁ ζ₂ h₂ h
    have e := centeredLoewnerMap_injective hU t
      (a₁ := ⟨_, hmaps ζ₁ h₁⟩) (a₂ := ⟨_, hmaps ζ₂ h₂⟩) (by
        rw [centeredLoewnerMap_eq_fPath hU t (hmaps ζ₁ h₁),
          centeredLoewnerMap_eq_fPath hU t (hmaps ζ₂ h₂)]
        exact h)
    have e' : z + (d : ℂ) * ζ₁ = z + (d : ℂ) * ζ₂ := congrArg Subtype.val e
    exact mul_left_cancel₀ hd0 (add_left_cancel e')
  have hkoebe := QuantumZipper.CA.Koebe.ball_subset_image_koebe (c := (0 : ℂ)) (r := 1) hdiff hinj
  have hF0 : F 0 = fPath U hU z t := by simp [hF]
  have hdF0 : deriv F 0 = derivPath U hU z t * (d : ℂ) := by
    have := hderiv 0 (mem_ball_self one_pos)
    simpa using this.deriv
  -- `0` is not in the image of the unit disc
  have hzero : (0 : ℂ) ∉ F '' ball (0 : ℂ) 1 := by
    rintro ⟨ζ, hζ, hζ0⟩
    exact fPath_coe_ne_zero hU (hmaps ζ hζ) hζ0
  have hnot : (0 : ℂ) ∉ ball (F 0) (QuantumZipper.CA.Koebe.koebeCovConst * 1 * ‖deriv F 0‖) :=
    fun h => hzero (hkoebe h)
  rw [mem_ball, dist_zero_left, not_lt, hF0, hdF0, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hd.le, KoebeChain.koebeCovConst_eq_inv, mul_one, inv_mul_le_iff₀
      KoebeChain.koebeK_pos] at hnot
  linarith

/-- The Koebe hitting bound for the complex derivative of `w ↦ f_t(w) = g_t(w) - U_t` at `z`:
`|(f_t)'(z)| · dist(z, L_t) ≤ koebeK |f_t(z)|`. -/
theorem norm_deriv_fPath_mul_infDist_le (hU : Continuous U) {z : ℂ} {t : ℝ≥0}
    (hd : 0 < infDist z (leftHull U t)) :
    ‖deriv (fun w => fPath U hU w t) z‖ * infDist z (leftHull U t) ≤
      KoebeChain.koebeK * ‖fPath U hU z t‖ := by
  have hz : z ∈ (leftHull U t)ᶜ := fun h => by
    rw [infDist_zero_of_mem h] at hd
    exact lt_irrefl _ hd
  rw [deriv_fPath_initial hU (coe_mem_lifeSet_iff.2 hz)]
  exact norm_derivPath_mul_infDist_le hU hd

/-- The same for the holomorphic extension `w ↦ g_t(w) = solPath U hU w t` of the Loewner map:
`|(g_t)'(z)| = |(f_t)'(z)|`. -/
theorem norm_deriv_solPath_mul_infDist_le (hU : Continuous U) {z : ℂ} {t : ℝ≥0}
    (hd : 0 < infDist z (leftHull U t)) :
    ‖deriv (fun w => solPath U hU w t) z‖ * infDist z (leftHull U t) ≤
      KoebeChain.koebeK * ‖fPath U hU z t‖ := by
  have hz : z ∈ (leftHull U t)ᶜ := fun h => by
    rw [infDist_zero_of_mem h] at hd
    exact lt_irrefl _ hd
  rw [deriv_solPath_initial hU (coe_mem_lifeSet_iff.2 hz)]
  exact norm_derivPath_mul_infDist_le hU hd

/-- The hypothesis `0 < dist(z, L_t)` is just `z ∉ L_t` (`L_t` is closed and nonempty). -/
theorem infDist_leftHull_pos (hU : Continuous U) {z : ℂ} {t : ℝ≥0} (hz : z ∉ leftHull U t) :
    0 < infDist z (leftHull U t) := by
  have hclosed : IsClosed (leftHull U t) := isOpen_compl_iff.1 (isOpen_compl_leftHull U hU t)
  exact (hclosed.notMem_iff_infDist_pos (leftHull_nonempty U t)).1 hz

/-- **The Koebe hitting bound for `z ∉ L_t`.** -/
theorem norm_derivPath_mul_infDist_le_of_notMem (hU : Continuous U) {z : ℂ} {t : ℝ≥0}
    (hz : z ∉ leftHull U t) :
    ‖derivPath U hU z t‖ * infDist z (leftHull U t) ≤ KoebeChain.koebeK * ‖fPath U hU z t‖ :=
  norm_derivPath_mul_infDist_le hU (infDist_leftHull_pos hU hz)

end ComplexSLE.Internal.Polar

end
