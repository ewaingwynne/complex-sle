/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.KoebeChainInv
public import ComplexSLE.Internal.Phases.KoebeHit
public import ComplexSLE.Internal.Loewner.Concatenation
public import ComplexSLE.Internal.Loewner.Injective
public import ComplexSLE.Internal.Polar.PolarDeriv
public import ComplexSLE.Frozen.Defs.RightHull
public import ComplexSLE.Frozen.Defs.LeftHull
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The Koebe chain (3.17)-(3.28) of Step 3 of `lem-converse-w-o-upgrade` (M7/E3, deterministic)

Source: paper.tex:L1655-1672 (Step 1 setup), L1700-1785 (Step 3: `eqn-two-formulas` ...
`eqn-dist-esc`, giving `eqn-dist-3`). Dependency-graph steps `step:hulls-compact`,
`step:future-point-outside-hulls`, `step:zero-in-future-left-hull`.

For a continuous driver `U`, times `t, s ≥ 0` and a point `z ∉ L_{s+t}` (the paper's
`s + t < T_z`), write `f_t(z) = fPath U hU z t`, `f_t'(z) = derivPath U hU z t`,
`L_{t,s+t} = leftHull V s` for the future driver `V = U(· + t) - U t`, `R_t = rightHull U hU t`.

* `koebeEvent` is the event `E_s` of `eqn-dist-event`:
  `dist(f_t z, L_{t,s+t}) ≤ dist(f_t z, R_t)`.
* **`koebe_chain`** is `eqn-dist-3` with the **explicit universal constant
  `C = koebeC = log (koebeK ^ 2) = log 2304`** (`koebeK = 48` is the Koebe constant of
  `KoebeChainInv.lean`; the sharp Koebe `1/4` would give `koebeK = 4` and `C = log 16`):

  `log(dist(f_t z, L_{t,s+t}) / |f_t z|) - log dist(z, L_{s+t})
     ≤ 1_{E_s} log(|f_t'(z)| / |f_t z|) + 1_{E_s^c} log(1 / dist(z, L_t)) + koebeC`.

  The multiplicative forms are `koebe_chain_of_event` (on `E_s` the left ratio is
  `≤ koebeK |f_t'(z)| / |f_t z|`) and `koebe_chain_of_not_event` (on `E_s^c` it is
  `≤ koebeK² / dist(z, L_t)`).

## Route (a substitution of the paper's route; reported, not a statement change)

The paper derives `eqn-dist-3` through the two-sided Koebe relations (3.7), (3.8), (3.9) for
`f_{t,s+t}` and the case analysis (3.11)-(3.16). Only three facts are needed:

1. `f_t` maps `ℂ ∖ L_{s+t}` *onto* `ℂ ∖ (L_{t,s+t} ∪ R_t)` (concatenation property (2.3)), so by the
   upper bound of the Koebe covering theorem (applied to the inverse map)
   `dist(f_t z, L_{t,s+t} ∪ R_t) ≤ koebeK |f_t'(z)| dist(z, L_{s+t})`   (`eqn-koebe-t`, one half);
2. `f_t` maps `ℂ ∖ L_t` into `ℂ ∖ R_t`, so by the lower bound of the Koebe covering theorem
   `|f_t'(z)| dist(z, L_t) ≤ koebeK dist(f_t z, R_t)`              (`eqn-hit-koebe`, other half);
3. `0 ∈ L_{t,s+t}` (the future driver starts at `0`), so `dist(f_t z, L_{t,s+t}) ≤ |f_t z|`.

On `E_s`, `dist(f_t z, L_{t,s+t} ∪ R_t) = dist(f_t z, L_{t,s+t})` and (1) is `eqn-koebe-union`; on
`E_s^c`, `dist(f_t z, L_{t,s+t} ∪ R_t) = dist(f_t z, R_t)`, and (1), (2), (3) give
`dist(z, L_t) ≤ koebeK² dist(z, L_{s+t})` directly. The detour through `f_{t,s+t}` and `R_{s+t}`
(`eqn-two-formulas`, `eqn-two-formulas-b`, `eqn-two-dist-ratio`, `eqn-dist-1`, `eqn-dist-2`) is
therefore not consumed.

No EXTERNAL input is consumed here (the Koebe covering constant `1/48` is proved, see
`KoebeChainInv.lean`).
-/

public section

open scoped NNReal ENNReal
open Set Metric ComplexSLE.Internal ComplexSLE.Internal.Polar

namespace ComplexSLE.Internal.KoebeChain

variable {U : ℝ≥0 → ℂ}

/-- The future driver `V = U(· + t) - U t` of the concatenation property (2.3), as a function. -/
@[expose] def futureDriver (U : ℝ≥0 → ℂ) (t : ℝ≥0) : ℝ≥0 → ℂ := fun r => U (r + t) - U t

theorem continuous_futureDriver (hU : Continuous U) (t : ℝ≥0) : Continuous (futureDriver U t) := by
  unfold futureDriver; fun_prop

/-- The event `E_s` (`eqn-dist-event`, paper.tex:L1744-1747):
`dist(f_t z, L_{t,s+t}) ≤ dist(f_t z, R_t)`. -/
@[expose] noncomputable def koebeEvent (U : ℝ≥0 → ℂ) (hU : Continuous U) (t s : ℝ≥0) (z : ℂ) :
    Prop :=
  infDist (fPath U hU z t) (leftHull (futureDriver U t) s) ≤
    infDist (fPath U hU z t) (rightHull U hU t)

/-! ### `f_t` as a holomorphic injective map -/

/-- `w ↦ f_t(w)` is holomorphic on `ℂ ∖ L_t`. -/
theorem differentiableOn_fPath (hU : Continuous U) (t : ℝ≥0) :
    DifferentiableOn ℂ (fun w => fPath U hU w t) (leftHull U t)ᶜ :=
  (differentiableOn_solPath_initial hU t).sub_const _

/-- `w ↦ f_t(w)` is injective on `ℂ ∖ L_t` (backward uniqueness). -/
theorem injOn_fPath (hU : Continuous U) (t : ℝ≥0) :
    InjOn (fun w => fPath U hU w t) (leftHull U t)ᶜ := by
  intro a ha b hb h
  have e := centeredLoewnerMap_injective hU t (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) (by
    rw [centeredLoewnerMap_eq_fPath hU t ha, centeredLoewnerMap_eq_fPath hU t hb]
    exact h)
  exact congrArg Subtype.val e

/-- `f_t'(w) = derivPath ≠ 0` on `ℂ ∖ L_t`. -/
theorem deriv_fPath_ne_zero (hU : Continuous U) {t : ℝ≥0} {w : ℂ} (hw : w ∈ (leftHull U t)ᶜ) :
    deriv (fun w => fPath U hU w t) w ≠ 0 := by
  rw [deriv_fPath_initial hU (coe_mem_lifeSet_iff.2 hw)]
  exact derivPath_ne_zero hU w t

theorem norm_deriv_fPath (hU : Continuous U) {t : ℝ≥0} {w : ℂ} (hw : w ∈ (leftHull U t)ᶜ) :
    ‖deriv (fun w => fPath U hU w t) w‖ = ‖derivPath U hU w t‖ := by
  rw [deriv_fPath_initial hU (coe_mem_lifeSet_iff.2 hw)]

/-! ### The concatenation facts used by the chain -/

section Concat

variable (hU : Continuous U) (t s : ℝ≥0)

theorem notMem_leftHull_of_notMem_add {z : ℂ} (hz : z ∉ leftHull U (s + t)) :
    z ∉ leftHull U t := fun h => hz (leftHull_mono le_add_self h)

/-- `f_t(z) ∈ L_{t,s+t} ↔ z ∈ L_{s+t}` for `z ∉ L_t` (concatenation property (2.3)). -/
theorem fPath_mem_leftHull_iff {z : ℂ} (hz₁ : z ∉ leftHull U t) :
    fPath U hU z t ∈ leftHull (futureDriver U t) s ↔ z ∈ leftHull U (s + t) := by
  rw [← centeredLoewnerMap_eq_fPath hU t hz₁]
  exact (mem_leftHull_add_iff hU s t z hz₁).symm

/-- `f_t` maps `ℂ ∖ L_{s+t}` into `ℂ ∖ (L_{t,s+t} ∪ R_t)`. -/
theorem fPath_notMem_union {z : ℂ} (hz : z ∉ leftHull U (s + t)) :
    fPath U hU z t ∉ leftHull (futureDriver U t) s ∪ rightHull U hU t := by
  have hz₁ := notMem_leftHull_of_notMem_add t s hz
  rintro (h | h)
  · exact hz ((fPath_mem_leftHull_iff hU t s hz₁).1 h)
  · rw [← centeredLoewnerMap_eq_fPath hU t hz₁] at h
    exact h ⟨⟨z, hz₁⟩, rfl⟩

/-- `f_t` maps `ℂ ∖ L_t` into `ℂ ∖ R_t`. -/
theorem fPath_notMem_rightHull {z : ℂ} (hz₁ : z ∉ leftHull U t) :
    fPath U hU z t ∉ rightHull U hU t := by
  rw [← centeredLoewnerMap_eq_fPath hU t hz₁]
  exact fun h => h ⟨⟨z, hz₁⟩, rfl⟩

/-- `f_t` maps `ℂ ∖ L_{s+t}` **onto** `ℂ ∖ (L_{t,s+t} ∪ R_t)`
(`f_t(L_{s+t} ∖ L_t) = L_{t,s+t} ∖ R_t`, read as in ERRATA R18). -/
theorem compl_union_subset_image :
    (leftHull (futureDriver U t) s ∪ rightHull U hU t)ᶜ ⊆
      (fun w => fPath U hU w t) '' (leftHull U (s + t))ᶜ := by
  intro u hu
  have hR : u ∈ Set.range (centeredLoewnerMap U hU t) := by
    by_contra h
    exact hu (Or.inr h)
  obtain ⟨⟨x, hx₁⟩, rfl⟩ := hR
  refine ⟨x, ?_, centeredLoewnerMap_eq_fPath hU t hx₁ ▸ rfl⟩
  intro hx
  exact hu (Or.inl ((mem_leftHull_add_iff hU s t x hx₁).1 hx))

/-- The maps formula of (2.3) in `fPath` form: `f_{s+t}(z) = f_{t,s+t}(f_t z)` for `z ∉ L_{s+t}`. -/
theorem fPath_add_eq {z : ℂ} (hz : z ∉ leftHull U (s + t)) :
    fPath U hU z ((s + t : ℝ≥0) : ℝ) =
      fPath (futureDriver U t) (continuous_futureDriver hU t) (fPath U hU z t) s := by
  have hz₁ := notMem_leftHull_of_notMem_add t s hz
  have hz₂ : centeredLoewnerMap U hU t ⟨z, hz₁⟩ ∈ (leftHull (futureDriver U t) s)ᶜ :=
    fun h => hz ((mem_leftHull_add_iff hU s t z hz₁).2 h)
  have h := centeredLoewnerMap_add_eq hU s t z hz hz₁ hz₂
  rw [centeredLoewnerMap_eq_fPath hU (s + t) hz] at h
  have hw : fPath U hU z t ∈ (leftHull (futureDriver U t) s)ᶜ := by
    rw [← centeredLoewnerMap_eq_fPath hU t hz₁]; exact hz₂
  have e : (⟨centeredLoewnerMap U hU t ⟨z, hz₁⟩, hz₂⟩ : ↥(leftHull (futureDriver U t) s)ᶜ) =
      ⟨fPath U hU z t, hw⟩ := Subtype.ext (centeredLoewnerMap_eq_fPath hU t hz₁)
  rw [h, ← centeredLoewnerMap_eq_fPath (continuous_futureDriver hU t) s hw]
  exact congrArg (fun a => centeredLoewnerMap (futureDriver U t) (continuous_futureDriver hU t) s a)
    e

/-- **The derivative chain rule** `f_{s+t}'(z) = f_{t,s+t}'(f_t z) · f_t'(z)` for `z ∉ L_{s+t}`
(from the maps formula of (2.3), `fPath_add_eq`, and the holomorphy of the centered maps in the
initial point, `hasDerivAt_fPath_initial`). -/
theorem derivPath_add_eq {z : ℂ} (hz : z ∉ leftHull U (s + t)) :
    derivPath U hU z ((s + t : ℝ≥0) : ℝ) =
      derivPath (futureDriver U t) (continuous_futureDriver hU t) (fPath U hU z t) s *
        derivPath U hU z t := by
  have hz₁ := notMem_leftHull_of_notMem_add t s hz
  have hw : fPath U hU z t ∉ leftHull (futureDriver U t) s := fun h =>
    fPath_notMem_union hU t s hz (Or.inl h)
  have hF := hasDerivAt_fPath_initial hU (coe_mem_lifeSet_iff.2 hz₁)
  have hG := hasDerivAt_fPath_initial (continuous_futureDriver hU t) (coe_mem_lifeSet_iff.2 hw)
  have hcomp := hG.comp z hF
  have hD := hasDerivAt_fPath_initial hU (coe_mem_lifeSet_iff.2 hz)
  have hev : (fun x => fPath U hU x ((s + t : ℝ≥0) : ℝ)) =ᶠ[nhds z]
      ((fun y => fPath (futureDriver U t) (continuous_futureDriver hU t) y s) ∘
        (fun x => fPath U hU x t)) := by
    filter_upwards [(isOpen_compl_leftHull U hU (s + t)).mem_nhds hz] with x hx
    exact fPath_add_eq hU t s hx
  exact hD.unique (hcomp.congr_of_eventuallyEq hev)

end Concat

/-! ### The future hull contains `0`; positivity of the distances -/

section Positivity

variable (hU : Continuous U) (t s : ℝ≥0)

/-- `0 ∈ L_{t,s+t}`: the future driver starts at `0` (`step:zero-in-future-left-hull`, deterministic
form `V 0 ∈ L^V_s`). -/
theorem zero_mem_leftHull_futureDriver : (0 : ℂ) ∈ leftHull (futureDriver U t) s := by
  have := driver_zero_mem_leftHull (futureDriver U t) s
  simpa [futureDriver] using this

/-- `dist(f_t z, L_{t,s+t}) ≤ |f_t z|` (because `0 ∈ L_{t,s+t}`). -/
theorem infDist_futureHull_le_norm (z : ℂ) :
    infDist (fPath U hU z t) (leftHull (futureDriver U t) s) ≤ ‖fPath U hU z t‖ := by
  have := infDist_le_dist_of_mem (x := fPath U hU z t) (zero_mem_leftHull_futureDriver (U := U) t s)
  simpa [dist_eq_norm] using this

variable {t s}

/-- `f_t z ∉ L_{t,s+t}` for `z ∉ L_{s+t}` (`step:future-point-outside-hulls`). -/
theorem fPath_notMem_futureHull {z : ℂ} (hz : z ∉ leftHull U (s + t)) :
    fPath U hU z t ∉ leftHull (futureDriver U t) s := fun h =>
  fPath_notMem_union hU t s hz (Or.inl h)

theorem infDist_futureHull_pos {z : ℂ} (hz : z ∉ leftHull U (s + t)) :
    0 < infDist (fPath U hU z t) (leftHull (futureDriver U t) s) := by
  have hclosed : IsClosed (leftHull (futureDriver U t) s) :=
    isOpen_compl_iff.1 (isOpen_compl_leftHull _ (continuous_futureDriver hU t) s)
  exact (hclosed.notMem_iff_infDist_pos (leftHull_nonempty _ s)).1 (fPath_notMem_futureHull hU hz)

/-- `f_t z ≠ 0` for `z ∉ L_{s+t}` (it is outside `L_{t,s+t} ∋ 0`). -/
theorem norm_fPath_pos' {z : ℂ} (hz : z ∉ leftHull U (s + t)) : 0 < ‖fPath U hU z t‖ :=
  lt_of_lt_of_le (infDist_futureHull_pos hU hz) (infDist_futureHull_le_norm hU t s z)

end Positivity

/-! ### The Koebe covering theorem for `f_t` on the two domains of the chain -/

section Koebe

variable (hU : Continuous U) {t s : ℝ≥0} {z : ℂ}

/-- **`eqn-koebe-t`, upper half** (paper.tex:L1727-1733), explicit constant `koebeK = 48`
(the paper's `4`): `dist(f_t z, L_{t,s+t} ∪ R_t) ≤ koebeK |f_t'(z)| dist(z, L_{s+t})`. The proof
applies the Koebe covering theorem to the inverse of
`f_t : ℂ ∖ L_{s+t} → ℂ ∖ (L_{t,s+t} ∪ R_t)`. -/
theorem infDist_union_le (hz : z ∉ leftHull U (s + t)) :
    infDist (fPath U hU z t) (leftHull (futureDriver U t) s ∪ rightHull U hU t) ≤
      koebeK * (‖derivPath U hU z t‖ * infDist z (leftHull U (s + t))) := by
  have hz₁ := notMem_leftHull_of_notMem_add t s hz
  have hsub : (leftHull U (s + t))ᶜ ⊆ (leftHull U t)ᶜ := compl_subset_compl.2
    (leftHull_mono le_add_self)
  have := KoebeChain.infDist_image_le (fun w => fPath U hU w t)
    (K := leftHull U (s + t)) (K' := leftHull (futureDriver U t) s ∪ rightHull U hU t)
    (leftHull_nonempty U _) (isOpen_compl_leftHull U hU (s + t))
    ((differentiableOn_fPath hU t).mono hsub) ((injOn_fPath hU t).mono hsub)
    (fun p hp => deriv_fPath_ne_zero hU (hsub hp)) (compl_union_subset_image hU t s) hz
  rwa [norm_deriv_fPath hU hz₁] at this

/-- **`eqn-hit-koebe` / `eqn-koebe-t`, lower half** (paper.tex:L1463, L1727), explicit constant
`koebeK = 48`: `|f_t'(z)| dist(z, L_t) ≤ koebeK dist(f_t z, R_t)`. -/
theorem norm_derivPath_mul_infDist_le_infDist_rightHull (hz₁ : z ∉ leftHull U t) :
    ‖derivPath U hU z t‖ * infDist z (leftHull U t) ≤
      koebeK * infDist (fPath U hU z t) (rightHull U hU t) := by
  have := KoebeChain.norm_deriv_mul_infDist_le (fun w => fPath U hU w t)
    (K := leftHull U t) (K' := rightHull U hU t) ⟨0, zero_mem_rightHull hU t⟩
    (differentiableOn_fPath hU t) (injOn_fPath hU t)
    (fun x hx => fPath_notMem_rightHull hU t hx) (z := z)
  rwa [norm_deriv_fPath hU hz₁] at this

end Koebe

/-- The distance to a union is at least the minimum of the distances. -/
theorem min_infDist_le_infDist_union {w : ℂ} {B R : Set ℂ} (hB : B.Nonempty) :
    min (infDist w B) (infDist w R) ≤ infDist w (B ∪ R) := by
  refine (le_infDist (hB.mono subset_union_left)).2 fun y hy => ?_
  rcases hy with hy | hy
  · exact (min_le_left _ _).trans (infDist_le_dist_of_mem hy)
  · exact (min_le_right _ _).trans (infDist_le_dist_of_mem hy)

/-! ### The Koebe chain -/

section Chain

variable (hU : Continuous U) {t s : ℝ≥0} {z : ℂ}

/-- **`eqn-koebe-union`, `eqn-dist-es`** (paper.tex:L1756-1766), on the event `E_s`:
`dist(f_t z, L_{t,s+t}) / (|f_t z| dist(z, L_{s+t})) ≤ koebeK |f_t'(z)| / |f_t z|`. -/
theorem koebe_chain_of_event (hz : z ∉ leftHull U (s + t)) (hE : koebeEvent U hU t s z) :
    infDist (fPath U hU z t) (leftHull (futureDriver U t) s) / ‖fPath U hU z t‖ /
        infDist z (leftHull U (s + t)) ≤
      koebeK * (‖derivPath U hU z t‖ / ‖fPath U hU z t‖) := by
  have hz₁ := notMem_leftHull_of_notMem_add t s hz
  have hdL : 0 < infDist z (leftHull U (s + t)) := infDist_leftHull_pos hU hz
  have hw : 0 < ‖fPath U hU z t‖ := norm_fPath_pos' hU hz
  have hmin := min_infDist_le_infDist_union (w := fPath U hU z t) (R := rightHull U hU t)
    (⟨_, zero_mem_leftHull_futureDriver (U := U) t s⟩ : (leftHull (futureDriver U t) s).Nonempty)
  rw [min_eq_left hE] at hmin
  have h1 := infDist_union_le hU hz
  have h2 : infDist (fPath U hU z t) (leftHull (futureDriver U t) s) ≤
      koebeK * (‖derivPath U hU z t‖ * infDist z (leftHull U (s + t))) := hmin.trans h1
  rw [div_div, div_le_iff₀ (mul_pos hw hdL)]
  calc infDist (fPath U hU z t) (leftHull (futureDriver U t) s)
      ≤ koebeK * (‖derivPath U hU z t‖ * infDist z (leftHull U (s + t))) := h2
    _ = koebeK * (‖derivPath U hU z t‖ / ‖fPath U hU z t‖) *
          (‖fPath U hU z t‖ * infDist z (leftHull U (s + t))) := by
        field_simp

/-- **`eqn-dist-2`, `eqn-dist-esc`** (paper.tex:L1768-1778), on the complement of `E_s`:
`dist(f_t z, L_{t,s+t}) / (|f_t z| dist(z, L_{s+t})) ≤ koebeK² / dist(z, L_t)`. -/
theorem koebe_chain_of_not_event (hz : z ∉ leftHull U (s + t)) (hE : ¬ koebeEvent U hU t s z) :
    infDist (fPath U hU z t) (leftHull (futureDriver U t) s) / ‖fPath U hU z t‖ /
        infDist z (leftHull U (s + t)) ≤
      koebeK ^ 2 * (1 / infDist z (leftHull U t)) := by
  have hz₁ := notMem_leftHull_of_notMem_add t s hz
  have hdL : 0 < infDist z (leftHull U (s + t)) := infDist_leftHull_pos hU hz
  have hdt : 0 < infDist z (leftHull U t) := infDist_leftHull_pos hU hz₁
  have hw : 0 < ‖fPath U hU z t‖ := norm_fPath_pos' hU hz
  have hD : 0 < ‖derivPath U hU z t‖ := norm_pos_iff.2 (derivPath_ne_zero hU z t)
  have hmin := min_infDist_le_infDist_union (w := fPath U hU z t) (R := rightHull U hU t)
    (⟨_, zero_mem_leftHull_futureDriver (U := U) t s⟩ : (leftHull (futureDriver U t) s).Nonempty)
  rw [min_eq_right (not_le.1 hE).le] at hmin
  have h1 := infDist_union_le hU hz
  have h3 := norm_derivPath_mul_infDist_le_infDist_rightHull hU hz₁
  -- `dist(z, L_t) ≤ koebeK² dist(z, L_{s+t})`
  have h4 : infDist z (leftHull U t) ≤ koebeK ^ 2 * infDist z (leftHull U (s + t)) := by
    have : ‖derivPath U hU z t‖ * infDist z (leftHull U t) ≤
        ‖derivPath U hU z t‖ * (koebeK ^ 2 * infDist z (leftHull U (s + t))) :=
      calc ‖derivPath U hU z t‖ * infDist z (leftHull U t)
          ≤ koebeK * infDist (fPath U hU z t) (rightHull U hU t) := h3
        _ ≤ koebeK * (koebeK * (‖derivPath U hU z t‖ * infDist z (leftHull U (s + t)))) :=
          mul_le_mul_of_nonneg_left (hmin.trans h1) koebeK_pos.le
        _ = ‖derivPath U hU z t‖ * (koebeK ^ 2 * infDist z (leftHull U (s + t))) := by ring
    exact le_of_mul_le_mul_left this hD
  have h5 := infDist_futureHull_le_norm hU t s z
  rw [div_div, div_le_iff₀ (mul_pos hw hdL)]
  have h6 : infDist (fPath U hU z t) (leftHull (futureDriver U t) s) ≤
      koebeK ^ 2 * (1 / infDist z (leftHull U t)) *
        (‖fPath U hU z t‖ * infDist z (leftHull U (s + t))) := by
    have e : koebeK ^ 2 * (1 / infDist z (leftHull U t)) *
          (‖fPath U hU z t‖ * infDist z (leftHull U (s + t))) =
        ‖fPath U hU z t‖ *
          (koebeK ^ 2 * infDist z (leftHull U (s + t)) / infDist z (leftHull U t)) := by
      field_simp
    rw [e]
    calc infDist (fPath U hU z t) (leftHull (futureDriver U t) s) ≤ ‖fPath U hU z t‖ := h5
      _ ≤ ‖fPath U hU z t‖ *
          (koebeK ^ 2 * infDist z (leftHull U (s + t)) / infDist z (leftHull U t)) := by
        refine le_mul_of_one_le_right hw.le ?_
        rw [le_div_iff₀ hdt]
        linarith
  exact h6

/-- The explicit universal constant `C = log (koebeK ^ 2) = log 2304` of `koebe_chain`
(`log 16` for the sharp Koebe constant `1/4`). -/
@[expose] noncomputable def koebeC : ℝ := Real.log (koebeK ^ 2)

theorem koebeC_nonneg : 0 ≤ koebeC :=
  Real.log_nonneg (one_le_pow₀ one_le_koebeK)

/-- **`eqn-dist-3` (paper.tex:L1668-1672), with the explicit universal constant
`C = koebeC = log (koebeK ^ 2)`.**
For a continuous driver `U`, `t, s ≥ 0` and `z ∉ L_{s+t}` (i.e. `s + t < T_z`):

`log(dist(f_t z, L_{t,s+t}) / |f_t z|) - log dist(z, L_{s+t})
   ≤ 1_{E_s} log(|f_t'(z)| / |f_t z|) + 1_{E_s^c} log(1 / dist(z, L_t)) + koebeC`,

where `E_s = koebeEvent U hU t s` is `dist(f_t z, L_{t,s+t}) ≤ dist(f_t z, R_t)`
(`eqn-dist-event`). -/
theorem koebe_chain [Decidable (koebeEvent U hU t s z)] (hz : z ∉ leftHull U (s + t)) :
    Real.log (infDist (fPath U hU z t) (leftHull (futureDriver U t) s) / ‖fPath U hU z t‖) -
        Real.log (infDist z (leftHull U (s + t))) ≤
      (if koebeEvent U hU t s z then Real.log (‖derivPath U hU z t‖ / ‖fPath U hU z t‖)
        else Real.log (1 / infDist z (leftHull U t))) + koebeC := by
  have hz₁ := notMem_leftHull_of_notMem_add t s hz
  have hdL : 0 < infDist z (leftHull U (s + t)) := infDist_leftHull_pos hU hz
  have hdt : 0 < infDist z (leftHull U t) := infDist_leftHull_pos hU hz₁
  have hw : 0 < ‖fPath U hU z t‖ := norm_fPath_pos' hU hz
  have hD : 0 < ‖derivPath U hU z t‖ := norm_pos_iff.2 (derivPath_ne_zero hU z t)
  have hB : 0 < infDist (fPath U hU z t) (leftHull (futureDriver U t) s) :=
    infDist_futureHull_pos hU hz
  have hQ : 0 < infDist (fPath U hU z t) (leftHull (futureDriver U t) s) / ‖fPath U hU z t‖ :=
    div_pos hB hw
  rw [← Real.log_div hQ.ne' hdL.ne']
  by_cases hE : koebeEvent U hU t s z
  · simp only [hE, ↓reduceIte]
    have h := koebe_chain_of_event hU hz hE
    have hpos : 0 < ‖derivPath U hU z t‖ / ‖fPath U hU z t‖ := div_pos hD hw
    calc Real.log (infDist (fPath U hU z t) (leftHull (futureDriver U t) s) /
            ‖fPath U hU z t‖ / infDist z (leftHull U (s + t)))
        ≤ Real.log (koebeK * (‖derivPath U hU z t‖ / ‖fPath U hU z t‖)) :=
          Real.log_le_log (div_pos hQ hdL) h
      _ ≤ Real.log (koebeK ^ 2 * (‖derivPath U hU z t‖ / ‖fPath U hU z t‖)) :=
          Real.log_le_log (mul_pos koebeK_pos hpos) (mul_le_mul_of_nonneg_right
            (by nlinarith [one_le_koebeK]) hpos.le)
      _ = Real.log (‖derivPath U hU z t‖ / ‖fPath U hU z t‖) + koebeC := by
          rw [koebeC, Real.log_mul (pow_pos koebeK_pos 2).ne' hpos.ne', add_comm]
  · simp only [hE, ↓reduceIte]
    have h := koebe_chain_of_not_event hU hz hE
    have hpos : 0 < 1 / infDist z (leftHull U t) := by positivity
    calc Real.log (infDist (fPath U hU z t) (leftHull (futureDriver U t) s) /
            ‖fPath U hU z t‖ / infDist z (leftHull U (s + t)))
        ≤ Real.log (koebeK ^ 2 * (1 / infDist z (leftHull U t))) :=
          Real.log_le_log (div_pos hQ hdL) h
      _ = Real.log (1 / infDist z (leftHull U t)) + koebeC := by
          rw [koebeC, Real.log_mul (pow_pos koebeK_pos 2).ne' hpos.ne', add_comm]

/-- `eqn-dist-3` with the hypothesis in the paper's form `s + t < T_z`
(`notMem_leftHull_iff`). -/
theorem koebe_chain_of_lt_absorbingTime [Decidable (koebeEvent U hU t s z)]
    (hz : ((s + t : ℝ≥0) : ℝ≥0∞) < absorbingTime U z) :
    Real.log (infDist (fPath U hU z t) (leftHull (futureDriver U t) s) / ‖fPath U hU z t‖) -
        Real.log (infDist z (leftHull U (s + t))) ≤
      (if koebeEvent U hU t s z then Real.log (‖derivPath U hU z t‖ / ‖fPath U hU z t‖)
        else Real.log (1 / infDist z (leftHull U t))) + koebeC :=
  koebe_chain hU (notMem_leftHull_iff.2 hz)

/-- `eqn-dist-3` in the literal indicator form of the paper (paper.tex:L1668-1672):
`… ≤ 1_{E_s} log(|f_t'(z)| / |f_t z|) + 1_{E_s^c} log(1 / dist(z, L_t)) + koebeC`. -/
theorem koebe_chain_indicator [Decidable (koebeEvent U hU t s z)] (hz : z ∉ leftHull U (s + t)) :
    Real.log (infDist (fPath U hU z t) (leftHull (futureDriver U t) s) / ‖fPath U hU z t‖) -
        Real.log (infDist z (leftHull U (s + t))) ≤
      (if koebeEvent U hU t s z then (1 : ℝ) else 0) *
          Real.log (‖derivPath U hU z t‖ / ‖fPath U hU z t‖) +
        (if koebeEvent U hU t s z then (0 : ℝ) else 1) *
          Real.log (1 / infDist z (leftHull U t)) + koebeC := by
  have h := koebe_chain hU hz
  by_cases hE : koebeEvent U hU t s z
  · simpa [hE] using h
  · simpa [hE] using h

end Chain

end ComplexSLE.Internal.KoebeChain

end
