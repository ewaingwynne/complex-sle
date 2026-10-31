/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.KoebeChain
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# The displays (3.7)-(3.17) of Step 3 of `lem-converse-w-o-upgrade`, with explicit constants (M7/E3)

Companion of `KoebeChain.lean`: the individual `≍` displays of the paper's Koebe chain
(paper.tex:L1700-1785), each with its universal constants made explicit (`1/4` and `4` from the
Koebe quarter theorem; products of these elsewhere). The final inequality `eqn-dist-3`
(`KoebeChain.koebe_chain`) does not consume (3.7)-(3.9), (3.11), (3.16) (see the route remark
there); they are provided for the dependency graph and for any consumer that wants the paper's
intermediate statements. Notation, for `z ∉ L_{s+t}`:

* `w = f_t z`, `y = f_{s+t} z = f_{t,s+t} w` (`fPath_add_eq`), `D = |f_t'(z)|`,
  `D' = |f_{t,s+t}'(w)|`; `B = L_{t,s+t}`, `R = R_t`, `R' = R_{t,s+t}`, `R'' = R_{s+t}`;
  `d_L = dist(z, L_{s+t})`, `d_t = dist(z, L_t)`.

| paper display | Lean |
| --- | --- |
| (3.7) `eqn-two-formulas` | `eqn_two_formulas` (constants `4`, `4`) |
| (3.8) `eqn-two-formulas'` | `eqn_two_formulas_b` (`4`, `4`) |
| (3.9) `eqn-two-dist-ratio` | `eqn_two_dist_ratio` (`16`, `16`) |
| (3.10) `eqn-koebe-t` | `eqn_koebe_t` (`4`, `4`) |
| (3.11) `eqn-dist-1` | `eqn_dist_1` (`64`) |
| (3.13) `eqn-dist-cases` | `eqn_dist_cases` |
| (3.14), (3.15) `eqn-koebe-union`, `eqn-dist-es` | `eqn_koebe_union`, `eqn_dist_es` (`4`) |
| (3.16) `eqn-dist-2` | `eqn_dist_2` (`16`) |
| (3.17) `eqn-dist-esc` | `eqn_dist_esc` (`4`, `4`, `4`); `koebe_chain_of_not_event` (`16`) |
| `step:converse-event-converges` | `eventually_koebeEvent` (deterministic form) |

Every result here consumes the EXTERNAL `koebe_quarter` (`PROVED_REL{koebe_quarter}`), except the
topological and algebraic ones.
-/

public section

open scoped NNReal ENNReal Topology
open Set Metric Filter ComplexSLE.Internal ComplexSLE.Internal.Polar

namespace ComplexSLE.Internal.KoebeChain

variable {U : ℝ≥0 → ℂ}

/-- The right hull `R_{t,s+t}` of the future map `f_{t,s+t}`. -/
noncomputable abbrev futureRightHull (U : ℝ≥0 → ℂ) (hU : Continuous U) (t s : ℝ≥0) : Set ℂ :=
  rightHull (futureDriver U t) (continuous_futureDriver hU t) s

/-- The derivative `f_{t,s+t}'(f_t z)`. -/
noncomputable abbrev futureDeriv (U : ℝ≥0 → ℂ) (hU : Continuous U) (t s : ℝ≥0)
    (z : ℂ) : ℂ :=
  derivPath (futureDriver U t) (continuous_futureDriver hU t) (fPath U hU z t) s

/-! ### Topology of the right hull -/

/-- The range of the centered map `f_t` is `f_t(ℂ ∖ L_t)`, as an image of the `fPath` extension. -/
theorem range_centeredLoewnerMap_eq (hU : Continuous U) (t : ℝ≥0) :
    Set.range (centeredLoewnerMap U hU t) = (fun w => fPath U hU w t) '' (leftHull U t)ᶜ := by
  ext u
  constructor
  · rintro ⟨⟨x, hx⟩, rfl⟩
    exact ⟨x, hx, (centeredLoewnerMap_eq_fPath hU t hx).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, centeredLoewnerMap_eq_fPath hU t hx⟩

/-- `f_t(ℂ ∖ L_t)` is open (an injective holomorphic map with nonvanishing derivative is open). -/
theorem isOpen_range_centeredLoewnerMap (hU : Continuous U) (t : ℝ≥0) :
    IsOpen (Set.range (centeredLoewnerMap U hU t)) := by
  rw [range_centeredLoewnerMap_eq, isOpen_iff_mem_nhds]
  rintro _ ⟨p, hp, rfl⟩
  have hΩ := isOpen_compl_leftHull U hU t
  have hstrict : HasStrictDerivAt (fun w => fPath U hU w t)
      (deriv (fun w => fPath U hU w t) p) p :=
    (DifferentiableOn.analyticAt (differentiableOn_fPath hU t) (hΩ.mem_nhds hp)).hasStrictDerivAt
  have hmap := hstrict.map_nhds_eq (deriv_fPath_ne_zero hU hp)
  have := Filter.image_mem_map (m := fun w => fPath U hU w t) (hΩ.mem_nhds hp)
  rwa [hmap] at this

/-- **`R_t` is closed** (the closedness half of `step:hulls-compact`). -/
theorem isClosed_rightHull (hU : Continuous U) (t : ℝ≥0) : IsClosed (rightHull U hU t) :=
  (isOpen_range_centeredLoewnerMap hU t).isClosed_compl

theorem isClosed_leftHull_union_rightHull (hU : Continuous U) (t s : ℝ≥0) :
    IsClosed (leftHull (futureDriver U t) s ∪ rightHull U hU t) :=
  (isOpen_compl_iff.1 (isOpen_compl_leftHull _ (continuous_futureDriver hU t) s)).union
    (isClosed_rightHull hU t)

theorem compl_rightHull_subset_image (hU : Continuous U) (t : ℝ≥0) :
    (rightHull U hU t)ᶜ ⊆ (fun w => fPath U hU w t) '' (leftHull U t)ᶜ := by
  rw [rightHull, compl_compl, range_centeredLoewnerMap_eq]

/-! ### Two-sided Koebe for `f_t : ℂ ∖ L_t → ℂ ∖ R_t` (`eqn-hit-koebe`, `asymp`) -/

/-- **`eqn-hit-koebe` (3.5) as a two-sided estimate** (paper.tex:L1463-1467, L1778), constants `4`:
for `z ∉ L_t`,
`|f_t'(z)| dist(z, L_t) ≤ 4 dist(f_t z, R_t)` and `dist(f_t z, R_t) ≤ 4 |f_t'(z)| dist(z, L_t)`. -/
theorem koebe_two_sided (hU : Continuous U) (t : ℝ≥0) {z : ℂ} (hz : z ∉ leftHull U t) :
    ‖derivPath U hU z t‖ * infDist z (leftHull U t) ≤
        4 * infDist (fPath U hU z t) (rightHull U hU t) ∧
      infDist (fPath U hU z t) (rightHull U hU t) ≤
        4 * (‖derivPath U hU z t‖ * infDist z (leftHull U t)) := by
  refine ⟨norm_derivPath_mul_infDist_le_infDist_rightHull hU hz, ?_⟩
  have := KoebeChain.infDist_image_le (fun w => fPath U hU w t)
    (K := leftHull U t) (K' := rightHull U hU t) (leftHull_nonempty U t)
    (isOpen_compl_leftHull U hU t) (differentiableOn_fPath hU t) (injOn_fPath hU t)
    (fun p hp => deriv_fPath_ne_zero hU hp) (compl_rightHull_subset_image hU t) hz
  rwa [norm_deriv_fPath hU hz] at this

/-! ### (3.7), (3.8), (3.10) -/

section Displays

variable (hU : Continuous U) {t s : ℝ≥0} {z : ℂ}

/-- **(3.7) `eqn-two-formulas`** (paper.tex:L1708-1714), constants `4`: Koebe for
`f_{t,s+t} : ℂ ∖ L_{t,s+t} → ℂ ∖ R_{t,s+t}` at `f_t z`, with `f_{t,s+t}(f_t z) = f_{s+t}(z)`:
`|f_{t,s+t}'(f_t z)| dist(f_t z, L_{t,s+t}) ≤ 4 dist(f_{s+t} z, R_{t,s+t})` and
`dist(f_{s+t} z, R_{t,s+t}) ≤ 4 |f_{t,s+t}'(f_t z)| dist(f_t z, L_{t,s+t})`. -/
theorem eqn_two_formulas (hz : z ∉ leftHull U (s + t)) :
    ‖futureDeriv U hU t s z‖ * infDist (fPath U hU z t) (leftHull (futureDriver U t) s) ≤
        4 * infDist (fPath U hU z ((s + t : ℝ≥0) : ℝ)) (futureRightHull U hU t s) ∧
      infDist (fPath U hU z ((s + t : ℝ≥0) : ℝ)) (futureRightHull U hU t s) ≤
        4 * (‖futureDeriv U hU t s z‖ *
          infDist (fPath U hU z t) (leftHull (futureDriver U t) s)) := by
  rw [fPath_add_eq hU t s hz]
  exact koebe_two_sided (continuous_futureDriver hU t) s (fPath_notMem_futureHull hU hz)

/-- `f_{s+t}(z) ∉ R_{s+t}` (it lies in the range of `f_{s+t}`). -/
theorem fPath_notMem_rightHull_add (hz : z ∉ leftHull U (s + t)) :
    fPath U hU z ((s + t : ℝ≥0) : ℝ) ∉ rightHull U hU (s + t) :=
  fPath_notMem_rightHull hU (s + t) hz

/-- **(3.8) `eqn-two-formulas'`** (paper.tex:L1716-1721), constants `4`: Koebe for
`f_{t,s+t}` restricted to `ℂ ∖ (L_{t,s+t} ∪ R_t) → ℂ ∖ R_{s+t}` (by `R_{s+t} = R_{t,s+t} ∪ ...`
this is the image, `mem_range_centeredLoewnerMap_add_iff`):
`|f_{t,s+t}'(f_t z)| dist(f_t z, L_{t,s+t} ∪ R_t) ≤ 4 dist(f_{s+t} z, R_{s+t})` and
`dist(f_{s+t} z, R_{s+t}) ≤ 4 |f_{t,s+t}'(f_t z)| dist(f_t z, L_{t,s+t} ∪ R_t)`. -/
theorem eqn_two_formulas_b (hz : z ∉ leftHull U (s + t)) :
    ‖futureDeriv U hU t s z‖ *
          infDist (fPath U hU z t) (leftHull (futureDriver U t) s ∪ rightHull U hU t) ≤
        4 * infDist (fPath U hU z ((s + t : ℝ≥0) : ℝ)) (rightHull U hU (s + t)) ∧
      infDist (fPath U hU z ((s + t : ℝ≥0) : ℝ)) (rightHull U hU (s + t)) ≤
        4 * (‖futureDeriv U hU t s z‖ *
          infDist (fPath U hU z t) (leftHull (futureDriver U t) s ∪ rightHull U hU t)) := by
  have hV := continuous_futureDriver hU t
  have hsub : (leftHull (futureDriver U t) s ∪ rightHull U hU t)ᶜ ⊆
      (leftHull (futureDriver U t) s)ᶜ := compl_subset_compl.2 subset_union_left
  have hmaps : ∀ x, x ∉ leftHull (futureDriver U t) s ∪ rightHull U hU t →
      fPath (futureDriver U t) hV x s ∉ rightHull U hU (s + t) := by
    intro x hx
    have hxB : x ∉ leftHull (futureDriver U t) s := fun h => hx (Or.inl h)
    have hxR : x ∈ Set.range (centeredLoewnerMap U hU t) := by
      by_contra h; exact hx (Or.inr h)
    rw [rightHull, mem_compl_iff, not_not, ← centeredLoewnerMap_eq_fPath hV s hxB]
    exact (mem_range_centeredLoewnerMap_add_iff hU s t _).2 ⟨⟨x, hxB⟩, hxR, rfl⟩
  have hsurj : (rightHull U hU (s + t))ᶜ ⊆ (fun x => fPath (futureDriver U t) hV x s) ''
      (leftHull (futureDriver U t) s ∪ rightHull U hU t)ᶜ := by
    intro u hu
    rw [rightHull, compl_compl] at hu
    obtain ⟨⟨x, hxB⟩, hxR, hxu⟩ := (mem_range_centeredLoewnerMap_add_iff hU s t u).1 hu
    refine ⟨x, ?_, ?_⟩
    · rintro (h | h)
      · exact hxB h
      · exact h hxR
    · change fPath (futureDriver U t) hV x s = u
      rw [← hxu]
      exact (centeredLoewnerMap_eq_fPath hV s hxB).symm
  have hw : fPath U hU z t ∉ leftHull (futureDriver U t) s ∪ rightHull U hU t :=
    fPath_notMem_union hU t s hz
  have hwB := fPath_notMem_futureHull hU hz
  have hnorm := norm_deriv_fPath hV hwB
  have hinj := injOn_fPath hV s
  have hdiff := differentiableOn_fPath hV s
  rw [fPath_add_eq hU t s hz]
  constructor
  · have := KoebeChain.norm_deriv_mul_infDist_le (fun x => fPath (futureDriver U t) hV x s)
      (K := leftHull (futureDriver U t) s ∪ rightHull U hU t) (K' := rightHull U hU (s + t))
      ⟨0, zero_mem_rightHull hU (s + t)⟩ (hdiff.mono hsub) (hinj.mono hsub) hmaps
      (z := fPath U hU z t)
    rwa [hnorm] at this
  · have := KoebeChain.infDist_image_le (fun x => fPath (futureDriver U t) hV x s)
      (K := leftHull (futureDriver U t) s ∪ rightHull U hU t) (K' := rightHull U hU (s + t))
      ⟨0, Or.inl (zero_mem_leftHull_futureDriver (U := U) t s)⟩
      (isClosed_leftHull_union_rightHull hU t s).isOpen_compl (hdiff.mono hsub) (hinj.mono hsub)
      (fun p hp => deriv_fPath_ne_zero hV (hsub hp)) hsurj hw
    rwa [hnorm] at this

/-- **(3.10) `eqn-koebe-t`** (paper.tex:L1727-1733), the first `≍`, constants `4`: Koebe for
`f_t : ℂ ∖ L_{s+t} → ℂ ∖ (L_{t,s+t} ∪ R_t)`:
`|f_t'(z)| dist(z, L_{s+t}) ≤ 4 dist(f_t z, L_{t,s+t} ∪ R_t)` and
`dist(f_t z, L_{t,s+t} ∪ R_t) ≤ 4 |f_t'(z)| dist(z, L_{s+t})`. -/
theorem eqn_koebe_t (hz : z ∉ leftHull U (s + t)) :
    ‖derivPath U hU z t‖ * infDist z (leftHull U (s + t)) ≤
        4 * infDist (fPath U hU z t) (leftHull (futureDriver U t) s ∪ rightHull U hU t) ∧
      infDist (fPath U hU z t) (leftHull (futureDriver U t) s ∪ rightHull U hU t) ≤
        4 * (‖derivPath U hU z t‖ * infDist z (leftHull U (s + t))) := by
  refine ⟨?_, infDist_union_le hU hz⟩
  have hz₁ := notMem_leftHull_of_notMem_add t s hz
  have hsub : (leftHull U (s + t))ᶜ ⊆ (leftHull U t)ᶜ := compl_subset_compl.2
    (leftHull_mono le_add_self)
  have := KoebeChain.norm_deriv_mul_infDist_le (fun w => fPath U hU w t)
    (K := leftHull U (s + t)) (K' := leftHull (futureDriver U t) s ∪ rightHull U hU t)
    ⟨0, Or.inl (zero_mem_leftHull_futureDriver (U := U) t s)⟩
    ((differentiableOn_fPath hU t).mono hsub) ((injOn_fPath hU t).mono hsub)
    (fun x hx => fPath_notMem_union hU t s hx) (z := z)
  rwa [norm_deriv_fPath hU hz₁] at this

/-- `dist(f_t z, L_{t,s+t} ∪ R_t) > 0` for `z ∉ L_{s+t}` (the union is closed and nonempty, and
`f_t z` lies outside it). -/
theorem infDist_union_pos (hz : z ∉ leftHull U (s + t)) :
    0 < infDist (fPath U hU z t) (leftHull (futureDriver U t) s ∪ rightHull U hU t) :=
  ((isClosed_leftHull_union_rightHull hU t s).notMem_iff_infDist_pos
    ⟨0, Or.inl (zero_mem_leftHull_futureDriver (U := U) t s)⟩).1 (fPath_notMem_union hU t s hz)

/-- `dist(f_{s+t} z, R_{s+t}) > 0` for `z ∉ L_{s+t}`. -/
theorem infDist_rightHull_add_pos (hz : z ∉ leftHull U (s + t)) :
    0 < infDist (fPath U hU z ((s + t : ℝ≥0) : ℝ)) (rightHull U hU (s + t)) :=
  ((isClosed_rightHull hU (s + t)).notMem_iff_infDist_pos
    ⟨0, zero_mem_rightHull hU (s + t)⟩).1 (fPath_notMem_rightHull_add hU hz)

/-- `dist(f_{s+t} z, R_{t,s+t}) > 0` for `z ∉ L_{s+t}`. -/
theorem infDist_futureRightHull_pos (hz : z ∉ leftHull U (s + t)) :
    0 < infDist (fPath U hU z ((s + t : ℝ≥0) : ℝ)) (futureRightHull U hU t s) := by
  have hV := continuous_futureDriver hU t
  rw [fPath_add_eq hU t s hz]
  exact ((isClosed_rightHull hV s).notMem_iff_infDist_pos
    ⟨0, zero_mem_rightHull hV s⟩).1
    (fPath_notMem_rightHull hV s (fPath_notMem_futureHull hU hz))

/-- Algebra of (3.9): from the four Koebe bounds, the two ratios agree up to the factor `16`. -/
theorem ratio_aux {a b c e D : ℝ} (ha : 0 < a) (hb : 0 < b) (h1 : D * a ≤ 4 * c)
    (h2 : c ≤ 4 * (D * a)) (h3 : D * b ≤ 4 * e) (h4 : e ≤ 4 * (D * b)) :
    c / a ≤ 16 * (e / b) ∧ e / b ≤ 16 * (c / a) := by
  have hD : D ≤ 4 * e / b := by rw [le_div_iff₀ hb]; linarith
  have hD' : D ≤ 4 * c / a := by rw [le_div_iff₀ ha]; linarith
  have hca : c / a ≤ 4 * D := by rw [div_le_iff₀ ha]; linarith
  have heb : e / b ≤ 4 * D := by rw [div_le_iff₀ hb]; linarith
  constructor
  · calc c / a ≤ 4 * D := hca
      _ ≤ 4 * (4 * e / b) := by linarith
      _ = 16 * (e / b) := by ring
  · calc e / b ≤ 4 * D := heb
      _ ≤ 4 * (4 * c / a) := by linarith
      _ = 16 * (c / a) := by ring

/-- **(3.9) `eqn-two-dist-ratio`** (paper.tex:L1722-1725), constants `16`:
`dist(f_{s+t} z, R_{t,s+t}) / dist(f_t z, L_{t,s+t})
  ≍ dist(f_{s+t} z, R_{s+t}) / dist(f_t z, L_{t,s+t} ∪ R_t)`. -/
theorem eqn_two_dist_ratio (hz : z ∉ leftHull U (s + t)) :
    infDist (fPath U hU z ((s + t : ℝ≥0) : ℝ)) (futureRightHull U hU t s) /
          infDist (fPath U hU z t) (leftHull (futureDriver U t) s) ≤
        16 * (infDist (fPath U hU z ((s + t : ℝ≥0) : ℝ)) (rightHull U hU (s + t)) /
          infDist (fPath U hU z t) (leftHull (futureDriver U t) s ∪ rightHull U hU t)) ∧
      infDist (fPath U hU z ((s + t : ℝ≥0) : ℝ)) (rightHull U hU (s + t)) /
          infDist (fPath U hU z t) (leftHull (futureDriver U t) s ∪ rightHull U hU t) ≤
        16 * (infDist (fPath U hU z ((s + t : ℝ≥0) : ℝ)) (futureRightHull U hU t s) /
          infDist (fPath U hU z t) (leftHull (futureDriver U t) s)) := by
  obtain ⟨h1, h2⟩ := eqn_two_formulas hU hz
  obtain ⟨h3, h4⟩ := eqn_two_formulas_b hU hz
  exact ratio_aux (infDist_futureHull_pos hU hz) (infDist_union_pos hU hz) h1 h2 h3 h4

/-! ### The case analysis (3.13)-(3.17) -/

/-- The distance to a union is the minimum of the distances. -/
theorem infDist_union_eq_min {w : ℂ} {B R : Set ℂ} (hB : B.Nonempty) (hR : R.Nonempty) :
    infDist w (B ∪ R) = min (infDist w B) (infDist w R) :=
  le_antisymm (le_min (infDist_le_infDist_of_subset subset_union_left hB)
    (infDist_le_infDist_of_subset subset_union_right hR)) (min_infDist_le_infDist_union hB)

theorem infDist_union_eq_min' (t s : ℝ≥0) (w : ℂ) :
    infDist w (leftHull (futureDriver U t) s ∪ rightHull U hU t) =
      min (infDist w (leftHull (futureDriver U t) s)) (infDist w (rightHull U hU t)) :=
  infDist_union_eq_min ⟨0, zero_mem_leftHull_futureDriver (U := U) t s⟩
    ⟨0, zero_mem_rightHull hU t⟩

/-- **(3.13) `eqn-dist-cases`** (paper.tex:L1750-1754):
`dist(f_t z, L_{t,s+t} ∪ R_t) = dist(f_t z, L_{t,s+t}) 1_{E_s} + dist(f_t z, R_t) 1_{E_s^c}`. -/
theorem eqn_dist_cases [Decidable (koebeEvent U hU t s z)] :
    infDist (fPath U hU z t) (leftHull (futureDriver U t) s ∪ rightHull U hU t) =
      if koebeEvent U hU t s z then infDist (fPath U hU z t) (leftHull (futureDriver U t) s)
      else infDist (fPath U hU z t) (rightHull U hU t) := by
  rw [infDist_union_eq_min' hU t s]
  by_cases hE : koebeEvent U hU t s z
  · simp only [hE, ↓reduceIte]; exact min_eq_left hE
  · simp only [hE, ↓reduceIte]; exact min_eq_right (not_le.1 hE).le

/-- **(3.14) `eqn-koebe-union`** (paper.tex:L1756-1761), on `E_s`, constants `4`:
`|f_t'(z)| dist(z, L_{s+t}) ≤ 4 dist(f_t z, L_{t,s+t})` and
`dist(f_t z, L_{t,s+t}) ≤ 4 |f_t'(z)| dist(z, L_{s+t})`. -/
theorem eqn_koebe_union (hz : z ∉ leftHull U (s + t)) (hE : koebeEvent U hU t s z) :
    ‖derivPath U hU z t‖ * infDist z (leftHull U (s + t)) ≤
        4 * infDist (fPath U hU z t) (leftHull (futureDriver U t) s) ∧
      infDist (fPath U hU z t) (leftHull (futureDriver U t) s) ≤
        4 * (‖derivPath U hU z t‖ * infDist z (leftHull U (s + t))) := by
  have hmin : infDist (fPath U hU z t) (leftHull (futureDriver U t) s ∪ rightHull U hU t) =
      infDist (fPath U hU z t) (leftHull (futureDriver U t) s) := by
    rw [infDist_union_eq_min' hU t s]; exact min_eq_left hE
  have := eqn_koebe_t hU hz
  rwa [hmin] at this

/-- **(3.15) `eqn-dist-es`** (paper.tex:L1762-1766), on `E_s`, constants `4`:
`dist(f_t z, L_{t,s+t}) / (|f_t z| dist(z, L_{s+t})) ≍ |f_t'(z)| / |f_t z|`. -/
theorem eqn_dist_es (hz : z ∉ leftHull U (s + t)) (hE : koebeEvent U hU t s z) :
    (1 / 4) * (‖derivPath U hU z t‖ / ‖fPath U hU z t‖) ≤
        infDist (fPath U hU z t) (leftHull (futureDriver U t) s) /
          (‖fPath U hU z t‖ * infDist z (leftHull U (s + t))) ∧
      infDist (fPath U hU z t) (leftHull (futureDriver U t) s) /
          (‖fPath U hU z t‖ * infDist z (leftHull U (s + t))) ≤
        4 * (‖derivPath U hU z t‖ / ‖fPath U hU z t‖) := by
  obtain ⟨h1, h2⟩ := eqn_koebe_union hU hz hE
  have hdL : 0 < infDist z (leftHull U (s + t)) := infDist_leftHull_pos hU hz
  have hw : 0 < ‖fPath U hU z t‖ := norm_fPath_pos' hU hz
  have hp := mul_pos hw hdL
  constructor
  · rw [show (1 / 4 : ℝ) * (‖derivPath U hU z t‖ / ‖fPath U hU z t‖) =
        ‖derivPath U hU z t‖ * infDist z (leftHull U (s + t)) /
          (4 * (‖fPath U hU z t‖ * infDist z (leftHull U (s + t)))) by field_simp,
      div_le_div_iff₀ (by positivity) hp]
    nlinarith
  · rw [div_le_iff₀ hp]
    calc infDist (fPath U hU z t) (leftHull (futureDriver U t) s)
        ≤ 4 * (‖derivPath U hU z t‖ * infDist z (leftHull U (s + t))) := h2
      _ = 4 * (‖derivPath U hU z t‖ / ‖fPath U hU z t‖) *
            (‖fPath U hU z t‖ * infDist z (leftHull U (s + t))) := by field_simp

/-- Algebra of (3.11): from (3.9) and (3.10) in cleared form. -/
theorem dist1_aux {a b c e D dL w : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (he : 0 < e)
    (hdL : 0 < dL) (hw : 0 < w) (hD : 0 < D) (k1 : D * dL ≤ 4 * b) (k2 : b ≤ 4 * (D * dL))
    (r1 : c / a ≤ 16 * (e / b)) (r2 : e / b ≤ 16 * (c / a)) :
    (1 / 64) * (D / w * (c / e)) ≤ a / (w * dL) ∧ a / (w * dL) ≤ 64 * (D / w * (c / e)) := by
  have r1' : c * b ≤ 16 * (a * e) := by
    have := mul_le_mul_of_nonneg_right r1 (by positivity : 0 ≤ a * b)
    have e1 : c / a * (a * b) = c * b := by field_simp
    have e2 : 16 * (e / b) * (a * b) = 16 * (a * e) := by field_simp
    rwa [e1, e2] at this
  have r2' : e * a ≤ 16 * (c * b) := by
    have := mul_le_mul_of_nonneg_right r2 (by positivity : 0 ≤ a * b)
    have e1 : e / b * (a * b) = e * a := by field_simp
    have e2 : 16 * (c / a) * (a * b) = 16 * (c * b) := by field_simp
    rwa [e1, e2] at this
  have hwe : 0 < w * e := mul_pos hw he
  have hwdL : 0 < w * dL := mul_pos hw hdL
  constructor
  · rw [show (1 / 64 : ℝ) * (D / w * (c / e)) = D * c / (64 * (w * e)) by field_simp,
      div_le_div_iff₀ (by positivity) hwdL]
    have h : D * c * dL ≤ 64 * (a * e) := by
      calc D * c * dL = c * (D * dL) := by ring
        _ ≤ c * (4 * b) := by gcongr
        _ = 4 * (c * b) := by ring
        _ ≤ 4 * (16 * (a * e)) := by gcongr
        _ = 64 * (a * e) := by ring
    nlinarith [mul_le_mul_of_nonneg_left h hw.le]
  · rw [show 64 * (D / w * (c / e)) = 64 * D * c / (w * e) by field_simp,
      div_le_div_iff₀ hwdL hwe]
    have h : a * e ≤ 64 * D * c * dL := by
      calc a * e = e * a := by ring
        _ ≤ 16 * (c * b) := r2'
        _ ≤ 16 * (c * (4 * (D * dL))) := by gcongr
        _ = 64 * D * c * dL := by ring
    nlinarith [mul_le_mul_of_nonneg_left h hw.le]

/-- **(3.11) `eqn-dist-1`** (paper.tex:L1734-1738), constant `64`:
`dist(f_t z, L_{t,s+t}) / (|f_t z| dist(z, L_{s+t}))
  ≍ (|f_t'(z)| / |f_t z|) · dist(f_{s+t} z, R_{t,s+t}) / dist(f_{s+t} z, R_{s+t})`. -/
theorem eqn_dist_1 (hz : z ∉ leftHull U (s + t)) :
    (1 / 64) * (‖derivPath U hU z t‖ / ‖fPath U hU z t‖ *
        (infDist (fPath U hU z ((s + t : ℝ≥0) : ℝ)) (futureRightHull U hU t s) /
          infDist (fPath U hU z ((s + t : ℝ≥0) : ℝ)) (rightHull U hU (s + t)))) ≤
        infDist (fPath U hU z t) (leftHull (futureDriver U t) s) /
          (‖fPath U hU z t‖ * infDist z (leftHull U (s + t))) ∧
      infDist (fPath U hU z t) (leftHull (futureDriver U t) s) /
          (‖fPath U hU z t‖ * infDist z (leftHull U (s + t))) ≤
        64 * (‖derivPath U hU z t‖ / ‖fPath U hU z t‖ *
          (infDist (fPath U hU z ((s + t : ℝ≥0) : ℝ)) (futureRightHull U hU t s) /
            infDist (fPath U hU z ((s + t : ℝ≥0) : ℝ)) (rightHull U hU (s + t)))) := by
  set a := infDist (fPath U hU z t) (leftHull (futureDriver U t) s) with ha_def
  set b := infDist (fPath U hU z t) (leftHull (futureDriver U t) s ∪ rightHull U hU t)
    with hb_def
  set c := infDist (fPath U hU z ((s + t : ℝ≥0) : ℝ)) (futureRightHull U hU t s) with hc_def
  set e := infDist (fPath U hU z ((s + t : ℝ≥0) : ℝ)) (rightHull U hU (s + t)) with he_def
  set D := ‖derivPath U hU z t‖ with hD_def
  set w := ‖fPath U hU z t‖ with hw_def
  set dL := infDist z (leftHull U (s + t)) with hdL_def
  have ha : 0 < a := infDist_futureHull_pos hU hz
  have hb : 0 < b := infDist_union_pos hU hz
  have he : 0 < e := infDist_rightHull_add_pos hU hz
  have hdL : 0 < dL := infDist_leftHull_pos hU hz
  have hw : 0 < w := norm_fPath_pos' hU hz
  have hD : 0 < D := norm_pos_iff.2 (derivPath_ne_zero hU z t)
  obtain ⟨k1, k2⟩ := eqn_koebe_t hU hz
  obtain ⟨r1, r2⟩ := eqn_two_dist_ratio hU hz
  exact dist1_aux ha hb infDist_nonneg he hdL hw hD k1 k2 r1 r2

/-- Algebra of (3.16): the ratios `c / e` and `a / b` agree up to the factor `16`. -/
theorem dist2_aux {a b c e : ℝ} (ha : 0 < a) (hb : 0 < b) (he : 0 < e)
    (r1 : c / a ≤ 16 * (e / b)) (r2 : e / b ≤ 16 * (c / a)) :
    c / e ≤ 16 * (a / b) ∧ a / b ≤ 16 * (c / e) := by
  have r1' : c * b ≤ 16 * (a * e) := by
    have := mul_le_mul_of_nonneg_right r1 (by positivity : 0 ≤ a * b)
    have e1 : c / a * (a * b) = c * b := by field_simp
    have e2 : 16 * (e / b) * (a * b) = 16 * (a * e) := by field_simp
    rwa [e1, e2] at this
  have r2' : e * a ≤ 16 * (c * b) := by
    have := mul_le_mul_of_nonneg_right r2 (by positivity : 0 ≤ a * b)
    have e1 : e / b * (a * b) = e * a := by field_simp
    have e2 : 16 * (c / a) * (a * b) = 16 * (c * b) := by field_simp
    rwa [e1, e2] at this
  constructor
  · rw [div_le_iff₀ he, show 16 * (a / b) * e = 16 * (a * e) / b by field_simp, le_div_iff₀ hb]
    linarith
  · rw [div_le_iff₀ hb, show 16 * (c / e) * b = 16 * (c * b) / e by field_simp, le_div_iff₀ he]
    linarith

/-- **(3.16) `eqn-dist-2`** (paper.tex:L1768-1772), constants `16`: the ratio of `R`-distances
`dist(f_{s+t} z, R_{t,s+t}) / dist(f_{s+t} z, R_{s+t})` is `≍` to
`dist(f_t z, L_{t,s+t}) / dist(f_t z, L_{t,s+t} ∪ R_t)`, and on the complement of `E_s` the latter
is `≤ |f_t z| / dist(f_t z, R_t)` (`0 ∈ L_{t,s+t}`, `eqn-dist-cases`). -/
theorem eqn_dist_2 (hz : z ∉ leftHull U (s + t)) (hE : ¬ koebeEvent U hU t s z) :
    infDist (fPath U hU z ((s + t : ℝ≥0) : ℝ)) (futureRightHull U hU t s) /
          infDist (fPath U hU z ((s + t : ℝ≥0) : ℝ)) (rightHull U hU (s + t)) ≤
        16 * (infDist (fPath U hU z t) (leftHull (futureDriver U t) s) /
          infDist (fPath U hU z t) (leftHull (futureDriver U t) s ∪ rightHull U hU t)) ∧
      infDist (fPath U hU z t) (leftHull (futureDriver U t) s) /
          infDist (fPath U hU z t) (leftHull (futureDriver U t) s ∪ rightHull U hU t) ≤
        16 * (infDist (fPath U hU z ((s + t : ℝ≥0) : ℝ)) (futureRightHull U hU t s) /
          infDist (fPath U hU z ((s + t : ℝ≥0) : ℝ)) (rightHull U hU (s + t))) ∧
      infDist (fPath U hU z t) (leftHull (futureDriver U t) s) /
          infDist (fPath U hU z t) (leftHull (futureDriver U t) s ∪ rightHull U hU t) ≤
        ‖fPath U hU z t‖ / infDist (fPath U hU z t) (rightHull U hU t) := by
  obtain ⟨r1, r2⟩ := eqn_two_dist_ratio hU hz
  obtain ⟨q1, q2⟩ := dist2_aux (infDist_futureHull_pos hU hz) (infDist_union_pos hU hz)
    (infDist_rightHull_add_pos hU hz) r1 r2
  refine ⟨q1, q2, ?_⟩
  have hb := infDist_union_pos hU hz
  have hbR : infDist (fPath U hU z t) (leftHull (futureDriver U t) s ∪ rightHull U hU t) =
      infDist (fPath U hU z t) (rightHull U hU t) := by
    rw [infDist_union_eq_min' hU t s]; exact min_eq_right (not_le.1 hE).le
  rw [hbR] at hb ⊢
  exact div_le_div_of_nonneg_right (infDist_futureHull_le_norm hU t s z) hb.le

/-- **(3.17) `eqn-dist-esc`** (paper.tex:L1773-1778), on the complement of `E_s`, constants `4`:
`dist(f_t z, L_{t,s+t}) / (|f_t z| dist(z, L_{s+t})) ≤ 4 |f_t'(z)| / dist(f_t z, R_t)` and
`|f_t'(z)| / dist(f_t z, R_t) ≍ 1 / dist(z, L_t)` (Koebe for `f_t : ℂ ∖ L_t → ℂ ∖ R_t`). (The
paper's route gives `≲` with a larger constant; the direct bound `16 / dist(z, L_t)` is
`KoebeChain.koebe_chain_of_not_event`.) -/
theorem eqn_dist_esc (hz : z ∉ leftHull U (s + t)) (hE : ¬ koebeEvent U hU t s z) :
    infDist (fPath U hU z t) (leftHull (futureDriver U t) s) /
          (‖fPath U hU z t‖ * infDist z (leftHull U (s + t))) ≤
        4 * (‖derivPath U hU z t‖ / infDist (fPath U hU z t) (rightHull U hU t)) ∧
      ‖derivPath U hU z t‖ / infDist (fPath U hU z t) (rightHull U hU t) ≤
        4 * (1 / infDist z (leftHull U t)) ∧
      1 / infDist z (leftHull U t) ≤
        4 * (‖derivPath U hU z t‖ / infDist (fPath U hU z t) (rightHull U hU t)) := by
  have hz₁ := notMem_leftHull_of_notMem_add t s hz
  have hdL : 0 < infDist z (leftHull U (s + t)) := infDist_leftHull_pos hU hz
  have hdt : 0 < infDist z (leftHull U t) := infDist_leftHull_pos hU hz₁
  have hw : 0 < ‖fPath U hU z t‖ := norm_fPath_pos' hU hz
  have hD : 0 < ‖derivPath U hU z t‖ := norm_pos_iff.2 (derivPath_ne_zero hU z t)
  obtain ⟨m1, m2⟩ := koebe_two_sided hU t hz₁
  have hbR : 0 < infDist (fPath U hU z t) (rightHull U hU t) := by
    by_contra h
    have h0 : infDist (fPath U hU z t) (rightHull U hU t) = 0 :=
      le_antisymm (not_lt.1 h) infDist_nonneg
    rw [h0] at m1
    exact absurd m1 (not_le.2 (by nlinarith [mul_pos hD hdt]))
  have hunion : infDist (fPath U hU z t) (leftHull (futureDriver U t) s ∪ rightHull U hU t) =
      infDist (fPath U hU z t) (rightHull U hU t) := by
    rw [infDist_union_eq_min' hU t s]; exact min_eq_right (not_le.1 hE).le
  obtain ⟨-, k2⟩ := eqn_koebe_t hU hz
  rw [hunion] at k2
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ (mul_pos hw hdL)]
    have ha := infDist_futureHull_le_norm hU t s z
    have h1 : 1 ≤ 4 * (‖derivPath U hU z t‖ / infDist (fPath U hU z t) (rightHull U hU t)) *
        infDist z (leftHull U (s + t)) := by
      rw [show 4 * (‖derivPath U hU z t‖ / infDist (fPath U hU z t) (rightHull U hU t)) *
          infDist z (leftHull U (s + t)) =
          4 * (‖derivPath U hU z t‖ * infDist z (leftHull U (s + t))) /
            infDist (fPath U hU z t) (rightHull U hU t) by field_simp, le_div_iff₀ hbR]
      linarith
    calc infDist (fPath U hU z t) (leftHull (futureDriver U t) s) ≤ ‖fPath U hU z t‖ := ha
      _ = ‖fPath U hU z t‖ * 1 := (mul_one _).symm
      _ ≤ ‖fPath U hU z t‖ * (4 * (‖derivPath U hU z t‖ /
            infDist (fPath U hU z t) (rightHull U hU t)) * infDist z (leftHull U (s + t))) :=
          mul_le_mul_of_nonneg_left h1 hw.le
      _ = 4 * (‖derivPath U hU z t‖ / infDist (fPath U hU z t) (rightHull U hU t)) *
            (‖fPath U hU z t‖ * infDist z (leftHull U (s + t))) := by ring
  · rw [div_le_iff₀ hbR, show 4 * (1 / infDist z (leftHull U t)) *
        infDist (fPath U hU z t) (rightHull U hU t) =
        4 * infDist (fPath U hU z t) (rightHull U hU t) / infDist z (leftHull U t) by field_simp,
      le_div_iff₀ hdt]
    linarith
  · rw [show 4 * (‖derivPath U hU z t‖ / infDist (fPath U hU z t) (rightHull U hU t)) =
        4 * ‖derivPath U hU z t‖ / infDist (fPath U hU z t) (rightHull U hU t) by ring,
      div_le_div_iff₀ hdt hbR]
    linarith

/-! ### `step:converse-event-converges`: `1_{E_s} → 1` (deterministic form) -/

/-- **Transfer through `f_t` at the interior point `z`** (the first half of the `SOURCE_GAP` of
`step:converse-event-converges`): if `z ∉ L_t` then for every `ε > 0` there is `δ > 0` such that
`dist(z, L_{s+t}) < δ` implies `dist(f_t z, L_{t,s+t}) < ε` (for every `s`). Only continuity of
`f_t` at `z` and the concatenation property (2.3) (`f_t(L_{s+t} ∖ L_t) ⊆ L_{t,s+t}`) are used. -/
theorem exists_infDist_futureHull_lt (hU : Continuous U) {t : ℝ≥0} {z : ℂ}
    (hz₁ : z ∉ leftHull U t) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s : ℝ≥0, infDist z (leftHull U (s + t)) < δ →
      infDist (fPath U hU z t) (leftHull (futureDriver U t) s) < ε := by
  have hdt : 0 < infDist z (leftHull U t) := infDist_leftHull_pos hU hz₁
  have hcont : ContinuousAt (fun w => fPath U hU w t) z :=
    (hasDerivAt_fPath_initial hU (coe_mem_lifeSet_iff.2 hz₁)).continuousAt
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuousAt_iff.1 hcont ε hε
  refine ⟨min δ₁ (infDist z (leftHull U t)), lt_min hδ₁ hdt, fun s hs => ?_⟩
  obtain ⟨p, hpL, hpd⟩ := (infDist_lt_iff (leftHull_nonempty U (s + t))).1 hs
  have hp₁ : p ∉ leftHull U t := by
    intro hp
    have h1 := infDist_le_dist_of_mem (x := z) hp
    exact absurd (lt_of_lt_of_le hpd (min_le_right _ _)) (not_lt.2 h1)
  have hpB : fPath U hU p t ∈ leftHull (futureDriver U t) s :=
    (fPath_mem_leftHull_iff hU t s hp₁).2 hpL
  have hdp : dist p z < δ₁ := by
    rw [dist_comm]; exact lt_of_lt_of_le hpd (min_le_left _ _)
  have := hδ₁' hdp
  rw [dist_comm] at this
  exact lt_of_le_of_lt (infDist_le_dist_of_mem hpB) this

/-- **`step:converse-event-converges`, deterministic form** (paper.tex:L1748): let `z ∉ L_t` (`t`
fixed) and let `l` be a filter on the times `s` along which `dist(z, L_{s+t}) → 0` (in the paper:
`s = σ(ŝ + t̂) - σ(t̂)`, `ŝ → ∞`, so `s + t → T_z`, with
`lim_{u → T_z⁻} dist(z, L_u) = 0`). Then eventually `E_s` holds:
`dist(f_t z, L_{t,s+t}) ≤ dist(f_t z, R_t)`. (The fixed positive distance `dist(f_t z, R_t) ≥
|f_t'(z)| dist(z, L_t) / 4` comes from the Koebe quarter theorem.) -/
theorem eventually_koebeEvent (hU : Continuous U) {t : ℝ≥0} {z : ℂ} (hz₁ : z ∉ leftHull U t)
    {l : Filter ℝ≥0}
    (h : Tendsto (fun s : ℝ≥0 => infDist z (leftHull U (s + t))) l (𝓝 0)) :
    ∀ᶠ s in l, koebeEvent U hU t s z := by
  have hdt : 0 < infDist z (leftHull U t) := infDist_leftHull_pos hU hz₁
  have hD : 0 < ‖derivPath U hU z t‖ := norm_pos_iff.2 (derivPath_ne_zero hU z t)
  have hε : 0 < infDist (fPath U hU z t) (rightHull U hU t) := by
    have := norm_derivPath_mul_infDist_le_infDist_rightHull hU hz₁
    nlinarith [mul_pos hD hdt]
  obtain ⟨δ, hδ, hδ'⟩ := exists_infDist_futureHull_lt hU hz₁ hε
  filter_upwards [h.eventually (Iio_mem_nhds hδ)] with s hs
  exact (hδ' s hs).le

end Displays

end ComplexSLE.Internal.KoebeChain

end
