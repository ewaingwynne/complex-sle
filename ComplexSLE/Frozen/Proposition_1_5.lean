/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.RightHull
public import ComplexSLE.Frozen.Defs.IsSLEDriver
import ComplexSLE.Internal.Proposition_1_5

/-!
# Proposition 1.5 (SLE_Σ duality), coupling form (ERRATA.md R28)
-/

public section

open scoped NNReal
open MeasureTheory

namespace ComplexSLE

/-- **Proposition 1.5 (SLE_Σ duality)** (paper.tex:L329-336), coupling form (proposed ruling): for an SLE_Σ
driver `U` and `t > 0`, the process `Ũ s = i (U (t - s) - U t) + i (U (max s t) - U t)` (time reversal of `U` on
`[0, t]`, continued by `i ×` the increments after `t`) is an SLE_Σ̃ driver with `Σ̃ = [[b, -c], [-c, a]]`, and a.s.
`L̃_t = i R_t`, `R̃_t = i L_t`, and `f̃_t(w) = i f_t^{-1}(-i w)` on `ℂ ∖ L̃_t`. Equality in law (the source's
statement) follows for any σ-algebra for which hulls and maps are measurable functions of the driver path. -/
theorem sle_duality (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c ^ 2 ≤ a * b) (U : ℝ≥0 → Ω → ℂ)
    (hU : IsSLEDriver a b c U P) (t : ℝ≥0) (ht : 0 < t) :
    IsSLEDriver b a (-c)
        (fun s ω => Complex.I * (U (t - s) ω - U t ω) + Complex.I * (U (max s t) ω - U t ω)) P ∧
      ∀ᵐ ω ∂P, ∀ (hω : Continuous fun s => U s ω),
        leftHull (fun s => Complex.I * (U (t - s) ω - U t ω) + Complex.I * (U (max s t) ω - U t ω)) t =
            (fun z => Complex.I * z) '' rightHull (fun s => U s ω) hω t ∧
          rightHull (fun s => Complex.I * (U (t - s) ω - U t ω) + Complex.I * (U (max s t) ω - U t ω))
              (by fun_prop) t =
            (fun z => Complex.I * z) '' leftHull (fun s => U s ω) t ∧
          ∀ (w : ℂ)
            (hw : w ∈ (leftHull (fun s => Complex.I * (U (t - s) ω - U t ω) +
              Complex.I * (U (max s t) ω - U t ω)) t)ᶜ),
            ∃ z : ↥(leftHull (fun s => U s ω) t)ᶜ,
              centeredLoewnerMap (fun s => U s ω) hω t z = -Complex.I * w ∧
              centeredLoewnerMap (fun s => Complex.I * (U (t - s) ω - U t ω) +
                  Complex.I * (U (max s t) ω - U t ω)) (by fun_prop) t ⟨w, hw⟩ = Complex.I * z :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ComplexSLE.Internal.sle_duality Ω P a b c ha hb hc U hU t ht
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE

end
-- FROZEN_ANCHOR_SUFFIX_END
