/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.RightHull
public import ComplexSLE.Frozen.Defs.IsSLEDriver
import ComplexSLE.Internal.Duality.PathLaw
import ComplexSLE.Internal.Duality.Deterministic

/-!
# Provider for `ComplexSLE.sle_duality`

Implementation module for the frozen anchor `ComplexSLE/Frozen/Proposition_1_5.lean`.
The anchor is SEALED: it is proved by this module.

The driver part is `IsSLEDriver.dual` (`ComplexSLE.Internal.Duality.PathLaw`): the process
`Y s = (U (t - s) - U t) + (U (max s t) - U t)` has the finite-dimensional laws of `U` (time
reversal on `[0, t]` and independence of the future increments from the past), hence is an
`SLE_Σ` driver, and `Ũ = i Y` is an `SLE_Σ̃` driver. The pathwise part is the deterministic duality
`ComplexSLE.Internal.Duality.Deterministic` for the a.s. continuous path with `U 0 = 0`.
-/

public section

open scoped NNReal
open MeasureTheory

namespace ComplexSLE.Internal

/-- **Proposition 1.5 (SLE_Σ duality)**, coupling form (provider of `ComplexSLE.sle_duality`). -/
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
                  Complex.I * (U (max s t) ω - U t ω)) (by fun_prop) t ⟨w, hw⟩ = Complex.I * z := by
  refine ⟨hU.dual t, ?_⟩
  filter_upwards [hU.zero] with ω h0 hω
  exact ⟨leftHull_dualDriver hω t, rightHull_dualDriver hω h0 t,
    fun w hw => centeredLoewnerMap_dualDriver hω h0 t w hw⟩

end ComplexSLE.Internal

end
