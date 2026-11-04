/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.ExitTimes
public import ComplexSLE.Internal.Polar.ClockArg
public import ComplexSLE.Frozen.Defs.IsSLEDriverAdapted

/-!
# Measurability of the polar objects for an `IsSLEDriverAdapted` driver (M6/S6 summary)

For `hU : IsSLEDriverAdapted a b c U P ℱ` (paths continuous for every `ω`, `U` adapted to `ℱ`) and
`z : ℂ`, the Loewner objects of `Path.lean`, `Sigma.lean`, `Argument.lean` are measurable /
adapted functionals of the driver. These are the specialisations of the results of `ExitTimes.lean`
and `ClockArg.lean`, which only use the continuity of the paths and the adaptedness of `U` (not the
Brownian increment property):

* `isStoppingTime_exitTime_of_isSLEDriverAdapted`: the annulus exit times `τ_n` are stopping times;
* `measurable_argPath_of_isSLEDriverAdapted`: the argument at a fixed time `t`, on `{t < T_z}`, is
  `ℱ t`-measurable.

Off the event `{t < T_z}` the measurable function is set to `0`.
-/

public section

open scoped NNReal ENNReal
open Set MeasureTheory

namespace ComplexSLE.Internal.Polar

variable {Ω : Type*} {m : MeasurableSpace Ω} {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 m}

/-- The annulus exit times `τ_n` are `ℱ`-stopping times (`exitTime` is nonnegative). -/
theorem isStoppingTime_exitTime_of_isSLEDriverAdapted
    (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) (n : ℕ) :
    IsStoppingTime ℱ fun ω =>
      (((exitTime (fun r => U r ω) (hU.cont ω) z n).toNNReal : ℝ≥0) : WithTop ℝ≥0) :=
  isStoppingTime_exitTime hU.cont hU.adapted z n

open Classical in
/-- The argument `θ_t(z)` on `{t < T_z}` (and `0` elsewhere) is `ℱ t`-measurable. -/
theorem measurable_argPath_of_isSLEDriverAdapted
    (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) (z : ℂ) :
    Measurable[ℱ t] fun ω =>
      if (t : ℝ) ∈ lifeSet (fun s => U s ω) z then argPath (fun s => U s ω) (hU.cont ω) z t
      else 0 :=
  measurable_argPath hU.cont hU.adapted t z

end ComplexSLE.Internal.Polar

end
