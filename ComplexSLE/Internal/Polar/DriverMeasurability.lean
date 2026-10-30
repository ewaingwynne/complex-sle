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
adapted functionals of the driver. These are the specialisations of the results of
`Measurability.lean`, `ExitTimes.lean`, `ClockArg.lean`, which only use the continuity of the paths
and the adaptedness of `U` (not the Brownian increment property):

* `isStoppingTime_absorbingTime_of_isSLEDriverAdapted`: `T_z` is an `ℱ`-stopping time;
* `measurableSet_mem_lifeSet_of_isSLEDriverAdapted`,
  `measurable_centeredPath_of_isSLEDriverAdapted`, `measurable_solPath_of_isSLEDriverAdapted`:
  the event `{t < T_z}` and the values `f_t(z)`,
  `g_t(z)` on it are `ℱ t`-measurable;
* `isStoppingTime_exitTime_of_isSLEDriverAdapted`: the annulus exit times `τ_n` are stopping times;
* `measurable_clock_of_isSLEDriverAdapted`, `measurable_argPath_of_isSLEDriverAdapted`: the clock
  and the argument at a fixed time `t`, on `{t < T_z}`, are `ℱ t`-measurable.

Off the event `{t < T_z}` the measurable functions are set to `0`.
-/

public section

open scoped NNReal ENNReal
open Set MeasureTheory

namespace ComplexSLE.Internal.Polar

variable {Ω : Type*} {m : MeasurableSpace Ω} {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 m}

/-- **`T_z` is an `ℱ`-stopping time.** -/
theorem isStoppingTime_absorbingTime_of_isSLEDriverAdapted
    (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) :
    IsStoppingTime ℱ fun ω => (absorbingTime (fun t => U t ω) z : WithTop ℝ≥0) :=
  isStoppingTime_absorbingTime hU.cont hU.adapted z

/-- The event `{t < T_z}` is `ℱ t`-measurable. -/
theorem measurableSet_mem_lifeSet_of_isSLEDriverAdapted
    (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) (z : ℂ) :
    MeasurableSet[ℱ t] {ω | (t : ℝ) ∈ lifeSet (fun s => U s ω) z} :=
  measurableSet_mem_lifeSet hU.cont hU.adapted t z

open Classical in
/-- `f_t(z)` on `{t < T_z}` (and `0` elsewhere) is `ℱ t`-measurable. -/
theorem measurable_centeredPath_of_isSLEDriverAdapted
    (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) (z : ℂ) :
    Measurable[ℱ t] fun ω =>
      if (t : ℝ) ∈ lifeSet (fun s => U s ω) z then fPath (fun s => U s ω) (hU.cont ω) z t
      else 0 :=
  measurable_centeredPath hU.cont hU.adapted t z

open Classical in
/-- `g_t(z)` on `{t < T_z}` (and `0` elsewhere) is `ℱ t`-measurable. -/
theorem measurable_solPath_of_isSLEDriverAdapted
    (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) (z : ℂ) :
    Measurable[ℱ t] fun ω =>
      if (t : ℝ) ∈ lifeSet (fun s => U s ω) z then solPath (fun s => U s ω) (hU.cont ω) z t
      else 0 :=
  measurable_solPath hU.cont hU.adapted t z

/-- The indicator of `{t < T_z}` is `ℱ t`-measurable. -/
theorem measurable_indicator_mem_lifeSet_of_isSLEDriverAdapted
    (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) (z : ℂ) :
    Measurable[ℱ t] ({ω | (t : ℝ) ∈ lifeSet (fun s => U s ω) z}.indicator fun _ => (1 : ℝ)) :=
  measurable_indicator_mem_lifeSet hU.cont hU.adapted t z

/-- The annulus exit times `τ_n` are `ℱ`-stopping times (`exitTime` is nonnegative). -/
theorem isStoppingTime_exitTime_of_isSLEDriverAdapted
    (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) (n : ℕ) :
    IsStoppingTime ℱ fun ω =>
      (((exitTime (fun r => U r ω) (hU.cont ω) z n).toNNReal : ℝ≥0) : WithTop ℝ≥0) :=
  isStoppingTime_exitTime hU.cont hU.adapted z n

open Classical in
/-- The clock `A_t(z)` on `{t < T_z}` (and `0` elsewhere) is `ℱ t`-measurable. -/
theorem measurable_clock_of_isSLEDriverAdapted
    (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) (z : ℂ) :
    Measurable[ℱ t] fun ω =>
      if (t : ℝ) ∈ lifeSet (fun s => U s ω) z then clock (fun s => U s ω) (hU.cont ω) z t
      else 0 :=
  measurable_clock hU.cont hU.adapted t z

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
