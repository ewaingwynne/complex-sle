/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.ErgodicMean
public import ComplexSLE.External.BirkhoffStationary

/-!
# Stationarity of the increments of `log |f̂_t(𝐳)|` and the Birkhoff limit (M7/A5a)

With `Y_t(ω, u) = log |f̂_t(e^{iu})(ω)|` (`logFHat`) and `ξ_n = Y_{n+1} - Y_n` (`xiInc`):

* `xiInc_stationary`: `(ξ_{n+k})_n` and `(ξ_n)_n` have the same law on `ℕ → ℝ` under
  `P ⊗ ν` (hypothesis shape of the EXTERNAL `birkhoff_stationary`). Indeed
  `(ξ_{n+k})_n = G (Ξ_k)` with the measurable map
  `G (_, _, ℓ) = (ℓ(n + 1) - ℓ(n))_n`, `Ξ_k` the path observable of `PathStat.lean`, and the law of
  `Ξ_k` does not depend on `k` (`map_pathObs_eq_zero`, modulo `hMO : MarkovOneDim`);
* `exists_birkhoff_logFHat`: there is an integrable `L` with `∫ L = (I)` and
  `Y_n / n → L` almost surely (`n → ∞`). Telescoping `∑_{k<n} ξ_k = Y_n - Y_0` and
  `Y_0 = 0` a.s.

Consumes the EXTERNAL `birkhoff_stationary` (E7), and (through the stationarity layer)
`hormander_oneDim`, `ito_formula`, `timeChange_isContLocalMartingale`, `strongMarkov_sleDriver`
and the EXTERNAL `markov_oneDim` (R29) as the explicit hypothesis `hMO : MarkovOneDim`.
-/

@[expose] public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal

open Polar

section Stat

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-- `ξ_n = Y_{n+1} - Y_n`, `Y_t = log |f̂_t(e^{iu})|`. -/
noncomputable def xiInc (hU : IsSLEDriverAdapted a b c U P ℱ) (n : ℕ) (q : Ω × ℝ) : ℝ :=
  logFHat hU ((n : ℝ≥0) + 1) q - logFHat hU (n : ℝ≥0) q

theorem measurable_xiInc (hU : IsSLEDriverAdapted a b c U P ℱ) (n : ℕ) :
    Measurable (xiInc hU n) :=
  (measurable_logFHat hU _).sub (measurable_logFHat hU _)

/-- The increment functional `G (_, _, ℓ) = (ℓ(n + 1) - ℓ(n))_n`. -/
noncomputable def incrementsOf (x : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) : ℕ → ℝ :=
  fun n => x.2.2 ((n : ℝ≥0) + 1) - x.2.2 (n : ℝ≥0)

theorem measurable_incrementsOf : Measurable incrementsOf :=
  measurable_pi_iff.2 fun n =>
    ((measurable_pi_apply ((n : ℝ≥0) + 1)).comp (measurable_snd.comp measurable_snd)).sub
      ((measurable_pi_apply (n : ℝ≥0)).comp (measurable_snd.comp measurable_snd))

theorem incrementsOf_pathObs (hU : IsSLEDriverAdapted a b c U P ℱ) (k : ℕ) (q : Ω × ℝ) :
    incrementsOf (pathObs hU (k : ℝ≥0) q) = fun n : ℕ => xiInc hU (n + k) q := by
  funext n
  simp only [incrementsOf, pathObs, pathObsAt, xiInc, logFHat]
  push_cast
  rw [show (k : ℝ≥0) + ((n : ℝ≥0) + 1) = (n : ℝ≥0) + k + 1 by ring,
    show (k : ℝ≥0) + (n : ℝ≥0) = (n : ℝ≥0) + k by ring]
  ring

/-- **Stationarity of `(ξ_n)`**: the laws of the shifted increment sequences on `ℕ → ℝ` agree. -/
theorem xiInc_stationary [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (k : ℕ) :
    (P.prod (admissibleMeasure p)).map (fun q (n : ℕ) => xiInc hU (n + k) q) =
      (P.prod (admissibleMeasure p)).map (fun q (n : ℕ) => xiInc hU n q) := by
  have h1 : (fun q (n : ℕ) => xiInc hU (n + k) q) =
      incrementsOf ∘ pathObs hU (k : ℝ≥0) := by
    funext q; exact (incrementsOf_pathObs hU k q).symm
  have h2 : (fun q (n : ℕ) => xiInc hU n q) = incrementsOf ∘ pathObs hU 0 := by
    funext q
    have := incrementsOf_pathObs hU 0 q
    simp only [Nat.cast_zero, add_zero] at this
    exact this.symm
  rw [h1, h2, ← Measure.map_map measurable_incrementsOf (measurable_pathObs hU _),
    ← Measure.map_map measurable_incrementsOf (measurable_pathObs hU _)]
  congr 1
  exact map_pathObs_eq_zero hMO hU ha hb hc hp (k : ℝ≥0)

end Stat

end ComplexSLE.Internal

end
