/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.PathStat

/-!
# Regeneration data for the 0-1 law of the Birkhoff limit (M7/A5b)

For an adapted driver `hU`, a point `z` and `k : ℕ`, a `RegenDatum hU z k` packages the output of
the construction of the regeneration time of Lemma 3.3 (paper.tex:L1361-1372): an a.s. finite
`ℱ`-stopping time `S` (the first `ℱ`-time at which `e^{2iθ_t(z)} = 1` after `σ_z(k)`), and its
σ-time `τ` (so `σ_z(τ) = S`, `τ ≥ k`, `e^{2iθ̂_τ} = 1`), such that the path observable after `τ`
is the observable of the rescaled post-`S` driver started at the `ℱ_S`-measurable state
`(|f̂_τ|, θ̂_τ)`. The consumers (`ErgodicConstFibre.lean`) use only these fields, together with the
strong Markov step (`lintegral_comp_scale_postPath`-type lemmas); the construction of the datum is
in `ErgodicConstStop.lean`.
-/

@[expose] public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal

open Polar

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-- **A regeneration datum at level `k`** for the chain started at `z` (see the module docstring).
`S` is an a.s. finite `ℱ`-stopping time; `τ` is the corresponding σ-time; the state
`X = (|f̂_τ|, θ̂_τ)` is `ℱ_S`-measurable, the state satisfies `e^{2iθ̂_τ} = 1`, the observable after
`τ` is the one of the rescaled post-`S` path, `τ ≥ k`, and `log |f̂_n|` is `ℱ_S`-measurable for
`n ≤ k`. -/
structure RegenDatum (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) (k : ℕ) where
  /-- the regeneration time (an `ℱ`-stopping time) -/
  S : Ω → WithTop ℝ≥0
  hS : IsStoppingTime ℱ S
  hfin : ∀ᵐ ω ∂P, S ω ≠ ⊤
  /-- its σ-time -/
  τ : Ω → ℝ≥0
  hX : Measurable[hS.measurableSpace]
    (fun ω => (‖fHat hU z (τ ω) ω‖₊, thetaHat hU z (τ ω) ω))
  hpos : ∀ᵐ ω ∂P, 0 < ‖fHat hU z (τ ω) ω‖₊
  hobs : ∀ᵐ ω ∂P, pathObsAt hU z (τ ω) ω =
    obsC (CPath.scale (‖fHat hU z (τ ω) ω‖₊)⁻¹ (postPath hU S ω), thetaHat hU z (τ ω) ω)
  hstate : ∀ᵐ ω ∂P, Complex.exp (2 * Complex.I * (thetaHat hU z (τ ω) ω : ℂ)) = 1
  hk : ∀ᵐ ω ∂P, (k : ℝ≥0) ≤ τ ω
  hpast : ∀ n : ℕ, n ≤ k →
    Measurable[hS.measurableSpace] (fun ω => Real.log ‖fHat hU z (n : ℝ≥0) ω‖)

end ComplexSLE.Internal

end
