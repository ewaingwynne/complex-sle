/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsContLocalMartingale
public import ComplexSLE.Frozen.Defs.PathIntegral
public import ComplexSLE.Infrastructure.Ito.LocalizeReduction

/-!
# Itô's formula, martingale form (proof of the external input)

A complete proof of the exact statement of `ComplexSLE.External.ito_formula` (E1, Protter II.35 /
Revuz–Yor IV.3.3). The statement is copied verbatim; this module deliberately does not import
`ComplexSLE.External.*`.

Route (`ComplexSLE/Infrastructure/Ito/Localize*.lean`), valid for an arbitrary filtration (neither
complete nor right-continuous), although `Mⁱ`, `Nⁱʲ` and the drift integrals are only almost surely
continuous / finite:

* the bounded core `Infrastructure.Ito.martingale_ito_bounded` (Mathlib martingales and conditional
  expectations; compactly supported cutoff of `F`);
* data of everywhere bounded variation (`LocalizeBV.lean`): `Mⁱ`, `Nⁱʲ` are everywhere continuous,
  so the exit times of `∑ᵢ |Mⁱ|` from `[-n, n]` and of `X` from `expU D n` (an open exhaustion of
  `D`, `LocalizeExit.lean`) are genuine stopping times; the data are frozen on
  `{X₀ ∉ expU D n}` (`LocalizeData.lean`) and a bounded continuous local martingale is a
  martingale (`LocalizeStopping.lean`);
* general densities (`LocalizeReduction.lean`): `lintPath φ t = ∫⁻_{(0,t]} (∑ |Aⁱ| + ∑ |Qⁱʲ|)`
  is `ℱ_t`-measurable; the densities are switched off from the first time it is infinite, which
  makes the total variation a right-continuous `[0,∞]`-valued adapted process for every `ω`
  (`LocalizeVariation.lean`), so its level-`n` hitting time is a stopping time. Stopping a local
  martingale with only a.s. continuous paths at a stopping time (`LocalizeStopping.lean`, via the
  completed filtration) gives the stopped `Mⁱ`, `Nⁱʲ`.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Internal.ExternalProofs

open ComplexSLE.Infrastructure.Ito

/-- **Itô's formula, martingale form (Protter II.35 / Revuz–Yor IV.3.3).** Same statement as
`ComplexSLE.External.ito_formula`, proved. -/
theorem ito_formula {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹_›) {n : ℕ} (X A : ℝ≥0 → Ω → (Fin n → ℝ))
    (Q : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : IsStronglyProgressive ℱ X) (hXc : ∀ ω, Continuous fun t => X t ω)
    (hA : IsStronglyProgressive ℱ A)
    (hAint : ∀ᵐ ω ∂P, ∀ (i : Fin n) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => A (Real.toNNReal s) ω i) volume 0 t)
    (hQ : IsStronglyProgressive ℱ Q)
    (hQint : ∀ᵐ ω ∂P, ∀ (i j : Fin n) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => Q (Real.toNNReal s) ω i j) volume 0 t)
    (hM : ∀ i, IsContLocalMartingale ℱ
      (fun t ω => X t ω i - X 0 ω i - pathIntegral (fun s ω => A s ω i) t ω) P)
    (hMM : ∀ i j, IsContLocalMartingale ℱ (fun t ω =>
      (X t ω i - X 0 ω i - pathIntegral (fun s ω => A s ω i) t ω) *
        (X t ω j - X 0 ω j - pathIntegral (fun s ω => A s ω j) t ω) -
        pathIntegral (fun s ω => Q s ω i j) t ω) P)
    (D : Set (Fin n → ℝ)) (hD : IsOpen D) (F : (Fin n → ℝ) → ℝ) (hFm : Measurable F)
    (hF : ContDiffOn ℝ 2 F D) (hXD : ∀ᵐ ω ∂P, ∀ t, X t ω ∈ D) :
    IsContLocalMartingale ℱ (fun t ω => F (X t ω) - F (X 0 ω) -
      pathIntegral (fun s ω =>
        ∑ i, fderiv ℝ F (X s ω) (Pi.single i 1) * A s ω i +
          (1 / 2) * ∑ i, ∑ j,
            iteratedFDeriv ℝ 2 F (X s ω) ![Pi.single i 1, Pi.single j 1] * Q s ω i j) t ω) P :=
  isContLocalMartingale_itoProc hX hXc hA hQ hAint hQint hM hMM hD hFm hF hXD

end ComplexSLE.Internal.ExternalProofs

end
