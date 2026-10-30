/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ComplexSLE.Frozen.Defs.IsSLEDriverAdapted
public import ComplexSLE.Frozen.Defs.IsDiffusionSolution
public import ComplexSLE.Frozen.Defs.DiffusionD
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# EXTERNAL input: `ito_formula`

Author-approved classical input (ERRATA.md R24, R25). Assumed, not proved: its body is a permanent
`sorry`, and every result that uses it is reported `PROVED_REL`.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.External

/-- **E1 (Itô's formula, martingale form; Protter II.35 / Revuz–Yor IV.3.3).** Let `X` be an
`ℝⁿ`-valued continuous semimartingale given by its characteristics: `X` is progressively
measurable, `A` (drift) and `Σ` (diffusion matrix) are progressively measurable with locally
integrable paths, each `Mⁱ := Xⁱ - Xⁱ₀ - ∫₀ᵗ Aⁱ_s ds` is a continuous local martingale and so is
each `Mⁱ Mʲ - ∫₀ᵗ Σⁱʲ_s ds` (this pins `⟨Mⁱ, Mʲ⟩ = ∫ Σⁱʲ`). If `F` is measurable and `C²` on an
open set `D` containing the path of `X` (`F` measurable so that `F ∘ X` is adapted off the null
set; `X` continuous for every `ω` so that exit times of compact subsets of `D` are stopping
times), then
`F(X_t) - F(X_0) - ∫₀ᵗ (∑ᵢ ∂ᵢF(X_s) Aⁱ_s + ½ ∑ᵢⱼ ∂ᵢⱼF(X_s) Σⁱʲ_s) ds`
is a continuous local martingale. The complex case (`log f_t(z)`, `step:polar-ito-log`) is
`n = 3` with `X = (A_t, Re U_t, Im U_t)`, `A_t = z + ∫ 2/f_s ds`, `Σ = diag(0, covMatrix)`, applied
to `Re` and `Im` of a branch of `log`, stopped before `f` leaves a compact subset of `ℂ∖{0}`;
the real case (`step:kol-ito-expectation`) is `n = 1` with `X` an `IsDiffusionSolution`. -/
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
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ComplexSLE.External

end
-- FROZEN_ANCHOR_SUFFIX_END
