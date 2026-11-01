/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Ito.Core
public import ComplexSLE.Infrastructure.Ito.Cutoff

/-!
# Itô's formula, bounded core (martingale form, no stochastic integrals)

`ComplexSLE.Infrastructure.Ito.martingale_ito_bounded`: the bounded core of the external
`ComplexSLE.External.ito_formula`, proved from Mathlib martingales and conditional expectations
(no external input, no stochastic integral).

Setting: an `ℝⁿ`-valued continuous progressive process `X` with progressive drift density `A` and
diffusion density `Q`, such that almost surely `X` stays in a compact set `K`, `∫₀^∞ |Aⁱ| ≤ C`,
`∫₀^∞ |Qⁱʲ| ≤ C`, `|Mⁱ| ≤ C` for `Mⁱ_t = Xⁱ_t - Xⁱ₀ - ∫₀ᵗ Aⁱ`; and `Mⁱ`,
`Nⁱʲ = Mⁱ Mʲ - ∫₀ᵗ Qⁱʲ` are martingales. For `F` measurable and `C²` on an open `D ⊇ K`,
`F(X_t) - F(X_0) - ∫₀ᵗ (∑ ∂ᵢF(X) Aⁱ + ½ ∑ ∂ᵢⱼF(X) Qⁱʲ)` is a martingale.

The proof replaces `F` by a compactly supported `C²` function `F'` that agrees with `F` near `K`
(`Cutoff.lean`), applies `BoundedSetting.martingale_core` to `F'` (`Core.lean`), and transfers the
conclusion along the almost sure equality of the two processes.
-/

@[expose] public section

open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Infrastructure.Ito

theorem measurable_gF {n : ℕ} (F : (Fin n → ℝ) → ℝ) (i : Fin n) : Measurable (gF F i) :=
  measurable_fderiv_apply_const ℝ F (Pi.single i 1)

theorem measurable_HF {n : ℕ} (F : (Fin n → ℝ) → ℝ) (i j : Fin n) : Measurable (HF F i j) := by
  have : HF F i j = fun x => fderiv ℝ (fderiv ℝ F) x (Pi.single i 1) (Pi.single j 1) :=
    funext (HF_eq F i j)
  rw [this]
  exact (ContinuousLinearMap.measurable_apply (Pi.single j 1)).comp
    (measurable_fderiv_apply_const ℝ (fderiv ℝ F) (Pi.single i 1))

theorem gF_congr {n : ℕ} {F F' : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (h : F' =ᶠ[𝓝 x] F) (i : Fin n) :
    gF F' i x = gF F i x := by
  simp only [gF, h.fderiv_eq]

theorem HF_congr {n : ℕ} {F F' : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (h : F' =ᶠ[𝓝 x] F)
    (i j : Fin n) : HF F' i j x = HF F i j x := by
  simp only [HF_eq]
  rw [h.fderiv.fderiv_eq]

/-- **Itô's formula, bounded core (martingale form, no stochastic integrals).**

Let `X = X₀ + M + ∫A` be an `ℝⁿ`-valued continuous progressive process with progressive drift `A`
and diffusion density `Q`, such that almost surely: `X` stays in the compact set `K`, the total
variations `∫₀^∞ |Aⁱ|` and `∫₀^∞ |Qⁱʲ|` are at most `C` and `|Mⁱ| ≤ C`, where
`Mⁱ_t = Xⁱ_t - Xⁱ₀ - ∫₀ᵗ Aⁱ`; and `Mⁱ`, `Nⁱʲ = Mⁱ Mʲ - ∫₀ᵗ Qⁱʲ` are martingales. If `F` is
measurable and `C²` on an open set `D ⊇ K`, then
`F(X_t) - F(X_0) - ∫₀ᵗ (∑ ∂ᵢF(X) Aⁱ + ½ ∑ ∂ᵢⱼF(X) Qⁱʲ)`
is a martingale. -/
theorem martingale_ito_bounded {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0) {n : ℕ} (X A : ℝ≥0 → Ω → (Fin n → ℝ))
    (Q : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : IsStronglyProgressive ℱ X) (hXc : ∀ ω, Continuous fun t => X t ω)
    (hA : IsStronglyProgressive ℱ A) (hQ : IsStronglyProgressive ℱ Q) (C : ℝ)
    (hAint : ∀ᵐ ω ∂P, ∀ (i : Fin n) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => A (Real.toNNReal s) ω i) volume 0 t)
    (hAC : ∀ᵐ ω ∂P, ∀ (i : Fin n) (t : ℝ≥0),
      ∫ s in (0 : ℝ)..(t : ℝ), |A (Real.toNNReal s) ω i| ≤ C)
    (hQint : ∀ᵐ ω ∂P, ∀ (i j : Fin n) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => Q (Real.toNNReal s) ω i j) volume 0 t)
    (hQC : ∀ᵐ ω ∂P, ∀ (i j : Fin n) (t : ℝ≥0),
      ∫ s in (0 : ℝ)..(t : ℝ), |Q (Real.toNNReal s) ω i j| ≤ C)
    (hMb : ∀ᵐ ω ∂P, ∀ (i : Fin n) (t : ℝ≥0),
      |X t ω i - X 0 ω i - pathIntegral (fun s ω => A s ω i) t ω| ≤ C)
    (hM : ∀ i, Martingale
      (fun t ω => X t ω i - X 0 ω i - pathIntegral (fun s ω => A s ω i) t ω) ℱ P)
    (hMM : ∀ i j, Martingale (fun t ω =>
      (X t ω i - X 0 ω i - pathIntegral (fun s ω => A s ω i) t ω) *
        (X t ω j - X 0 ω j - pathIntegral (fun s ω => A s ω j) t ω) -
        pathIntegral (fun s ω => Q s ω i j) t ω) ℱ P)
    (K : Set (Fin n → ℝ)) (hK : IsCompact K) (D : Set (Fin n → ℝ)) (hD : IsOpen D) (hKD : K ⊆ D)
    (hXK : ∀ᵐ ω ∂P, ∀ t, X t ω ∈ K)
    (F : (Fin n → ℝ) → ℝ) (hFm : Measurable F) (hF : ContDiffOn ℝ 2 F D) :
    Martingale (fun t ω => F (X t ω) - F (X 0 ω) -
      pathIntegral (fun s ω =>
        ∑ i, fderiv ℝ F (X s ω) (Pi.single i 1) * A s ω i +
          (1 / 2) * ∑ i, ∑ j,
            iteratedFDeriv ℝ 2 F (X s ω) ![Pi.single i 1, Pi.single j 1] * Q s ω i j) t ω) ℱ P := by
  obtain ⟨F', hF'c, hF'cs, hF'eq⟩ := exists_cutoff hK hD hKD hF
  have hset : BoundedSetting ℱ P X A Q (max C 0) :=
    { C_nonneg := le_max_right _ _
      prog_X := hX
      cont_X := hXc
      prog_A := hA
      prog_Q := hQ
      int_A := hAint
      int_Q := hQint
      abs_A := by
        filter_upwards [hAC] with ω h i t using (h i t).trans (le_max_left _ _)
      abs_Q := by
        filter_upwards [hQC] with ω h i j t using (h i j t).trans (le_max_left _ _)
      bd_M := by
        filter_upwards [hMb] with ω h i t using (h i t).trans (le_max_left _ _)
      mart_M := hM
      mart_N := hMM }
  have hcore := hset.martingale_core hF'c hF'cs
  -- the drifts of `F` and `F'` agree along paths in `K`
  have hdrift : ∀ᵐ ω ∂P, ∀ s, itoDrift F X A Q s ω = itoDrift F' X A Q s ω := by
    filter_upwards [hXK] with ω hω s
    have h := hF'eq _ (hω s)
    simp only [itoDrift, gF_congr h, HF_congr h]
  have hFeq : ∀ᵐ ω ∂P, ∀ t, F' (X t ω) = F (X t ω) := by
    filter_upwards [hXK] with ω hω t
    exact (hF'eq _ (hω t)).self_of_nhds
  -- adaptedness of the process for `F`
  have hGp : IsStronglyProgressive ℱ (itoDrift F X A Q) :=
    isStronglyProgressive_itoDrift hX hA hQ (measurable_gF F) (measurable_HF F)
  have hFXp : IsStronglyProgressive ℱ fun t ω => F (X t ω) :=
    isStronglyProgressive_comp_measurable hX hFm
  have hadapt : StronglyAdapted ℱ
      (fun t ω => F (X t ω) - F (X 0 ω) - pathIntegral (itoDrift F X A Q) t ω) := fun t =>
    ((hFXp.stronglyAdapted t).sub
      ((hFXp.stronglyAdapted 0).mono (ℱ.mono (by simp : (0 : ℝ≥0) ≤ t)))).sub
      ((isStronglyProgressive_pathIntegral hGp).stronglyAdapted t)
  refine hcore.congr hadapt fun t => ?_
  filter_upwards [hdrift, hFeq] with ω h1 h2
  have h3 : pathIntegral (itoDrift F' X A Q) t ω = pathIntegral (itoDrift F X A Q) t ω := by
    unfold pathIntegral
    exact intervalIntegral.integral_congr fun x _ => (h1 _).symm
  change F' (X t ω) - F' (X 0 ω) - pathIntegral (itoDrift F' X A Q) t ω =
    F (X t ω) - F (X 0 ω) - pathIntegral (itoDrift F X A Q) t ω
  rw [h3, h2, h2]

end ComplexSLE.Infrastructure.Ito

end
