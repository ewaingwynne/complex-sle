/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Ito.Discrete
public import ComplexSLE.Infrastructure.Ito.MartingaleTransform
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# The setting of the bounded core of Itô's formula

* `BoundedSetting ℱ P X A Q C`: the hypotheses on the process (`X` continuous and progressive,
  drift and diffusion densities `A`, `Q` with bounded total variation, bounded martingale part,
  `Mⁱ` and `Nⁱʲ` martingales).
* `exists_bounds`: global bounds for a `C²` function with compact support (the function, its
  first partials and its second partials), together with the continuity of `∂ᵢF`, `∂ᵢⱼF` and the
  uniform continuity of `D²F`.
-/

@[expose] public section

open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Infrastructure.Ito

section FBounds

variable {n : ℕ} {F : (Fin n → ℝ) → ℝ}

theorem HF_eq (F : (Fin n → ℝ) → ℝ) (i j : Fin n) (x : Fin n → ℝ) :
    HF F i j x = fderiv ℝ (fderiv ℝ F) x (Pi.single i 1) (Pi.single j 1) := by
  simp [HF, iteratedFDeriv_two_apply]

theorem continuous_gF (hF : ContDiff ℝ 2 F) (i : Fin n) : Continuous (gF F i) :=
  (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem continuous_HF (hF : ContDiff ℝ 2 F) (i j : Fin n) : Continuous (HF F i j) := by
  have : HF F i j = fun x => fderiv ℝ (fderiv ℝ F) x (Pi.single i 1) (Pi.single j 1) :=
    funext (HF_eq F i j)
  rw [this]
  exact (((hF.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply
    continuous_const).clm_apply continuous_const

theorem continuous_iteratedFDeriv_two (hF : ContDiff ℝ 2 F) :
    Continuous (iteratedFDeriv ℝ 2 F) :=
  hF.continuous_iteratedFDeriv (by norm_cast)

/-- Global bounds for a `C²` function with compact support. -/
theorem exists_bounds (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) :
    ∃ L₀ L₁ L₂ : ℝ, (∀ x, |F x| ≤ L₀) ∧ (∀ i x, |gF F i x| ≤ L₁) ∧
      (∀ i j x, |HF F i j x| ≤ L₂) ∧ (∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ L₂) := by
  obtain ⟨L₀, hL₀⟩ := hFc.exists_bound_of_continuous hF.continuous
  obtain ⟨L₁, hL₁⟩ := (hFc.fderiv ℝ).exists_bound_of_continuous (hF.continuous_fderiv (by norm_num))
  obtain ⟨L₂, hL₂⟩ := (hFc.iteratedFDeriv 2).exists_bound_of_continuous
    (continuous_iteratedFDeriv_two hF)
  refine ⟨L₀, L₁, L₂, fun x => by simpa using hL₀ x, fun i x => ?_, fun i j x => ?_,
    fun x => hL₂ x⟩
  · have := (fderiv ℝ F x).le_opNorm (Pi.single i 1)
    rw [Pi.norm_single, norm_one, mul_one] at this
    simpa [gF, Real.norm_eq_abs] using this.trans (hL₁ x)
  · have := (iteratedFDeriv ℝ 2 F x).le_opNorm ![Pi.single i 1, Pi.single j 1]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.norm_single,
      norm_one, mul_one] at this
    simpa [HF, Real.norm_eq_abs] using this.trans (hL₂ x)

theorem uniformContinuous_iteratedFDeriv_two (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) :
    UniformContinuous (iteratedFDeriv ℝ 2 F) :=
  (hFc.iteratedFDeriv 2).uniformContinuous_of_continuous (continuous_iteratedFDeriv_two hF)

end FBounds

section Setting

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {n : ℕ}

/-- The hypotheses of the bounded core of Itô's formula: a continuous progressive process
`X = X₀ + M + ∫A` whose drift and diffusion densities `A`, `Q` have a.s. bounded total variation
`≤ C`, whose martingale part is a.s. bounded by `C`, and such that `Mⁱ` and
`Nⁱʲ = Mⁱ Mʲ - ∫Qⁱʲ` are martingales. -/
structure BoundedSetting (ℱ : Filtration ℝ≥0 m0) (P : Measure Ω) (X A : ℝ≥0 → Ω → (Fin n → ℝ))
    (Q : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ) (C : ℝ) : Prop where
  C_nonneg : 0 ≤ C
  prog_X : IsStronglyProgressive ℱ X
  cont_X : ∀ ω, Continuous fun t => X t ω
  prog_A : IsStronglyProgressive ℱ A
  prog_Q : IsStronglyProgressive ℱ Q
  int_A : ∀ᵐ ω ∂P, ∀ (i : Fin n) (t : ℝ≥0),
    IntervalIntegrable (fun s : ℝ => A s.toNNReal ω i) volume 0 t
  int_Q : ∀ᵐ ω ∂P, ∀ (i j : Fin n) (t : ℝ≥0),
    IntervalIntegrable (fun s : ℝ => Q s.toNNReal ω i j) volume 0 t
  abs_A : ∀ᵐ ω ∂P, ∀ (i : Fin n) (t : ℝ≥0), ∫ s in (0 : ℝ)..(t : ℝ), |A s.toNNReal ω i| ≤ C
  abs_Q : ∀ᵐ ω ∂P, ∀ (i j : Fin n) (t : ℝ≥0),
    ∫ s in (0 : ℝ)..(t : ℝ), |Q s.toNNReal ω i j| ≤ C
  bd_M : ∀ᵐ ω ∂P, ∀ (i : Fin n) (t : ℝ≥0), |Mp X A i t ω| ≤ C
  mart_M : ∀ i, Martingale (Mp X A i) ℱ P
  mart_N : ∀ i j, Martingale (Np X A Q i j) ℱ P

namespace BoundedSetting

variable {P : Measure Ω} {ℱ : Filtration ℝ≥0 m0} {X A : ℝ≥0 → Ω → (Fin n → ℝ)}
  {Q : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ} {C : ℝ} (h : BoundedSetting ℱ P X A Q C)
include h

theorem stronglyMeasurable_X (u : ℝ≥0) : StronglyMeasurable[ℱ u] (X u) :=
  h.prog_X.stronglyAdapted u

theorem measurable_X (u : ℝ≥0) : Measurable (X u) :=
  ((h.stronglyMeasurable_X u).mono (ℱ.le u)).measurable

theorem abs_Np_le : ∀ᵐ ω ∂P, ∀ (i j : Fin n) (t : ℝ≥0), |Np X A Q i j t ω| ≤ C ^ 2 + C := by
  filter_upwards [h.bd_M, h.abs_Q] with ω h1 h2 i j t
  have hQ : |pathIntegral (fun s ω => Q s ω i j) t ω| ≤ C :=
    (abs_pathIntegral_le t).trans (h2 i j t)
  have hM : |Mp X A i t ω * Mp X A j t ω| ≤ C ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul (h1 i t) (h1 j t) (abs_nonneg _) h.C_nonneg
  calc |Np X A Q i j t ω| = |Mp X A i t ω * Mp X A j t ω -
        pathIntegral (fun s ω => Q s ω i j) t ω| := rfl
    _ ≤ |Mp X A i t ω * Mp X A j t ω| + |pathIntegral (fun s ω => Q s ω i j) t ω| := abs_sub _ _
    _ ≤ C ^ 2 + C := add_le_add hM hQ

end BoundedSetting

end Setting

end ComplexSLE.Infrastructure.Ito

end
