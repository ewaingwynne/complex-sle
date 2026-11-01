/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Ito.Bounded
public import ComplexSLE.Infrastructure.Ito.LocalizeData

/-!
# Measurability and continuity of the Itô process `Y = F(X) - F(X₀) - ∫ (generator)`

* `isStronglyProgressive_itoProc`: `Y` is progressively measurable for every `ω`
  (`F ∘ X`, `F ∘ X₀`, and the path integral of the progressive generator).
* `continuous_itoProc`: along a path that stays in the open set `D` where `F` is `C²`, with locally
  integrable drift and diffusion densities, `Y` is continuous (the generator is locally integrable
  because it agrees on the compact image of `[0, t]` with the generator of a compactly supported
  `C²` function, `exists_cutoff`).
-/

@[expose] public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Infrastructure.Ito

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m0} {d : ℕ}
  {X A : ℝ≥0 → Ω → (Fin d → ℝ)} {Q : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ}
  {F : (Fin d → ℝ) → ℝ}

/-- The process `(t, ω) ↦ X₀ ω` (constant in time) is progressive. -/
theorem isStronglyProgressive_initial (hX : IsStronglyProgressive ℱ X) :
    IsStronglyProgressive ℱ fun _ ω => X 0 ω := fun i => by
  let _ : MeasurableSpace (Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
  have h : StronglyMeasurable[ℱ i] (X 0) :=
    (hX.stronglyAdapted 0).mono (ℱ.mono (zero_le : (0 : ℝ≥0) ≤ i))
  exact h.comp_measurable (@measurable_snd (Iic i) Ω Subtype.instMeasurableSpace (ℱ i))

/-- The Itô process is progressive (no regularity of `F` beyond measurability is needed). -/
theorem isStronglyProgressive_itoProc (hX : IsStronglyProgressive ℱ X)
    (hA : IsStronglyProgressive ℱ A) (hQ : IsStronglyProgressive ℱ Q) (hFm : Measurable F) :
    IsStronglyProgressive ℱ (itoProc F X A Q) :=
  ((isStronglyProgressive_comp_measurable hX hFm).sub
    (isStronglyProgressive_comp_measurable (isStronglyProgressive_initial hX) hFm)).sub
    (isStronglyProgressive_pathIntegral
      (isStronglyProgressive_itoDrift hX hA hQ (measurable_gF F) (measurable_HF F)))

/-- The generator of Itô's formula is locally integrable along a path in `D`. -/
theorem intervalIntegrable_itoDrift_of_contDiffOn (hXc : ∀ ω, Continuous fun t => X t ω) {ω : Ω}
    (hA : ∀ (i : Fin d) (t : ℝ≥0), IntervalIntegrable (fun s : ℝ => A s.toNNReal ω i) volume 0 t)
    (hQ : ∀ (i j : Fin d) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => Q s.toNNReal ω i j) volume 0 t)
    {D : Set (Fin d → ℝ)} (hD : IsOpen D) (hF : ContDiffOn ℝ 2 F D) (hXD : ∀ t, X t ω ∈ D)
    (t : ℝ≥0) :
    IntervalIntegrable (fun x : ℝ => itoDrift F X A Q x.toNNReal ω) volume 0 t := by
  set K : Set (Fin d → ℝ) := (fun s : ℝ≥0 => X s ω) '' Icc 0 t with hKdef
  have hK : IsCompact K := isCompact_Icc.image (hXc ω)
  have hKD : K ⊆ D := by
    rintro _ ⟨s, -, rfl⟩
    exact hXD s
  obtain ⟨F', hF'c, -, hF'eq⟩ := exists_cutoff hK hD hKD hF
  refine (intervalIntegrable_itoDrift hF'c hXc hA hQ t).congr fun x hx => ?_
  rw [uIoc_of_le t.coe_nonneg] at hx
  have hxt : x.toNNReal ≤ t := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (le_of_lt hx.1)]; exact hx.2
  have h := hF'eq _ (⟨x.toNNReal, ⟨zero_le, hxt⟩, rfl⟩ : X x.toNNReal ω ∈ K)
  simp only [itoDrift, gF_congr h, HF_congr h]

/-- **Path continuity of the Itô process** along a path in `D` with locally integrable densities. -/
theorem continuous_itoProc (hXc : ∀ ω, Continuous fun t => X t ω) {ω : Ω}
    (hA : ∀ (i : Fin d) (t : ℝ≥0), IntervalIntegrable (fun s : ℝ => A s.toNNReal ω i) volume 0 t)
    (hQ : ∀ (i j : Fin d) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => Q s.toNNReal ω i j) volume 0 t)
    {D : Set (Fin d → ℝ)} (hD : IsOpen D) (hF : ContDiffOn ℝ 2 F D) (hXD : ∀ t, X t ω ∈ D) :
    Continuous fun t => itoProc F X A Q t ω :=
  ((hF.continuousOn.comp_continuous (hXc ω) hXD).sub continuous_const).sub
    (continuous_pathIntegral (intervalIntegrable_itoDrift_of_contDiffOn hXc hA hQ hD hF hXD))

/-- `Mⁱ = Xⁱ - Xⁱ₀ - ∫ Aⁱ` is progressive. -/
theorem isStronglyProgressive_Mp (hX : IsStronglyProgressive ℱ X) (hA : IsStronglyProgressive ℱ A)
    (i : Fin d) : IsStronglyProgressive ℱ (Mp X A i) :=
  ((isStronglyProgressive_apply hX i).sub
    (isStronglyProgressive_apply (isStronglyProgressive_initial hX) i)).sub
    (isStronglyProgressive_pathIntegral (isStronglyProgressive_apply hA i))

/-- `Nⁱʲ = Mⁱ Mʲ - ∫ Qⁱʲ` is progressive. -/
theorem isStronglyProgressive_Np (hX : IsStronglyProgressive ℱ X) (hA : IsStronglyProgressive ℱ A)
    (hQ : IsStronglyProgressive ℱ Q) (i j : Fin d) : IsStronglyProgressive ℱ (Np X A Q i j) :=
  ((isStronglyProgressive_Mp hX hA i).mul (isStronglyProgressive_Mp hX hA j)).sub
    (isStronglyProgressive_pathIntegral (isStronglyProgressive_matrix_apply hQ i j))

end ComplexSLE.Infrastructure.Ito

end
