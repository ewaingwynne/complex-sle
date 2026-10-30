/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Independent families on a product space

If `X : ι → Ω₁ → β₁` is an independent family under `μ` and `Y : ι → Ω₂ → β₂` is an independent
family under `ν`, then the paired family `i ↦ (X i ω.1, Y i ω.2)` is independent under `μ.prod ν`.
(Used for two independent copies of a Brownian motion.)
-/

public section

open MeasureTheory ProbabilityTheory

namespace ComplexSLE.Internal

variable {ι : Type*} [Finite ι] {Ω₁ Ω₂ β₁ β₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
  [MeasurableSpace β₁] [MeasurableSpace β₂] {μ : Measure Ω₁} {ν : Measure Ω₂}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Pairing two independent families, living on the two factors of a product probability space,
gives an independent family. -/
theorem iIndepFun_prod_pair {X : ι → Ω₁ → β₁} {Y : ι → Ω₂ → β₂} (hX : iIndepFun X μ)
    (hY : iIndepFun Y ν) (mX : ∀ i, AEMeasurable (X i) μ) (mY : ∀ i, AEMeasurable (Y i) ν) :
    iIndepFun (fun i (ω : Ω₁ × Ω₂) => (X i ω.1, Y i ω.2)) (μ.prod ν) := by
  have := Fintype.ofFinite ι
  have mXf : AEMeasurable (fun ω i => X i ω) μ := AEMeasurable.of_eval mX
  have mYf : AEMeasurable (fun ω i => Y i ω) ν := AEMeasurable.of_eval mY
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => by fun_prop)]
  have hfun : (fun (ω : Ω₁ × Ω₂) i => (X i ω.1, Y i ω.2)) =
      (MeasurableEquiv.arrowProdEquivProdArrow β₁ β₂ ι).symm ∘
        Prod.map (fun ω i => X i ω) (fun ω i => Y i ω) := by
    ext ω i <;> rfl
  have hpair : ∀ i, (μ.prod ν).map (fun ω : Ω₁ × Ω₂ => (X i ω.1, Y i ω.2)) =
      (μ.map (X i)).prod (ν.map (Y i)) := fun i =>
    (Measure.map_prod_map_of_aemeasurable μ ν (mX i) (mY i)).symm
  simp_rw [hpair]
  rw [hfun, ← AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map_of_aemeasurable μ ν mXf mYf, hX.map_fun_eq_pi_map mX,
    hY.map_fun_eq_pi_map mY]
  have := (measurePreserving_arrowProdEquivProdArrow β₁ β₂ ι (fun i => μ.map (X i))
    (fun i => ν.map (Y i))).symm
  exact this.map_eq

end ComplexSLE.Internal

end
