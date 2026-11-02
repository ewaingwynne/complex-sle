/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsSLEDriver
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import ComplexSLE.External.ExistsIsBrownianReal
import ComplexSLE.Internal.Driver.ProdIndep
import ComplexSLE.Internal.Driver.Process
import Mathlib.Probability.BrownianMotion.Basic

/-!
# Provider for `ComplexSLE.exists_sleDriver`

Implementation module for the frozen anchor `ComplexSLE/Frozen/ExistsSLEDriver.lean`.
The anchor is SEALED: it is proved by this module.

Proof. Take a real Brownian motion `B` on `(Ω, P)` (classical input `exists_isBrownianReal`) and put
`U t (ω₁, ω₂) = L (B t ω₁, B t ω₂)` on `(Ω × Ω, P ⊗ P)`, where `L` is the real-linear map
`driverCLM a b c : ℝ × ℝ →L[ℝ] ℂ` with `A Aᵀ = covMatrix a b c`
(`ComplexSLE.Internal.Driver.Process`).
Path continuity and `U 0 = 0` come from the two components; independent increments from the
independence of the two factors (`iIndepFun_prod_pair`) transported through the linear map `L`;
the increment law from `map_prod_gaussianReal_matrixApplyPair` (a linear image of a product of
two `N(0, t - s)` laws is the multivariate Gaussian `N(0, (t - s) A Aᵀ)`).
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ComplexSLE.Internal

/-- See `ComplexSLE.exists_sleDriver`. -/
theorem exists_sleDriver (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (U : ℝ≥0 → Ω → ℂ), IsSLEDriver a b c U P := by
  -- `0 < b` is not needed: `0 ≤ b` already follows from `c ^ 2 ≤ a * b`
  have _ := hb
  obtain ⟨Ω, mΩ, P, hP, B, hB⟩ := External.exists_isBrownianReal
  refine ⟨Ω × Ω, inferInstance, P.prod P, inferInstance,
    fun t ω => driverCLM a b c (B t ω.1, B t ω.2), ?_⟩
  have aeB : ∀ t, AEMeasurable (B t) P := hB.toIsPreBrownianReal.aemeasurable
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- continuity
    have h1 : ∀ᵐ ω ∂(P.prod P), Continuous fun t => B t ω.1 :=
      Measure.quasiMeasurePreserving_fst.ae hB.cont
    have h2 : ∀ᵐ ω ∂(P.prod P), Continuous fun t => B t ω.2 :=
      Measure.quasiMeasurePreserving_snd.ae hB.cont
    filter_upwards [h1, h2] with ω hω1 hω2
    exact (driverCLM a b c).continuous.comp (hω1.prodMk hω2)
  · -- `U 0 = 0`
    have h1 : ∀ᵐ ω ∂(P.prod P), B 0 ω.1 = 0 :=
      Measure.quasiMeasurePreserving_fst.ae hB.eval_zero_ae_eq_zero
    have h2 : ∀ᵐ ω ∂(P.prod P), B 0 ω.2 = 0 :=
      Measure.quasiMeasurePreserving_snd.ae hB.eval_zero_ae_eq_zero
    filter_upwards [h1, h2] with ω hω1 hω2
    show driverCLM a b c (B 0 ω.1, B 0 ω.2) = 0
    rw [hω1, hω2, Prod.mk_zero_zero, map_zero]
  · -- independent increments
    have hW : HasIndepIncrements (fun t (ω : Ω × Ω) => (B t ω.1, B t ω.2)) (P.prod P) := by
      intro n t ht
      have hX := hB.hasIndepIncrements n t ht
      exact iIndepFun_prod_pair hX hX (fun i => (aeB _).sub (aeB _)) (fun i => (aeB _).sub (aeB _))
    exact hW.map (driverCLM a b c)
  · -- law of the increments
    intro s t hst
    have hst' : (s : ℝ) ≤ t := NNReal.coe_le_coe.2 hst
    have hlaw := hB.hasLaw_sub t s
    have hv : ((nndist t.1 s.1 : ℝ≥0) : ℝ) = (t : ℝ) - s := by
      rw [coe_nndist, Real.dist_eq]
      exact abs_of_nonneg (sub_nonneg.2 hst')
    have := hasLaw_driverCLM_pair hlaw a b c ha hc
    rw [hv] at this
    convert this using 2
    rw [← map_sub]
    rfl

end ComplexSLE.Internal

end
