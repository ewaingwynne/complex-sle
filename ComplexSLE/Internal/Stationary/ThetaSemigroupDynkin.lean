/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.ThetaSemigroupFeller
public import ComplexSLE.Internal.Stationary.ItoReal
public import ComplexSLE.Infrastructure.Stochastic.ContinuousModification
public import ComplexSLE.Internal.Density.Basic

/-!
# The semigroup of `θ̂` (M10-R3): Dynkin's formula

`thetaSemigroup_sub_self` (Dynkin): for `β` continuous with `β² = 2D` and `g ∈ C²` that is
`π`-periodic,

  `Q_t g(u) - g(u) = ∫₀ᵗ Q_s (L g)(u) ds`,   `L = generator µ β`.

Route: `θ̂(e^{iu})` solves the martingale problem for `(µ, β)`
(`isDiffusionSolution_thetaHat_of_sq`); take an everywhere-continuous modification `X`
(`IsDiffusionSolution.exists_continuous_version`, for the completed filtration), apply the Itô
identity in expectation `IsDiffusionSolution.integral_sub_integral_eq` to `X`, transfer back to `θ̂`
(`X = θ̂` a.s. for all times), use `θ̂_0 = [u]_{2π}` a.s. and `2π`-periodicity of `g`, and exchange
`E` and `∫₀ᵗ ds` by Fubini.

The Itô identity in expectation is `IsDiffusionSolution.integral_sub_integral_eq` (`ItoReal.lean`).
-/

public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter Function

namespace ComplexSLE.Internal

open Polar

section Dynkin

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-- `g([u]_{2π}) = g(u)` for `π`-periodic `g`. -/
theorem periodic_toIcoMod {g : ℝ → ℝ} (hper : Periodic g π) (u : ℝ) :
    g (toIcoMod Real.two_pi_pos 0 u) = g u := by
  rw [← self_sub_toIcoDiv_zsmul, zsmul_eq_mul]
  have : u - (toIcoDiv Real.two_pi_pos 0 u : ℝ) * (2 * π) =
      u - ((2 * toIcoDiv Real.two_pi_pos 0 u : ℤ) : ℝ) * π := by push_cast; ring
  rw [this]
  exact hper.sub_int_mul_eq _

/-- The generator of `(µ, β)` is `π`-periodic on a `π`-periodic `g`. -/
theorem periodic_generator_mu {β : ℝ → ℝ} (hβsq : ∀ v, β v ^ 2 = 2 * diffusionD a b c v)
    {g : ℝ → ℝ} (hper : Periodic g π) :
    Periodic (generator (mu a b c) β g) π := by
  intro v
  have hd : ∀ {h : ℝ → ℝ}, Periodic h π → ∀ v, deriv h (v + π) = deriv h v := by
    intro h hh v
    rw [← deriv_comp_add_const]
    congr 1
    funext x
    exact hh x
  have h1 : deriv g (v + π) = deriv g v := hd hper v
  have h2 : deriv (deriv g) (v + π) = deriv (deriv g) v := by
    refine hd (fun x => ?_) v
    exact hd hper x
  unfold generator
  rw [h1, h2, mu_periodic a b c v, hβsq, hβsq, diffusionD_periodic a b c v]

variable [IsProbabilityMeasure P]

/-- **Dynkin's formula for `θ̂`**: `Q_t g(u) - g(u) = ∫₀ᵗ Q_s (Lg)(u) ds` for `g ∈ C²` that is
`π`-periodic. -/
theorem thetaSemigroup_sub_self (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b)
    (hc : c ^ 2 ≤ a * b) {β : ℝ → ℝ} (hβc : Continuous β)
    (hβsq : ∀ v, β v ^ 2 = 2 * diffusionD a b c v) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hper : Periodic g π) (t : ℝ≥0) (u : ℝ) :
    thetaSemigroup hU t g u - g u =
      ∫ s in (0 : ℝ)..(t : ℝ),
        thetaSemigroup hU s.toNNReal (generator (mu a b c) β g) u := by
  set L := generator (mu a b c) β g with hL
  obtain ⟨Cg, hCg⟩ := exists_abs_le_of_periodic hg.continuous hper
  have hLc : Continuous L := continuous_generator (continuous_mu a b c) hβc hg
  have hLper : Periodic L π := periodic_generator_mu hβsq hper
  obtain ⟨CL, hCL⟩ := exists_abs_le_of_periodic hLc hLper
  -- an everywhere-continuous modification of `θ̂(e^{iu})`
  have hsol := isDiffusionSolution_thetaHat_of_sq hU ha hb hc hβsq u
  let 𝒢 : Filtration ℝ≥0 m :=
    { seq := fun s => sigmaFiltration hU (unitPt u) s ⊔
        MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet[m] N ∧ P N = 0}
      mono' := fun _ _ hst => sup_le_sup_right ((sigmaFiltration hU (unitPt u)).mono hst) _
      le' := fun s => sup_le ((sigmaFiltration hU (unitPt u)).le s)
        (MeasurableSpace.generateFrom_le fun _ hN => hN.1) }
  obtain ⟨X, hae, hXc, hX⟩ := hsol.exists_continuous_version 𝒢 fun s => rfl
  have hXm : ∀ s, Measurable (X s) := fun s => IsDiffusionSolution.measurable hX s
  have hmain := IsDiffusionSolution.integral_sub_integral_eq hX hXc (continuous_mu a b c) hβc hg
    hCg hCL t
  -- the left-hand side
  have hae' : ∀ᵐ ω ∂P, ∀ s, X s ω = thetaHat hU (unitPt u) s ω := hae
  have hlhs : ∀ s : ℝ≥0, ∀ {φ : ℝ → ℝ}, ∫ ω, φ (X s ω) ∂P = thetaSemigroup hU s φ u := fun s φ =>
    integral_congr_ae (by filter_upwards [hae'] with ω hω; simp only [hω])
  have h0 : ∫ ω, g (X 0 ω) ∂P = g u := by
    rw [integral_congr_ae (g := fun _ => g u)
      (by
        filter_upwards [hae', ae_thetaHat_zero hU ha hc u] with ω h1 h2
        rw [h1, h2, periodic_toIcoMod hper]), integral_const]
    simp
  -- the right-hand side, by Fubini
  have hjoint : Measurable (Function.uncurry X) :=
    measurable_uncurry_of_continuous_of_measurable hXc hXm
  have hFm : Measurable (Function.uncurry fun (s : ℝ) (ω : Ω) => L (X s.toNNReal ω)) :=
    hLc.measurable.comp (hjoint.comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd))
  have : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) (t : ℝ))) := by
    rw [uIoc_of_le t.coe_nonneg]; infer_instance
  have hint : Integrable (Function.uncurry fun (s : ℝ) (ω : Ω) => L (X s.toNNReal ω))
      ((volume.restrict (uIoc (0 : ℝ) (t : ℝ))).prod P) :=
    (integrable_const CL).mono' hFm.aestronglyMeasurable
      (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hCL _)
  have hswap := intervalIntegral_integral_swap (a := (0 : ℝ)) (b := (t : ℝ)) hint
  have hrhs : ∫ ω, pathIntegral (fun s ω => L (X s ω)) t ω ∂P =
      ∫ s in (0 : ℝ)..(t : ℝ), thetaSemigroup hU s.toNNReal L u := by
    unfold pathIntegral
    rw [← hswap]
    congr 1
    funext s
    exact hlhs s.toNNReal
  rw [hlhs t, h0, hrhs] at hmain
  exact hmain

end Dynkin

end ComplexSLE.Internal

end
