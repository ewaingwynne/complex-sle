/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.PeriodicODE.PoissonMax
public import ComplexSLE.Infrastructure.PeriodicODE.PoissonConst
public import ComplexSLE.Infrastructure.PeriodicODE.PoissonSolve

/-!
# The periodic Poisson equation for a non-degenerate generator

For `T`-periodic continuous `α`, `D`, `r` with `D > 0`, there are a constant `C` and a `C²`
`T`-periodic `g` with `α g' + D g'' = r - C`.

Proof outline. Put `a = α / D` and `A x = ∫₀ˣ a`; every solution of `D h' + α h = f` is
`h = linSol a (f / D) K = e^{-A} (K + ∫₀ˣ e^{A} f / D)`, and `h` is `T`-periodic as soon as
`e^{-A T} (K + ∫₀ᵀ e^{A} f / D) = K`.

* If `A T ≠ 0`, such a `K` exists for every `f`. Take `f = 1` and `f = r` and apply
  `exists_periodic_poisson_of_solutions` (which uses the maximum principle).
* If `A T = 0`, the periodicity condition reads `∫₀ᵀ e^{A} f / D = 0` and does not involve
  `K`. Choose `C` so that it holds for `f = r - C`, then choose `K` so that `∫₀ᵀ h = 0` and
  take `g = ∫₀ˣ h`.

The maximum principle `eq_zero_of_periodic_generator_eq_const` is proved in `PoissonMax`
and `exists_periodic_poisson_of_solutions` in `PoissonConst`.
-/

public section

open Set Filter Topology MeasureTheory intervalIntegral Function
open scoped ContDiff

namespace ComplexSLE.Infrastructure

/-- `linSol (α / D) (f / D) K` solves `D h' + α h = f`. -/
theorem linSol_equation_of_pos {α D f : ℝ → ℝ} (hα : Continuous α) (hD : Continuous D)
    (hDpos : ∀ u, 0 < D u) (hf : Continuous f) (K u : ℝ) :
    D u * deriv (linSol (fun u => α u / D u) (fun u => f u / D u) K) u +
      α u * linSol (fun u => α u / D u) (fun u => f u / D u) K u = f u := by
  have hDne : ∀ u, D u ≠ 0 := fun u => (hDpos u).ne'
  rw [deriv_linSol (a := fun u => α u / D u) (ρ := fun u => f u / D u)
    (hα.div hD hDne) (hf.div hD hDne)]
  have := hDne u
  field_simp
  ring

/-- The periodic Poisson equation when `D > 0` everywhere. -/
theorem exists_periodic_poisson_of_pos {α D r : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hα : Continuous α) (hD : Continuous D) (hDpos : ∀ u, 0 < D u) (hr : Continuous r)
    (hαper : Function.Periodic α T) (hDper : Function.Periodic D T)
    (hrper : Function.Periodic r T) :
    ∃ C : ℝ, ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ Function.Periodic g T ∧
      ∀ u, α u * deriv g u + D u * deriv (deriv g) u = r u - C := by
  have hDne : ∀ u, D u ≠ 0 := fun u => (hDpos u).ne'
  set a : ℝ → ℝ := fun u => α u / D u with ha_def
  have ha : Continuous a := hα.div hD hDne
  have haper : Periodic a T := fun u => by simp only [ha_def, hαper u, hDper u]
  have hperDiv : ∀ {f : ℝ → ℝ}, Periodic f T → Periodic (fun u => f u / D u) T :=
    fun {f} hf u => by simp only [hf u, hDper u]
  have hcDiv : ∀ {f : ℝ → ℝ}, Continuous f → Continuous (fun u => f u / D u) :=
    fun {f} hf => hf.div hD hDne
  have hone : Continuous (fun _ : ℝ => (1 : ℝ)) := continuous_const
  have honeper : Periodic (fun _ : ℝ => (1 : ℝ)) T := fun _ => rfl
  by_cases hAT : primA a T = 0
  · -- the periodicity condition does not involve `K`
    set w₁ : ℝ → ℝ := fun u => Real.exp (primA a u) * (1 / D u) with hw₁
    set wr : ℝ → ℝ := fun u => Real.exp (primA a u) * (r u / D u) with hwr
    have hw₁c : Continuous w₁ := (continuous_primA ha).rexp.mul (hcDiv hone)
    have hwrc : Continuous wr := (continuous_primA ha).rexp.mul (hcDiv hr)
    have hI₁ : 0 < ∫ u in (0)..T, w₁ u :=
      intervalIntegral_pos_of_pos (hw₁c.intervalIntegrable _ _)
        (fun u => mul_pos (Real.exp_pos _) (one_div_pos.2 (hDpos u))) hT
    set C : ℝ := (∫ u in (0)..T, wr u) / ∫ u in (0)..T, w₁ u with hC
    have hrC : Continuous (fun u => r u - C) := hr.sub continuous_const
    have hrCper : Periodic (fun u => r u - C) T := fun u => by simp only [hrper u]
    have hint0 : ∫ u in (0)..T, Real.exp (primA a u) * ((r u - C) / D u) = 0 := by
      have hpt : ∀ u, Real.exp (primA a u) * ((r u - C) / D u) = wr u - C * w₁ u := by
        intro u; simp only [hwr, hw₁]; ring
      simp only [hpt]
      have hi1 : IntervalIntegrable wr volume 0 T := hwrc.intervalIntegrable _ _
      have hi2 : IntervalIntegrable (fun u => C * w₁ u) volume 0 T :=
        (continuous_const.mul hw₁c).intervalIntegrable _ _
      rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul, hC,
        div_mul_cancel₀ _ hI₁.ne', sub_self]
    have hper : ∀ K, Periodic (linSol a (fun u => (r u - C) / D u) K) T := fun K =>
      periodic_linSol ha (hcDiv hrC) haper (hperDiv hrCper) (by simp [hAT, hint0])
    -- choose `K` so that the mean of `h` vanishes
    set ρ : ℝ → ℝ := fun u => (r u - C) / D u with hρ
    have hρc : Continuous ρ := hcDiv hrC
    have hM : 0 < ∫ u in (0)..T, Real.exp (-primA a u) :=
      intervalIntegral_pos_of_pos
        ((continuous_primA ha).neg.rexp.intervalIntegrable _ _) (fun u => Real.exp_pos _) hT
    have hsplit : ∀ K u, linSol a ρ K u = K * Real.exp (-primA a u) + linSol a ρ 0 u := by
      intro K u; unfold linSol; ring
    have hmean : ∀ K, ∫ u in (0)..T, linSol a ρ K u =
        K * (∫ u in (0)..T, Real.exp (-primA a u)) + ∫ u in (0)..T, linSol a ρ 0 u := by
      intro K
      simp only [hsplit K]
      have hi1 : IntervalIntegrable (fun u => K * Real.exp (-primA a u)) volume 0 T :=
        (continuous_const.mul (continuous_primA ha).neg.rexp).intervalIntegrable _ _
      have hi2 : IntervalIntegrable (linSol a ρ 0) volume 0 T :=
        (continuous_linSol ha hρc 0).intervalIntegrable _ _
      rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul]
    set K : ℝ := -(∫ u in (0)..T, linSol a ρ 0 u) / ∫ u in (0)..T, Real.exp (-primA a u)
      with hK
    have hK0 : ∫ u in (0)..T, linSol a ρ K u = 0 := by
      rw [hmean K, hK, div_mul_cancel₀ _ hM.ne']
      ring
    obtain ⟨g, hgc, hgper, hg⟩ := exists_periodic_poisson_of_mean_zero (α := α) (D := D)
      (f := fun u => r u - C) (contDiff_one_linSol ha hρc K) (hper K) hK0
      (fun u => linSol_equation_of_pos hα hD hDpos hrC K u)
    exact ⟨C, g, hgc, hgper, hg⟩
  · -- `A T ≠ 0`: periodic solutions exist for every right-hand side
    obtain ⟨K₁, hK₁⟩ := exists_periodic_linSol_of_ne ha (hcDiv hone) haper (hperDiv honeper) hAT
    obtain ⟨Kr, hKr⟩ := exists_periodic_linSol_of_ne ha (hcDiv hr) haper (hperDiv hrper) hAT
    exact exists_periodic_poisson_of_solutions (r := r) (h₁ := linSol a (fun u => 1 / D u) K₁)
      (hr := linSol a (fun u => r u / D u) Kr) hT (fun u => (hDpos u).le)
      (contDiff_one_linSol ha (hcDiv hone) K₁) hK₁
      (fun u => linSol_equation_of_pos hα hD hDpos hone K₁ u)
      (contDiff_one_linSol ha (hcDiv hr) Kr) hKr
      (fun u => linSol_equation_of_pos hα hD hDpos hr Kr u)

end ComplexSLE.Infrastructure

end
