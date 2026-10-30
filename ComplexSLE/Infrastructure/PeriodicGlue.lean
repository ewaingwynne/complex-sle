/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Gluing periodic functions

Facts about a `T`-periodic function on `ℝ` that is known on one period `[x, x + T)`:
continuity, differentiability and smoothness off the lattice `x + Tℤ` transfer from a single
period, a derivative at a gluing point can be obtained from one-sided limits of the derivative,
and the integral over `[0, 2T]` of a non-negative periodic function that is positive on a
period is positive.
-/

public section

open Set Filter Topology MeasureTheory intervalIntegral Function
open scoped ContDiff

namespace ComplexSLE.Infrastructure

variable {T x : ℝ}

/-- A `T`-periodic function continuous at each point of one period is continuous. -/
theorem Periodic.continuous_of_continuousAt_Ico {f : ℝ → ℝ} (hT : 0 < T) (hf : Periodic f T)
    (h : ∀ v ∈ Ico x (x + T), ContinuousAt f v) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro u
  set k := toIcoDiv hT x u
  have hv : toIcoMod hT x u ∈ Ico x (x + T) := toIcoMod_mem_Ico hT x u
  have hfe : f = fun w => f (w - k • T) := funext fun w => (hf.sub_zsmul_eq k).symm
  rw [hfe]
  have hc : ContinuousAt (fun w => w - k • T) u := (continuous_id.sub continuous_const).continuousAt
  exact ContinuousAt.comp (f := fun w => w - k • T) (h _ hv) hc

/-- A `T`-periodic function with `T`-periodic derivative candidate `f'` that has derivative
`f' v` at each point of one period has derivative `f'` everywhere. -/
theorem Periodic.hasDerivAt_of_Ico {f f' : ℝ → ℝ} (hT : 0 < T) (hf : Periodic f T)
    (hf' : Periodic f' T) (h : ∀ v ∈ Ico x (x + T), HasDerivAt f (f' v) v) (u : ℝ) :
    HasDerivAt f (f' u) u := by
  set k := toIcoDiv hT x u
  have hv : toIcoMod hT x u ∈ Ico x (x + T) := toIcoMod_mem_Ico hT x u
  have hfe : f = fun w => f (w - k • T) := funext fun w => (hf.sub_zsmul_eq k).symm
  have hu : u - k • T = toIcoMod hT x u := rfl
  have h1 : HasDerivAt (fun w => f (w - k • T)) (f' (u - k • T)) u := by
    have := h _ (hu ▸ hv)
    exact this.comp_sub_const u (k • T)
  rw [hf'.sub_zsmul_eq k] at h1
  rwa [hfe]

/-- A `T`-periodic function equal on `(x, x+T)` to a function that is `C^n` there is `C^n`
off the lattice `x + Tℤ`. -/
theorem Periodic.contDiffOn_compl_lattice {f p₀ : ℝ → ℝ} {n : ℕ∞ω} (hT : 0 < T)
    (hf : Periodic f T) (h₀ : ContDiffOn ℝ n p₀ (Ioo x (x + T)))
    (heq : ∀ v ∈ Ioo x (x + T), f v = p₀ v) :
    ContDiffOn ℝ n f {u | ∀ k : ℤ, u ≠ x + k * T} := by
  apply contDiffOn_of_locally_contDiffOn
  intro u hu
  set k := toIcoDiv hT x u
  have hv : toIcoMod hT x u ∈ Ico x (x + T) := toIcoMod_mem_Ico hT x u
  have hu' : u = toIcoMod hT x u + k • T := (toIcoMod_add_toIcoDiv_zsmul hT x u).symm
  have hvx : toIcoMod hT x u ≠ x := by
    intro hvx
    apply hu k
    rw [hu', hvx, zsmul_eq_mul]
  refine ⟨Ioo (x + k * T) (x + T + k * T), isOpen_Ioo, ?_, ?_⟩
  · rw [hu', zsmul_eq_mul]
    exact ⟨by linarith [lt_of_le_of_ne hv.1 (Ne.symm hvx)], by linarith [hv.2]⟩
  · have hmaps : MapsTo (fun w => w - k * T) (Ioo (x + k * T) (x + T + k * T)) (Ioo x (x + T)) :=
      fun w hw => ⟨by linarith [hw.1], by linarith [hw.2]⟩
    have hc : ContDiffOn ℝ n (fun w => p₀ (w - k * T)) (Ioo (x + k * T) (x + T + k * T)) :=
      h₀.comp (contDiff_id.sub contDiff_const).contDiffOn hmaps
    refine (hc.mono inter_subset_right).congr fun w hw => ?_
    rw [← heq _ (hmaps hw.2), ← zsmul_eq_mul, hf.sub_zsmul_eq k]

/-- A function continuous at `x`, differentiable on both sides of `x` with derivative `G`,
`G` continuous at `x`, is differentiable at `x` with derivative `G x`. -/
theorem hasDerivAt_of_hasDerivAt_Ioo_Ioo {F G : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hcont : ContinuousAt F x) (hR : ∀ u ∈ Ioo x (x + δ), HasDerivAt F (G u) u)
    (hL : ∀ u ∈ Ioo (x - δ) x, HasDerivAt F (G u) u) (hG : ContinuousAt G x) :
    HasDerivAt F (G x) x := by
  have hR' : HasDerivWithinAt F (G x) (Ici x) x := by
    refine hasDerivWithinAt_Ici_of_tendsto_deriv
      (fun u hu => (hR u hu).differentiableAt.differentiableWithinAt)
      hcont.continuousWithinAt (Ioo_mem_nhdsGT (by linarith)) ?_
    have h1 : ∀ᶠ u in 𝓝[>] x, deriv F u = G u := by
      filter_upwards [Ioo_mem_nhdsGT (show x < x + δ by linarith)] with u hu
      exact (hR u hu).deriv
    exact (hG.tendsto.mono_left nhdsWithin_le_nhds).congr' (h1.mono fun u hu => hu.symm)
  have hL' : HasDerivWithinAt F (G x) (Iic x) x := by
    refine hasDerivWithinAt_Iic_of_tendsto_deriv
      (fun u hu => (hL u hu).differentiableAt.differentiableWithinAt)
      hcont.continuousWithinAt (Ioo_mem_nhdsLT (by linarith)) ?_
    have h1 : ∀ᶠ u in 𝓝[<] x, deriv F u = G u := by
      filter_upwards [Ioo_mem_nhdsLT (show x - δ < x by linarith)] with u hu
      exact (hL u hu).deriv
    exact (hG.tendsto.mono_left nhdsWithin_le_nhds).congr' (h1.mono fun u hu => hu.symm)
  have := hR'.union hL'
  rwa [Ici_union_Iic, hasDerivWithinAt_univ] at this

/-- The integral over `[0, 2T]` of a continuous `T`-periodic function that is positive on some
period is positive. -/
theorem Periodic.integral_two_mul_pos {f : ℝ → ℝ} (hT : 0 < T) (hf : Periodic f T)
    (hcont : Continuous f) (hpos : ∀ u ∈ Ioo x (x + T), 0 < f u) :
    0 < ∫ u in (0)..(2 * T), f u := by
  have hx : 0 < ∫ u in x..(x + T), f u :=
    intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable _ _) hpos (by linarith)
  have h0 : ∫ u in (0)..(0 + T), f u = ∫ u in x..(x + T), f u := hf.intervalIntegral_add_eq 0 x
  have hT' : ∫ u in T..(T + T), f u = ∫ u in x..(x + T), f u := hf.intervalIntegral_add_eq T x
  have hsplit : ∫ u in (0)..(2 * T), f u =
      (∫ u in (0)..T, f u) + ∫ u in T..(2 * T), f u :=
    (integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)).symm
  have h0' : ∫ u in (0)..T, f u = ∫ u in x..(x + T), f u := by simpa using h0
  rw [hsplit, show (2 * T) = T + T by ring, hT', h0']
  linarith

end ComplexSLE.Infrastructure

end
