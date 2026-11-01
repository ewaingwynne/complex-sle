/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# A bounded null sequence times an `L²`-bounded sequence is `L¹`-null

If `|ρ_m| ≤ e_m |S_m|` with `0 ≤ e_m ≤ B`, `e_m → 0` almost surely and `E[S_m²] ≤ K` for all `m`
(on a probability space), then `E|ρ_m| → 0` (`tendsto_integral_abs_of_le_mul`). The proof uses
`e S ≤ ½(λ e² + S²/λ)` and dominated convergence for `E[e_m²]`. This is the mechanism by which the
Taylor remainder of the discretized Itô expansion vanishes in `L¹`: the sum of squared increments is
only bounded in `L²`, not pathwise.
-/

@[expose] public section

open scoped Topology
open MeasureTheory Filter Set

namespace ComplexSLE.Infrastructure.Ito

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}

/-- **A bounded sequence tending to `0` a.e. times an `L²`-bounded sequence tends to `0` in `L¹`.**
If `|ρ_m| ≤ e_m S_m` with `0 ≤ e_m ≤ B`, `e_m → 0` a.e. and `E[S_m²] ≤ K`, then `E|ρ_m| → 0`. -/
theorem tendsto_integral_abs_of_le_mul [IsProbabilityMeasure P] {e S ρ : ℕ → Ω → ℝ} {B K : ℝ}
    (he : ∀ m, AEStronglyMeasurable (e m) P) (he0 : ∀ m, ∀ᵐ ω ∂P, 0 ≤ e m ω)
    (heB : ∀ m, ∀ᵐ ω ∂P, e m ω ≤ B)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun m => e m ω) atTop (𝓝 0))
    (hSint : ∀ m, Integrable (fun ω => S m ω ^ 2) P) (hSK : ∀ m, ∫ ω, S m ω ^ 2 ∂P ≤ K)
    (hρ : ∀ m, Integrable (ρ m) P) (hρe : ∀ m, ∀ᵐ ω ∂P, |ρ m ω| ≤ e m ω * |S m ω|) :
    Tendsto (fun m => ∫ ω, |ρ m ω| ∂P) atTop (𝓝 0) := by
  -- `∫ e_m² → 0`
  have hB0 : ∀ m, ∀ᵐ ω ∂P, e m ω ^ 2 ≤ B ^ 2 := fun m => by
    filter_upwards [he0 m, heB m] with ω h0 hB
    nlinarith
  have hee : Tendsto (fun m => ∫ ω, e m ω ^ 2 ∂P) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := P) (F := fun m ω => e m ω ^ 2)
      (f := fun _ => (0 : ℝ)) (fun _ => B ^ 2) (fun m => (he m).pow 2) (integrable_const _)
      (fun m => by
        filter_upwards [hB0 m] with ω h
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact h)
      (by
        filter_upwards [hlim] with ω h
        simpa using h.pow 2)
    simpa using this
  rw [Metric.tendsto_atTop]
  intro ε hε
  set K' : ℝ := max K 0 + 1 with hK'
  have hK'pos : 0 < K' := by positivity
  set lam : ℝ := K' / ε with hlam
  have hlampos : 0 < lam := div_pos hK'pos hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hee (ε / (lam + 1)) (div_pos hε (by linarith))
  refine ⟨N, fun m hm => ?_⟩
  have hint_e : Integrable (fun ω => e m ω ^ 2) P := by
    refine Integrable.mono' (integrable_const (B ^ 2)) ((he m).pow 2) ?_
    filter_upwards [hB0 m] with ω h
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact h
  have hbound : ∫ ω, |ρ m ω| ∂P ≤ ∫ ω, (lam / 2 * e m ω ^ 2 + (1 / (2 * lam)) * S m ω ^ 2) ∂P := by
    refine integral_mono_ae (hρ m).abs
      ((hint_e.const_mul _).add ((hSint m).const_mul _)) ?_
    filter_upwards [hρe m] with ω h
    have h2 : e m ω * |S m ω| ≤ lam / 2 * e m ω ^ 2 + (1 / (2 * lam)) * S m ω ^ 2 := by
      have hS : |S m ω| ^ 2 = S m ω ^ 2 := sq_abs _
      have : 0 ≤ (lam * e m ω - |S m ω|) ^ 2 := sq_nonneg _
      have h3 : e m ω * |S m ω| * (2 * lam) ≤ lam * (lam * e m ω ^ 2) + |S m ω| ^ 2 := by
        nlinarith
      rw [← hS]
      have : e m ω * |S m ω| ≤ (lam * (lam * e m ω ^ 2) + |S m ω| ^ 2) / (2 * lam) := by
        rw [le_div_iff₀ (by positivity)]; exact h3
      calc e m ω * |S m ω| ≤ (lam * (lam * e m ω ^ 2) + |S m ω| ^ 2) / (2 * lam) := this
        _ = _ := by field_simp
    exact h.trans h2
  rw [integral_add (hint_e.const_mul _) ((hSint m).const_mul _), integral_const_mul,
    integral_const_mul] at hbound
  have h1 := hN m hm
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun ω => sq_nonneg _)] at h1
  have h2 : ∫ ω, S m ω ^ 2 ∂P ≤ K' := (hSK m).trans (by rw [hK']; linarith [le_max_left K 0])
  have h3 : 1 / (2 * lam) * ∫ ω, S m ω ^ 2 ∂P ≤ ε / 2 := by
    calc 1 / (2 * lam) * ∫ ω, S m ω ^ 2 ∂P ≤ 1 / (2 * lam) * K' :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ε / 2 := by rw [hlam]; field_simp
  have h4 : lam / 2 * ∫ ω, e m ω ^ 2 ∂P < ε / 2 := by
    calc lam / 2 * ∫ ω, e m ω ^ 2 ∂P ≤ lam / 2 * (ε / (lam + 1)) :=
          mul_le_mul_of_nonneg_left h1.le (by positivity)
      _ < ε / 2 := by
          rw [div_mul_div_comm, div_lt_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun ω => abs_nonneg _)]
  linarith

end ComplexSLE.Infrastructure.Ito

end
