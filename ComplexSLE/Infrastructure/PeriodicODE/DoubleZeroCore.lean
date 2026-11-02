/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.PeriodicODE.DoubleZeroResidual
public import ComplexSLE.Infrastructure.PeriodicODE.DoubleZeroLocal
public import ComplexSLE.Infrastructure.PeriodicODE.DoubleZeroInterval
public import ComplexSLE.Infrastructure.PeriodicODE.DoubleZeroGlue

/-!
# The periodic equation `D K' + α K = D ρ` at a double zero of `D`

For `D` with a nondegenerate double zero on the lattice `Tℤ`, `α 0 > 0` and `ρ` continuous
`T`-periodic with `ρ 0 = 0`, there is a `C¹` `T`-periodic `K` with `D K' + α K = D ρ`.
It is the `T`-periodic extension of `H = e^{-A} ∫₀^x e^{A} ρ`, where `A' = α / D`.
-/

public section

open Set Filter Topology Function

namespace ComplexSLE.Infrastructure

theorem exists_periodic_solution_core {α D ρ : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hα : ContDiff ℝ 1 α) (hD : ContDiff ℝ 2 D) (hαper : Periodic α T) (hDper : Periodic D T)
    (hρ : Continuous ρ) (hρper : Periodic ρ T) (hρ0 : ρ 0 = 0)
    (hD0 : ∀ u, 0 ≤ D u) (hDzero : ∀ u, D u = 0 ↔ ∃ n : ℤ, u = n * T)
    (hD2 : 0 < deriv (deriv D) 0) (hα0 : 0 < α 0) :
    ∃ K : ℝ → ℝ, ContDiff ℝ 1 K ∧ Periodic K T ∧
      ∀ u, D u * deriv K u + α u * K u = D u * ρ u := by
  have hDz : D 0 = 0 := (hDzero 0).2 ⟨0, by simp⟩
  have hD1 : deriv D 0 = 0 := by
    have hmin : IsLocalMin D 0 := Filter.Eventually.of_forall fun x => by rw [hDz]; exact hD0 x
    exact hmin.deriv_eq_zero
  obtain ⟨δ₀, hδ₀, c, hc, hloc⟩ := exists_local_data hα hD hDz hD1 hD2 hα0
  have hαd : Differentiable ℝ α := hα.differentiable one_ne_zero
  have hDd : Differentiable ℝ D := (contDiff_two_deriv_facts hD).1
  set δ : ℝ := min δ₀ (T / 2) with hδdef
  have hδ : 0 < δ := lt_min hδ₀ (by linarith)
  have hδT : δ ≤ T / 2 := min_le_right _ _
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  set a : ℝ → ℝ := fun u => α u / D u with ha
  set b : ℝ → ℝ := fun u => D u / α u with hb
  have hα'per : Periodic (deriv α) T := periodic_deriv hαper
  have hD'per : Periodic (deriv D) T := periodic_deriv hDper
  have hb'per : Periodic (ratioDeriv α D) T := fun u => by
    simp only [ratioDeriv, hDper u, hαper u, hα'per u, hD'per u]
  have haper : Periodic a T := fun u => by simp only [ha, hDper u, hαper u]
  have hDpos : ∀ x ∈ Ioo 0 T, 0 < D x := fun x hx =>
    lt_of_le_of_ne (hD0 x) (fun h => not_lattice_of_mem_Ioo hT hx ((hDzero x).1 h.symm))
  have hcontA : ContinuousOn a (Ioo 0 T) := fun x hx =>
    (hα.continuous.continuousAt.div hD.continuous.continuousAt (hDpos x hx).ne').continuousWithinAt
  have hρT : ρ T = 0 := by simpa [hρ0] using hρper 0
  -- left end
  have hLoc : ∀ x ∈ Ioo 0 δ, 0 < α x ∧ 0 < D x ∧ -(1 / 2) ≤ ratioDeriv α D x ∧
      c / x ^ 2 ≤ a x := fun x hx => by
    have hxI : x ∈ Icc (-δ₀) δ₀ := ⟨by linarith [hx.1, hδ₀], by linarith [hx.2]⟩
    obtain ⟨h1, h2, h3⟩ := hloc x hxI
    obtain ⟨h4, h5⟩ := h3 hx.1.ne'
    exact ⟨by linarith, h4, h2, h5⟩
  -- right end, by periodicity
  have hLocR : ∀ x ∈ Ioo (T - δ) T, 0 < α x ∧ 0 < D x ∧ -(1 / 2) ≤ ratioDeriv α D x ∧
      c / (T - x) ^ 2 ≤ a x := fun x hx => by
    have hxI : x - T ∈ Icc (-δ₀) δ₀ :=
      ⟨by linarith [hx.1, hδδ₀], by linarith [hx.2, hδ₀]⟩
    obtain ⟨h1, h2, h3⟩ := hloc (x - T) hxI
    obtain ⟨h4, h5⟩ := h3 (by linarith [hx.2])
    rw [hαper.sub_eq] at h1 h5
    rw [hDper.sub_eq] at h4 h5
    rw [hb'per.sub_eq] at h2
    refine ⟨by linarith, h4, h2, ?_⟩
    have : (T - x) ^ 2 = (x - T) ^ 2 := by ring
    rw [this]
    exact h5
  have hb0 : ContinuousAt b 0 :=
    hD.continuous.continuousAt.div hα.continuous.continuousAt hα0.ne'
  have hb0v : b 0 = 0 := by simp [hb, hDz]
  have hbT : ContinuousAt b T := by
    have hαT : α T ≠ 0 := by
      have := hαper 0
      rw [zero_add] at this
      rw [this]; exact hα0.ne'
    exact hD.continuous.continuousAt.div hα.continuous.continuousAt hαT
  have hbTv : b T = 0 := by simp [hb, (hDzero T).2 ⟨1, by simp⟩]
  obtain ⟨H, hH0, hHd, hL1, hL2, hR1, hR2⟩ := exists_bounded_solution (b := b)
    (b' := ratioDeriv α D) (c := c) hT hδ hδT hc hcontA hρ hρ0 hρT
    (fun x hx => hasDerivAt_ratio hαd hDd (hLoc x hx).1.ne')
    (fun x hx => (hLoc x hx).2.2.1)
    (fun x hx => by
      have h1 := (hLoc x hx).1.ne'
      have h2 := (hLoc x hx).2.1.ne'
      simp only [ha, hb]; field_simp)
    (fun x hx => (hLoc x hx).2.2.2)
    (by simpa [hb0v] using hb0.tendsto.mono_left nhdsWithin_le_nhds)
    (fun x hx => hasDerivAt_ratio hαd hDd (hLocR x hx).1.ne')
    (fun x hx => (hLocR x hx).2.2.1)
    (fun x hx => by
      have h1 := (hLocR x hx).1.ne'
      have h2 := (hLocR x hx).2.1.ne'
      simp only [ha, hb]; field_simp)
    (fun x hx => (hLocR x hx).2.2.2)
    (by simpa [hbTv] using hbT.tendsto.mono_left nhdsWithin_le_nhds)
  obtain ⟨K, hKc, hKper, hK0, hKd⟩ := exists_periodic_C1_of_bounded_solution hT haper hcontA hρ
    hρper hρ0 hH0 hHd hL1 hL2 hR1 hR2
  refine ⟨K, hKc, hKper, fun u => ?_⟩
  rw [(hKd u).deriv]
  by_cases hu : D u = 0
  · obtain ⟨n, hn⟩ := (hDzero u).1 hu
    have : K u = 0 := by
      rw [hn, show (n : ℝ) * T = 0 + n * T by ring, (hKper.int_mul n) 0, hK0]
    rw [hu, this]; ring
  · simp only [ha]
    field_simp
    ring

end ComplexSLE.Infrastructure

end
