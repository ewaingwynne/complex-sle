/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.Stability

/-!
# Dependence of the Loewner solution on the initial point (M7/D0)

Shifting the initial point and the driver by the same constant `c` carries solutions of the
Loewner problem to solutions: `γ` solves `γ' = 2/(γ - U)`, `γ 0 = w`, iff `γ - c` solves the
problem with driver `U - c` from `w - c`. Hence `T_w(U) = T_{w-c}(U - c)`, and on the life set
`g^U_t(w) = g^{U-c}_t(w - c) + c` and `f^U_t(w) = f^{U-c}_t(w - c)` (uniqueness,
`loewner_wellDefined`).

Consequently a perturbation of the *initial point* `z ↦ w` is a perturbation of the *driver* by
the constant `w - z`, and the stability estimate `exists_stability` gives: for `t ∈ [0, T_z)` there
are `ρ > 0`, `C ≥ 0` with `t < T_w` and `‖f_s(w) - f_s(z)‖ ≤ C ‖w - z‖` on `[0, t]` whenever
`‖w - z‖ < ρ` (`exists_lipschitz_initial`). In particular `ℂ ∖ L_t` is open
(`isOpen_compl_leftHull`). This is the deterministic input to the `z`-differentiability of
`g_t` (`PolarDeriv.lean`).
-/

public section

open scoped NNReal ENNReal
open Set

namespace ComplexSLE.Internal.Polar

variable {U : ℝ≥0 → ℂ}

/-! ### Shifting the driver and the initial point by a constant -/

/-- `γ` solves the Loewner problem for `(U, w)` iff `γ - c` solves it for `(U - c, w - c)`. -/
theorem isLoewnerSolution_sub_const_iff {w : ℂ} {τ : ℝ≥0∞} {γ : ℝ → ℂ} (c : ℂ) :
    IsLoewnerSolution U w τ γ ↔
      IsLoewnerSolution (fun s => U s - c) (w - c) τ (fun t => γ t - c) := by
  have key : ∀ (V : ℝ≥0 → ℂ) (v : ℂ) (δ : ℝ → ℂ) (d : ℂ), IsLoewnerSolution V v τ δ →
      IsLoewnerSolution (fun s => V s - d) (v - d) τ (fun t => δ t - d) := by
    intro V v δ d h
    refine ⟨by simp only [h.1], fun t ht hτ => ?_⟩
    obtain ⟨hne, hd⟩ := h.2 t ht hτ
    refine ⟨fun h' => hne (sub_left_inj.1 h'), ?_⟩
    rw [sub_sub_sub_cancel_right]
    exact hd.sub_const d
  constructor
  · exact key U w γ c
  · intro h
    have := key _ _ _ (-c) h
    simpa only [sub_neg_eq_add, sub_add_cancel] using this

/-- The absorbing time is invariant under a common shift of the driver and the initial point. -/
theorem absorbingTime_sub_const (w c : ℂ) :
    absorbingTime (fun s => U s - c) (w - c) = absorbingTime U w := by
  unfold absorbingTime
  congr 1
  ext τ
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨fun t => γ t + c, ?_⟩
    rw [isLoewnerSolution_sub_const_iff c]
    simpa only [add_sub_cancel_right] using hγ
  · rintro ⟨γ, hγ⟩
    exact ⟨fun t => γ t - c, (isLoewnerSolution_sub_const_iff c).1 hγ⟩

theorem lifeSet_sub_const (w c : ℂ) : lifeSet (fun s => U s - c) (w - c) = lifeSet U w := by
  ext t; simp [mem_lifeSet, absorbingTime_sub_const]

/-- On the life set, `g^U_t(w) = g^{U-c}_t(w - c) + c`. -/
theorem solPath_sub_const (hU : Continuous U) {c : ℂ} (hU' : Continuous fun s => U s - c)
    {w : ℂ} {t : ℝ} (ht : t ∈ lifeSet U w) :
    solPath U hU w t = solPath (fun s => U s - c) hU' (w - c) t + c := by
  have h₁ : IsLoewnerSolution U w (absorbingTime U w) (solPath U hU w) :=
    solPath_isLoewnerSolution hU w
  have h₂ : IsLoewnerSolution U w (absorbingTime U w)
      (fun t => solPath (fun s => U s - c) hU' (w - c) t + c) := by
    rw [isLoewnerSolution_sub_const_iff c, ← absorbingTime_sub_const w c]
    simpa only [add_sub_cancel_right] using solPath_isLoewnerSolution hU' (w - c)
  exact (loewner_wellDefined U hU w).2 _ _ _ h₁ h₂ ht

/-- On the life set, `f^U_t(w) = f^{U-c}_t(w - c)`. -/
theorem fPath_sub_const (hU : Continuous U) {c : ℂ} (hU' : Continuous fun s => U s - c)
    {w : ℂ} {t : ℝ} (ht : t ∈ lifeSet U w) :
    fPath U hU w t = fPath (fun s => U s - c) hU' (w - c) t := by
  simp only [fPath]
  rw [solPath_sub_const hU hU' ht]
  ring

/-! ### Lipschitz dependence on the initial point -/

/-- **Lipschitz dependence of `f_s(·)` on the initial point.** If `t ∈ [0, T_z)`, there are
`ρ > 0` and `C ≥ 0` such that every `w` with `‖w - z‖ < ρ` has `t < T_w` and
`‖f_s(w) - f_s(z)‖ ≤ C ‖w - z‖` for `s ∈ [0, t]`. -/
theorem exists_lipschitz_initial (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    ∃ ρ > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, ‖w - z‖ < ρ →
      t ∈ lifeSet U w ∧ ∀ s ∈ Icc (0 : ℝ) t, ‖fPath U hU w s - fPath U hU z s‖ ≤ C * ‖w - z‖ := by
  obtain ⟨ρ, hρ, C, hC0, hC⟩ := exists_stability hU ht
  refine ⟨ρ, hρ, C, hC0, fun w hw => ?_⟩
  have hU' : Continuous fun s => U s - (w - z) := hU.sub continuous_const
  obtain ⟨hlife, hbound⟩ := hC (fun s => U s - (w - z)) hU' ‖w - z‖ hw
    (fun s _ => by simp)
  have hwz : w - (w - z) = z := sub_sub_cancel w z
  have hlife' := lifeSet_sub_const (U := U) w (w - z)
  rw [hwz] at hlife'
  rw [hlife'] at hlife
  refine ⟨hlife, fun s hs => ?_⟩
  have hf := fPath_sub_const hU hU' (c := w - z) (Icc_subset_lifeSet hlife hs)
  rw [hwz] at hf
  rw [hf]
  exact hbound s hs

/-- The set of initial points alive at time `t` is open. -/
theorem isOpen_lifeSet_initial (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ) :
    IsOpen {z : ℂ | t ∈ lifeSet U z} := by
  rw [Metric.isOpen_iff]
  intro z hz
  obtain ⟨ρ, hρ, C, -, hC⟩ := exists_lipschitz_initial hU hz
  refine ⟨ρ, hρ, fun w hw => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hw
  exact (hC w hw).1

/-- **`ℂ ∖ L_t` is open** (the first conjunct of `loewnerMap_conformal`, proved). -/
theorem isOpen_compl_leftHull (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) :
    IsOpen (leftHull U t)ᶜ := by
  have : (leftHull U t)ᶜ = {z : ℂ | (t : ℝ) ∈ lifeSet U z} := by
    ext z; exact (coe_mem_lifeSet_iff (U := U)).symm
  rw [this]
  exact isOpen_lifeSet_initial U hU t

end ComplexSLE.Internal.Polar

end
