/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.Lemma38Koebe
public import ComplexSLE.Internal.Phases.Lemma38Hull

/-!
# Lemma 3.8, the deterministic multi-scale step (M7/E2)

Source: paper.tex:L1569-1600. For a continuous driver `U` with `U 0 = 0` and a unit point `z` let
`dd t = dist(z, L_t)` (non-increasing in `t`), `lvl k = 16^{-k}` and
`hitTime U z r = inf {t | dd t ≤ r}` (`⊤` if empty; the infimum is attained, `dd_hitTime_le`, by the
right-continuity of `dd`).

* `lvl_le_dd_hitTime` (`dist(z, L_{τ_k}) ≥ 16^{-k}`, paper (3.18)): the hull does not jump over the
  level (`ball_subset_compl_leftHull_of_forall_lt`);
* `step_good` (the Koebe step plus the clock increment): if `τ ∈ [0, T_z)` has
  `dist(z, L_τ) ≥ 16^{-k}`, `R = |f_τ(z)|`, and the restarted rescaled driver
  `V_s = R⁻¹ (U_{τ + R² s} - U_τ)` satisfies `|V_s| ≤ 1/16` for `s ≤ u₀` (`u₀ < 1/64`), then
  `τ + R² u₀ < T_z`, `dist(z, L_{τ + R² s}) ≥ 16^{-k}/14` for `s ≤ u₀`, and the clock increment
  `A(τ + R² u₀) - A(τ) ≥ u₀/4`. This holds uniformly over the restart direction `f_τ(z)/R`, which is
  the point the paper glosses over.
-/

public section

open scoped NNReal ENNReal Topology
open Set Metric Filter

namespace ComplexSLE.Internal.Polar

variable {U : ℝ≥0 → ℂ}

/-- The level `16^{-k}`. -/
@[expose] noncomputable def lvl (k : ℕ) : ℝ := (1 / 16 : ℝ) ^ k

theorem lvl_pos (k : ℕ) : 0 < lvl k := by unfold lvl; positivity

theorem lvl_le_one (k : ℕ) : lvl k ≤ 1 := by
  unfold lvl; exact pow_le_one₀ (by norm_num) (by norm_num)

theorem lvl_succ (k : ℕ) : lvl (k + 1) = lvl k / 16 := by
  unfold lvl; rw [pow_succ]; ring

theorem lvl_succ_lt_div (k : ℕ) : lvl (k + 1) < lvl k / 14 := by
  rw [lvl_succ]
  have := lvl_pos k
  linarith

theorem lvl_anti {k l : ℕ} (h : k ≤ l) : lvl l ≤ lvl k := by
  unfold lvl; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h

/-- With `U 0 = 0` and `‖z‖ = 1`, `L_0 = {0}` and `dist(z, L_0) = 1`. -/
theorem infDist_leftHull_zero (hU : Continuous U) (h0 : U 0 = 0) {z : ℂ} (hz : ‖z‖ = 1) :
    infDist z (leftHull U 0) = 1 := by
  have hsub : leftHull U 0 ⊆ {0} := by
    intro w hw
    by_contra hw0
    have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
    have := (lifeSet_and_norm_bounds_of_small (u₀ := 0) (ε := 0) (w := w) hU h0
      (fun s hs => by
        have : s = 0 := le_antisymm hs bot_le
        rw [this, h0]; simp) (by simp [hwpos.le]) (by simp [hwpos])).1
    exact (coe_mem_lifeSet_iff (t := (0 : ℝ≥0))).1 this hw
  have h1 : (0 : ℂ) ∈ leftHull U 0 := by
    have := driver_zero_mem_leftHull U 0
    rwa [h0] at this
  apply le_antisymm
  · calc infDist z (leftHull U 0) ≤ dist z 0 := infDist_le_dist_of_mem h1
      _ = 1 := by rw [dist_zero_right, hz]
  · have : leftHull U 0 = {0} := Subset.antisymm hsub (singleton_subset_iff.2 h1)
    rw [this, infDist_singleton, dist_zero_right, hz]

/-! ### Hitting times of the levels -/

open Classical in
/-- The first time `t` with `dist(z, L_t) ≤ r` (`⊤` if there is none). -/
@[expose] noncomputable def hitTime (U : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ) : WithTop ℝ≥0 :=
  if {t : ℝ≥0 | infDist z (leftHull U t) ≤ r}.Nonempty then
    ((sInf {t : ℝ≥0 | infDist z (leftHull U t) ≤ r} : ℝ≥0) : WithTop ℝ≥0) else ⊤

theorem sInf_mem_hitSet (hU : Continuous U) {z : ℂ} {r : ℝ}
    (hne : {t : ℝ≥0 | infDist z (leftHull U t) ≤ r}.Nonempty) :
    infDist z (leftHull U (sInf {t : ℝ≥0 | infDist z (leftHull U t) ≤ r})) ≤ r := by
  refine infDist_leftHull_le_of_forall_gt hU z _ r fun s hs => ?_
  obtain ⟨b, hb, hbs⟩ := exists_lt_of_csInf_lt hne hs
  exact (infDist_leftHull_anti z hbs.le).trans hb

theorem hitTime_le_iff (hU : Continuous U) {z : ℂ} {r : ℝ} {t : ℝ≥0} :
    hitTime U z r ≤ (t : WithTop ℝ≥0) ↔ infDist z (leftHull U t) ≤ r := by
  unfold hitTime
  by_cases hne : {t : ℝ≥0 | infDist z (leftHull U t) ≤ r}.Nonempty
  · simp only [hne, ↓reduceIte, WithTop.coe_le_coe]
    constructor
    · intro h
      exact (infDist_leftHull_anti z h).trans (sInf_mem_hitSet hU hne)
    · intro h
      exact csInf_le (OrderBot.bddBelow _) h
  · simp only [hne, ↓reduceIte]
    constructor
    · intro h; exact absurd h (WithTop.not_top_le_coe t)
    · intro h; exact absurd ⟨t, h⟩ hne

theorem hitTime_eq_top_iff {z : ℂ} {r : ℝ} :
    hitTime U z r = ⊤ ↔ ∀ t : ℝ≥0, r < infDist z (leftHull U t) := by
  unfold hitTime
  by_cases hne : {t : ℝ≥0 | infDist z (leftHull U t) ≤ r}.Nonempty
  · simp only [hne, ↓reduceIte]
    constructor
    · intro h; exact absurd h WithTop.coe_ne_top
    · intro h
      obtain ⟨t, ht⟩ := hne
      exact absurd (h t) (not_lt.2 ht)
  · simp only [hne, ↓reduceIte]
    simp only [true_iff]
    intro t
    by_contra h
    exact hne ⟨t, not_lt.1 h⟩

/-- If `hitTime = τ` is finite, then `dist(z, L_τ) ≤ r` and `dist(z, L_t) > r` for `t < τ`. -/
theorem infDist_hitTime_le (hU : Continuous U) {z : ℂ} {r : ℝ} {τ : ℝ≥0}
    (h : hitTime U z r = (τ : WithTop ℝ≥0)) : infDist z (leftHull U τ) ≤ r :=
  (hitTime_le_iff hU).1 h.le

theorem lt_infDist_of_lt_hitTime (hU : Continuous U) {z : ℂ} {r : ℝ} {τ t : ℝ≥0}
    (h : hitTime U z r = (τ : WithTop ℝ≥0)) (ht : t < τ) : r < infDist z (leftHull U t) := by
  by_contra hcon
  have : hitTime U z r ≤ (t : WithTop ℝ≥0) := (hitTime_le_iff hU).2 (not_lt.1 hcon)
  rw [h, WithTop.coe_le_coe] at this
  exact absurd ht (not_lt.2 this)

theorem hitTime_mono {z : ℂ} {r r' : ℝ} (h : r' ≤ r) : hitTime U z r ≤ hitTime U z r' := by
  unfold hitTime
  by_cases h' : {t : ℝ≥0 | infDist z (leftHull U t) ≤ r'}.Nonempty
  · have hne : {t : ℝ≥0 | infDist z (leftHull U t) ≤ r}.Nonempty :=
      h'.mono (s := {t : ℝ≥0 | infDist z (leftHull U t) ≤ r'}) (t := {t : ℝ≥0 | infDist z (leftHull U t) ≤ r}) fun t ht => le_trans ht h
    simp only [hne, h', ↓reduceIte, WithTop.coe_le_coe]
    exact csInf_le_csInf (OrderBot.bddBelow _) h' fun t ht => ht.trans h
  · simp only [h', ↓reduceIte]; exact le_top

/-- **No jump at the hitting time** (paper (3.18): `dist(z, L_{τ_k}) ≥ 16^{-k}`). -/
theorem lvl_le_infDist_hitTime (hU : Continuous U) (h0 : U 0 = 0) {z : ℂ} (hz : ‖z‖ = 1) {k : ℕ}
    {τ : ℝ≥0} (h : hitTime U z (lvl k) = (τ : WithTop ℝ≥0))
    (hτ : (τ : ℝ) ∈ lifeSet U z) : lvl k ≤ infDist z (leftHull U τ) := by
  rcases eq_zero_or_pos τ with h' | hpos
  · rw [h', infDist_leftHull_zero hU h0 hz]; exact lvl_le_one k
  · have hzτ : z ∉ leftHull U τ := coe_mem_lifeSet_iff.1 hτ
    have hr := lvl_pos k
    have hball : ball z (lvl k) ⊆ (leftHull U τ)ᶜ :=
      ball_subset_compl_leftHull_of_forall_lt hU hr hpos hzτ fun t ht => by
        intro y hy hyL
        have h1 := lt_infDist_of_lt_hitTime hU h ht
        have h2 := infDist_le_dist_of_mem (x := z) hyL
        rw [mem_ball, dist_comm] at hy
        linarith
    have := le_infDist_leftHull_of_ball (U := U) (y := z) hball
    simpa using this

/-! ### The good step -/

/-- **The Koebe step with the clock increment** (paper (3.19) and the clock identity of the proof of
Lemma 3.8). Let `τ ∈ [0, T_z)` with `dist(z, L_τ) ≥ 16^{-k}`, `R = |f_τ(z)|`, and suppose the
restarted rescaled driver `V_s = R⁻¹ (U_{τ + R² s} - U_τ)` satisfies `|V_s| ≤ 1/16` for `s ≤ u₀`,
where `u₀ < 1/64`. Then `τ + R² u₀ < T_z`; `dist(z, L_{τ + R² s}) ≥ 16^{-k} / 14` for `s ≤ u₀`; and
`A(τ + R² u₀) - A(τ) ≥ u₀ / 4`. The conclusion does not depend on the restart direction
`f_τ(z) / R`. Uses the EXTERNAL `koebe_quarter`. -/
theorem step_good (hU : Continuous U) {z : ℂ} {k : ℕ} {τ : ℝ≥0}
    (hτ : (τ : ℝ) ∈ lifeSet U z) (hdd : lvl k ≤ infDist z (leftHull U τ))
    {u₀ : ℝ≥0} (hu₀ : (u₀ : ℝ) < 1 / 64) {R : ℝ≥0} (hR : (R : ℝ) = ‖fPath U hU z τ‖)
    (hgood : ∀ s : ℝ≥0, s ≤ u₀ → ‖restartDriver U τ R s‖ ≤ 1 / 16) :
    ((τ : ℝ) + (R : ℝ) ^ 2 * u₀ ∈ lifeSet U z) ∧
    (∀ s : ℝ≥0, s ≤ u₀ → lvl k / 14 ≤ infDist z (leftHull U (τ + R ^ 2 * s))) ∧
    (u₀ : ℝ) / 4 ≤ clock U hU z ((τ : ℝ) + (R : ℝ) ^ 2 * u₀) - clock U hU z τ := by
  have hzτ : z ∉ leftHull U τ := coe_mem_lifeSet_iff.1 hτ
  have hRpos : 0 < R := by
    have : (0 : ℝ) < R := by rw [hR]; exact norm_pos_iff.2 (fPath_ne_zero hU hτ)
    exact_mod_cast this
  have hRp : (0 : ℝ) < R := by exact_mod_cast hRpos
  have hVc := restartDriver_continuous hU τ R
  have hV0 := restartDriver_zero U τ R
  have hz'norm : ‖restartPt U hU z τ R‖ = 1 := by
    simp only [restartPt, norm_mul, norm_inv, Complex.norm_real, NNReal.norm_eq]
    rw [hR]
    have : ‖fPath U hU z τ‖ ≠ 0 := (norm_pos_iff.2 (fPath_ne_zero hU hτ)).ne'
    field_simp
  have hu₀nn : (u₀ : ℝ) ≥ 0 := u₀.coe_nonneg
  -- the hull of the restarted chain is small
  have hhull : ∀ s : ℝ≥0, s ≤ u₀ → leftHull (restartDriver U τ R) s ⊆ ball 0 (1 / 2) := by
    intro s hs w hw
    rw [mem_ball_zero_iff]
    by_contra hcon
    push Not at hcon
    have hlife := (lifeSet_and_norm_bounds_of_small hVc hV0 hgood (ε := 1 / 16) (w := w)
      (by linarith) (by nlinarith)).1
    have := (coe_mem_lifeSet_iff (t := u₀)).1 hlife
    exact this (leftHull_mono hs hw)
  have hz'bounds := lifeSet_and_norm_bounds_of_small hVc hV0 hgood (ε := 1 / 16)
    (w := restartPt U hU z τ R) (by rw [hz'norm]; norm_num) (by rw [hz'norm]; linarith)
  have hlife := hz'bounds.1
  have hlife' := (mem_lifeSet_restart hU hτ hRpos).1 hlife
  refine ⟨hlife'.2, ?_, ?_⟩
  · intro s hs
    have hball : ball z (lvl k) ⊆ (leftHull U τ)ᶜ := by
      intro y hy hyL
      have h2 := infDist_le_dist_of_mem (x := z) hyL
      rw [mem_ball, dist_comm] at hy
      linarith
    have hb := ball_subset_compl_leftHull_restart hU (lvl_pos k) hball hR (hhull s hs)
    have := le_infDist_leftHull_of_ball (U := U) (y := z) hb
    simpa using this
  · have hc := clock_restart hU hτ hRpos hlife
    have hcpos : (u₀ : ℝ) / 4 ≤ clock (restartDriver U τ R) hVc (restartPt U hU z τ R) u₀ := by
      unfold clock
      have hint := intervalIntegrable_clockRate hVc hlife
      have hmono := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := u₀) hu₀nn
        (intervalIntegrable_const (c := (1 / 4 : ℝ))) hint (fun s hs => by
          have hb := hz'bounds.2 s hs
          rw [hz'norm] at hb
          have hsl : s ∈ lifeSet (restartDriver U τ R) (restartPt U hU z τ R) :=
            mem_lifeSet_of_le hlife hs.1 hs.2
          have hpos := norm_fPath_pos hVc hsl
          have hle : ‖fPath (restartDriver U τ R) hVc (restartPt U hU z τ R) s‖ ≤ 2 := by
            have := hb.2
            have h4 : 4 * (u₀ : ℝ) / 1 ≤ 1 / 16 := by linarith
            linarith
          unfold clockRate
          have hsq : ‖fPath (restartDriver U τ R) hVc (restartPt U hU z τ R) s‖ ^ 2 ≤ 4 := by
            nlinarith
          rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num]
          exact inv_anti₀ (by positivity) hsq)
      simpa [mul_comm, div_eq_mul_inv] using hmono
    rw [hc] at hcpos
    exact hcpos

end ComplexSLE.Internal.Polar

end
