/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.Prop32AEvents
public import ComplexSLE.Internal.Phases.Lemma38Koebe

/-!
# The event of Proposition 3.2(b): scale invariance, future dependence, the Koebe ball (M7/E5)

Source: paper.tex:L1786-1816 (proof of Proposition 3.2(b)), with the R14 `ε`-form

  `StaysAway u z = ∃ ε > 0, ∀ t < T_z, ε ≤ dist(z, L_t)`

of "`lim_{t → T_z⁻} dist(z, L_t) > 0`".

* `StaysAway` is the negation of the event of Proposition 3.2(a), hence it is scale invariant,
  future dependent and measurable (`scaleInvariantEvents_staysAway`,
  `futureDependentEvents_staysAway`, `measurableEvents_staysAway`).
* `StaysAwayBy r u z`: the radius-`r` version `0 < T_z ∧ ∀ t < T_z, r ≤ dist(z, L_t)`.
  `StaysAwayBy.mono` (smaller radius), and `exists_staysAwayBy` (every `StaysAway` event with
  `T_z > 0` has a radius).
* **Koebe ball** (paper.tex:L1806-1810, deterministic): `StaysAwayBy r u z` implies
  `StaysAway u w` for every `w ∈ B(z, r/16)` (`staysAway_of_staysAwayBy`). By the Koebe
  distortion theorem the paper shows `dist(f_t(w), R_t) → 0` as `t → T_z`; here the Grönwall form
  of the Koebe step (`norm_fPath_sub_le_of_ball`, which consumes only the EXTERNAL
  `koebe_quarter`) gives `|f_t(w) - f_t(z)| ≤ (e^K - 1)|f_t(z)|` on `B(z, r)`, hence
  `f_t(w) → 0` as `t → T_z⁻` (Lemma 2.5, `tendsto_norm_fPath_nhdsWithin`), and then `T_w ≤ T_z`
  because `f_{T_z}(w) ≠ 0` if `T_z < T_w` (`fPath_ne_zero`, continuity of `f_·(w)` at `T_z`).

Every result consuming the Koebe step is `PROVED_REL{koebe_quarter}`.
-/

@[expose] public section

open scoped NNReal ENNReal Topology
open Set Metric Filter

namespace ComplexSLE.Internal

/-- **The event of Proposition 3.2(b)** (R14 `ε`-form): `∃ ε > 0, ∀ t < T_z, ε ≤ dist(z, L_t)`. -/
def StaysAway (u : ℝ≥0 → ℂ) (z : ℂ) : Prop :=
  ∃ ε > 0, ∀ t : ℝ≥0, (t : ℝ≥0∞) < absorbingTime u z → ε ≤ infDist z (leftHull u t)

/-- The radius-`r` version of `StaysAway`: `0 < T_z` and `r ≤ dist(z, L_t)` for all `t < T_z`. -/
def StaysAwayBy (r : ℝ) (u : ℝ≥0 → ℂ) (z : ℂ) : Prop :=
  0 < absorbingTime u z ∧
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < absorbingTime u z → r ≤ infDist z (leftHull u t)

theorem staysAway_iff_not_approach (u : ℝ≥0 → ℂ) (z : ℂ) :
    StaysAway u z ↔ ¬ ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < absorbingTime u z ∧
      infDist z (leftHull u t) < ε := by
  unfold StaysAway
  push Not
  rfl

theorem scaleInvariantEvents_staysAway : ScaleInvariantEvents StaysAway := by
  intro u hu r hr z
  simp only [staysAway_iff_not_approach]
  exact not_congr (scaleInvariantEvents_hull_approach u hu r hr z)

theorem futureDependentEvents_staysAway : FutureDependentEvents StaysAway := by
  intro u hu s z hz
  simp only [staysAway_iff_not_approach]
  exact not_congr (futureDependentEvents_hull_approach u hu s z hz)

theorem measurableEvents_staysAway : MeasurableEvents StaysAway :=
  measurableEvents_hull_stays_away

/-! ### Radii -/

theorem StaysAwayBy.staysAway {r : ℝ} (hr : 0 < r) {u : ℝ≥0 → ℂ} {z : ℂ}
    (h : StaysAwayBy r u z) : StaysAway u z :=
  ⟨r, hr, h.2⟩

theorem StaysAwayBy.mono {r r' : ℝ} (hrr : r' ≤ r) {u : ℝ≥0 → ℂ} {z : ℂ}
    (h : StaysAwayBy r u z) : StaysAwayBy r' u z :=
  ⟨h.1, fun t ht => hrr.trans (h.2 t ht)⟩

/-- Every `StaysAway` event with `T_z > 0` holds with some radius `1/(n+1)`. -/
theorem exists_staysAwayBy {u : ℝ≥0 → ℂ} {z : ℂ} (h : StaysAway u z)
    (h0 : 0 < absorbingTime u z) : ∃ n : ℕ, StaysAwayBy (1 / ((n : ℝ) + 1)) u z := by
  obtain ⟨ε, hε, hz⟩ := h
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  exact ⟨n, h0, fun t ht => hn.le.trans (hz t ht)⟩

/-- `StaysAwayBy` is monotone in the radius along `1/(n+1)`. -/
theorem staysAwayBy_one_div_mono {u : ℝ≥0 → ℂ} {z : ℂ} {m n : ℕ} (hmn : m ≤ n)
    (h : StaysAwayBy (1 / ((m : ℝ) + 1)) u z) : StaysAwayBy (1 / ((n : ℝ) + 1)) u z :=
  h.mono (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1))

/-! ### The Koebe ball -/

section Koebe

variable {u : ℝ≥0 → ℂ}

/-- A disc `B(z, r)` with `r ≤ dist(z, L_t)` does not meet `L_t`. -/
theorem ball_subset_compl_leftHull_of_le_infDist {z : ℂ} {t : ℝ≥0} {r : ℝ}
    (h : r ≤ infDist z (leftHull u t)) : ball z r ⊆ (leftHull u t)ᶜ :=
  (ball_subset_ball h).trans (Polar.ball_infDist_subset_compl_leftHull z t)

/-- If `B(z, r)` avoids `L_t` for all `t < T_z`, `0 < T_z`, and `‖w - z‖ < r / 16`, then
`T_w ≤ T_z` (so `T_w = T_z`: the whole ball is absorbed at time `T_z`). -/
theorem absorbingTime_le_of_staysAwayBy (hu : Continuous u) {z w : ℂ} {r : ℝ}
    (h : StaysAwayBy r u z) (hw : ‖w - z‖ < r / 16) :
    absorbingTime u w ≤ absorbingTime u z := by
  have hr : 0 < r := by
    by_contra hr
    push Not at hr
    exact absurd (lt_of_le_of_lt (norm_nonneg _) hw) (by linarith)
  by_contra hlt
  push Not at hlt
  have hne : absorbingTime u z ≠ ⊤ := ne_top_of_lt hlt
  set T : ℝ := (absorbingTime u z).toReal with hTdef
  have hTpos : 0 < T := ENNReal.toReal_pos h.1.ne' hne
  have hTw : T ∈ Polar.lifeSet u w := by
    refine ⟨hTpos.le, ?_⟩
    rw [hTdef, ENNReal.ofReal_toReal hne]
    exact hlt
  have hfT : Polar.fPath u hu w T ≠ 0 := Polar.fPath_ne_zero hu hTw
  -- the Koebe step on `B(z, r)`
  set K : ℝ := 4 * ‖w - z‖ / (r - ‖w - z‖) with hK
  have hbound : ∀ t ∈ Polar.lifeSet u z,
      ‖Polar.fPath u hu w t‖ ≤ Real.exp K * ‖Polar.fPath u hu z t‖ := by
    intro t ht
    set τ : ℝ≥0 := t.toNNReal with hτ
    have hτt : (τ : ℝ) = t := Real.coe_toNNReal t ht.1
    have hτlt : (τ : ℝ≥0∞) < absorbingTime u z := by
      have := ht.2
      rwa [ENNReal.ofReal] at this
    have hball : ball z r ⊆ (leftHull u τ)ᶜ :=
      ball_subset_compl_leftHull_of_le_infDist (h.2 τ hτlt)
    have hwr : ‖w - z‖ < r := by linarith
    have := Polar.norm_fPath_sub_le_of_ball hu hball hwr
    rw [hτt] at this
    calc ‖Polar.fPath u hu w t‖
        = ‖(Polar.fPath u hu w t - Polar.fPath u hu z t) + Polar.fPath u hu z t‖ := by
          congr 1; ring
      _ ≤ ‖Polar.fPath u hu w t - Polar.fPath u hu z t‖ + ‖Polar.fPath u hu z t‖ :=
          norm_add_le _ _
      _ ≤ (Real.exp K - 1) * ‖Polar.fPath u hu z t‖ + ‖Polar.fPath u hu z t‖ :=
          add_le_add this le_rfl
      _ = Real.exp K * ‖Polar.fPath u hu z t‖ := by ring
  -- `f_t(w) → 0` as `t → T_z⁻`
  have hz0 : Tendsto (fun t => ‖Polar.fPath u hu z t‖) (𝓝[Polar.lifeSet u z] T) (𝓝 0) :=
    Polar.tendsto_norm_fPath_nhdsWithin hu hne
  have hw0 : Tendsto (fun t => ‖Polar.fPath u hu w t‖) (𝓝[Polar.lifeSet u z] T) (𝓝 0) := by
    have h1 : Tendsto (fun t => Real.exp K * ‖Polar.fPath u hu z t‖)
        (𝓝[Polar.lifeSet u z] T) (𝓝 (Real.exp K * 0)) := hz0.const_mul _
    rw [mul_zero] at h1
    exact squeeze_zero' (eventually_nhdsWithin_of_forall fun t _ => norm_nonneg _)
      (eventually_nhdsWithin_of_forall hbound) h1
  -- continuity of `f_·(w)` at `T`
  have hcont : Tendsto (fun t => ‖Polar.fPath u hu w t‖) (𝓝[Polar.lifeSet u z] T)
      (𝓝 ‖Polar.fPath u hu w T‖) :=
    ((Polar.continuousWithinAt_fPath_Ici hu hTw).norm).tendsto.mono_left
      (nhdsWithin_mono T (Polar.lifeSet_subset_Ici z))
  have hNe : (𝓝[Polar.lifeSet u z] T).NeBot := by
    rw [Polar.lifeSet_eq_Ico hne, ← hTdef, nhdsWithin_Ico_eq_nhdsLT hTpos]
    exact nhdsLT_neBot_of_exists_lt ⟨0, hTpos⟩
  have := tendsto_nhds_unique hcont hw0
  exact hfT (norm_eq_zero.1 this)

/-- **The Koebe ball** (paper.tex:L1806-1810): if `dist(z, L_t) ≥ r` for all `t < T_z` (and
`T_z > 0`), then for each `w ∈ B(z, r/16)` also `dist(w, L_t) ≥ 15 r / 16` for all `t < T_w`. -/
theorem staysAway_of_staysAwayBy (hu : Continuous u) {z w : ℂ} {r : ℝ}
    (h : StaysAwayBy r u z) (hw : ‖w - z‖ < r / 16) : StaysAway u w := by
  have hr : 0 < r := by
    by_contra hr
    push Not at hr
    exact absurd (lt_of_le_of_lt (norm_nonneg _) hw) (by linarith)
  refine ⟨15 * r / 16, by positivity, fun t ht => ?_⟩
  have htz : (t : ℝ≥0∞) < absorbingTime u z :=
    lt_of_lt_of_le ht (absorbingTime_le_of_staysAwayBy hu h hw)
  have hball : ball z r ⊆ (leftHull u t)ᶜ :=
    ball_subset_compl_leftHull_of_le_infDist (h.2 t htz)
  have := Polar.le_infDist_leftHull_of_ball (y := w) hball
  linarith

end Koebe

end ComplexSLE.Internal

end
