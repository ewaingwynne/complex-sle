/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.KoebeHit
public import ComplexSLE.Internal.Polar.PolarRestartClock
public import ComplexSLE.Internal.Hull.EndpointCont
public import Mathlib.Analysis.ODE.Gronwall

/-!
# Lemma 3.10, deterministic Koebe step (M7/E2, `eqn-finite-exp-1`, `eqn-finite-exp-2`)

Source: paper.tex:L1569-1576. For a continuous driver `U`, a time `t` and a disc `B(x, ρ)` disjoint
from the left hull `L_t`, the centered map `f_t = g_t - U_t` varies by a controlled factor on `B(x, ρ)`:

* `norm_fPath_sub_le_of_ball`: for `w ∈ B(x, ρ)`,
  `‖f_t(w) - f_t(x)‖ ≤ (exp (koebeK ‖w - x‖ / (ρ - ‖w - x‖)) - 1) ‖f_t(x)‖`;
* `norm_fPath_sub_le_ninth`: in particular `‖f_t(w) - f_t(x)‖ ≤ (4/9) ‖f_t(x)‖` if
  `‖w - x‖ ≤ ρ / koebeN`, where `koebeN = 1 + 13 koebeK / 4 = 157`.

The paper derives (3.9) from the Koebe distortion theorem. Here only the Koebe covering theorem
with the non-sharp constant `koebeK = 48` (`KoebeChainInv.lean`; the paper's sharp `1/4` would give
`koebeK = 4` and `koebeN = 14`) is used (through `norm_derivPath_mul_infDist_le_of_notMem`, which
gives `|f_t'(y)| ≤ koebeK |f_t(y)| / dist(y, L_t)`), followed by a Grönwall estimate along the
segment `[x, w]`. The radius ratio `koebeN` is chosen so that the bound `4/9` (hence `5/9 > 1/2`
for `|f_t(w)| / |f_t(x)|`) is the same for every `koebeK`: `koebeK / (koebeN - 1) = 4/13`.
No EXTERNAL input is consumed.
-/

public section

open scoped NNReal ENNReal
open Set Metric

namespace ComplexSLE.Internal.Polar

open ComplexSLE.Internal
open ComplexSLE.Internal.KoebeChain (koebeK koebeK_pos one_le_koebeK)

variable {U : ℝ≥0 → ℂ}

/-- The radius ratio `koebeN = 1 + 13 koebeK / 4 = 157` of the Koebe step: for
`‖w - x‖ ≤ ρ / koebeN` one has `koebeK ‖w - x‖ / (ρ - ‖w - x‖) ≤ 4/13`
(for the sharp Koebe constant `koebeK = 4` this is the paper's `14`). -/
@[expose] noncomputable def koebeN : ℝ := 1 + 13 * koebeK / 4

theorem one_lt_koebeN : 1 < koebeN := by
  rw [koebeN]; linarith [koebeK_pos]

theorem koebeN_pos : 0 < koebeN := one_pos.trans one_lt_koebeN

/-- A point `y` of a disc `B(x, ρ)` disjoint from `L_t` is at distance `≥ ρ - ‖y - x‖` from `L_t`. -/
theorem le_infDist_leftHull_of_ball {t : ℝ≥0} {x y : ℂ} {ρ : ℝ}
    (hball : ball x ρ ⊆ (leftHull U t)ᶜ) : ρ - ‖y - x‖ ≤ infDist y (leftHull U t) := by
  refine (le_infDist (leftHull_nonempty U t)).2 fun ℓ hℓ => ?_
  have h1 : ρ ≤ ‖x - ℓ‖ := by
    by_contra h
    exact hball (mem_ball.2 (by rw [dist_eq_norm, norm_sub_rev]; exact not_le.1 h)) hℓ
  have h2 : ‖x - ℓ‖ ≤ ‖x - y‖ + ‖y - ℓ‖ := by
    calc ‖x - ℓ‖ = ‖(x - y) + (y - ℓ)‖ := by congr 1; ring
      _ ≤ ‖x - y‖ + ‖y - ℓ‖ := norm_add_le _ _
  rw [dist_eq_norm]
  linarith [norm_sub_rev y x]

/-- **Koebe step, general form.** If `B(x, ρ) ∩ L_t = ∅` and `‖w - x‖ < ρ`, then
`‖f_t(w) - f_t(x)‖ ≤ (exp (koebeK ‖w - x‖ / (ρ - ‖w - x‖)) - 1) ‖f_t(x)‖`. -/
theorem norm_fPath_sub_le_of_ball (hU : Continuous U) {t : ℝ≥0} {x w : ℂ} {ρ : ℝ}
    (hball : ball x ρ ⊆ (leftHull U t)ᶜ) (hw : ‖w - x‖ < ρ) :
    ‖fPath U hU w t - fPath U hU x t‖ ≤
      (Real.exp (koebeK * ‖w - x‖ / (ρ - ‖w - x‖)) - 1) * ‖fPath U hU x t‖ := by
  set δ : ℂ := w - x with hδ
  set K : ℝ := koebeK * ‖δ‖ / (ρ - ‖δ‖) with hK
  have hρδ : 0 < ρ - ‖δ‖ := by linarith
  have hmem : ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → x + (s : ℂ) * δ ∈ ball x ρ := by
    intro s hs
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hs.1]
    calc s * ‖δ‖ ≤ 1 * ‖δ‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
      _ < ρ := by linarith
  have hnot : ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → x + (s : ℂ) * δ ∈ (leftHull U t)ᶜ :=
    fun s hs => hball (hmem s hs)
  set φ : ℝ → ℂ := fun s => fPath U hU (x + (s : ℂ) * δ) t with hφ
  set φ' : ℝ → ℂ := fun s => derivPath U hU (x + (s : ℂ) * δ) t * δ with hφ'
  have hderiv : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ (φ' s) s := by
    intro s hs
    have h1 := hasDerivAt_fPath_initial hU (coe_mem_lifeSet_iff.2 (hnot s hs))
    have h2 : HasDerivAt (fun s : ℝ => x + (s : ℂ) * δ) δ s := by
      have := ((hasDerivAt_id s).ofReal_comp.mul_const δ).const_add x
      simpa using this
    have := h1.scomp s h2
    simpa [hφ, hφ', Function.comp_def, mul_comm] using this
  have hcont : ContinuousOn φ (Icc 0 1) := fun s hs => (hderiv s hs).continuousAt.continuousWithinAt
  set ψ : ℝ → ℂ := fun s => φ s - φ 0 with hψ
  have hψcont : ContinuousOn ψ (Icc 0 1) := hcont.sub continuousOn_const
  have hψderiv : ∀ s ∈ Ico (0 : ℝ) 1, HasDerivWithinAt ψ (φ' s) (Ici s) s := fun s hs =>
    ((hderiv s ⟨hs.1, hs.2.le⟩).sub_const (φ 0)).hasDerivWithinAt
  have hbound : ∀ s ∈ Ico (0 : ℝ) 1, ‖φ' s‖ ≤ K * ‖ψ s‖ + K * ‖φ 0‖ := by
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
    set y : ℂ := x + (s : ℂ) * δ with hy
    have hynot : y ∉ leftHull U t := hnot s hs'
    have hkoebe := norm_derivPath_mul_infDist_le_of_notMem hU hynot
    have hdist : ρ - ‖δ‖ ≤ infDist y (leftHull U t) := by
      have := le_infDist_leftHull_of_ball (U := U) (y := y) hball
      have hyx : ‖y - x‖ ≤ ‖δ‖ := by
        rw [hy, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1]
        calc s * ‖δ‖ ≤ 1 * ‖δ‖ := mul_le_mul_of_nonneg_right hs.2.le (norm_nonneg _)
          _ = ‖δ‖ := one_mul _
      linarith
    have hdpos : 0 < infDist y (leftHull U t) := lt_of_lt_of_le hρδ hdist
    have hnorm : ‖derivPath U hU y t‖ ≤ koebeK * ‖fPath U hU y t‖ / (ρ - ‖δ‖) := by
      rw [le_div_iff₀ hρδ]
      calc ‖derivPath U hU y t‖ * (ρ - ‖δ‖)
          ≤ ‖derivPath U hU y t‖ * infDist y (leftHull U t) :=
            mul_le_mul_of_nonneg_left hdist (norm_nonneg _)
        _ ≤ koebeK * ‖fPath U hU y t‖ := hkoebe
    have hφs : ‖φ s‖ ≤ ‖ψ s‖ + ‖φ 0‖ := by
      have : φ s = ψ s + φ 0 := by simp [hψ]
      calc ‖φ s‖ = ‖ψ s + φ 0‖ := by rw [← this]
        _ ≤ ‖ψ s‖ + ‖φ 0‖ := norm_add_le _ _
    have : ‖φ' s‖ ≤ K * ‖φ s‖ := by
      simp only [hφ', norm_mul]
      calc ‖derivPath U hU y t‖ * ‖δ‖ ≤ koebeK * ‖fPath U hU y t‖ / (ρ - ‖δ‖) * ‖δ‖ :=
            mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
        _ = K * ‖φ s‖ := by simp only [hK, hφ, hy]; ring
    calc ‖φ' s‖ ≤ K * ‖φ s‖ := this
      _ ≤ K * (‖ψ s‖ + ‖φ 0‖) := by
          refine mul_le_mul_of_nonneg_left hφs ?_
          rw [hK]; have := koebeK_pos; positivity
      _ = K * ‖ψ s‖ + K * ‖φ 0‖ := by ring
  have hψ0 : ‖ψ 0‖ ≤ 0 := by simp [hψ]
  have hG := norm_le_gronwallBound_of_norm_deriv_right_le hψcont hψderiv hψ0 hbound 1
    ⟨zero_le_one, le_rfl⟩
  have hφ1 : φ 1 = fPath U hU w t := by simp [hφ, hδ]
  have hφ0 : φ 0 = fPath U hU x t := by simp [hφ]
  have hK0 : 0 ≤ K := by rw [hK]; have := koebeK_pos; positivity
  have hexp : gronwallBound 0 K (K * ‖φ 0‖) (1 - 0) = (Real.exp K - 1) * ‖φ 0‖ := by
    by_cases hKz : K = 0
    · simp [gronwallBound, hKz]
    · simp only [gronwallBound, hKz, ite_false, sub_zero, mul_one, zero_mul, zero_add]
      field_simp
  rw [hexp] at hG
  have : ψ 1 = fPath U hU w t - fPath U hU x t := by simp [hψ, hφ1, hφ0]
  rw [this, hφ0] at hG
  exact hG

/-- **Koebe step, quantitative form** (paper (3.9), `eqn-finite-exp-1`, constants `1/koebeN`,
`4/9`): if `B(x, ρ) ∩ L_t = ∅` and `‖w - x‖ ≤ ρ / koebeN` then `‖f_t(w) - f_t(x)‖ ≤ (4/9) ‖f_t(x)‖`. -/
theorem norm_fPath_sub_le_ninth (hU : Continuous U) {t : ℝ≥0} {x w : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : ball x ρ ⊆ (leftHull U t)ᶜ) (hw : ‖w - x‖ ≤ ρ / koebeN) :
    ‖fPath U hU w t - fPath U hU x t‖ ≤ (4 / 9) * ‖fPath U hU x t‖ := by
  have hw' : ‖w - x‖ < ρ := lt_of_le_of_lt hw (div_lt_self hρ one_lt_koebeN)
  refine (norm_fPath_sub_le_of_ball hU hball hw').trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  set a : ℝ := ‖w - x‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have hden : 0 < ρ - a := by linarith
  have hK : koebeK * a / (ρ - a) ≤ 4 / 13 := by
    rw [div_le_iff₀ hden]
    rw [le_div_iff₀ koebeN_pos, koebeN] at hw
    linarith
  have hK0 : 0 ≤ koebeK * a / (ρ - a) := by have := koebeK_pos; positivity
  have hexp : Real.exp (koebeK * a / (ρ - a)) ≤ 13 / 9 := by
    have h1 : Real.exp (koebeK * a / (ρ - a)) ≤ Real.exp (4 / 13) := Real.exp_le_exp.2 hK
    have h2 : (1 : ℝ) - 4 / 13 ≤ Real.exp (-(4 / 13)) := by
      have := Real.add_one_le_exp (-(4 / 13 : ℝ)); linarith
    have h3 : Real.exp (4 / 13) * Real.exp (-(4 / 13)) = 1 := by
      rw [← Real.exp_add]; simp
    have h4 : 0 < Real.exp (-(4 / 13 : ℝ)) := Real.exp_pos _
    have h5 : Real.exp (4 / 13) ≤ 13 / 9 := by
      by_contra hcon
      push Not at hcon
      have : (13 / 9 : ℝ) * Real.exp (-(4 / 13)) < Real.exp (4 / 13) * Real.exp (-(4 / 13)) :=
        mul_lt_mul_of_pos_right hcon h4
      rw [h3] at this
      nlinarith
    exact h1.trans h5
  linarith

/-- The ball of radius `r / koebeN` around `z` stays disjoint from the left hull `L_{t₀ + R² s}` of
a Loewner chain restarted at `t₀` and rescaled by `R = |f_{t₀}(z)|`, as long as the hull of the
restarted chain at time `s` stays in `B(0, 1/2)` (paper (3.19), `eqn-finite-exp-2`). -/
theorem ball_subset_compl_leftHull_restart (hU : Continuous U) {z : ℂ} {t₀ : ℝ≥0} {r : ℝ}
    (hr : 0 < r) (hball : ball z r ⊆ (leftHull U t₀)ᶜ) {R : ℝ≥0}
    (hRf : (R : ℝ) = ‖fPath U hU z t₀‖) {s : ℝ≥0}
    (hs : leftHull (restartDriver U t₀ R) s ⊆ ball 0 (1 / 2)) :
    ball z (r / koebeN) ⊆ (leftHull U (t₀ + R ^ 2 * s))ᶜ := by
  intro w hw hwL
  have hz0 : z ∈ (leftHull U t₀)ᶜ := hball (mem_ball_self hr)
  have hzf : fPath U hU z t₀ ≠ 0 := fPath_coe_ne_zero hU hz0
  have hRpos : 0 < R := by
    have : (0 : ℝ) < R := by rw [hRf]; exact norm_pos_iff.2 hzf
    exact_mod_cast this
  have hwr : w ∈ ball z r := by
    refine ball_subset_ball ?_ hw
    exact (div_lt_self hr one_lt_koebeN).le
  have hw0 : w ∈ (leftHull U t₀)ᶜ := hball hwr
  have hmem := (mem_leftHull_add_iff hU (R ^ 2 * s) t₀ w hw0).1 (by
    rw [add_comm]; exact hwL)
  rw [centeredLoewnerMap_eq_fPath hU t₀ hw0] at hmem
  -- the scaled hull
  have hRinv : 0 < R⁻¹ := inv_pos.2 hRpos
  have hscale := leftHull_scale (fun x => U (x + t₀) - U t₀) R⁻¹ hRinv s
  rw [← restartDriver_eq_scale_shift U t₀ hRpos] at hscale
  have hmem' : (R⁻¹ : ℂ) * fPath U hU w t₀ ∈ leftHull (restartDriver U t₀ R) s := by
    rw [hscale]
    refine ⟨fPath U hU w t₀, ?_, by simp⟩
    have h3 : s / (R⁻¹) ^ 2 = R ^ 2 * s := by
      rw [inv_pow, div_inv_eq_mul, mul_comm]
    rw [h3]
    exact hmem
  have h1 := hs hmem'
  rw [mem_ball_zero_iff, norm_mul, norm_inv, Complex.norm_real] at h1
  simp only [NNReal.norm_eq] at h1
  have hRp : (0 : ℝ) < R := by exact_mod_cast hRpos
  have h2 : (R : ℝ)⁻¹ * ‖fPath U hU w t₀‖ < 1 / 2 := h1
  have h3 : ‖fPath U hU w t₀‖ < R / 2 := by
    rw [inv_mul_lt_iff₀ hRp] at h2; linarith
  have h4 := norm_fPath_sub_le_ninth hU hr hball (x := z) (w := w)
    (by rw [mem_ball, dist_eq_norm] at hw; linarith)
  have h5 : ‖fPath U hU z t₀‖ - ‖fPath U hU w t₀‖ ≤ ‖fPath U hU w t₀ - fPath U hU z t₀‖ := by
    have := norm_sub_norm_le (fPath U hU z t₀) (fPath U hU w t₀)
    rwa [norm_sub_rev] at this
  rw [← hRf] at h4 h5
  nlinarith

/-! ### No jump of the hull at a hitting time -/

open Filter Topology in
/-- **No swallowing jump near a non-swallowed point.** Let `τ > 0`, `z ∉ L_τ`, and suppose the disc
`B(z, r)` is disjoint from `L_t` for every `t < τ`. Then `B(z, r)` is disjoint from `L_τ` as well
(the paper uses this tacitly: "by the definition of `τ_k` we have `dist(z, L_{τ_k}) ≥ 16^{-k}`",
where our `lvl k` replaces `16^{-k}`).

Proof: `B(z, r) ∩ L_τ` is closed in `B(z, r)`; it is also open, because for `x ∈ B(z, r) ∩ L_τ` one
has `T_x = τ`, so `|f_t(x)| → 0` as `t ↑ τ` (Lemma 2.5), while the Koebe step gives
`|f_t(x)| ≥ (5/9) |f_t(x')|` for `x'` near `x`, and `|f_t(x')| → |f_τ(x')| > 0` if `x' ∉ L_τ`. -/
theorem ball_subset_compl_leftHull_of_forall_lt (hU : Continuous U) {z : ℂ} {τ : ℝ≥0} {r : ℝ}
    (hr : 0 < r) (hτ : 0 < τ) (hz : z ∉ leftHull U τ)
    (hbefore : ∀ t : ℝ≥0, t < τ → ball z r ⊆ (leftHull U t)ᶜ) :
    ball z r ⊆ (leftHull U τ)ᶜ := by
  have key : ∀ x ∈ ball z r, x ∈ leftHull U τ → x ∈ interior (leftHull U τ) := by
    intro x hxB hxL
    rw [mem_interior]
    set ρx : ℝ := r - ‖x - z‖ with hρx
    have hxz : ‖x - z‖ < r := by rwa [mem_ball, dist_eq_norm] at hxB
    have hρxpos : 0 < ρx := by linarith
    have hN := koebeN_pos
    refine ⟨ball x (ρx / (2 * koebeN)), ?_, isOpen_ball, mem_ball_self (by positivity)⟩
    intro x' hx'
    by_contra hx'L
    -- the absorbing time of `x` is `τ`
    have hTx : absorbingTime U x = τ := by
      refine le_antisymm (mem_leftHull_iff.1 hxL) ?_
      refine ENNReal.le_of_forall_nnreal_lt fun t ht => ?_
      have ht' : t < τ := by exact_mod_cast ht
      exact (notMem_leftHull_iff.1 (hbefore t ht' hxB)).le
    have hTne : absorbingTime U x ≠ ⊤ := by rw [hTx]; exact ENNReal.coe_ne_top
    have hTreal : (absorbingTime U x).toReal = (τ : ℝ) := by rw [hTx]; simp
    have hlife : lifeSet U x = Ico 0 (τ : ℝ) := by rw [lifeSet_eq_Ico hTne, hTreal]
    have hτpos : (0 : ℝ) < τ := by exact_mod_cast hτ
    have hlim1 := tendsto_norm_fPath_nhdsWithin hU hTne
    rw [hTreal, hlife] at hlim1
    have hτ' : (τ : ℝ) ∈ lifeSet U x' := coe_mem_lifeSet_iff.2 hx'L
    have hlim2 : Tendsto (fun t : ℝ => ‖fPath U hU x' t‖) (𝓝[Ico 0 (τ : ℝ)] (τ : ℝ))
        (𝓝 ‖fPath U hU x' τ‖) := by
      have := (continuousWithinAt_fPath_Ici hU hτ').norm
      exact this.tendsto.mono_left (nhdsWithin_mono _ Ico_subset_Ici_self)
    have : (𝓝[Ico 0 (τ : ℝ)] (τ : ℝ)).NeBot := by
      rw [nhdsWithin_Ico_eq_nhdsLT hτpos]; infer_instance
    have hev : ∀ᶠ t in 𝓝[Ico 0 (τ : ℝ)] (τ : ℝ),
        (5 / 9) * ‖fPath U hU x' t‖ ≤ ‖fPath U hU x t‖ := by
      refine eventually_nhdsWithin_of_forall fun t ht => ?_
      set t' : ℝ≥0 := t.toNNReal with ht'
      have htt' : (t' : ℝ) = t := Real.coe_toNNReal t ht.1
      have ht'lt : t' < τ := by
        rw [← NNReal.coe_lt_coe, htt']; exact ht.2
      have hball' : ball x' (ρx / 2) ⊆ (leftHull U t')ᶜ := by
        refine fun y hy => hbefore t' ht'lt ?_
        rw [mem_ball, dist_eq_norm] at hy ⊢
        have hxx' : ‖x' - x‖ < ρx / (2 * koebeN) := by rwa [mem_ball, dist_eq_norm] at hx'
        have hρN : ρx / (2 * koebeN) ≤ ρx / 2 :=
          div_le_div_of_nonneg_left hρxpos.le (by norm_num) (by linarith [one_lt_koebeN])
        have : ‖y - z‖ ≤ ‖y - x'‖ + ‖x' - x‖ + ‖x - z‖ := by
          calc ‖y - z‖ = ‖(y - x') + (x' - x) + (x - z)‖ := by congr 1; ring
            _ ≤ ‖(y - x') + (x' - x)‖ + ‖x - z‖ := norm_add_le _ _
            _ ≤ ‖y - x'‖ + ‖x' - x‖ + ‖x - z‖ := by gcongr; exact norm_add_le _ _
        linarith
      have h1 := norm_fPath_sub_le_ninth hU (by positivity : (0 : ℝ) < ρx / 2) hball'
        (x := x') (w := x) (by
          rw [mem_ball, dist_eq_norm] at hx'
          rw [norm_sub_rev, div_div]; linarith)
      have h2 : ‖fPath U hU x' t'‖ - ‖fPath U hU x t'‖ ≤ ‖fPath U hU x t' - fPath U hU x' t'‖ := by
        have := norm_sub_norm_le (fPath U hU x' t') (fPath U hU x t')
        rwa [norm_sub_rev] at this
      rw [htt'] at h1 h2
      linarith
    have hle := le_of_tendsto_of_tendsto (hlim2.const_mul (5 / 9)) hlim1 hev
    have hpos : 0 < ‖fPath U hU x' τ‖ := norm_pos_iff.2 (fPath_coe_ne_zero hU hx'L)
    linarith
  by_contra hcon
  rw [subset_def] at hcon
  push Not at hcon
  obtain ⟨x, hxB, hxL⟩ := hcon
  have hxL' : x ∈ leftHull U τ := by simpa using hxL
  have hopen1 : IsOpen (leftHull U τ)ᶜ := isOpen_compl_leftHull U hU τ
  have hconn := (convex_ball z r).isPreconnected
  obtain ⟨y, hyB, hyu, hyv⟩ := hconn (leftHull U τ)ᶜ (interior (leftHull U τ)) hopen1
    isOpen_interior (by
      intro y hy
      by_cases hyL : y ∈ leftHull U τ
      · exact Or.inr (key y hy hyL)
      · exact Or.inl hyL)
    ⟨z, mem_ball_self hr, hz⟩ ⟨x, hxB, key x hxB hxL'⟩
  exact hyu (interior_subset hyv)

end ComplexSLE.Internal.Polar

end
