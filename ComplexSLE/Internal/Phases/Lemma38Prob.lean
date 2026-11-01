/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.Lemma38Markov

/-!
# Lemma 3.10, the pathwise one-step inequality (M7/E2)

Fix an adapted driver `U` with `U 0 = 0`, a unit point `z`, `t̃` and `u₀ < 1/64`, `q = u₀/4`,
`κ = 1 - e^{-q}`. On a path with `σ_z` defined on `[0, ∞)` (a.s., Remark 2.12), put
`V_k = ` the post-`τ̂_k` driver rescaled by `|f_{τ̂_k}(z)|⁻¹`, and `G_k = {V_k ∈ 𝒢}`
(`𝒢 = Gset u₀`). Then

  `Y_{k+1} ≤ Y_k (1 - κ 1_{G_k})`   (`Yk_succ_le`)

where `Y_k = 1_{τ_k ≤ θ} e^{-A(τ̂_k)}`. Proof: if `τ_{k+1} ≤ θ` then `τ_k ≤ τ_{k+1} ≤ θ`, both
finite, and `A` is non-decreasing on the life set; on `G_k` the deterministic Koebe step
(`step_good`) forces `τ_{k+1} ≥ τ_k + R² u₀` and the clock to increase by `≥ q = u₀/4`.
-/

public section

open scoped NNReal ENNReal Topology Real
open Set Metric Filter MeasureTheory ProbabilityTheory

namespace ComplexSLE.Internal

open Polar

section Pathwise

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

variable (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) (tt : ℝ≥0)

/-- On `{τ_k ≤ θ}` (for a path with `σ_z` defined everywhere): the data at `τ̂_k = τ_k`. -/
theorem Yk_of_le {ω : Ω} (hω : sigmaDom (fun s => U s ω) (hU.cont ω) z = Ici 0) {k : ℕ}
    (h : hitK (U := U) z k ω ≤ sigmaTop hU z tt ω) :
    ∃ x : ℝ≥0, hitTime (fun s => U s ω) z (lvl k) = (x : WithTop ℝ≥0) ∧
      (x : ℝ) ∈ lifeSet (fun s => U s ω) z ∧ tauHat hU z tt k ω = (x : WithTop ℝ≥0) ∧
      (x : ℝ) ≤ sigmaTime (fun s => U s ω) (hU.cont ω) z tt ∧
      Yk hU z tt k ω = Real.exp (-clock (fun s => U s ω) (hU.cont ω) z x) ∧
      (rhoK hU z tt k ω : ℝ) = ‖fPath (fun s => U s ω) (hU.cont ω) z x‖ := by
  obtain ⟨hcoe, hlife⟩ := tauHat_untopA_mem hU z tt hω k
  set x : ℝ≥0 := (tauHat hU z tt k ω).untopA with hx
  have htau : tauHat hU z tt k ω = hitK (U := U) z k ω := min_eq_left h
  have hhit : hitTime (fun s => U s ω) z (lvl k) = (x : WithTop ℝ≥0) := by
    have : hitK (U := U) z k ω = (x : WithTop ℝ≥0) := htau ▸ hcoe
    exact this
  have hmem : (tt : ℝ) ∈ sigmaDom (fun s => U s ω) (hU.cont ω) z := by
    rw [hω]; exact tt.coe_nonneg
  have hθ := sigmaTop_of_mem hU hmem
  have hσ := sigmaTime_mem_lifeSet (hU.cont ω) hmem
  have hle : (x : ℝ) ≤ sigmaTime (fun s => U s ω) (hU.cont ω) z tt := by
    have h1 : tauHat hU z tt k ω ≤ sigmaTop hU z tt ω := min_le_right _ _
    rw [hθ, hcoe, WithTop.coe_le_coe] at h1
    have h2 : (((sigmaTime (fun s => U s ω) (hU.cont ω) z tt).toNNReal : ℝ≥0) : ℝ) =
      sigmaTime (fun s => U s ω) (hU.cont ω) z tt := Real.coe_toNNReal _ hσ.1
    rw [← h2]; exact_mod_cast h1
  refine ⟨x, hhit, hlife, hcoe, hle, ?_, ?_⟩
  · have hif : (if hitK (U := U) z k ω ≤ sigmaTop hU z tt ω then (1 : ℝ) else 0) = 1 :=
      by simp only [h, ↓reduceIte]
    unfold Yk cK clockOrZero
    rw [hif, one_mul, ← hx]
    simp only [hlife, ↓reduceIte]
  · unfold rhoK
    rw [← hx, centeredOrZero_eq hU.cont z hlife]
    simp

/-- **The one-step inequality** `Y_{k+1} ≤ Y_k (1 - κ 1_{V_k ∈ 𝒢})`. -/
theorem Yk_succ_le {ω : Ω} (hω : sigmaDom (fun s => U s ω) (hU.cont ω) z = Ici 0)
    (hU0 : U 0 ω = 0) (hz : ‖z‖ = 1) {u₀ : ℝ≥0} (hu₀ : (u₀ : ℝ) < 1 / 64) (j : ℕ) :
    Yk hU z tt (j + 1) ω ≤ Yk hU z tt j ω *
      (1 - (1 - Real.exp (-((u₀ : ℝ) / 4))) * (Gset u₀).indicator (fun _ => (1 : ℝ))
        (CPath.scale (rhoK hU z tt j ω)⁻¹ (postPath hU (tauHat hU z tt j) ω))) := by
  set κ : ℝ := 1 - Real.exp (-((u₀ : ℝ) / 4)) with hκ
  have hq : 0 ≤ (u₀ : ℝ) / 4 := by positivity
  have hκ0 : 0 ≤ κ := by
    rw [hκ, sub_nonneg, Real.exp_le_one_iff]; linarith
  have hκ1 : κ ≤ 1 := by rw [hκ]; linarith [Real.exp_pos (-((u₀ : ℝ) / 4))]
  set G : Set CPath := Gset u₀
  set Vj : CPath := CPath.scale (rhoK hU z tt j ω)⁻¹ (postPath hU (tauHat hU z tt j) ω) with hVj
  have hind01 : G.indicator (fun _ => (1 : ℝ)) Vj = 0 ∨ G.indicator (fun _ => (1 : ℝ)) Vj = 1 := by
    by_cases h : Vj ∈ G
    · right; simp [h]
    · left; simp [h]
  have hY0 := Yk_nonneg hU z tt j ω
  have hfac : 0 ≤ 1 - κ * G.indicator (fun _ => (1 : ℝ)) Vj := by
    rcases hind01 with h | h <;> rw [h] <;> nlinarith
  by_cases hΘ' : hitK (U := U) z (j + 1) ω ≤ sigmaTop hU z tt ω
  · -- both levels are reached before `θ`
    obtain ⟨a', ha'hit, ha'life, ha'tau, ha'le, hY', hρ'⟩ := Yk_of_le hU z tt hω hΘ'
    have hmono : hitK (U := U) z j ω ≤ hitK (U := U) z (j + 1) ω :=
      hitTime_mono (lvl_anti (Nat.le_succ j))
    have hΘ : hitK (U := U) z j ω ≤ sigmaTop hU z tt ω := hmono.trans hΘ'
    obtain ⟨x, hxhit, hxlife, hxtau, hxle, hY, hρ⟩ := Yk_of_le hU z tt hω hΘ
    have hxa' : x ≤ a' := by
      have h1 : hitTime (fun s => U s ω) z (lvl j) ≤ hitTime (fun s => U s ω) z (lvl (j + 1)) :=
        hmono
      rw [hxhit, ha'hit, WithTop.coe_le_coe] at h1
      exact h1
    have hclock : clock (fun s => U s ω) (hU.cont ω) z x ≤
        clock (fun s => U s ω) (hU.cont ω) z a' :=
      clock_monotoneOn (hU.cont ω) z hxlife ha'life (by exact_mod_cast hxa')
    by_cases hG : Vj ∈ G
    · -- the good step
      have hind : G.indicator (fun _ => (1 : ℝ)) Vj = 1 := by simp [hG]
      rw [hind, hY', hY]
      have hhit' : hitTime (fun s => U s ω) z (lvl j) = (x : WithTop ℝ≥0) := hxhit
      have hdd := lvl_le_infDist_hitTime (hU.cont ω) hU0 hz hhit' hxlife
      have hRr : (rhoK hU z tt j ω : ℝ) = ‖fPath (fun s => U s ω) (hU.cont ω) z x‖ := hρ
      have hgood : ∀ s : ℝ≥0, s ≤ u₀ →
          ‖restartDriver (fun r => U r ω) x (rhoK hU z tt j ω) s‖ ≤ 1 / 16 := by
        intro s hs
        have := hG s hs
        rw [hVj, scale_postPath_apply hU (tauHat hU z tt j) (rhoK hU z tt j ω) ω s, hxtau] at this
        exact this
      obtain ⟨hstar, hball, hclk⟩ := step_good (hU.cont ω) hxlife hdd hu₀ hRr hgood
      set R := rhoK hU z tt j ω with hRdef
      have hRpos : 0 < R := by
        have : (0 : ℝ) < R := by
          rw [hRr]; exact norm_pos_iff.2 (fPath_ne_zero (hU.cont ω) hxlife)
        exact_mod_cast this
      have hstar_le : (x : ℝ) + (R : ℝ) ^ 2 * u₀ ≤ a' := by
        by_contra hlt
        push Not at hlt
        have hxa'R : (x : ℝ) ≤ a' := by exact_mod_cast hxa'
        set s : ℝ≥0 := (a' - x) / R ^ 2 with hs
        have hRsq : (R : ℝ) ^ 2 ≠ 0 := by positivity
        have hs' : (R : ℝ) ^ 2 * s = (a' : ℝ) - x := by
          rw [hs]
          have : ((a' - x : ℝ≥0) : ℝ) = (a' : ℝ) - x := NNReal.coe_sub hxa'
          rw [NNReal.coe_div, NNReal.coe_pow, this]
          field_simp
        have hsu : s ≤ u₀ := by
          rw [← NNReal.coe_le_coe]
          have : (R : ℝ) ^ 2 * s < (R : ℝ) ^ 2 * u₀ := by rw [hs']; linarith
          exact (lt_of_mul_lt_mul_left this (by positivity)).le
        have h1 := hball s hsu
        have haeq : x + R ^ 2 * s = a' := by
          rw [← NNReal.coe_inj]
          push_cast
          rw [hs']; ring
        rw [haeq] at h1
        have h2 := infDist_hitTime_le (hU.cont ω) ha'hit
        have h3 := lvl_succ_lt_div j
        linarith
      have hclk2 : clock (fun s => U s ω) (hU.cont ω) z ((x : ℝ) + (R : ℝ) ^ 2 * u₀) ≤
          clock (fun s => U s ω) (hU.cont ω) z a' :=
        clock_monotoneOn (hU.cont ω) z hstar ha'life hstar_le
      have hexp : Real.exp (-clock (fun s => U s ω) (hU.cont ω) z a') ≤
          Real.exp (-clock (fun s => U s ω) (hU.cont ω) z x - (u₀ : ℝ) / 4) :=
        Real.exp_le_exp.2 (by linarith)
      calc Real.exp (-clock (fun s => U s ω) (hU.cont ω) z a')
          ≤ Real.exp (-clock (fun s => U s ω) (hU.cont ω) z x - (u₀ : ℝ) / 4) := hexp
        _ = Real.exp (-clock (fun s => U s ω) (hU.cont ω) z x) *
            (1 - (1 - Real.exp (-((u₀ : ℝ) / 4))) * 1) := by
          rw [sub_eq_add_neg, Real.exp_add]; ring_nf
    · have hind : G.indicator (fun _ => (1 : ℝ)) Vj = 0 := by simp [hG]
      rw [hind, hY', hY]
      simp only [mul_zero, sub_zero, mul_one]
      exact Real.exp_le_exp.2 (by linarith)
  · have : Yk hU z tt (j + 1) ω = 0 := by
      unfold Yk
      simp only [hΘ', ↓reduceIte, zero_mul]
    rw [this]
    exact mul_nonneg hY0 hfac

end Pathwise

end ComplexSLE.Internal

end
