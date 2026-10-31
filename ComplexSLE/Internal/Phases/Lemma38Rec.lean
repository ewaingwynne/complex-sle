/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.Lemma38Prob

/-!
# Lemma 3.8, the recursion and the geometric tail bound (M7/E2)

Source: paper.tex:L1600-1630. Let `a_k = E[Y_k]`. The strong Markov step (`lintegral_Gset_mul_Yk`)
and the pathwise inequality `Y_{k+1} ≤ Y_k (1 - κ 1_{V_k ∈ 𝒢})` (`Yk_succ_le`) give

  `a_{k+1} + κ Λ(𝒢) a_k ≤ a_k`,

and `Λ(𝒢) ≥ 1/2` for a suitable `u₀ ∈ (0, 1/64)` (path continuity at `0`, `exists_u₀`). Hence
`a_k ≤ (1 - κ/2)^k`. Since `{dist(z, L_{σ_z(t̃)}) ≤ 16^{-k}} ⊆ {τ_k ≤ θ}` and `A(τ_k) ≤ A(θ) = t̃`
there, `1 ≤ e^{t̃} Y_k` on that event, so

  `P(dist(z, L_{σ_z(t̃)}) ≤ 16^{-k}) ≤ e^{t̃} (1 - κ/2)^k`   (`tail_bound`),

uniformly over the unit points `z`. This replaces the paper's `C_N 2^{-k}` (which needs the
independence of the events and a uniform lower bound for the exit clock): the Markov step is used
for the *conditional* probability `P(V_k ∈ 𝒢 | ℱ_{τ̂_k}) = Λ(𝒢) ≥ 1/2`, and the exponential moment
replaces the binomial count.
-/

public section

open scoped NNReal ENNReal Topology Real
open Set Metric Filter MeasureTheory ProbabilityTheory

namespace ComplexSLE.Internal

open Polar

section Rec

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-- **A good oscillation level.** For an adapted driver (continuous paths, `U 0 = 0` a.s.) there is
`u₀ ∈ (0, 1/64)` with `P(|U_s| ≤ 1/16 for all s ≤ u₀) ≥ 1/2`. -/
theorem exists_u₀ [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ) :
    ∃ u₀ : ℝ≥0, 0 < u₀ ∧ (u₀ : ℝ) < 1 / 64 ∧
      (1 / 2 : ℝ≥0∞) ≤ P.map (CPath.ofDriver U hU.cont) (Gset u₀) := by
  set u : ℕ → ℝ≥0 := fun n => ((n : ℝ≥0) + 65)⁻¹ with hu
  set B : ℕ → Set Ω := fun n => {ω | ∀ s : ℝ≥0, s ≤ u n → ‖U s ω‖ ≤ 1 / 16} with hB
  have hmono : Monotone B := by
    intro n k hnk ω hω s hs
    refine hω s (hs.trans ?_)
    simp only [hu]
    exact inv_anti₀ (by positivity) (by gcongr)
  have hU0 := hU.toIsSLEDriver.zero
  have hcover : ∀ᵐ ω ∂P, ω ∈ ⋃ n, B n := by
    filter_upwards [hU0] with ω hω0
    have hcont : Continuous fun t => U t ω := hU.cont ω
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 (hcont.continuousAt (x := 0)) (1 / 16)
      (by norm_num)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    refine mem_iUnion.2 ⟨n, fun s hs => ?_⟩
    have hs' : dist s 0 < δ := by
      rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg s.coe_nonneg]
      have h1 : (s : ℝ) ≤ ((n : ℝ) + 65)⁻¹ := by
        have := (NNReal.coe_le_coe.2 hs)
        simpa [hu] using this
      have h2 : ((n : ℝ) + 65)⁻¹ < 1 / ((n : ℝ) + 1) := by
        rw [one_div]; exact inv_strictAnti₀ (by positivity) (by linarith)
      linarith
    have := hδ' hs'
    rw [hω0, dist_eq_norm, sub_zero] at this
    exact this.le
  have hUm : ∀ t, Measurable (U t) := fun t => hU.adapted.measurable
  have hBeq : ∀ n, B n = CPath.ofDriver U hU.cont ⁻¹' Gset (u n) := fun n => rfl
  have hBm : ∀ n, MeasurableSet (B n) := fun n => by
    rw [hBeq]; exact CPath.measurable_ofDriver hU.cont hUm (measurableSet_Gset _)
  have hunion : P (⋃ n, B n) = 1 := by
    have hm : MeasurableSet (⋃ n, B n) := MeasurableSet.iUnion hBm
    rw [← prob_compl_eq_zero_iff hm]
    rw [ae_iff] at hcover
    exact hcover
  have htend := tendsto_measure_iUnion_atTop (μ := P) hmono
  rw [hunion] at htend
  obtain ⟨n, hn⟩ := ((tendsto_order.1 htend).1 (1 / 2) (by norm_num)).exists
  refine ⟨u n, by simp only [hu]; positivity, ?_, ?_⟩
  · simp only [hu]
    have : ((n : ℝ) + 65)⁻¹ < 1 / 64 := by
      rw [one_div]; exact inv_strictAnti₀ (by norm_num) (by linarith [n.cast_nonneg (α := ℝ)])
    exact_mod_cast this
  · rw [Measure.map_apply (CPath.measurable_ofDriver hU.cont hUm) (measurableSet_Gset _), ← hBeq]
    exact hn.le

variable (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) (tt : ℝ≥0)

/-- **The recursion** `a_{j+1} + κ Λ(𝒢) a_j ≤ a_j`, `a_j = E[Y_j]`. -/
theorem lintegral_Yk_succ_le [IsProbabilityMeasure P] (ha : 0 < a) (hc : c ^ 2 ≤ a * b)
    (hz : ‖z‖ = 1) {u₀ : ℝ≥0} (hu₀ : (u₀ : ℝ) < 1 / 64) (j : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Yk hU z tt (j + 1) ω) ∂P +
      ENNReal.ofReal (1 - Real.exp (-((u₀ : ℝ) / 4))) *
        (P.map (CPath.ofDriver U hU.cont) (Gset u₀) *
          ∫⁻ ω, ENNReal.ofReal (Yk hU z tt j ω) ∂P) ≤
    ∫⁻ ω, ENNReal.ofReal (Yk hU z tt j ω) ∂P := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; exact zero_ne_one hz
  have hgood := Polar.ae_sigmaDom_eq_Ici hU z ha hc hz0
  have hU0 := hU.toIsSLEDriver.zero
  set κ : ℝ := 1 - Real.exp (-((u₀ : ℝ) / 4)) with hκ
  have hκ0 : 0 ≤ κ := by
    rw [hκ, sub_nonneg, Real.exp_le_one_iff]
    have : (0 : ℝ) ≤ (u₀ : ℝ) / 4 := by positivity
    linarith
  have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal (Yk hU z tt (j + 1) ω) +
      ENNReal.ofReal κ * ((Gset u₀).indicator (fun _ => (1 : ℝ≥0∞))
        (CPath.scale (rhoK hU z tt j ω)⁻¹ (postPath hU (tauHat hU z tt j) ω)) *
        ENNReal.ofReal (Yk hU z tt j ω)) ≤ ENNReal.ofReal (Yk hU z tt j ω) := by
    filter_upwards [hgood, hU0] with ω hω hω0
    have hs := Yk_succ_le hU z tt hω hω0 hz hu₀ j
    set Vj := CPath.scale (rhoK hU z tt j ω)⁻¹ (postPath hU (tauHat hU z tt j) ω)
    have hY0 := Yk_nonneg hU z tt j ω
    have hY1 := Yk_nonneg hU z tt (j + 1) ω
    by_cases hG : Vj ∈ Gset u₀
    · simp only [hG, Set.indicator_of_mem, mul_one, one_mul] at hs ⊢
      have h2 : Yk hU z tt (j + 1) ω + κ * Yk hU z tt j ω ≤ Yk hU z tt j ω := by
        rw [← hκ] at hs; nlinarith
      calc ENNReal.ofReal (Yk hU z tt (j + 1) ω) + ENNReal.ofReal κ *
            ENNReal.ofReal (Yk hU z tt j ω)
          = ENNReal.ofReal (Yk hU z tt (j + 1) ω + κ * Yk hU z tt j ω) := by
            rw [ENNReal.ofReal_add hY1 (mul_nonneg hκ0 hY0), ENNReal.ofReal_mul hκ0]
        _ ≤ _ := ENNReal.ofReal_le_ofReal h2
    · simp only [hG, Set.indicator_of_notMem, not_false_eq_true, zero_mul, mul_zero, add_zero] at hs ⊢
      simp only [sub_zero, mul_one] at hs
      exact ENNReal.ofReal_le_ofReal hs
  have hYm := measurable_Yk hU z tt (j + 1)
  calc ∫⁻ ω, ENNReal.ofReal (Yk hU z tt (j + 1) ω) ∂P +
        ENNReal.ofReal κ * (P.map (CPath.ofDriver U hU.cont) (Gset u₀) *
          ∫⁻ ω, ENNReal.ofReal (Yk hU z tt j ω) ∂P)
      = ∫⁻ ω, (ENNReal.ofReal (Yk hU z tt (j + 1) ω) +
        ENNReal.ofReal κ * ((Gset u₀).indicator (fun _ => (1 : ℝ≥0∞))
          (CPath.scale (rhoK hU z tt j ω)⁻¹ (postPath hU (tauHat hU z tt j) ω)) *
          ENNReal.ofReal (Yk hU z tt j ω))) ∂P := by
        rw [lintegral_add_left (f := fun ω => ENNReal.ofReal (Yk hU z tt (j + 1) ω))
          (ENNReal.measurable_ofReal.comp hYm),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_Gset_mul_Yk hU z tt ha hc hz0 u₀ j]
    _ ≤ _ := lintegral_mono_ae hpt

theorem lintegral_Yk_le_one [IsProbabilityMeasure P] (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Yk hU z tt k ω) ∂P ≤ 1 := by
  calc ∫⁻ ω, ENNReal.ofReal (Yk hU z tt k ω) ∂P ≤ ∫⁻ _ω, 1 ∂P :=
        lintegral_mono fun ω => by
          rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (Yk_le_one hU z tt k ω)
    _ = 1 := by simp

/-- **Geometric decay of `E[Y_k]`**, with a rate `r < 1` depending only on the law of the driver. -/
theorem exists_rate [IsProbabilityMeasure P] (ha : 0 < a) (hc : c ^ 2 ≤ a * b) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ (z : ℂ) (tt : ℝ≥0), ‖z‖ = 1 → ∀ k : ℕ,
      ∫⁻ ω, ENNReal.ofReal (Yk hU z tt k ω) ∂P ≤ ENNReal.ofReal r ^ k := by
  obtain ⟨u₀, hu₀pos, hu₀, hΛ⟩ := exists_u₀ hU
  set κ : ℝ := 1 - Real.exp (-((u₀ : ℝ) / 4)) with hκ
  have hq : (0 : ℝ) < (u₀ : ℝ) / 4 := by
    have : (0 : ℝ) < u₀ := by exact_mod_cast hu₀pos
    positivity
  have hκpos : 0 < κ := by
    rw [hκ, sub_pos, Real.exp_lt_one_iff]; linarith
  have hκ1 : κ ≤ 1 := by rw [hκ]; linarith [Real.exp_pos (-((u₀ : ℝ) / 4))]
  refine ⟨1 - κ / 2, by linarith, by linarith, fun z tt hz k => ?_⟩
  have hstep : ∀ j : ℕ, ∫⁻ ω, ENNReal.ofReal (Yk hU z tt (j + 1) ω) ∂P ≤
      ENNReal.ofReal (1 - κ / 2) * ∫⁻ ω, ENNReal.ofReal (Yk hU z tt j ω) ∂P := by
    intro j
    have h1 := lintegral_Yk_succ_le hU z tt ha hc hz hu₀ j
    rw [← hκ] at h1
    set A := ∫⁻ ω, ENNReal.ofReal (Yk hU z tt j ω) ∂P with hA
    have hAfin : A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (lintegral_Yk_le_one hU z tt j)
    have hhalf : ENNReal.ofReal (κ / 2) = ENNReal.ofReal κ * (1 / 2) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat, div_eq_mul_inv,
        one_div]
    have h2 : ENNReal.ofReal (κ / 2) * A ≤ ENNReal.ofReal κ *
        (P.map (CPath.ofDriver U hU.cont) (Gset u₀) * A) := by
      rw [hhalf, mul_assoc]
      exact mul_le_mul' le_rfl (mul_le_mul' hΛ le_rfl)
    have hsum : ENNReal.ofReal (1 - κ / 2) * A + ENNReal.ofReal (κ / 2) * A = A := by
      rw [← add_mul, ← ENNReal.ofReal_add (by linarith) (by linarith)]
      have : 1 - κ / 2 + κ / 2 = 1 := by ring
      rw [this, ENNReal.ofReal_one, one_mul]
    have hfin2 : ENNReal.ofReal (κ / 2) * A ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin
    have h3 : ∫⁻ ω, ENNReal.ofReal (Yk hU z tt (j + 1) ω) ∂P + ENNReal.ofReal (κ / 2) * A ≤
        ENNReal.ofReal (1 - κ / 2) * A + ENNReal.ofReal (κ / 2) * A := by
      rw [hsum]
      exact (add_le_add le_rfl h2).trans h1
    exact (ENNReal.add_le_add_iff_right hfin2).1 h3
  have hind : ∀ n : ℕ, ∫⁻ ω, ENNReal.ofReal (Yk hU z tt n ω) ∂P ≤ ENNReal.ofReal (1 - κ / 2) ^ n := by
    intro n
    induction n with
    | zero => simpa using lintegral_Yk_le_one hU z tt 0
    | succ n ih =>
      calc _ ≤ ENNReal.ofReal (1 - κ / 2) * ∫⁻ ω, ENNReal.ofReal (Yk hU z tt n ω) ∂P := hstep n
        _ ≤ ENNReal.ofReal (1 - κ / 2) * ENNReal.ofReal (1 - κ / 2) ^ n := by gcongr
        _ = _ := by rw [pow_succ']
  exact hind k

/-- **The geometric tail bound** (paper (3.20)-(3.21), `eqn-log-finite-show`): there is `r < 1`,
depending only on the law of the driver, such that for every unit `z`, every `t̃ ≥ 0`, and every `k`,

  `P(dist(z, L_{σ_z(t̃)}) ≤ 16^{-k}) ≤ e^{t̃} r^k`.

The constants do not depend on the point `z`. Uses the EXTERNAL `koebe_quarter` and, through the
Markov step, `strongMarkov_sleDriver`. -/
theorem tail_bound [IsProbabilityMeasure P] (ha : 0 < a) (hc : c ^ 2 ≤ a * b) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ (z : ℂ) (tt : ℝ≥0), ‖z‖ = 1 → ∀ k : ℕ,
      P {ω | infDist z (leftHull (fun s => U s ω)
          (sigmaTime (fun s => U s ω) (hU.cont ω) z tt).toNNReal) ≤ lvl k} ≤
        ENNReal.ofReal (Real.exp tt) * ENNReal.ofReal r ^ k := by
  obtain ⟨r, hr0, hr1, hrate⟩ := exists_rate hU ha hc
  refine ⟨r, hr0, hr1, fun z tt hz k => ?_⟩
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; exact zero_ne_one hz
  have hgood := Polar.ae_sigmaDom_eq_Ici hU z ha hc hz0
  set f : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp tt) * ENNReal.ofReal (Yk hU z tt k ω)
    with hf
  have hfm : Measurable f :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp (measurable_Yk hU z tt k))
  have hsub : {ω | infDist z (leftHull (fun s => U s ω)
      (sigmaTime (fun s => U s ω) (hU.cont ω) z tt).toNNReal) ≤ lvl k} ≤ᵐ[P]
      {ω | 1 ≤ f ω} := by
    filter_upwards [hgood] with ω hω hmem
    have hmemσ : (tt : ℝ) ∈ sigmaDom (fun s => U s ω) (hU.cont ω) z := by
      rw [hω]; exact tt.coe_nonneg
    have hθ := sigmaTop_of_mem hU hmemσ
    have hle : hitK (U := U) z k ω ≤ sigmaTop hU z tt ω := by
      rw [hθ]
      exact (hitTime_le_iff (hU.cont ω)).2 hmem
    obtain ⟨x, -, hxlife, -, hxle, hY, -⟩ := Yk_of_le hU z tt hω hle
    have hσlife := sigmaTime_mem_lifeSet (hU.cont ω) hmemσ
    have hclock : clock (fun s => U s ω) (hU.cont ω) z x ≤ tt := by
      have h1 := clock_monotoneOn (hU.cont ω) z hxlife hσlife hxle
      rwa [clock_sigmaTime (hU.cont ω) hmemσ] at h1
    have hYge : Real.exp (-(tt : ℝ)) ≤ Yk hU z tt k ω := by
      rw [hY]; exact Real.exp_le_exp.2 (by linarith)
    change 1 ≤ f ω
    simp only [hf]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (1 : ℝ) = Real.exp tt * Real.exp (-(tt : ℝ)) := by rw [← Real.exp_add]; simp
      _ ≤ Real.exp tt * Yk hU z tt k ω := mul_le_mul_of_nonneg_left hYge (Real.exp_pos _).le
  calc _ ≤ P {ω | 1 ≤ f ω} := measure_mono_ae hsub
    _ ≤ ∫⁻ ω, f ω ∂P := by
      have := mul_meas_ge_le_lintegral₀ hfm.aemeasurable (μ := P) 1
      simpa using this
    _ = ENNReal.ofReal (Real.exp tt) * ∫⁻ ω, ENNReal.ofReal (Yk hU z tt k ω) ∂P :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by gcongr; exact hrate z tt hz k

end Rec

end ComplexSLE.Internal

end
