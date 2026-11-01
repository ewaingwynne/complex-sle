/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Stochastic.SupportChain
public import ComplexSLE.Infrastructure.Stochastic.SupportInterpolation

/-!
# Support theorem for a measurable planar Gaussian process

Source-independent probability. For a process `U` with measurable coordinates, a.s. continuous
paths, `U 0 = 0` a.s., restarted paths independent of the past and Gaussian increments
`N (0, (t - s) S)` (`MeasurableDriver S U P`, `S` positive semidefinite), and a continuous path `φ`
with `φ 0 = 0` taking values in the range of `S`, the process stays within `δ` of `φ` on `[0, T]`
with positive probability (`support_of_measurableDriver`).

Route (no Cameron–Martin). Stop `φ` at `T + 1` and take its piecewise linear interpolation on a fine
grid of mesh `h = 1 / (M K)`; the drift per step is at most `δ / (8 K) = L h` with `L` independent
of `K`. In the scale `√h` the one-step event ("the increment is `√h`-close to `w - θ x`", the push
towards the target) has Gaussian probability at least `q₀`, uniformly in `h` and in the offset `x`
(`exists_complexGaussian_ball_lower_bound`), while the oscillation event has probability at most
`q₀ / 2` for `h` small (`exists_small_oscSet`). The chain of `n` steps then has probability at least
`(q₀ / 2) ^ n > 0` (`ChainParam.chain_bound`), and on the good event, paths are within `δ`
(`ChainParam.good_close`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ComplexSLE.Infrastructure.Support

open ComplexSLE.Infrastructure.SupportGaussian

/-- Uniform continuity of the stopped path: an integer `M ≥ 1` with oscillation at most `δ'` over
intervals of length `1 / M`. -/
theorem exists_modulus {φ : ℝ≥0 → ℂ} (hφ : Continuous φ) (N : ℝ≥0) {δ' : ℝ} (hδ' : 0 < δ') :
    ∃ M : ℕ, 0 < M ∧ ∀ s s' : ℝ≥0, s ≤ s' + (M : ℝ≥0)⁻¹ → s' ≤ s + (M : ℝ≥0)⁻¹ →
      ‖φ (min s N) - φ (min s' N)‖ ≤ δ' := by
  have huc := (isCompact_Icc (a := (0 : ℝ≥0)) (b := N)).uniformContinuousOn_of_continuous
    hφ.continuousOn
  obtain ⟨η, hη, hηφ⟩ := Metric.uniformContinuousOn_iff.1 huc δ' hδ'
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt hη
  refine ⟨M + 1, by omega, fun s s' h1 h2 => ?_⟩
  have hd : dist (min s N) (min s' N) < η := by
    rw [NNReal.dist_eq]
    have h1' : (s : ℝ) ≤ s' + 1 / ((M : ℝ) + 1) := by
      have := (NNReal.coe_le_coe.2 h1); push_cast at this; simpa [one_div] using this
    have h2' : (s' : ℝ) ≤ s + 1 / ((M : ℝ) + 1) := by
      have := (NNReal.coe_le_coe.2 h2); push_cast at this; simpa [one_div] using this
    have h3 : |(min s N : ℝ) - min s' N| ≤ |(s : ℝ) - s'| := by
      push_cast
      simpa using abs_min_sub_min_le_max (s : ℝ) N s' N
    refine lt_of_le_of_lt h3 (lt_of_le_of_lt ?_ hM)
    rw [abs_le]; constructor <;> linarith
  have := hηφ _ ⟨zero_le, min_le_right _ _⟩ _ ⟨zero_le, min_le_right _ _⟩ hd
  rw [dist_eq_norm] at this
  exact this.le

/-- **Support theorem for a measurable planar Gaussian process.** -/
theorem support_of_measurableDriver {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {S : Matrix (Fin 2) (Fin 2) ℝ} (hS : S.PosSemidef)
    {U : ℝ≥0 → Ω → ℂ} (hU : MeasurableDriver S U P) {φ : ℝ≥0 → ℂ} (hφ : Continuous φ)
    (hφ0 : φ 0 = 0) (hφS : ∀ t, φ t ∈ covRange S) (T : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    0 < P {ω | ∀ t ≤ T, ‖U t ω - φ t‖ < δ} := by
  obtain ⟨q₀, hq₀pos, hq₀⟩ := exists_complexGaussian_ball_lower_bound hS
  have hγ : 0 < q₀ / 2 := ENNReal.half_pos hq₀pos.ne'
  obtain ⟨η, hη, hηosc⟩ := exists_small_oscSet hU.measurable hU.cont (T + 1)
    (r := δ / 4) (by positivity) hγ
  -- the stopped path and its modulus of continuity
  set φ' : ℝ≥0 → ℂ := fun t => φ (min t (T + 1)) with hφ'
  have hφ'c : Continuous φ' := hφ.comp (continuous_id.min continuous_const)
  obtain ⟨M, hM, hmod⟩ := exists_modulus hφ (T + 1) (δ' := δ / 8) (by positivity)
  have hφ'0 : φ' 0 = 0 := by simp [hφ', hφ0]
  have hφ'R : ∀ t, φ' t ∈ covRange S := fun t => hφS _
  set L : ℝ := δ / 8 * M with hL
  have hL0 : 0 ≤ L := by positivity
  -- the mesh
  set H : ℝ := min (min (η : ℝ) 1) (min (δ ^ 2 / 16) (1 / (L ^ 2 + 1))) with hH
  have hHpos : 0 < H := by
    have : (0 : ℝ) < η := by exact_mod_cast hη
    positivity
  obtain ⟨K₀, hK₀⟩ := exists_nat_gt (1 / ((M : ℝ) * H))
  set K := K₀ + 1 with hK
  have hKpos : 0 < K := by omega
  have hMK : (0 : ℝ) < (M : ℝ) * K := by positivity
  set hq : ℚ≥0 := (((M * K : ℕ) : ℚ≥0))⁻¹ with hhq
  have hh : 0 < hq := by
    rw [hhq]; exact inv_pos.2 (by exact_mod_cast Nat.mul_pos hM hKpos)
  set c : ChainParam := ⟨S, hq, δ, δ / 4, interpSeq φ' M K⟩ with hc
  have hmesh : (c.mesh : ℝ) = 1 / ((M : ℝ) * K) := by
    simp [ChainParam.mesh, hc, hhq]
  have hmeshH : (c.mesh : ℝ) ≤ H := by
    rw [hmesh, div_le_iff₀ hMK]
    have : 1 / ((M : ℝ) * H) < K := by
      have : (K₀ : ℝ) + 1 = K := by simp [hK]
      linarith
    rw [div_lt_iff₀ (by positivity)] at this
    nlinarith
  have hHη : H ≤ η := (min_le_left _ _).trans (min_le_left _ _)
  have hH1 : H ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hHδ : H ≤ δ ^ 2 / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hHL : H ≤ 1 / (L ^ 2 + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hmeshη : c.mesh ≤ η := by
    rw [← NNReal.coe_le_coe]; exact hmeshH.trans hHη
  have hmesh1 : c.mesh ≤ 1 := by
    rw [← NNReal.coe_le_coe]; exact (hmeshH.trans hH1)
  have hmeshpos : (0 : ℝ) < c.mesh := by rw [hmesh]; positivity
  have hsq : c.sq * c.sq = (c.mesh : ℝ) := Real.mul_self_sqrt hmeshpos.le
  have hsq0 : 0 < c.sq := Real.sqrt_pos.2 hmeshpos
  have hε : 0 < c.ε := hδ
  have hθ : c.θ ≤ 1 := by
    have h1 : c.sq ≤ δ / 4 := by
      have : c.sq ^ 2 ≤ (δ / 4) ^ 2 := by nlinarith
      exact le_of_sq_le_sq this (by positivity)
    unfold ChainParam.θ
    change 4 * c.sq / δ ≤ 1
    rw [div_le_one hδ]; linarith
  have hLsq : c.sq * L ≤ 1 := by
    by_contra hcon
    have hcon := not_le.1 hcon
    have h1 : (c.sq * L) ^ 2 = c.mesh * L ^ 2 := by rw [mul_pow, sq, hsq]
    have h2 : (c.mesh : ℝ) * L ^ 2 ≤ H * L ^ 2 := by gcongr
    have h3 : H * L ^ 2 ≤ 1 / (L ^ 2 + 1) * L ^ 2 := by gcongr
    have h4 : 1 / (L ^ 2 + 1) * L ^ 2 < 1 := by
      rw [one_div, inv_mul_lt_iff₀ (by positivity)]; linarith
    nlinarith
  have hψ0 : c.ψ 0 = 0 := interpSeq_zero φ' M K
  have hdriftR : ∀ j, c.drift j ∈ covRange c.S := fun j =>
    interpSeq_succ_sub_mem hφ'R M K j
  have hdriftL : ∀ j, ‖c.drift j‖ ≤ L * c.mesh := by
    intro j
    refine (norm_interpSeq_succ_sub_le (φ := φ') (M := M) (δ' := δ / 8) hmod K j).trans
      (le_of_eq ?_)
    rw [hmesh, hL]
    field_simp
  have hosc : P (oscSet U (T + 1) c.mesh c.r) ≤ q₀ / 2 := hηosc c.mesh hmeshη
  set n := ⌊T / c.mesh⌋₊ + 1 with hn
  have hmeshNN : (0 : ℝ≥0) < c.mesh := by exact_mod_cast hmeshpos
  have hTn : T < c.time n := by
    rw [ChainParam.time_eq, ← div_lt_iff₀ hmeshNN, hn]
    push_cast
    exact Nat.lt_floor_add_one _
  have htn : c.time n ≤ T + 1 := by
    rw [ChainParam.time_eq, hn]
    push_cast
    calc ((⌊T / c.mesh⌋₊ : ℝ≥0) + 1) * c.mesh = ⌊T / c.mesh⌋₊ * c.mesh + c.mesh := by ring
      _ ≤ T + 1 := by
        gcongr
        · have := Nat.floor_le (zero_le : 0 ≤ T / c.mesh)
          rwa [le_div_iff₀ hmeshNN] at this
  have hchain := c.chain_bound hU hS hh hq₀ hosc hLsq hε hθ hψ0 hdriftR hdriftL n htn
  have hmeshNN' : c.mesh = ((M : ℝ≥0) * K)⁻¹ := by
    simp [ChainParam.mesh, hc, hhq]
  have hsub : {ω | c.Good n (fun s => U s ω)} ⊆
      {ω | ∀ t ≤ T, ‖U t ω - φ t‖ < δ} ∪ {ω | ¬ Continuous fun t => U t ω} := by
    intro ω hω
    by_cases hcont : Continuous fun t => U t ω
    · left
      have hb : ∀ j < n, ∀ t, c.time j ≤ t → t ≤ c.time (j + 1) → ‖c.ψ j - φ t‖ ≤ δ / 4 := by
        intro j hj t ht1 ht2
        have ht3 : t ≤ T + 1 := ht2.trans ((c.time_mono (Nat.succ_le_of_lt hj)).trans htn)
        have hφt : φ' t = φ t := by simp [hφ', min_eq_left ht3]
        have h1 : (j : ℝ≥0) / ((M : ℝ≥0) * K) ≤ t := by
          rw [ChainParam.time_eq, hmeshNN', ← div_eq_mul_inv] at ht1; exact ht1
        have h2 : t ≤ ((j : ℝ≥0) + 1) / ((M : ℝ≥0) * K) := by
          rw [ChainParam.time_eq, hmeshNN', ← div_eq_mul_inv] at ht2; push_cast at ht2; exact ht2
        have := norm_interpSeq_sub_le φ' hφ'0 hM hKpos (δ' := δ / 8) hmod j t h1 h2
        rw [hφt] at this
        change ‖interpSeq φ' M K j - φ t‖ ≤ δ / 4
        linarith
      intro t ht
      have := c.good_close hε hθ hψ0 hdriftR hh hω hcont hTn hb t ht
      change ‖U t ω - φ t‖ < δ
      have e : c.ε / 4 + c.r + δ / 4 = 3 * δ / 4 := by
        change δ / 4 + δ / 4 + δ / 4 = 3 * δ / 4
        ring
      linarith
    · right; exact hcont
  have hnull : P {ω | ¬ Continuous fun t => U t ω} = 0 := ae_iff.1 hU.cont
  have hle : (q₀ / 2) ^ n ≤ P {ω | ∀ t ≤ T, ‖U t ω - φ t‖ < δ} := by
    calc (q₀ / 2) ^ n ≤ P {ω | c.Good n (fun s => U s ω)} := hchain
      _ ≤ P ({ω | ∀ t ≤ T, ‖U t ω - φ t‖ < δ} ∪ {ω | ¬ Continuous fun t => U t ω}) :=
          measure_mono hsub
      _ ≤ P {ω | ∀ t ≤ T, ‖U t ω - φ t‖ < δ} + P {ω | ¬ Continuous fun t => U t ω} :=
          measure_union_le _ _
      _ = _ := by rw [hnull, add_zero]
  exact lt_of_lt_of_le (ENNReal.pow_pos hγ n) hle

end ComplexSLE.Infrastructure.Support

end
