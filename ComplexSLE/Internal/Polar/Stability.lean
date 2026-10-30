/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.Path
public import ComplexSLE.Infrastructure.ODE.GronwallBootstrap

/-!
# Stability of the Loewner solution under sup-norm perturbations of the driver

Fix a continuous driver `U₁`, a point `z` and a time `t` in the life set `[0, T_z(U₁))`. If a
second continuous driver `U₂` is uniformly `ε`-close to `U₁` on `[0, t]` with `ε` small enough
(depending only on `t` and on the minimal distance `η` of the solution `f(z)` from `0` on `[0, t]`),
then

* `t` lies in the life set of `U₂` (`T_z(U₂) > t`), and
* `‖f^{U₂}_s(z) - f^{U₁}_s(z)‖ ≤ e^{4t/η²} ε` for `s ∈ [0, t]`.

The proof compares the two solutions by Grönwall's inequality in a tube (the bootstrap form
`Infrastructure.norm_le_gronwallBound_of_forall_le`) and uses the persistence of existence
`lt_absorbingTime_of_norm_sub_ge`. Taking `ε = 0` gives *locality*: `1[t < T_z]` and `f_s(z)`,
`s ≤ t`, depend on `U` only through `U|[0, t]`.
-/

public section

open scoped NNReal ENNReal
open Set Real

namespace ComplexSLE.Internal.Polar

variable {U U₁ U₂ : ℝ≥0 → ℂ}

/-- The Loewner vector field `w ↦ 2 / w` is `4/η²`-Lipschitz between points at distance at least
`η/2` and `η` from the origin. -/
theorem norm_two_div_sub_two_div_le {a b : ℂ} {η : ℝ} (hη : 0 < η) (ha : η / 2 ≤ ‖a‖)
    (hb : η ≤ ‖b‖) : ‖2 / a - 2 / b‖ ≤ 4 / η ^ 2 * ‖a - b‖ := by
  have ha0 : 0 < ‖a‖ := lt_of_lt_of_le (by positivity) ha
  have hb0 : 0 < ‖b‖ := lt_of_lt_of_le hη hb
  have hane : a ≠ 0 := norm_pos_iff.1 ha0
  have hbne : b ≠ 0 := norm_pos_iff.1 hb0
  have key : 2 / a - 2 / b = 2 * (b - a) / (a * b) := by field_simp
  rw [key, norm_div, norm_mul, norm_mul, norm_sub_rev b a]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2, div_le_iff₀ (mul_pos ha0 hb0)]
  have hprod : η ^ 2 / 2 ≤ ‖a‖ * ‖b‖ := by
    have := mul_le_mul ha hb hη.le ha0.le
    nlinarith
  have hn := norm_nonneg (a - b)
  have : 4 / η ^ 2 * (η ^ 2 / 2) = 2 := by field_simp; norm_num
  calc 2 * ‖a - b‖ = 4 / η ^ 2 * (η ^ 2 / 2) * ‖a - b‖ := by rw [this]
    _ ≤ 4 / η ^ 2 * ‖a - b‖ * (‖a‖ * ‖b‖) := by
        have h4 : 0 ≤ 4 / η ^ 2 * ‖a - b‖ := by positivity
        calc 4 / η ^ 2 * (η ^ 2 / 2) * ‖a - b‖ = 4 / η ^ 2 * ‖a - b‖ * (η ^ 2 / 2) := by ring
          _ ≤ 4 / η ^ 2 * ‖a - b‖ * (‖a‖ * ‖b‖) := mul_le_mul_of_nonneg_left hprod h4

/-- The Grönwall bound `gronwallBound 0 K (K ε)` for positive `K` is `ε (e^{K x} - 1)`. -/
theorem gronwallBound_zero_mul {K ε x : ℝ} (hK : 0 < K) :
    gronwallBound 0 K (K * ε) x = ε * (Real.exp (K * x) - 1) := by
  rw [gronwallBound_of_K_ne_0 hK.ne']
  field_simp
  ring

/-- **Stability of the Loewner solution under sup-norm perturbation of the driver.**
If `t ∈ [0, T_z(U₁))`, there are `ρ > 0` and `C ≥ 0` such that every continuous driver `U₂` with
`‖U₁ - U₂‖ ≤ ε < ρ` on `[0, t]` has `t < T_z(U₂)` and `‖f^{U₂}_s(z) - f^{U₁}_s(z)‖ ≤ C ε` for
`s ∈ [0, t]`. -/
theorem exists_stability (hU₁ : Continuous U₁) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U₁ z) :
    ∃ ρ > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ (U₂ : ℝ≥0 → ℂ) (hU₂ : Continuous U₂) (ε : ℝ), ε < ρ →
      (∀ s ∈ Icc (0 : ℝ) t, ‖U₁ s.toNNReal - U₂ s.toNNReal‖ ≤ ε) →
      t ∈ lifeSet U₂ z ∧
        ∀ s ∈ Icc (0 : ℝ) t, ‖fPath U₂ hU₂ z s - fPath U₁ hU₁ z s‖ ≤ C * ε := by
  obtain ⟨η, hη, hηle⟩ := exists_pos_le_norm_fPath hU₁ ht
  set K : ℝ := 4 / η ^ 2 with hKdef
  have hK : 0 < K := by positivity
  refine ⟨η / 4 * Real.exp (-(K * t)), by positivity, Real.exp (K * t), (Real.exp_pos _).le, ?_⟩
  intro U₂ hU₂ ε hερ hdist
  have ht0 : 0 ≤ t := ht.1
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hdist 0 ⟨le_rfl, ht0⟩)
  -- `ε e^{K t} < η/4`
  have hεexp : ε * Real.exp (K * t) < η / 4 := by
    have := mul_lt_mul_of_pos_right hερ (Real.exp_pos (K * t))
    rwa [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at this
  have hε4 : ε ≤ η / 4 := by
    have h1 : 1 ≤ Real.exp (K * t) := Real.one_le_exp (by positivity)
    nlinarith
  -- the exponential bound is monotone
  have hexp_le : ∀ x, x ≤ t → ε * (Real.exp (K * x) - 1) ≤ ε * Real.exp (K * t) := by
    intro x hx
    have : Real.exp (K * x) ≤ Real.exp (K * t) := Real.exp_le_exp.2 (by nlinarith)
    nlinarith
  -- Step A: the bootstrap on `[0, m]`, `m ≤ t`, `m` in the life set of `U₂`
  have hA : ∀ m : ℝ, m ≤ t → m ∈ lifeSet U₂ z → ∀ x ∈ Icc (0 : ℝ) m,
      ‖solPath U₂ hU₂ z x - solPath U₁ hU₁ z x‖ ≤ ε * (Real.exp (K * x) - 1) := by
    intro m hmt hm2
    have hm1 : m ∈ lifeSet U₁ z := mem_lifeSet_of_le ht hm2.1 hmt
    have hsub1 : Icc 0 m ⊆ lifeSet U₁ z := Icc_subset_lifeSet hm1
    have hsub2 : Icc 0 m ⊆ lifeSet U₂ z := Icc_subset_lifeSet hm2
    have hcont : ContinuousOn (fun x => solPath U₂ hU₂ z x - solPath U₁ hU₁ z x) (Icc 0 m) :=
      ((continuousOn_solPath hU₂ z).mono hsub2).sub ((continuousOn_solPath hU₁ z).mono hsub1)
    have hderiv : ∀ x ∈ Ico (0 : ℝ) m, HasDerivWithinAt
        (fun x => solPath U₂ hU₂ z x - solPath U₁ hU₁ z x)
        (2 / fPath U₂ hU₂ z x - 2 / fPath U₁ hU₁ z x) (Ici x) x := by
      intro x hx
      have h1 := (hasDerivWithinAt_solPath hU₂ (hsub2 (Ico_subset_Icc_self hx))).mono
        (Ici_subset_Ici.2 hx.1)
      have h2 := (hasDerivWithinAt_solPath hU₁ (hsub1 (Ico_subset_Icc_self hx))).mono
        (Ici_subset_Ici.2 hx.1)
      exact h1.sub h2
    have h0 : ‖solPath U₂ hU₂ z 0 - solPath U₁ hU₁ z 0‖ ≤ 0 := by
      simp [solPath_zero]
    have hbound : ∀ x ∈ Ico (0 : ℝ) m,
        ‖solPath U₂ hU₂ z x - solPath U₁ hU₁ z x‖ ≤ η / 4 →
        ‖2 / fPath U₂ hU₂ z x - 2 / fPath U₁ hU₁ z x‖ ≤
          K * ‖solPath U₂ hU₂ z x - solPath U₁ hU₁ z x‖ + K * ε := by
      intro x hx hxr
      have hxt : x ∈ Icc (0 : ℝ) t := ⟨hx.1, hx.2.le.trans hmt⟩
      have hb : η ≤ ‖fPath U₁ hU₁ z x‖ := hηle x hxt
      have hdiff : ‖fPath U₂ hU₂ z x - fPath U₁ hU₁ z x‖ ≤
          ‖solPath U₂ hU₂ z x - solPath U₁ hU₁ z x‖ + ε := by
        have : fPath U₂ hU₂ z x - fPath U₁ hU₁ z x =
            (solPath U₂ hU₂ z x - solPath U₁ hU₁ z x) - (U₂ x.toNNReal - U₁ x.toNNReal) := by
          simp only [fPath]; ring
        rw [this]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_sub_rev (U₂ x.toNNReal)]
        exact add_le_add le_rfl (hdist x hxt)
      have ha : η / 2 ≤ ‖fPath U₂ hU₂ z x‖ := by
        have := norm_sub_norm_le (fPath U₁ hU₁ z x) (fPath U₂ hU₂ z x)
        rw [norm_sub_rev] at this
        linarith
      have := norm_two_div_sub_two_div_le hη ha hb
      calc ‖2 / fPath U₂ hU₂ z x - 2 / fPath U₁ hU₁ z x‖
          ≤ 4 / η ^ 2 * ‖fPath U₂ hU₂ z x - fPath U₁ hU₁ z x‖ := this
        _ ≤ K * (‖solPath U₂ hU₂ z x - solPath U₁ hU₁ z x‖ + ε) := by
            rw [hKdef]; exact mul_le_mul_of_nonneg_left hdiff (by positivity)
        _ = _ := by ring
    have hr : gronwallBound 0 K (K * ε) (m - 0) < η / 4 := by
      rw [gronwallBound_zero_mul hK, sub_zero]
      exact lt_of_le_of_lt (hexp_le m hmt) hεexp
    intro x hx
    have := Infrastructure.norm_le_gronwallBound_of_forall_le le_rfl hK.le (by positivity)
      hcont hderiv h0 hr hbound x hx
    rwa [sub_zero, gronwallBound_zero_mul hK] at this
  -- Step B: `t` lies in the life set of `U₂`
  have hz2 : z ≠ U₂ 0 := by
    intro hz
    have h1 := hηle 0 ⟨le_rfl, ht0⟩
    have h2 := hdist 0 ⟨le_rfl, ht0⟩
    rw [fPath_zero] at h1
    rw [Real.toNNReal_zero] at h2
    rw [← hz] at h2
    have : ‖z - U₁ 0‖ ≤ ε := by rw [norm_sub_rev]; exact h2
    linarith
  have hT2 : 0 < absorbingTime U₂ z := absorbingTime_pos_of_ne hU₂ hz2
  have hB : t ∈ lifeSet U₂ z := by
    by_contra hnt
    have hle : absorbingTime U₂ z ≤ ENNReal.ofReal t := by
      by_contra h
      exact hnt ⟨ht0, not_le.1 h⟩
    have hTne : absorbingTime U₂ z ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
    set τ := (absorbingTime U₂ z).toReal with hτ
    have hτpos : 0 < τ := ENNReal.toReal_pos hT2.ne' hTne
    have hτt : τ ≤ t := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      rwa [ENNReal.toReal_ofReal ht0] at this
    have hsol : IsLoewnerSolution U₂ z (ENNReal.ofReal τ) (solPath U₂ hU₂ z) := by
      rw [hτ, ENNReal.ofReal_toReal hTne]
      exact solPath_isLoewnerSolution hU₂ z
    have hτ' : ENNReal.ofReal τ < absorbingTime U₂ z := by
      refine lt_absorbingTime_of_norm_sub_ge hU₂ hτpos hsol hτpos (η := η / 2) (a := 0)
        (by positivity) ?_
      intro s hs
      have hsl : s ∈ lifeSet U₂ z := by
        rw [lifeSet_eq_Ico hTne]; exact hs
      have hst : s ≤ t := hs.2.le.trans hτt
      have hAs := hA s hst hsl s ⟨hs.1, le_rfl⟩
      have hst' : s ∈ Icc (0 : ℝ) t := ⟨hs.1, hst⟩
      have hb : η ≤ ‖fPath U₁ hU₁ z s‖ := hηle s hst'
      have hd := hdist s hst'
      have hnorm : ‖solPath U₂ hU₂ z s - solPath U₁ hU₁ z s‖ ≤ η / 4 :=
        hAs.trans ((hexp_le s hst).trans hεexp.le)
      have : fPath U₁ hU₁ z s = (solPath U₁ hU₁ z s - solPath U₂ hU₂ z s) +
          ((solPath U₂ hU₂ z s - U₂ s.toNNReal) + (U₂ s.toNNReal - U₁ s.toNNReal)) := by
        simp only [fPath]; ring
      have h3 : ‖fPath U₁ hU₁ z s‖ ≤ ‖solPath U₂ hU₂ z s - solPath U₁ hU₁ z s‖ +
          (‖solPath U₂ hU₂ z s - U₂ s.toNNReal‖ + ε) := by
        rw [this]
        refine (norm_add_le _ _).trans (add_le_add ?_ ((norm_add_le _ _).trans
          (add_le_add le_rfl ?_)))
        · rw [norm_sub_rev]
        · rw [norm_sub_rev]; exact hd
      linarith
    rw [hτ, ENNReal.ofReal_toReal hTne] at hτ'
    exact lt_irrefl _ hτ'
  refine ⟨hB, fun s hs => ?_⟩
  have hAs := hA t le_rfl hB s ⟨hs.1, hs.2⟩
  have : fPath U₂ hU₂ z s - fPath U₁ hU₁ z s =
      (solPath U₂ hU₂ z s - solPath U₁ hU₁ z s) - (U₂ s.toNNReal - U₁ s.toNNReal) := by
    simp only [fPath]; ring
  rw [this]
  refine (norm_sub_le _ _).trans ?_
  have hd := hdist s hs
  rw [norm_sub_rev] at hd
  have h1 : Real.exp (K * s) ≤ Real.exp (K * t) := Real.exp_le_exp.2 (by nlinarith [hs.2])
  calc ‖solPath U₂ hU₂ z s - solPath U₁ hU₁ z s‖ + ‖U₂ s.toNNReal - U₁ s.toNNReal‖
      ≤ ε * (Real.exp (K * s) - 1) + ε := add_le_add hAs hd
    _ = ε * Real.exp (K * s) := by ring
    _ ≤ Real.exp (K * t) * ε := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right h1 hε0

/-- **Locality, forward direction.** If two continuous drivers agree on `[0, t]` and `t` is in the
life set of the first, then `t` is in the life set of the second and `f_s(z)` agrees for
`s ∈ [0, t]`. -/
theorem lifeSet_and_fPath_congr (hU₁ : Continuous U₁) (hU₂ : Continuous U₂) {z : ℂ} {t : ℝ}
    (ht : t ∈ lifeSet U₁ z) (h : ∀ s ∈ Icc (0 : ℝ) t, U₁ s.toNNReal = U₂ s.toNNReal) :
    t ∈ lifeSet U₂ z ∧ ∀ s ∈ Icc (0 : ℝ) t, fPath U₁ hU₁ z s = fPath U₂ hU₂ z s := by
  obtain ⟨ρ, hρ, C, -, hC⟩ := exists_stability hU₁ ht
  obtain ⟨h2, hf⟩ := hC U₂ hU₂ 0 hρ (fun s hs => by simp [h s hs])
  refine ⟨h2, fun s hs => ?_⟩
  have := hf s hs
  rw [mul_zero, norm_le_zero_iff, sub_eq_zero] at this
  exact this.symm

/-- **Locality**: membership of `t` in the life set depends only on `U|[0, t]`. -/
theorem mem_lifeSet_congr (hU₁ : Continuous U₁) (hU₂ : Continuous U₂) {z : ℂ} {t : ℝ}
    (h : ∀ s ∈ Icc (0 : ℝ) t, U₁ s.toNNReal = U₂ s.toNNReal) :
    t ∈ lifeSet U₁ z ↔ t ∈ lifeSet U₂ z :=
  ⟨fun ht => (lifeSet_and_fPath_congr hU₁ hU₂ ht h).1,
    fun ht => (lifeSet_and_fPath_congr hU₂ hU₁ ht fun s hs => (h s hs).symm).1⟩

/-- **Locality**: `f_s(z)` for `s ∈ [0, t]`, `t` in the life set, depends only on `U|[0, t]`. -/
theorem fPath_congr (hU₁ : Continuous U₁) (hU₂ : Continuous U₂) {z : ℂ} {t : ℝ}
    (ht : t ∈ lifeSet U₁ z) (h : ∀ s ∈ Icc (0 : ℝ) t, U₁ s.toNNReal = U₂ s.toNNReal) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) t) : fPath U₁ hU₁ z s = fPath U₂ hU₂ z s :=
  (lifeSet_and_fPath_congr hU₁ hU₂ ht h).2 s hs

end ComplexSLE.Internal.Polar

end
