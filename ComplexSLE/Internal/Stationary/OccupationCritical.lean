/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.OccupationMeasure
public import ComplexSLE.Internal.Stationary.OccupationBump
public import ComplexSLE.Internal.Stationary.OccupationBound

/-!
# No time at the critical zero lattice (M10-R5a)

In the critical case `c² = ab`, `β² = 2D = R² sin²(· - x₀)` vanishes exactly on the lattice
`Z = x₀ + πℤ`, where the drift `µ(x₀) ≠ 0` (`CriticalCoefficients`). We show
`occupation X P T Z = 0`: `X` spends zero time on `Z`.

Dynkin's formula against the occupation measure `ρ` with `g = g_N`, `g_N' = ψ_N - mean ψ_N`
(`ψ_N = critBump`, `exists_periodic_contDiff_two_first_deriv`) gives
`|∫ ψ_N µ dρ| ≤ 4 M_N + (K_φ R² / N) T + (M_N/π) ‖µ‖ T`, `M_N = ∫₀^π ψ_N`. As `N → ∞`,
`M_N → 0` (dominated convergence) and `ψ_N µ → 1_Z µ = µ(x₀) 1_Z` boundedly, hence
`µ(x₀) ρ(Z) = 0`.
-/

public section

open scoped NNReal ENNReal Topology Real
open MeasureTheory ProbabilityTheory Filter Set Function

namespace ComplexSLE.Internal

/-! ### The zero lattice `{sin (x - x₀) = 0}` -/

section Lattice

variable {a b c : ℝ} (x₀ : ℝ)

theorem measurableSet_sin_sub_eq_zero : MeasurableSet {x : ℝ | Real.sin (x - x₀) = 0} :=
  (isClosed_eq (by fun_prop) continuous_const).measurableSet

theorem volume_sin_sub_eq_zero : volume {x : ℝ | Real.sin (x - x₀) = 0} = 0 := by
  refine Set.Countable.measure_zero ?_ _
  refine (Set.countable_range fun n : ℤ => x₀ + n * π).mono fun x hx => ?_
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 hx
  exact ⟨n, by simp only; linarith⟩

theorem mu_eq_of_sin_sub_eq_zero {x : ℝ} (hx : Real.sin (x - x₀) = 0) :
    mu a b c x = mu a b c x₀ := by
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 hx
  have : x = x₀ + n * π := by linarith
  rw [this]
  exact (mu_periodic a b c).int_mul n x₀

theorem tendsto_critBump_of_sin_ne_zero {x : ℝ} (hx : Real.sin (x - x₀) ≠ 0) :
    Tendsto (fun n : ℕ => critBump x₀ ((n : ℝ) + 1) x) atTop (𝓝 0) := by
  have hσ : 0 < Real.sin (x - x₀) ^ 2 := by positivity
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈(Real.sin (x - x₀) ^ 2)⁻¹⌉₊] with n hn
  refine (critBump_eq_zero_of_one_le ?_).symm
  have h1 : (Real.sin (x - x₀) ^ 2)⁻¹ ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have h2 : (1 : ℝ) ≤ n * Real.sin (x - x₀) ^ 2 := by
    calc (1 : ℝ) = (Real.sin (x - x₀) ^ 2)⁻¹ * Real.sin (x - x₀) ^ 2 :=
          (inv_mul_cancel₀ hσ.ne').symm
      _ ≤ n * Real.sin (x - x₀) ^ 2 := mul_le_mul_of_nonneg_right h1 hσ.le
  have h3 : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [n.cast_nonneg (α := ℝ)]
  nlinarith

theorem tendsto_integral_critBump :
    Tendsto (fun n : ℕ => ∫ s in (0 : ℝ)..π, critBump x₀ ((n : ℝ) + 1) s) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioc (0 : ℝ) π))
    (F := fun (n : ℕ) (s : ℝ) => critBump x₀ ((n : ℝ) + 1) s) (f := fun _ => (0 : ℝ))
    (fun _ => 1)
    (fun n => (((contDiff_critBump x₀ _).continuous).aestronglyMeasurable))
    (integrable_const 1)
    (fun n => Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (critBump_nonneg _ _ _)]
      exact critBump_le_one _ _ _)
    (by
      refine ae_restrict_of_ae ?_
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 (volume_sin_sub_eq_zero x₀)] with x hx
      exact tendsto_critBump_of_sin_ne_zero x₀ hx)
  simp only [integral_zero] at h
  refine h.congr fun n => ?_
  rw [intervalIntegral.integral_of_le Real.pi_pos.le]

end Lattice

/-! ### The Dynkin estimate for `ψ_N` -/

section Estimate

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ≥0 mΩ} {a b c : ℝ} {β : ℝ → ℝ} {X : ℝ≥0 → Ω → ℝ}

theorem abs_integral_critBump_mul_mu_le {R x₀ : ℝ} (hX : IsDiffusionSolution ℱ (mu a b c) β X P)
    (hXc : ∀ ω, Continuous fun t => X t ω) (hβc : Continuous β)
    (hβsq : ∀ v, β v ^ 2 = 2 * diffusionD a b c v)
    (hD : ∀ u, diffusionD a b c u = R ^ 2 / 2 * Real.sin (u - x₀) ^ 2) (T : ℝ≥0) {Kφ CM : ℝ}
    (hK0 : 0 ≤ Kφ) (hK : ∀ s, 0 ≤ s → |deriv bumpProfile s| ≤ Kφ)
    (hCM : ∀ x, |mu a b c x| ≤ CM) {N : ℝ} (hN : 0 < N) :
    |∫ x, critBump x₀ N x * mu a b c x ∂(occupation X P T)| ≤
      4 * (∫ s in (0 : ℝ)..π, critBump x₀ N s) + Kφ * R ^ 2 / N * T +
        (∫ s in (0 : ℝ)..π, critBump x₀ N s) / π * (CM * T) := by
  have hXm : ∀ t, Measurable (X t) := IsDiffusionSolution.measurable hX
  set ρ := occupation X P T with hρ
  have hρT : ρ.real univ = T := real_occupation_univ hXc hXm T
  have hCM0 : 0 ≤ CM := (abs_nonneg _).trans (hCM 0)
  set ψ := critBump x₀ N with hψ
  obtain ⟨g, hg, hgper, hg1, hg2, hg0⟩ := exists_periodic_contDiff_two_first_deriv
    (contDiff_critBump x₀ N) (periodic_critBump x₀ N) (critBump_nonneg x₀ N)
  set M := ∫ s in (0 : ℝ)..π, ψ s with hM
  have hM0 : 0 ≤ M :=
    intervalIntegral.integral_nonneg Real.pi_pos.le fun t _ => critBump_nonneg x₀ N t
  have hLc : Continuous (generator (mu a b c) β g) :=
    continuous_generator (continuous_mu a b c) hβc hg
  obtain ⟨CL, hCL⟩ := exists_abs_le_of_periodic hLc (periodic_generator_mu hβsq hgper)
  have hdyn := abs_integral_generator_occupation_le hX hXc (continuous_mu a b c) hβc hg hg0 hCL T
  have hβ2 : ∀ x, β x ^ 2 = R ^ 2 * Real.sin (x - x₀) ^ 2 := fun x => by
    rw [hβsq, hD]; ring
  have hid : ∀ x, ψ x * mu a b c x = generator (mu a b c) β g x -
      1 / 2 * deriv ψ x * (R ^ 2 * Real.sin (x - x₀) ^ 2) + (M / π) * mu a b c x := fun x => by
    unfold generator
    rw [hg1 x, hg2 x, hβ2 x]
    ring
  have hψ'c : Continuous (deriv ψ) := (contDiff_critBump x₀ N).continuous_deriv le_rfl
  have b2 : ∀ x, |1 / 2 * deriv ψ x * (R ^ 2 * Real.sin (x - x₀) ^ 2)| ≤ Kφ * R ^ 2 / N :=
    fun x => abs_half_deriv_critBump_mul_le hN hK0 hK x
  have i1 : Integrable (generator (mu a b c) β g) ρ := integrable_of_abs_le hLc hCL
  have i2 : Integrable (fun x => 1 / 2 * deriv ψ x * (R ^ 2 * Real.sin (x - x₀) ^ 2)) ρ :=
    integrable_of_abs_le (by fun_prop) b2
  have i3 : Integrable (mu a b c) ρ := integrable_of_abs_le (continuous_mu a b c) hCM
  have hsplit : ∫ x, (generator (mu a b c) β g x -
      1 / 2 * deriv ψ x * (R ^ 2 * Real.sin (x - x₀) ^ 2) + (M / π) * mu a b c x) ∂ρ =
      ∫ x, generator (mu a b c) β g x ∂ρ -
      ∫ x, 1 / 2 * deriv ψ x * (R ^ 2 * Real.sin (x - x₀) ^ 2) ∂ρ +
      (M / π) * ∫ x, mu a b c x ∂ρ := by
    have h12 : Integrable (fun x => generator (mu a b c) β g x -
        1 / 2 * deriv ψ x * (R ^ 2 * Real.sin (x - x₀) ^ 2)) ρ := i1.sub i2
    rw [integral_add h12 (i3.const_mul _), integral_sub i1 i2, integral_const_mul]
  have hint : ∫ x, ψ x * mu a b c x ∂ρ = ∫ x, generator (mu a b c) β g x ∂ρ -
      ∫ x, 1 / 2 * deriv ψ x * (R ^ 2 * Real.sin (x - x₀) ^ 2) ∂ρ +
      (M / π) * ∫ x, mu a b c x ∂ρ := by
    rw [← hsplit]
    exact integral_congr_ae (Eventually.of_forall hid)
  have e2 := abs_integral_le_mul_of_abs_le (ρ := ρ) b2
  have e3 := abs_integral_le_mul_of_abs_le (ρ := ρ) hCM
  rw [hρT] at e2 e3
  have hπ := Real.pi_pos
  rw [hint]
  have e4 : |M / π * ∫ x, mu a b c x ∂ρ| ≤ M / π * (CM * T) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left e3 (by positivity)
  calc |∫ x, generator (mu a b c) β g x ∂ρ -
        ∫ x, 1 / 2 * deriv ψ x * (R ^ 2 * Real.sin (x - x₀) ^ 2) ∂ρ +
        (M / π) * ∫ x, mu a b c x ∂ρ|
      ≤ |∫ x, generator (mu a b c) β g x ∂ρ -
        ∫ x, 1 / 2 * deriv ψ x * (R ^ 2 * Real.sin (x - x₀) ^ 2) ∂ρ| +
        |(M / π) * ∫ x, mu a b c x ∂ρ| := abs_add_le _ _
    _ ≤ (|∫ x, generator (mu a b c) β g x ∂ρ| +
        |∫ x, 1 / 2 * deriv ψ x * (R ^ 2 * Real.sin (x - x₀) ^ 2) ∂ρ|) +
        M / π * (CM * T) := add_le_add (abs_sub _ _) e4
    _ ≤ 4 * M + Kφ * R ^ 2 / N * T + M / π * (CM * T) := by
        have := hdyn
        linarith

end Estimate

/-! ### No time at the zero lattice -/

section Zero

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ≥0 mΩ} {a b c : ℝ} {β : ℝ → ℝ} {X : ℝ≥0 → Ω → ℝ}

/-- **No time at the critical zero lattice.** For `0 < a`, `0 < b`, `c² = ab`, an
everywhere-continuous solution `X` of the martingale problem for `(µ, β)` with `β² = 2D` has
`occupation X P T {β² = 0} = 0`: `E Leb{s ≤ T : β²(X_s) = 0} = 0`. -/
theorem occupation_zeroSet_eq_zero (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a * b)
    (hX : IsDiffusionSolution ℱ (mu a b c) β X P) (hXc : ∀ ω, Continuous fun t => X t ω)
    (hβc : Continuous β) (hβsq : ∀ v, β v ^ 2 = 2 * diffusionD a b c v) (T : ℝ≥0) :
    occupation X P T {x | β x ^ 2 = 0} = 0 := by
  obtain ⟨R, x₀, hR, hD, hμ⟩ := exists_diffusionD_eq_mul_sin_sq ha hb hc
  have hXm : ∀ t, Measurable (X t) := IsDiffusionSolution.measurable hX
  set ρ := occupation X P T with hρ
  have hβ2 : ∀ x, β x ^ 2 = R ^ 2 * Real.sin (x - x₀) ^ 2 := fun x => by
    rw [hβsq, hD]; ring
  have hZ : {x | β x ^ 2 = 0} = {x | Real.sin (x - x₀) = 0} := by
    ext x
    change β x ^ 2 = 0 ↔ Real.sin (x - x₀) = 0
    rw [hβ2 x]
    simp [hR.ne']
  rw [hZ]
  set Zs := {x : ℝ | Real.sin (x - x₀) = 0} with hZs
  have hZm : MeasurableSet Zs := measurableSet_sin_sub_eq_zero x₀
  obtain ⟨CM, hCM⟩ := exists_abs_le_of_periodic (continuous_mu a b c) (mu_periodic a b c)
  obtain ⟨Kφ, hK0, hK⟩ := exists_abs_deriv_bumpProfile_le
  have hCM0 : 0 ≤ CM := (abs_nonneg _).trans (hCM 0)
  set F : ℕ → ℝ := fun n => ∫ x, critBump x₀ ((n : ℝ) + 1) x * mu a b c x ∂ρ with hF
  set Mn : ℕ → ℝ := fun n => ∫ s in (0 : ℝ)..π, critBump x₀ ((n : ℝ) + 1) s with hMn
  have hMn0 : Tendsto Mn atTop (𝓝 0) := tendsto_integral_critBump x₀
  have hbound : ∀ n : ℕ, ‖F n‖ ≤ 4 * Mn n + Kφ * R ^ 2 * T * (1 / ((n : ℝ) + 1)) +
      Mn n / π * (CM * T) := fun n => by
    have := abs_integral_critBump_mul_mu_le hX hXc hβc hβsq hD T hK0 hK hCM
      (N := (n : ℝ) + 1) (by positivity)
    rw [Real.norm_eq_abs]
    refine this.trans (le_of_eq ?_)
    simp only [hMn]
    ring
  have hlim0 : Tendsto (fun n : ℕ => 4 * Mn n + Kφ * R ^ 2 * T * (1 / ((n : ℝ) + 1)) +
      Mn n / π * (CM * T)) atTop (𝓝 0) := by
    have h1 := (hMn0.const_mul 4).add
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Kφ * R ^ 2 * T))
    have h2 := h1.add ((hMn0.div_const π).mul_const (CM * T))
    simpa using h2
  have hF0 : Tendsto F atTop (𝓝 0) := squeeze_zero_norm hbound hlim0
  -- the limit of `F`
  have hFlim : Tendsto F atTop (𝓝 (∫ x, Zs.indicator (fun _ => mu a b c x₀) x ∂ρ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => CM)
      (fun n => ?_) (integrable_const CM) (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · exact (((contDiff_critBump x₀ _).continuous).mul (continuous_mu a b c)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (critBump_nonneg _ _ _)]
      calc critBump x₀ ((n : ℝ) + 1) x * |mu a b c x| ≤ 1 * CM :=
            mul_le_mul (critBump_le_one _ _ _) (hCM x) (abs_nonneg _) zero_le_one
        _ = CM := one_mul CM
    · by_cases hx : Real.sin (x - x₀) = 0
      · have hxZ : x ∈ Zs := hx
        simp only [indicator_of_mem hxZ, critBump_of_sin_eq_zero hx,
          mu_eq_of_sin_sub_eq_zero x₀ (a := a) (b := b) (c := c) hx, one_mul]
        exact tendsto_const_nhds
      · have hxZ : x ∉ Zs := hx
        simp only [indicator_of_notMem hxZ]
        simpa using (tendsto_critBump_of_sin_ne_zero x₀ hx).mul_const (mu a b c x)
  have hint : ∫ x, Zs.indicator (fun _ => mu a b c x₀) x ∂ρ = ρ.real Zs * mu a b c x₀ := by
    rw [integral_indicator_const _ hZm, smul_eq_mul]
  have := tendsto_nhds_unique hFlim hF0
  rw [hint] at this
  have hreal : ρ.real Zs = 0 := by
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hμ
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hreal

end Zero

end ComplexSLE.Internal

end
