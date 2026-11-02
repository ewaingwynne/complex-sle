/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.PeriodicODE.DoubleZeroEnds
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The bounded solution on a period

On `(0, T)`, let `a` be continuous with `a ≥ c / x²` near `0` and `a ≥ c / (T - x)²` near `T`.
The primitive `A = ∫ a` tends to `-∞` at `0⁺` and to `+∞` at `T⁻`, and
`H = e^{-A} ∫₀^x e^{A} ρ` solves `H' = ρ - a H` on `(0, T)` with `H → 0` and `a H → 0` at both
ends (the latter by `DoubleZeroEnds`).
-/

public section

open Set Filter Topology MeasureTheory intervalIntegral Real

namespace ComplexSLE.Infrastructure

/-- `A' = a ≥ c / x²` near `0` forces `A → -∞` at `0⁺`. -/
theorem tendsto_atBot_of_deriv_ge {A a : ℝ → ℝ} {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (hA : ∀ x ∈ Ioo 0 δ, HasDerivAt A (a x) x) (ha : ∀ x ∈ Ioo 0 δ, c / x ^ 2 ≤ a x) :
    Tendsto A (𝓝[>] 0) atBot := by
  set x₁ : ℝ := δ / 2 with hx₁
  have hx₁I : x₁ ∈ Ioo 0 δ := ⟨by rw [hx₁]; linarith, by rw [hx₁]; linarith⟩
  have hB : ∀ x ∈ Ioo 0 δ, HasDerivAt (fun x => A x + c * x⁻¹) (a x + c * (-(x ^ 2)⁻¹)) x :=
    fun x hx => (hA x hx).add ((hasDerivAt_inv hx.1.ne').const_mul c)
  have hmono : MonotoneOn (fun x => A x + c * x⁻¹) (Ioc 0 x₁) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioc _ _) ?_ ?_ ?_
    · intro x hx
      exact (hB x ⟨hx.1, hx.2.trans_lt hx₁I.2⟩).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      exact (hB x ⟨hx.1, hx.2.trans hx₁I.2⟩).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      have hxI : x ∈ Ioo 0 δ := ⟨hx.1, hx.2.trans hx₁I.2⟩
      rw [(hB x hxI).deriv]
      have := ha x hxI
      rw [div_eq_mul_inv, ← inv_pow] at this
      rw [← inv_pow]
      nlinarith
  have hup : ∀ x ∈ Ioc 0 x₁, A x ≤ (A x₁ + c * x₁⁻¹) - c * x⁻¹ := fun x hx => by
    have := hmono hx ⟨hx₁I.1, le_rfl⟩ hx.2
    simp only at this
    linarith
  have hlim : Tendsto (fun x : ℝ => (A x₁ + c * x₁⁻¹) - c * x⁻¹) (𝓝[>] 0) atBot := by
    have h1 : Tendsto (fun x : ℝ => c * x⁻¹) (𝓝[>] 0) atTop :=
      tendsto_inv_nhdsGT_zero.const_mul_atTop hc
    exact tendsto_atBot_add_const_left _ _ (tendsto_neg_atTop_atBot.comp h1)
  refine tendsto_atBot_mono' _ ?_ hlim
  filter_upwards [Ioc_mem_nhdsGT hx₁I.1] with x hx using hup x hx

/-- `A' = a ≥ c / (T - x)²` near `T` forces `A → +∞` at `T⁻`. -/
theorem tendsto_atTop_of_deriv_ge {A a : ℝ → ℝ} {T δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (hA : ∀ x ∈ Ioo (T - δ) T, HasDerivAt A (a x) x)
    (ha : ∀ x ∈ Ioo (T - δ) T, c / (T - x) ^ 2 ≤ a x) :
    Tendsto A (𝓝[<] T) atTop := by
  set x₁ : ℝ := T - δ / 2 with hx₁
  have hx₁I : x₁ ∈ Ioo (T - δ) T := ⟨by rw [hx₁]; linarith, by rw [hx₁]; linarith⟩
  have hB : ∀ x ∈ Ioo (T - δ) T, HasDerivAt (fun x => A x - c * (T - x)⁻¹)
      (a x - c * (-(-1) / (T - x) ^ 2)) x := fun x hx => by
    have h1 : HasDerivAt (fun x => T - x) (-1) x := (hasDerivAt_id x).const_sub T
    exact (hA x hx).sub ((h1.inv (by linarith [hx.2])).const_mul c)
  have hmono : MonotoneOn (fun x => A x - c * (T - x)⁻¹) (Ico x₁ T) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico _ _) ?_ ?_ ?_
    · intro x hx
      exact (hB x ⟨by linarith [hx.1, hx₁I.1], hx.2⟩).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      exact (hB x ⟨by linarith [hx.1, hx₁I.1], hx.2⟩).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      have hxI : x ∈ Ioo (T - δ) T := ⟨by linarith [hx.1, hx₁I.1], hx.2⟩
      rw [(hB x hxI).deriv]
      have h2 : c * (-(-1) / (T - x) ^ 2) = c / (T - x) ^ 2 := by ring
      rw [h2]
      linarith [ha x hxI]
  have hlow : ∀ x ∈ Ico x₁ T, (A x₁ - c * (T - x₁)⁻¹) + c * (T - x)⁻¹ ≤ A x := fun x hx => by
    have := hmono (left_mem_Ico.2 hx₁I.2) hx hx.1
    simp only at this
    linarith
  have hlim : Tendsto (fun x : ℝ => (A x₁ - c * (T - x₁)⁻¹) + c * (T - x)⁻¹) (𝓝[<] T) atTop := by
    have h0 : Tendsto (fun x : ℝ => T - x) (𝓝[<] T) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun x : ℝ => T - x) (𝓝 T) (𝓝 (T - T)) :=
          (continuous_const.sub continuous_id).tendsto T
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        exact sub_pos.2 hx
    have h1 : Tendsto (fun x : ℝ => c * (T - x)⁻¹) (𝓝[<] T) atTop :=
      (tendsto_inv_nhdsGT_zero.comp h0).const_mul_atTop hc
    exact tendsto_atTop_add_const_left _ _ h1
  refine tendsto_atTop_mono' _ ?_ hlim
  filter_upwards [Ico_mem_nhdsLT hx₁I.2] with x hx using hlow x hx

/-- **The bounded solution on a period.** See the module docstring. -/
theorem exists_bounded_solution {a b b' ρ : ℝ → ℝ} {T δ c : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : δ ≤ T / 2) (hc : 0 < c) (ha : ContinuousOn a (Ioo 0 T)) (hρ : Continuous ρ)
    (hρ0 : ρ 0 = 0) (hρT : ρ T = 0)
    (hbL : ∀ x ∈ Ioo 0 δ, HasDerivAt b (b' x) x) (hb'L : ∀ x ∈ Ioo 0 δ, -(1 / 2) ≤ b' x)
    (habL : ∀ x ∈ Ioo 0 δ, a x * b x = 1) (haL : ∀ x ∈ Ioo 0 δ, c / x ^ 2 ≤ a x)
    (hb0 : Tendsto b (𝓝[>] 0) (𝓝 0))
    (hbR : ∀ x ∈ Ioo (T - δ) T, HasDerivAt b (b' x) x)
    (hb'R : ∀ x ∈ Ioo (T - δ) T, -(1 / 2) ≤ b' x)
    (habR : ∀ x ∈ Ioo (T - δ) T, a x * b x = 1)
    (haR : ∀ x ∈ Ioo (T - δ) T, c / (T - x) ^ 2 ≤ a x)
    (hbT : Tendsto b (𝓝[<] T) (𝓝 0)) :
    ∃ H : ℝ → ℝ, H 0 = 0 ∧ (∀ x ∈ Ioo 0 T, HasDerivAt H (ρ x - a x * H x) x) ∧
      Tendsto H (𝓝[>] 0) (𝓝 0) ∧ Tendsto (fun x => a x * H x) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto H (𝓝[<] T) (𝓝 0) ∧ Tendsto (fun x => a x * H x) (𝓝[<] T) (𝓝 0) := by
  have hδT' : δ < T := by linarith
  have hsubL : Ioo 0 δ ⊆ Ioo 0 T := Ioo_subset_Ioo_right hδT'.le
  have hsubR : Ioo (T - δ) T ⊆ Ioo 0 T := Ioo_subset_Ioo_left (by linarith)
  -- the primitive `A`
  set A : ℝ → ℝ := fun x => ∫ t in (T / 2)..x, a t with hAdef
  have hAd : ∀ x ∈ Ioo 0 T, HasDerivAt A (a x) x := by
    intro x hx
    have hint : IntervalIntegrable a volume (T / 2) x := by
      refine (ha.mono ?_).intervalIntegrable
      exact Set.ordConnected_Ioo.uIcc_subset ⟨by linarith, by linarith⟩ hx
    exact integral_hasDerivAt_right hint (ha.stronglyMeasurableAtFilter isOpen_Ioo x hx)
      (ha.continuousAt (Ioo_mem_nhds hx.1 hx.2))
  have hAcont : ContinuousOn A (Ioo 0 T) := fun t ht => (hAd t ht).continuousAt.continuousWithinAt
  have hA0 : Tendsto A (𝓝[>] 0) atBot :=
    tendsto_atBot_of_deriv_ge hδ hc (fun x hx => hAd x (hsubL hx)) haL
  have hAT : Tendsto A (𝓝[<] T) atTop :=
    tendsto_atTop_of_deriv_ge hδ hc (fun x hx => hAd x (hsubR hx)) haR
  -- the integrand `e^A ρ`, extended by `0` at `0`
  set f : ℝ → ℝ := fun t => if 0 < t then Real.exp (A t) * ρ t else 0 with hf
  have hfeq : ∀ t ∈ Ioo 0 T, f t = Real.exp (A t) * ρ t := fun t ht => by simp [hf, ht.1]
  have hfopen : ContinuousOn f (Ioo 0 T) :=
    ((Real.continuous_exp.comp_continuousOn hAcont).mul hρ.continuousOn).congr hfeq
  have hρL : Tendsto ρ (𝓝[>] 0) (𝓝 0) := by
    simpa [hρ0] using (hρ.tendsto 0).mono_left nhdsWithin_le_nhds
  have hρR : Tendsto ρ (𝓝[<] T) (𝓝 0) := by
    simpa [hρT] using (hρ.tendsto T).mono_left nhdsWithin_le_nhds
  have hf0 : ContinuousWithinAt f (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici]
    have h1 : Tendsto (fun t => Real.exp (A t) * ρ t) (𝓝[>] 0) (𝓝 0) := by
      simpa using (Real.tendsto_exp_atBot.comp hA0).mul hρL
    have hf00 : f 0 = 0 := by simp [hf]
    rw [ContinuousWithinAt, hf00]
    refine h1.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hT] with t ht using (hfeq t ht).symm
  have hfcont : ContinuousOn f (Ico 0 T) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0t | h0t
    · rw [← h0t]; exact hf0.mono Ico_subset_Ici_self
    · exact (hfopen.continuousAt (Ioo_mem_nhds h0t ht.2)).continuousWithinAt
  have hint : ∀ x ∈ Ico 0 T, IntervalIntegrable f volume 0 x := fun x hx => by
    refine (hfcont.mono ?_).intervalIntegrable
    rw [uIcc_of_le hx.1]
    exact fun t ht => ⟨ht.1, ht.2.trans_lt hx.2⟩
  set G : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, f t with hGdef
  have hGd : ∀ x ∈ Ioo 0 T, HasDerivAt G (Real.exp (A x) * ρ x) x := by
    intro x hx
    have := integral_hasDerivAt_right (hint x ⟨hx.1.le, hx.2⟩)
      (hfopen.stronglyMeasurableAtFilter isOpen_Ioo x hx)
      (hfopen.continuousAt (Ioo_mem_nhds hx.1 hx.2))
    rwa [hfeq x hx] at this
  have hG00 : G 0 = 0 := by simp [hGdef]
  have hG0 : Tendsto G (𝓝[>] 0) (𝓝 0) := by
    have hcont : ContinuousOn G (uIcc 0 δ) :=
      intervalIntegral.continuousOn_primitive_interval' (hint δ ⟨hδ.le, hδT'⟩)
        (by simp [hδ.le])
    have := (hcont 0 (by simp [hδ.le])).tendsto
    rw [hG00] at this
    refine this.mono_left ?_
    rw [← nhdsWithin_Ioo_eq_nhdsGT hδ]
    exact nhdsWithin_mono _ (by rw [uIcc_of_le hδ.le]; exact Ioo_subset_Icc_self)
  -- the solution
  have hGdL := fun x (hx : x ∈ Ioo 0 δ) => hGd x (hsubL hx)
  have hGdR := fun x (hx : x ∈ Ioo (T - δ) T) => hGd x (hsubR hx)
  have hapos : ∀ x ∈ Ioo (T - δ) T, 0 < a x := fun x hx =>
    lt_of_lt_of_le (div_pos hc (pow_pos (by linarith [hx.2]) 2)) (haR x hx)
  obtain ⟨hL1, hL2⟩ := tendsto_left_end hδ (fun x hx => hAd x (hsubL hx)) hGdL hbL hb'L habL hA0
    hG0 hb0 hρL
  obtain ⟨hR1, hR2⟩ := tendsto_right_end hδ (fun x hx => hAd x (hsubR hx)) hGdR hbR hb'R habR hapos
    hAT hbT hρR
  refine ⟨fun x => Real.exp (-A x) * G x, by simp [hG00], fun x hx => ?_, hL1, hL2, hR1, hR2⟩
  have h1 := ((hAd x hx).neg.exp).mul (hGd x hx)
  convert h1 using 1
  have : Real.exp (-A x) * Real.exp (A x) = 1 := by rw [← Real.exp_add]; simp
  linear_combination (-(ρ x)) * this

end ComplexSLE.Infrastructure

end
