/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.LHopitalAtTop
public import ComplexSLE.Infrastructure.Primitive
public import ComplexSLE.Infrastructure.PeriodicGlue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The singular first-order equation `-μp + (Dp)' = 1` on a period

Abstract core of Case 2 of Lemma 2.13 (paper.tex:L1082-1105). Given `T`-periodic smooth
coefficients `μ, D` with `D > 0` on `(x, x+T)`, `D(x) = D'(x) = 0`, `μ(x) < 0`, and the
quadratic blow-up `μ/D ≤ -κ/(u-x)²` near `x` (resp. `-κ/(x+T-u)²` near `x+T`), the function
`p(u) = (∫ₓᵘ e^{-Ψ}) / (D(u) e^{-Ψ(u)})`, `Ψ(u) = ∫_{x+T/2}^u μ/D`, is positive and smooth on
`(x, x+T)`, solves `-μp + (Dp)' = 1` there and tends to `-1/μ(x)` at both ends (L'Hôpital,
(2.32)–(2.33)). Its `T`-periodic continuous extension is `C²` off `x + Tℤ` and `Dp` is `C¹`
on `ℝ` with `(Dp)' = 1 + μp` everywhere.
-/

public section

open Set Filter Topology MeasureTheory intervalIntegral Function Real
open scoped ContDiff

namespace ComplexSLE.Internal

/-- Hypotheses of the singular construction. -/
structure SingularData (μ D : ℝ → ℝ) (x T : ℝ) : Prop where
  T_pos : 0 < T
  D_smooth : ContDiff ℝ ∞ D
  μ_smooth : ContDiff ℝ ∞ μ
  D_per : Periodic D T
  μ_per : Periodic μ T
  D_pos : ∀ u ∈ Ioo x (x + T), 0 < D u
  D_x : D x = 0
  D'_x : deriv D x = 0
  μ_x : μ x < 0
  bound : ∃ κ > 0, ∃ δ > 0, (∀ u ∈ Ioo x (x + δ), μ u / D u ≤ -κ / (u - x) ^ 2) ∧
    ∀ u ∈ Ioo (x + T - δ) (x + T), μ u / D u ≤ -κ / (x + T - u) ^ 2
  D_low : ∃ κ₂ > 0, ∃ δ > 0, ∀ u ∈ Ioo (x + T - δ) (x + T), κ₂ * (x + T - u) ^ 2 ≤ D u

/-! ### Auxiliary limits and monotonicity lemmas -/

theorem tendsto_sub_const_nhdsGT (x : ℝ) : Tendsto (fun u => u - x) (𝓝[>] x) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun u hu => ?_⟩
  · have h1 : Tendsto (fun u => u - x) (𝓝 x) (𝓝 (x - x)) := (continuous_sub_right x).tendsto x
    rw [sub_self] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  · exact sub_pos.2 hu

theorem tendsto_const_sub_nhdsLT (y : ℝ) : Tendsto (fun u => y - u) (𝓝[<] y) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun u hu => ?_⟩
  · have h1 : Tendsto (fun u => y - u) (𝓝 y) (𝓝 (y - y)) := (continuous_sub_left y).tendsto y
    rw [sub_self] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  · exact sub_pos.2 hu

theorem tendsto_add_const_nhdsLT (x T : ℝ) :
    Tendsto (fun u => u + T) (𝓝[<] x) (𝓝[<] (x + T)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun u hu => ?_⟩
  · exact ((continuous_id.add continuous_const : Continuous fun u : ℝ => u + T).tendsto x).mono_left
      nhdsWithin_le_nhds
  · exact show u + T < x + T by linarith [show u < x from hu]

theorem antitoneOn_Ioc_of_hasDerivAt {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ u ∈ Ioc a b, HasDerivAt f (f' u) u) (hf' : ∀ u ∈ Ioo a b, f' u ≤ 0) :
    AntitoneOn f (Ioc a b) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioc a b) (HasDerivAt.continuousOn hf)
    (fun u hu => (hf u (interior_subset hu)).differentiableAt.differentiableWithinAt)
    fun u hu => ?_
  rw [interior_Ioc] at hu
  rw [(hf u (Ioo_subset_Ioc_self hu)).deriv]
  exact hf' u hu

theorem antitoneOn_Ico_of_hasDerivAt {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ u ∈ Ico a b, HasDerivAt f (f' u) u) (hf' : ∀ u ∈ Ioo a b, f' u ≤ 0) :
    AntitoneOn f (Ico a b) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ico a b) (HasDerivAt.continuousOn hf)
    (fun u hu => (hf u (interior_subset hu)).differentiableAt.differentiableWithinAt)
    fun u hu => ?_
  rw [interior_Ico] at hu
  rw [(hf u (Ioo_subset_Ico_self hu)).deriv]
  exact hf' u hu

/-! ### The construction -/

namespace SingularData

variable {μ D : ℝ → ℝ} {x T : ℝ}

/-- The singular construction: a `T`-periodic, continuous, non-negative `p`, positive and
`C²` on `(x, x+T)`, with `(Dp)' = 1 + μ p` everywhere on `ℝ`. -/
theorem exists_solution (h : SingularData μ D x T) :
    ∃ p : ℝ → ℝ, Continuous p ∧ (∀ u, 0 ≤ p u) ∧ Periodic p T ∧
      (∀ u ∈ Ioo x (x + T), 0 < p u) ∧
      ContDiffOn ℝ 2 p {u | ∀ n : ℤ, u ≠ x + n * T} ∧
      ∀ u, HasDerivAt (fun v => D v * p v) (1 + μ u * p u) u := by
  obtain ⟨hT, hD, hμ, hDper, hμper, hDpos, hDx, hD'x, hμx, ⟨κ, hκ, δ₁, hδ₁, hb1, hb2⟩,
    ⟨κ₂, hκ₂, δ₂, hδ₂, hlow⟩⟩ := h
  set y : ℝ := x + T with hy
  have hxy : x < y := by rw [hy]; linarith
  set m : ℝ := x + T / 2 with hm
  have hm_mem : m ∈ Ioo x y := ⟨by rw [hm]; linarith, by rw [hm, hy]; linarith⟩
  have hDne : ∀ u ∈ Ioo x y, D u ≠ 0 := fun u hu => (hDpos u hu).ne'
  have hDcont : Continuous D := hD.continuous
  have hμcont : Continuous μ := hμ.continuous
  have hD' : ∀ u, HasDerivAt D (deriv D u) u := fun u =>
    (hD.differentiable (by simp) u).hasDerivAt
  have hD'cont : Continuous (deriv D) := hD.continuous_deriv (by simp)
  -- periodicity of `deriv D`
  have hD'per : deriv D y = deriv D x := by
    have h1 : HasDerivAt (fun u => D (u - T)) (deriv D x) y := by
      have h0 : HasDerivAt D (deriv D x) (y - T) := by
        rw [show y - T = x by rw [hy]; ring]; exact hD' x
      exact h0.comp_sub_const y T
    have h2 : (fun u => D (u - T)) = D := funext fun u => hDper.sub_eq u
    rw [h2] at h1
    exact h1.deriv
  have hμy : μ y = μ x := hμper x
  -- `g₀ = μ / D`
  set g₀ : ℝ → ℝ := fun u => μ u / D u with hg₀
  have hg₀cont : ContinuousOn g₀ (Ioo x y) :=
    hμcont.continuousOn.div hDcont.continuousOn hDne
  have hg₀smooth : ContDiffOn ℝ ∞ g₀ (Ioo x y) :=
    hμ.contDiffOn.div hD.contDiffOn hDne
  -- `Ψ = ∫ₘᵘ g₀`
  set Ψ : ℝ → ℝ := fun u => ∫ s in m..u, g₀ s with hΨ
  have hsub : ∀ u ∈ Ioo x y, uIcc m u ⊆ Ioo x y := by
    intro u hu
    rcases le_total m u with hmu | hmu
    · rw [uIcc_of_le hmu]; exact Icc_subset_Ioo hm_mem.1 hu.2
    · rw [uIcc_of_ge hmu]; exact Icc_subset_Ioo hu.1 hm_mem.2
  have hΨ_deriv : ∀ u ∈ Ioo x y, HasDerivAt Ψ (g₀ u) u := fun u hu =>
    Infrastructure.hasDerivAt_integral_right_of_continuousOn isOpen_Ioo hg₀cont hu
      (hg₀cont.mono (hsub u hu)).intervalIntegrable
  have hΨ_smooth : ContDiffOn ℝ ∞ Ψ (Ioo x y) :=
    Infrastructure.contDiffOn_infty_of_hasDerivAt isOpen_Ioo hΨ_deriv hg₀smooth
  -- the lower bound `Ψ u ≥ κ/(u-x) + C₁` near `x`
  set δ : ℝ := min (min δ₁ δ₂) (T / 2) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]; exact lt_min (lt_min hδ₁ hδ₂) (by linarith)
  have hδ_le₁ : δ ≤ δ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hδ_le₂ : δ ≤ δ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hδ_le : δ ≤ T / 2 := min_le_right _ _
  have hIoo_x : Ioo x (x + δ) ⊆ Ioo x y := Ioo_subset_Ioo le_rfl (by rw [hy]; linarith)
  have hIoo_y : Ioo (y - δ) y ⊆ Ioo x y := Ioo_subset_Ioo (by rw [hy]; linarith) le_rfl
  obtain ⟨C₁, hC₁⟩ : ∃ C₁, ∀ u ∈ Ioo x (x + δ), κ / (u - x) + C₁ ≤ Ψ u := by
    have hanti : AntitoneOn (fun u => Ψ u - κ / (u - x)) (Ioc x (x + δ)) := by
      refine antitoneOn_Ioc_of_hasDerivAt (f' := fun u => g₀ u + κ / (u - x) ^ 2) ?_ ?_
      · intro u hu
        have hu' : u ∈ Ioo x y := ⟨hu.1, by linarith [hu.2, hδ_le, hy]⟩
        have hux : u - x ≠ 0 := sub_ne_zero.2 hu.1.ne'
        have h1 : HasDerivAt (fun u => κ / (u - x)) (-κ / (u - x) ^ 2) u := by
          have := ((hasDerivAt_id u).sub_const x).inv hux
          simpa [div_eq_mul_inv] using this.const_mul κ
        convert (hΨ_deriv u hu').sub h1 using 1
        ring
      · intro u hu
        have := hb1 u ⟨hu.1, by linarith [hu.2, hδ_le₁]⟩
        rw [neg_div] at this
        simp only [hg₀] at this ⊢
        linarith
    refine ⟨Ψ (x + δ) - κ / (x + δ - x), fun u hu => ?_⟩
    have := hanti (Ioo_subset_Ioc_self hu) ⟨by linarith [hδpos], le_rfl⟩ hu.2.le
    simp only at this
    linarith
  -- the upper bound `Ψ u ≤ C₂ - κ/(y-u)` near `y`
  obtain ⟨C₂, hC₂⟩ : ∃ C₂, ∀ u ∈ Ioo (y - δ) y, Ψ u ≤ C₂ - κ / (y - u) := by
    have hanti : AntitoneOn (fun u => Ψ u + κ / (y - u)) (Ico (y - δ) y) := by
      refine antitoneOn_Ico_of_hasDerivAt (f' := fun u => g₀ u + κ / (y - u) ^ 2) ?_ ?_
      · intro u hu
        have hu' : u ∈ Ioo x y := ⟨by linarith [hu.1, hδ_le, hy], hu.2⟩
        have huy : y - u ≠ 0 := sub_ne_zero.2 hu.2.ne'
        have h1 : HasDerivAt (fun u => κ / (y - u)) (κ / (y - u) ^ 2) u := by
          have := ((hasDerivAt_id' u).const_sub y).inv huy
          have h2 := this.const_mul κ
          convert h2 using 1
          · funext v; simp [div_eq_mul_inv]
          · ring
        exact (hΨ_deriv u hu').add h1
      · intro u hu
        have := hb2 u ⟨by linarith [hu.1, hδ_le₂], hu.2⟩
        rw [neg_div] at this
        simp only [hg₀] at this ⊢
        linarith
    refine ⟨Ψ (y - δ) + κ / (y - (y - δ)), fun u hu => ?_⟩
    have := hanti ⟨le_rfl, by linarith [hδpos]⟩ (Ioo_subset_Ico_self hu) hu.1.le
    simp only at this
    linarith
  -- limits of `exp (-Ψ)`
  have hκ_inv_x : Tendsto (fun u => κ / (u - x)) (𝓝[>] x) atTop := by
    have := (tendsto_inv_nhdsGT_zero.comp (tendsto_sub_const_nhdsGT x)).const_mul_atTop hκ
    exact this.congr fun u => by simp [div_eq_mul_inv]
  have hκ_inv_y : Tendsto (fun u => κ / (y - u)) (𝓝[<] y) atTop := by
    have := (tendsto_inv_nhdsGT_zero.comp (tendsto_const_sub_nhdsLT y)).const_mul_atTop hκ
    exact this.congr fun u => by simp [div_eq_mul_inv]
  have hexp_x : Tendsto (fun u => exp (-Ψ u)) (𝓝[>] x) (𝓝 0) := by
    apply tendsto_exp_atBot.comp
    have h1 : Tendsto (fun u => -(κ / (u - x)) + -C₁) (𝓝[>] x) atBot :=
      tendsto_atBot_add_const_right _ _ (tendsto_neg_atTop_atBot.comp hκ_inv_x)
    refine tendsto_atBot_mono' _ ?_ h1
    filter_upwards [Ioo_mem_nhdsGT (show x < x + δ by linarith)] with u hu
    linarith [hC₁ u hu]
  have hG_x : Tendsto (fun u => D u * exp (-Ψ u)) (𝓝[>] x) (𝓝 0) := by
    have := ((hDcont.tendsto x).mono_left nhdsWithin_le_nhds).mul hexp_x
    simpa using this
  have hG_y : Tendsto (fun u => D u * exp (-Ψ u)) (𝓝[<] y) atTop := by
    have h1 : Tendsto (fun u => κ₂ * κ ^ 2 * exp (-C₂) * (exp (κ / (y - u)) / (κ / (y - u)) ^ 2))
        (𝓝[<] y) atTop :=
      ((tendsto_exp_div_pow_atTop 2).comp hκ_inv_y).const_mul_atTop (by positivity)
    refine tendsto_atTop_mono' _ ?_ h1
    filter_upwards [Ioo_mem_nhdsLT (show y - δ < y by linarith)] with u hu
    have hu' : u ∈ Ioo x y := hIoo_y hu
    have huy : 0 < y - u := sub_pos.2 hu.2
    have hlow' : κ₂ * (y - u) ^ 2 ≤ D u := hlow u ⟨by linarith [hu.1, hδ_le₂], hu.2⟩
    have hexp' : exp (κ / (y - u) - C₂) ≤ exp (-Ψ u) := exp_le_exp.2 (by linarith [hC₂ u hu])
    calc κ₂ * κ ^ 2 * exp (-C₂) * (exp (κ / (y - u)) / (κ / (y - u)) ^ 2)
        = κ₂ * (y - u) ^ 2 * exp (κ / (y - u) - C₂) := by
          rw [exp_sub, exp_neg]; field_simp
      _ ≤ D u * exp (-Ψ u) := mul_le_mul hlow' hexp' (exp_pos _).le (hDpos u hu').le
  -- the integrand `E`, continuous on `[x, y)`
  set E : ℝ → ℝ := fun s => if s ∈ Ioo x y then exp (-Ψ s) else 0 with hE
  have hE_eq : ∀ s ∈ Ioo x y, E s = exp (-Ψ s) := fun s hs => ite_eq_left hs
  have hE_x : E x = 0 := ite_eq_right (fun h => lt_irrefl x h.1)
  have hE_eventually : ∀ s ∈ Ioo x y, E =ᶠ[𝓝 s] fun s => exp (-Ψ s) := fun s hs =>
    (isOpen_Ioo.eventually_mem hs).mono fun t ht => hE_eq t ht
  have hexpΨ_cont : ∀ s ∈ Ioo x y, ContinuousAt (fun s => exp (-Ψ s)) s := fun s hs =>
    Real.continuous_exp.continuousAt.comp ((hΨ_deriv s hs).continuousAt.neg)
  have hE_cont : ContinuousOn E (Ico x y) := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with rfl | hxs
    · apply (continuousWithinAt_Ioi_iff_Ici.1 _).mono Ico_subset_Ici_self
      rw [ContinuousWithinAt, hE_x]
      refine hexp_x.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hxy] with t ht
      exact (hE_eq t ht).symm
    · exact ((hexpΨ_cont s ⟨hxs, hs.2⟩).congr (hE_eventually s ⟨hxs, hs.2⟩).symm).continuousWithinAt
  have hE_int : ∀ u ∈ Ioo x y, IntervalIntegrable E volume x u := fun u hu =>
    (hE_cont.mono (by rw [uIcc_of_le hu.1.le]; exact Icc_subset_Ico_right hu.2)).intervalIntegrable
  -- `f = ∫ₓᵘ E`
  set f : ℝ → ℝ := fun u => ∫ s in x..u, E s with hf
  have hf_deriv : ∀ u ∈ Ioo x y, HasDerivAt f (E u) u := fun u hu =>
    Infrastructure.hasDerivAt_integral_right_of_continuousOn isOpen_Ioo
      (hE_cont.mono Ioo_subset_Ico_self) hu (hE_int u hu)
  have hf_pos : ∀ u ∈ Ioo x y, 0 < f u := fun u hu =>
    intervalIntegral_pos_of_pos_on (hE_int u hu)
      (fun s hs => by rw [hE_eq s ⟨hs.1, hs.2.trans hu.2⟩]; exact exp_pos _) hu.1
  have hf_x : Tendsto f (𝓝[>] x) (𝓝 0) := by
    have hc : ContinuousOn f (uIcc x m) :=
      continuousOn_primitive_interval' (hE_int m hm_mem) left_mem_uIcc
    have h1 : Tendsto f (𝓝[uIcc x m] x) (𝓝 (f x)) := hc.continuousWithinAt left_mem_uIcc
    have h2 : f x = 0 := integral_same
    rw [h2] at h1
    refine h1.mono_left (nhdsWithin_le_of_mem ?_)
    rw [uIcc_of_le hm_mem.1.le]
    exact mem_of_superset (Ioo_mem_nhdsGT hm_mem.1) Ioo_subset_Icc_self
  have hf_smooth : ContDiffOn ℝ ∞ f (Ioo x y) :=
    Infrastructure.contDiffOn_infty_of_hasDerivAt isOpen_Ioo hf_deriv
      ((hΨ_smooth.neg.exp).congr hE_eq)
  -- the denominator `G = D exp (-Ψ)`
  set G : ℝ → ℝ := fun u => D u * exp (-Ψ u) with hG
  have hG_pos : ∀ u ∈ Ioo x y, 0 < G u := fun u hu => mul_pos (hDpos u hu) (exp_pos _)
  have hG_deriv : ∀ u ∈ Ioo x y, HasDerivAt G ((deriv D u - μ u) * exp (-Ψ u)) u := by
    intro u hu
    have h1 := (hD' u).mul ((hΨ_deriv u hu).neg.exp)
    have hDu := hDne u hu
    convert h1 using 1
    simp only [hg₀, Pi.neg_apply]
    field_simp
    ring
  -- the solution on `(x, y)` and its limits
  set p₀ : ℝ → ℝ := fun u => f u / G u with hp₀
  have hp₀_pos : ∀ u ∈ Ioo x y, 0 < p₀ u := fun u hu => div_pos (hf_pos u hu) (hG_pos u hu)
  set L : ℝ := 1 / (deriv D x - μ x) with hL
  have hL_pos : 0 < L := by rw [hL, hD'x]; exact one_div_pos.2 (by linarith)
  have hne_x : ∀ᶠ u in 𝓝 x, deriv D u - μ u ≠ 0 :=
    (hD'cont.sub hμcont).continuousAt.eventually_ne
      (by simp only [Pi.sub_apply]; rw [hD'x]; linarith)
  have hne_y : ∀ᶠ u in 𝓝 y, deriv D u - μ u ≠ 0 :=
    (hD'cont.sub hμcont).continuousAt.eventually_ne
      (by simp only [Pi.sub_apply]; rw [hD'per, hD'x, hμy]; linarith)
  have hratio : ∀ u ∈ Ioo x y, E u / ((deriv D u - μ u) * exp (-Ψ u)) =
      1 / (deriv D u - μ u) := by
    intro u hu
    rw [hE_eq u hu]
    by_cases hz : deriv D u - μ u = 0
    · simp [hz]
    · field_simp
  have hdiv_x : Tendsto (fun u => E u / ((deriv D u - μ u) * exp (-Ψ u))) (𝓝[>] x) (𝓝 L) := by
    have h1 : Tendsto (fun u => 1 / (deriv D u - μ u)) (𝓝 x) (𝓝 L) := by
      rw [hL]
      exact (tendsto_const_nhds.div ((hD'cont.sub hμcont).tendsto x)
        (by rw [hD'x]; linarith))
    refine (h1.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hxy] with u hu
    exact (hratio u hu).symm
  have hdiv_y : Tendsto (fun u => E u / ((deriv D u - μ u) * exp (-Ψ u))) (𝓝[<] y) (𝓝 L) := by
    have h1 : Tendsto (fun u => 1 / (deriv D u - μ u)) (𝓝 y) (𝓝 L) := by
      have : L = 1 / (deriv D y - μ y) := by rw [hL, hD'per, hμy]
      rw [this]
      exact (tendsto_const_nhds.div ((hD'cont.sub hμcont).tendsto y)
        (by rw [hD'per, hD'x, hμy]; linarith))
    refine (h1.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hxy] with u hu
    exact (hratio u hu).symm
  have hp₀_x : Tendsto p₀ (𝓝[>] x) (𝓝 L) := by
    obtain ⟨ε, hε, hεne⟩ := Metric.eventually_nhds_iff.1 hne_x
    set δ₃ : ℝ := min ε T with hδ₃
    have hδ₃pos : 0 < δ₃ := lt_min hε hT
    have hsub₃ : Ioo x (x + δ₃) ⊆ Ioo x y :=
      Ioo_subset_Ioo le_rfl (by rw [hy]; linarith [min_le_right ε T])
    refine HasDerivAt.lhopital_zero_right_on_Ioo (show x < x + δ₃ by linarith)
      (fun u hu => hf_deriv u (hsub₃ hu)) (fun u hu => hG_deriv u (hsub₃ hu)) ?_ hf_x hG_x hdiv_x
    intro u hu
    have h1 : deriv D u - μ u ≠ 0 := by
      apply hεne
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hu.1, hu.2, min_le_left ε T]
    exact mul_ne_zero h1 (exp_pos _).ne'
  have hp₀_y : Tendsto p₀ (𝓝[<] y) (𝓝 L) := by
    obtain ⟨ε, hε, hεne⟩ := Metric.eventually_nhds_iff.1 hne_y
    set δ₃ : ℝ := min ε T with hδ₃
    have hδ₃pos : 0 < δ₃ := lt_min hε hT
    have hsub₃ : Ioo (y - δ₃) y ⊆ Ioo x y :=
      Ioo_subset_Ioo (by rw [hy]; linarith [min_le_right ε T]) le_rfl
    refine Infrastructure.lhopital_atTop_left_on_Ioo (show y - δ₃ < y by linarith)
      (fun u hu => hf_deriv u (hsub₃ hu)) (fun u hu => hG_deriv u (hsub₃ hu)) ?_ hG_y hdiv_y
    intro u hu
    have h1 : deriv D u - μ u ≠ 0 := by
      apply hεne
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hu.1, hu.2, min_le_left ε T]
    exact mul_ne_zero h1 (exp_pos _).ne'
  -- the first-order equation on `(x, y)`
  have hDp₀ : ∀ u ∈ Ioo x y, HasDerivAt (fun v => D v * p₀ v) (1 + μ u * p₀ u) u := by
    intro u hu
    have hw : HasDerivAt (fun v => exp (Ψ v) * f v)
        (exp (Ψ u) * g₀ u * f u + exp (Ψ u) * E u) u :=
      ((hΨ_deriv u hu).exp).mul (hf_deriv u hu)
    have heq : (fun v => D v * p₀ v) =ᶠ[𝓝 u] fun v => exp (Ψ v) * f v := by
      filter_upwards [isOpen_Ioo.eventually_mem hu] with v hv
      have hDv := hDne v hv
      simp only [hp₀, hG]
      rw [exp_neg]
      field_simp
    refine (hw.congr_of_eventuallyEq heq).congr_deriv ?_
    rw [hE_eq u hu, exp_neg]
    simp only [hp₀, hG, hg₀]
    rw [exp_neg]
    field_simp
    ring
  have hp₀_smooth : ContDiffOn ℝ 2 p₀ (Ioo x y) := by
    have : ContDiffOn ℝ ∞ p₀ (Ioo x y) :=
      hf_smooth.div (hD.contDiffOn.mul hΨ_smooth.neg.exp) fun u hu => (hG_pos u hu).ne'
    exact this.of_le (by simp)
  have hp₀_cont : ∀ u ∈ Ioo x y, ContinuousAt p₀ u := fun u hu =>
    (hf_deriv u hu).continuousAt.div (hG_deriv u hu).continuousAt (hG_pos u hu).ne'
  -- the periodic extension
  set p₁ : ℝ → ℝ := fun v => if v = x then L else p₀ v with hp₁
  set p : ℝ → ℝ := fun u => p₁ (toIcoMod hT x u) with hp
  have hp_per : Periodic p T := fun u => by simp only [hp, toIcoMod_add_right]
  have hp_Ioo : ∀ v ∈ Ioo x y, p v = p₀ v := by
    intro v hv
    simp only [hp, hp₁]
    rw [(toIcoMod_eq_self hT).2 (Ioo_subset_Ico_self hv), ite_eq_right hv.1.ne']
  have hp_x : p x = L := by
    simp only [hp, hp₁]
    rw [(toIcoMod_eq_self hT).2 ⟨le_rfl, by linarith⟩, ite_eq_left rfl]
  have hp_left : ∀ u ∈ Ioo (x - T) x, p u = p₀ (u + T) := by
    intro u hu
    have h1 : u + T ∈ Ioo x y := ⟨by linarith [hu.1], by rw [hy]; linarith [hu.2]⟩
    rw [← hp_per u, hp_Ioo _ h1]
  have hp_eventually : ∀ v ∈ Ioo x y, p =ᶠ[𝓝 v] p₀ := fun v hv =>
    (isOpen_Ioo.eventually_mem hv).mono fun t ht => hp_Ioo t ht
  have hp_Ico : ∀ v ∈ Ico x y, 0 ≤ p v := by
    intro v hv
    rcases eq_or_lt_of_le hv.1 with rfl | hxv
    · rw [hp_x]; exact hL_pos.le
    · rw [hp_Ioo v ⟨hxv, hv.2⟩]; exact (hp₀_pos v ⟨hxv, hv.2⟩).le
  have hp_nonneg : ∀ u, 0 ≤ p u := by
    intro u
    have h1 : p u = p (toIcoMod hT x u) := by
      simp only [hp]
      congr 1
      exact ((toIcoMod_eq_self hT).2 (toIcoMod_mem_Ico hT x u)).symm
    rw [h1]
    exact hp_Ico _ (toIcoMod_mem_Ico hT x u)
  have hp_pos : ∀ u ∈ Ioo x y, 0 < p u := fun u hu => by
    rw [hp_Ioo u hu]; exact hp₀_pos u hu
  -- continuity
  have hp_contAt_x : ContinuousAt p x := by
    rw [continuousAt_iff_continuous_left_right]
    constructor
    · rw [← continuousWithinAt_Iio_iff_Iic, ContinuousWithinAt, hp_x]
      refine (hp₀_y.comp (tendsto_add_const_nhdsLT x T)).congr' ?_
      filter_upwards [Ioo_mem_nhdsLT (show x - T < x by linarith)] with u hu
      exact (hp_left u hu).symm
    · rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt, hp_x]
      refine hp₀_x.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hxy] with u hu
      exact (hp_Ioo u hu).symm
  have hp_cont : Continuous p := by
    refine Infrastructure.Periodic.continuous_of_continuousAt_Ico (x := x) hT hp_per
      fun v hv => ?_
    rcases eq_or_lt_of_le hv.1 with rfl | hxv
    · exact hp_contAt_x
    · exact (hp₀_cont v ⟨hxv, hv.2⟩).congr (hp_eventually v ⟨hxv, hv.2⟩).symm
  -- smoothness off the lattice
  have hp_smooth : ContDiffOn ℝ 2 p {u | ∀ n : ℤ, u ≠ x + n * T} :=
    Infrastructure.Periodic.contDiffOn_compl_lattice hT hp_per hp₀_smooth hp_Ioo
  -- the first-order equation everywhere
  have hDp_Ioo : ∀ u ∈ Ioo x y, HasDerivAt (fun v => D v * p v) (1 + μ u * p u) u := by
    intro u hu
    have heq : (fun v => D v * p v) =ᶠ[𝓝 u] fun v => D v * p₀ v :=
      (hp_eventually u hu).mono fun v hv => by simp only [hv]
    rw [hp_Ioo u hu]
    exact (hDp₀ u hu).congr_of_eventuallyEq heq
  have hDp_per : Periodic (fun v => D v * p v) T := fun u => by
    simp only [hDper u, hp_per u]
  have hrhs_per : Periodic (fun u => 1 + μ u * p u) T := fun u => by
    simp only [hμper u, hp_per u]
  have hDp_left : ∀ u ∈ Ioo (x - T) x, HasDerivAt (fun v => D v * p v) (1 + μ u * p u) u := by
    intro u hu
    have h1 : u + T ∈ Ioo x y := ⟨by linarith [hu.1], by rw [hy]; linarith [hu.2]⟩
    have h2 := (hDp_Ioo _ h1).comp_add_const u T
    have h3 : (fun v => D (v + T) * p (v + T)) = fun v => D v * p v :=
      funext fun v => hDp_per v
    rw [h3] at h2
    rwa [hμper u, hp_per u] at h2
  have hDp_x : HasDerivAt (fun v => D v * p v) (1 + μ x * p x) x := by
    refine Infrastructure.hasDerivAt_of_hasDerivAt_Ioo_Ioo hT
      ((hDcont.continuousAt).mul hp_cont.continuousAt) hDp_Ioo hDp_left ?_
    exact continuous_const.continuousAt.add (hμcont.continuousAt.mul hp_cont.continuousAt)
  have hDp : ∀ u, HasDerivAt (fun v => D v * p v) (1 + μ u * p u) u := by
    refine Infrastructure.Periodic.hasDerivAt_of_Ico (x := x) hT hDp_per hrhs_per fun v hv => ?_
    rcases eq_or_lt_of_le hv.1 with rfl | hxv
    · exact hDp_x
    · exact hDp_Ioo v ⟨hxv, hv.2⟩
  exact ⟨p, hp_cont, hp_nonneg, hp_per, hp_pos, hp_smooth, hDp⟩

end SingularData

end ComplexSLE.Internal

end
