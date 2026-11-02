/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Second-order Taylor sandwich at a double zero

If `g` is `C²` with `g 0 = 0`, `g' 0 = 0` and `m ≤ g'' ≤ M` on `[-δ, δ]`, then
`m y² / 2 ≤ g y ≤ M y² / 2` on `[-δ, δ]`. This is used for the diffusion coefficient `D`
(`c y² ≤ D (x₀ + y) ≤ C y²`) and for a residual vanishing to second order
(`r y = o (y²)`), without going through the Lagrange remainder in Mathlib's `taylor_*` API.
-/

public section

open Set Filter Topology

namespace ComplexSLE.Infrastructure

theorem contDiff_two_deriv_facts {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) :
    Differentiable ℝ g ∧ Differentiable ℝ (deriv g) ∧ Continuous (deriv (deriv g)) := by
  have hs : ContDiff ℝ (1 + 1) g := hg
  obtain ⟨hd1, -, hc1⟩ := contDiff_succ_iff_deriv.1 hs
  have hs' : ContDiff ℝ (0 + 1) (deriv g) := by simpa using hc1
  obtain ⟨hd2, -, hc2⟩ := contDiff_succ_iff_deriv.1 hs'
  exact ⟨hd1, hd2, hc2.continuous⟩

/-- A `C²` function with `ψ 0 = ψ' 0 = 0` and `ψ'' ≥ 0` on `[-δ, δ]` is nonnegative there. -/
theorem nonneg_of_deriv_deriv_nonneg {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (h0 : ψ 0 = 0)
    (h1 : deriv ψ 0 = 0) {δ : ℝ} (h2 : ∀ y ∈ Icc (-δ) δ, 0 ≤ deriv (deriv ψ) y) :
    ∀ y ∈ Icc (-δ) δ, 0 ≤ ψ y := by
  obtain ⟨hd1, hd2, -⟩ := contDiff_two_deriv_facts hψ
  intro y hy
  have hδ : 0 ≤ δ := by linarith [hy.1, hy.2]
  have hmono : MonotoneOn (deriv ψ) (Icc (-δ) δ) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) hd2.continuous.continuousOn
      hd2.differentiableOn fun x hx => h2 x ?_
    rw [interior_Icc] at hx
    exact ⟨hx.1.le, hx.2.le⟩
  have h00 : (0 : ℝ) ∈ Icc (-δ) δ := ⟨by linarith, hδ⟩
  rcases le_total 0 y with hy0 | hy0
  · have hpos : MonotoneOn ψ (Icc 0 δ) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) hd1.continuous.continuousOn
        hd1.differentiableOn fun x hx => ?_
      rw [interior_Icc] at hx
      have := hmono h00 (show x ∈ Icc (-δ) δ from ⟨by linarith [hx.1], hx.2.le⟩) hx.1.le
      rwa [h1] at this
    have := hpos (show (0 : ℝ) ∈ Icc 0 δ from ⟨le_rfl, hδ⟩) (show y ∈ Icc 0 δ from ⟨hy0, hy.2⟩) hy0
    rwa [h0] at this
  · have hneg : AntitoneOn ψ (Icc (-δ) 0) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hd1.continuous.continuousOn
        hd1.differentiableOn fun x hx => ?_
      rw [interior_Icc] at hx
      have := hmono (show x ∈ Icc (-δ) δ from ⟨hx.1.le, by linarith [hx.2]⟩) h00 hx.2.le
      rwa [h1] at this
    have := hneg (show y ∈ Icc (-δ) 0 from ⟨hy.1, hy0⟩)
      (show (0 : ℝ) ∈ Icc (-δ) 0 from ⟨by linarith, le_rfl⟩) hy0
    rwa [h0] at this

/-- **Second-order sandwich.** If `g` is `C²`, `g 0 = g' 0 = 0` and `m ≤ g'' ≤ M` on `[-δ, δ]`,
then `m y² / 2 ≤ g y ≤ M y² / 2` on `[-δ, δ]`. -/
theorem sandwich_of_deriv_deriv {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (h0 : g 0 = 0)
    (h1 : deriv g 0 = 0) {δ m M : ℝ} (hm : ∀ y ∈ Icc (-δ) δ, m ≤ deriv (deriv g) y)
    (hM : ∀ y ∈ Icc (-δ) δ, deriv (deriv g) y ≤ M) :
    ∀ y ∈ Icc (-δ) δ, m / 2 * y ^ 2 ≤ g y ∧ g y ≤ M / 2 * y ^ 2 := by
  obtain ⟨hd1, hd2, hc2⟩ := contDiff_two_deriv_facts hg
  have hq : ∀ c : ℝ, ContDiff ℝ 2 (fun y : ℝ => c / 2 * y ^ 2) := fun c =>
    contDiff_const.mul (contDiff_id.pow 2)
  have hqd : ∀ c : ℝ, Differentiable ℝ (fun y : ℝ => c / 2 * y ^ 2) := fun c =>
    (hq c).differentiable (by norm_num)
  have hq1 : ∀ c y : ℝ, deriv (fun y : ℝ => c / 2 * y ^ 2) y = c * y := fun c y => by
    have := ((hasDerivAt_pow 2 y).const_mul (c / 2)).deriv
    rw [this]; push_cast; ring
  have hq1' : ∀ c : ℝ, deriv (fun y : ℝ => c / 2 * y ^ 2) = fun y => c * y := fun c =>
    funext (hq1 c)
  have hdm : ∀ c y : ℝ, DifferentiableAt ℝ (fun y : ℝ => c * y) y := fun c y => by fun_prop
  have hid : ∀ c y : ℝ, deriv (fun y : ℝ => c * y) y = c := fun c y => by
    simp
  have hlow : ∀ y ∈ Icc (-δ) δ, m / 2 * y ^ 2 ≤ g y := by
    intro y hy
    have := nonneg_of_deriv_deriv_nonneg (ψ := fun y => g y - m / 2 * y ^ 2) (hg.sub (hq m))
      (by simp [h0]) (by rw [deriv_fun_sub (hd1 0) (hqd m 0), hq1, h1]; simp) (δ := δ)
      (fun y hy => by
        have e1 : deriv (fun y => g y - m / 2 * y ^ 2) = fun y => deriv g y - m * y := by
          funext y
          rw [deriv_fun_sub (hd1 y) (hqd m y), hq1]
        rw [e1, deriv_fun_sub (hd2 y) (hdm m y), hid]
        linarith [hm y hy]) y hy
    linarith
  have hup : ∀ y ∈ Icc (-δ) δ, g y ≤ M / 2 * y ^ 2 := by
    intro y hy
    have := nonneg_of_deriv_deriv_nonneg (ψ := fun y => M / 2 * y ^ 2 - g y) ((hq M).sub hg)
      (by simp [h0]) (by rw [deriv_fun_sub (hqd M 0) (hd1 0), hq1, h1]; simp) (δ := δ)
      (fun y hy => by
        have e1 : deriv (fun y => M / 2 * y ^ 2 - g y) = fun y => M * y - deriv g y := by
          funext y
          rw [deriv_fun_sub (hqd M y) (hd1 y), hq1]
        rw [e1, deriv_fun_sub (hdm M y) (hd2 y), hid]
        linarith [hM y hy]) y hy
    linarith
  exact fun y hy => ⟨hlow y hy, hup y hy⟩

/-- A property that holds eventually near `0` holds on a symmetric closed interval. -/
theorem exists_Icc_of_eventually_nhds_zero {P : ℝ → Prop} (h : ∀ᶠ y in 𝓝 (0 : ℝ), P y) :
    ∃ δ > 0, ∀ y ∈ Icc (-δ) δ, P y := by
  obtain ⟨ε, hε, hP⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨ε / 2, by positivity, fun y hy => hP ?_⟩
  rw [Real.dist_eq, sub_zero]
  rw [abs_lt]
  constructor <;> linarith [hy.1, hy.2]

/-- **Quadratic bounds at a nondegenerate double zero.** If `g` is `C²`, `g 0 = g' 0 = 0` and
`g'' 0 > 0`, then `c y² ≤ g y ≤ C y²` on some `[-δ, δ]`. -/
theorem exists_sq_bounds {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (h0 : g 0 = 0) (h1 : deriv g 0 = 0)
    (h2 : 0 < deriv (deriv g) 0) :
    ∃ δ > 0, ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ y ∈ Icc (-δ) δ, c * y ^ 2 ≤ g y ∧ g y ≤ C * y ^ 2 := by
  obtain ⟨-, -, hc2⟩ := contDiff_two_deriv_facts hg
  set q := deriv (deriv g) 0 with hq
  have hev : ∀ᶠ y in 𝓝 (0 : ℝ), q / 2 < deriv (deriv g) y ∧ deriv (deriv g) y < 2 * q :=
    (hc2.continuousAt).eventually (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨δ, hδ, hP⟩ := exists_Icc_of_eventually_nhds_zero hev
  refine ⟨δ, hδ, q / 4, q, by positivity, h2, fun y hy => ?_⟩
  have := sandwich_of_deriv_deriv hg h0 h1 (δ := δ) (m := q / 2) (M := 2 * q)
    (fun y hy => (hP y hy).1.le) (fun y hy => (hP y hy).2.le) y hy
  constructor <;> nlinarith [this.1, this.2, sq_nonneg y]

/-- **Second-order vanishing.** If `g` is `C²` and `g`, `g'`, `g''` all vanish at `0`, then
`|g y| ≤ ε y²` near `0`, for every `ε > 0`. -/
theorem abs_le_sq_of_second_order_zero {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (h0 : g 0 = 0)
    (h1 : deriv g 0 = 0) (h2 : deriv (deriv g) 0 = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ Icc (-δ) δ, |g y| ≤ ε * y ^ 2 := by
  obtain ⟨-, -, hc2⟩ := contDiff_two_deriv_facts hg
  have hev : ∀ᶠ y in 𝓝 (0 : ℝ), -(2 * ε) < deriv (deriv g) y ∧ deriv (deriv g) y < 2 * ε := by
    refine (hc2.continuousAt).eventually (Ioo_mem_nhds (a := -(2 * ε)) (b := 2 * ε)
      (x := deriv (deriv g) 0) ?_ ?_) <;> rw [h2] <;> linarith
  obtain ⟨δ, hδ, hP⟩ := exists_Icc_of_eventually_nhds_zero hev
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have := sandwich_of_deriv_deriv hg h0 h1 (δ := δ) (m := -(2 * ε)) (M := 2 * ε)
    (fun y hy => (hP y hy).1.le) (fun y hy => (hP y hy).2.le) y hy
  rw [abs_le]
  constructor <;> nlinarith [this.1, this.2]

end ComplexSLE.Infrastructure

end
