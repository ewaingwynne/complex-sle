/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.KolmogorovDensity
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The case `c = 0`: the explicit stationary density

Deterministic part of Lemma 3.11 (`lem-c0-phases`, paper.tex:L1824-1910): for `a, b > 0` every
admissible density for `c = 0` is the explicit density (3.30),
`p(u) = Z⁻¹ (a + b + (b - a) cos 2u)^{4/(b-a)}` if `a ≠ b` and `p(u) = Z⁻¹ exp((4/a) cos² u)`
if `a = b`, `Z = ∫₀^{2π}` of the unnormalised function.

* `IsAdmissibleDensity.exists_hasDerivAt`: for *any* `(a, b, c)`, an admissible density solves the
  first-order equation `(D p)' = J + µ p` on all of `ℝ` for some constant `J`. (The second-order
  equation holds off the lattice `x + πℤ`, `D p` is `C¹` on `ℝ`, and everything is `π`-periodic.)
* `eq_const_mul_of_hasDerivAt`: a `π`-periodic solution of `(D p)' = J + µ p`, with `D > 0`
  `π`-periodic, is a multiple of any positive `π`-periodic solution `P` of `(D P)' = µ P`, and
  `J = 0`. The proof differentiates `D p / (D P)`, whose derivative is `J / (D P)`.
* `hasDerivAt_diffusionD_mul_c0Shape`: the formula (3.30) verified: `(D P)' = µ P` for `c = 0`.
* `IsAdmissibleDensity.eq_c0Shape_div`: the uniqueness statement.
-/

@[expose] public section

open Set Filter Topology MeasureTheory intervalIntegral Function Real
open scoped ContDiff

namespace ComplexSLE.Internal

/-! ### The first-order equation for an admissible density -/

/-- An admissible density solves `(D p)' = J + µ p` on all of `ℝ` for some constant `J`. -/
theorem IsAdmissibleDensity.exists_hasDerivAt {a b c : ℝ} {p : ℝ → ℝ}
    (hp : IsAdmissibleDensity a b c p) :
    ∃ J : ℝ, ∀ u, HasDerivAt (fun v => diffusionD a b c v * p v) (J + mu a b c u * p u) u := by
  obtain ⟨hcont, -, hper, -, x, hC2, hode, hC1⟩ := hp
  set q : ℝ → ℝ := fun v => diffusionD a b c v * p v with hq
  have hqdiff : Differentiable ℝ q := hC1.differentiable one_ne_zero
  have hq'cont : Continuous (deriv q) := hC1.continuous_deriv_one
  set g : ℝ → ℝ := fun u => deriv q u - mu a b c u * p u with hg
  have hgcont : Continuous g := hq'cont.sub ((continuous_mu a b c).mul hcont)
  have hqper : Periodic q π := (diffusionD_periodic a b c).mul hper
  have hgper : Periodic g π := fun u => by
    simp only [hg, hqper.deriv_periodic u, mu_periodic a b c u, hper u]
  -- `g` is locally constant on the open interval `(x, x + π)`
  set I : Set ℝ := Ioo x (x + π) with hI
  have hIS : I ⊆ {u | ∀ n : ℤ, u ≠ x + n * π} := fun u hu => notMem_lattice_of_mem_Ioo hu
  have hpC2 : ContDiffOn ℝ 2 p I := hC2.mono hIS
  have hDC2 : ContDiff ℝ 2 (diffusionD a b c) :=
    (contDiff_diffusionD a b c).of_le (by simp)
  have hμC1 : ContDiff ℝ 1 (mu a b c) := (contDiff_mu a b c).of_le (by simp)
  have hqC2 : ContDiffOn ℝ 2 q I := hDC2.contDiffOn.mul hpC2
  have hq'diff : DifferentiableOn ℝ (deriv q) I :=
    (hqC2.deriv_of_isOpen isOpen_Ioo (by norm_num)).differentiableOn one_ne_zero
  have hμpdiff : DifferentiableOn ℝ (fun v => mu a b c v * p v) I :=
    (hμC1.differentiable one_ne_zero).differentiableOn.mul (hpC2.differentiableOn two_ne_zero)
  have hg' : ∀ u ∈ I, HasDerivAt g 0 u := by
    intro u hu
    have h1 : DifferentiableAt ℝ (deriv q) u := hq'diff.differentiableAt (isOpen_Ioo.mem_nhds hu)
    have h2 : DifferentiableAt ℝ (fun v => mu a b c v * p v) u :=
      hμpdiff.differentiableAt (isOpen_Ioo.mem_nhds hu)
    have h3 := h1.hasDerivAt.sub h2.hasDerivAt
    have h4 := hode u (hIS hu)
    convert h3 using 1
    linarith
  have hgdiff : DifferentiableOn ℝ g I := fun u hu =>
    (hg' u hu).differentiableAt.differentiableWithinAt
  obtain ⟨K, hK⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo hgdiff
    (fun u hu => (hg' u hu).deriv)
  -- `g = K` on `[x, x + π]` by continuity, hence everywhere by periodicity
  have hclosed : IsClosed {u | g u = K} := isClosed_eq hgcont continuous_const
  have hIcc : Icc x (x + π) ⊆ {u | g u = K} := by
    rw [← closure_Ioo (by linarith [pi_pos] : x ≠ x + π)]
    exact closure_minimal (fun y hy => hK y hy) hclosed
  have hgK : ∀ u, g u = K := by
    intro u
    obtain ⟨y, hy, hgy⟩ := hgper.exists_mem_Ico pi_pos u x
    rw [hgy]
    exact hIcc ⟨hy.1, hy.2.le⟩
  refine ⟨K, fun u => ?_⟩
  have h1 := (hqdiff u).hasDerivAt
  convert h1 using 1
  have := hgK u
  simp only [hg] at this
  linarith

/-! ### Uniqueness for the first-order equation -/

/-- Let `D > 0` and `P > 0` be `π`-periodic with `(D P)' = µ P`, and let `p` be `π`-periodic with
`(D p)' = J + µ p`. Then `J = 0` and `p = C P` for a constant `C`. -/
theorem eq_const_mul_of_hasDerivAt {D μ P p : ℝ → ℝ} {J : ℝ}
    (hD : ∀ u, 0 < D u) (hDper : Periodic D π) (hP : ∀ u, 0 < P u) (hPper : Periodic P π)
    (hpper : Periodic p π)
    (hPd : ∀ u, HasDerivAt (fun v => D v * P v) (μ u * P u) u)
    (hpd : ∀ u, HasDerivAt (fun v => D v * p v) (J + μ u * p u) u) :
    J = 0 ∧ ∃ C : ℝ, ∀ u, p u = C * P u := by
  set G : ℝ → ℝ := fun v => D v * P v with hG
  have hGpos : ∀ u, 0 < G u := fun u => mul_pos (hD u) (hP u)
  have hGper : Periodic G π := hDper.mul hPper
  set q : ℝ → ℝ := fun v => D v * p v with hq
  have hqper : Periodic q π := hDper.mul hpper
  set R : ℝ → ℝ := fun v => q v / G v with hR
  have hRd : ∀ u, HasDerivAt R (J / G u) u := by
    intro u
    have h := (hpd u).div (hPd u) (hGpos u).ne'
    convert h using 1
    have hGu : G u ≠ 0 := (hGpos u).ne'
    simp only [hG, hq] at hGu ⊢
    field_simp
    ring
  have hRper : Periodic R π := hqper.div hGper
  have hRπ : R π = R 0 := by simpa using hRper 0
  have hJ : J = 0 := by
    by_contra hJ
    rcases lt_or_gt_of_ne hJ with h | h
    · have hanti : StrictAnti R :=
        strictAnti_of_hasDerivAt_neg hRd (fun u => div_neg_of_neg_of_pos h (hGpos u))
      have := hanti pi_pos
      rw [hRπ] at this
      exact lt_irrefl _ this
    · have hmono : StrictMono R :=
        strictMono_of_hasDerivAt_pos hRd (fun u => div_pos h (hGpos u))
      have := hmono pi_pos
      rw [hRπ] at this
      exact lt_irrefl _ this
  refine ⟨hJ, R 0, fun u => ?_⟩
  have hconst : ∀ x y, R x = R y :=
    is_const_of_deriv_eq_zero (fun u => (hRd u).differentiableAt)
      (fun u => by rw [(hRd u).deriv, hJ, zero_div])
  have h := hconst u 0
  simp only [hR, hq, hG] at h ⊢
  have hDu : D u ≠ 0 := (hD u).ne'
  have hPu : P u ≠ 0 := (hP u).ne'
  rw [← h]
  field_simp

/-! ### The explicit density (3.30) -/

/-- The unnormalised density (3.30) (paper.tex:L1832-1838): `(a + b + (b - a) cos 2u)^{4/(b-a)}`
if `a ≠ b` and `exp ((4/a) cos² u)` if `a = b`. -/
noncomputable def c0Shape (a b u : ℝ) : ℝ :=
  if a = b then exp (4 / a * cos u ^ 2) else (a + b + (b - a) * cos (2 * u)) ^ (4 / (b - a))

variable {a b : ℝ}

/-- `a + b + (b - a) t = a (1 - t) + b (1 + t) > 0` for `t ∈ [-1, 1]` and `a, b > 0`. -/
theorem base_pos_of_mem_Icc (ha : 0 < a) (hb : 0 < b) {t : ℝ} (h1 : -1 ≤ t) (h2 : t ≤ 1) :
    0 < a + b + (b - a) * t := by
  rcases le_total t 0 with h | h
  · nlinarith [mul_nonneg hb.le (show 0 ≤ 1 + t by linarith),
      mul_pos ha (show 0 < 1 - t by linarith)]
  · nlinarith [mul_nonneg ha.le (show 0 ≤ 1 - t by linarith),
      mul_pos hb (show 0 < 1 + t by linarith)]

theorem c0Base_pos (ha : 0 < a) (hb : 0 < b) (u : ℝ) : 0 < a + b + (b - a) * cos (2 * u) :=
  base_pos_of_mem_Icc ha hb (neg_one_le_cos _) (cos_le_one _)

/-- For `c = 0`, `D(u) = (a + b + (b - a) cos 2u) / 4`. -/
theorem diffusionD_zero_eq (a b u : ℝ) :
    diffusionD a b 0 u = (a + b + (b - a) * cos (2 * u)) / 4 := by
  have h := sin_sq_add_cos_sq u
  rw [cos_two_mul]
  simp only [diffusionD]
  linear_combination (a / 2) * h

theorem c0Shape_pos (ha : 0 < a) (hb : 0 < b) (u : ℝ) : 0 < c0Shape a b u := by
  unfold c0Shape
  split_ifs
  · exact exp_pos _
  · exact rpow_pos_of_pos (c0Base_pos ha hb u) _

theorem c0Shape_periodic (a b : ℝ) : Periodic (c0Shape a b) π := by
  intro u
  unfold c0Shape
  rw [show 2 * (u + π) = 2 * u + 2 * π by ring, cos_add_two_pi, cos_add_pi]
  simp

theorem continuous_c0Shape (ha : 0 < a) (hb : 0 < b) : Continuous (c0Shape a b) := by
  unfold c0Shape
  split_ifs
  · fun_prop
  · exact (by fun_prop : Continuous fun u : ℝ => a + b + (b - a) * cos (2 * u)).rpow_const
      (fun u => Or.inl (c0Base_pos ha hb u).ne')

theorem integral_c0Shape_pos (ha : 0 < a) (hb : 0 < b) : 0 < ∫ v in (0)..(2 * π), c0Shape a b v :=
  intervalIntegral.intervalIntegral_pos_of_pos
    ((continuous_c0Shape ha hb).intervalIntegrable 0 (2 * π)) (c0Shape_pos ha hb) (by positivity)

/-- **Verification of (3.30).** With `P = c0Shape a b` we have `(D P)' = µ P` for `c = 0`, i.e. the
explicit function solves `-µ p + (D p)' = 0`. -/
theorem hasDerivAt_diffusionD_mul_c0Shape (ha : 0 < a) (hb : 0 < b) (u : ℝ) :
    HasDerivAt (fun v => diffusionD a b 0 v * c0Shape a b v) (mu a b 0 u * c0Shape a b u) u := by
  by_cases hab : a = b
  · subst hab
    have hD : ∀ v, diffusionD a a 0 v = a / 2 := fun v => by rw [diffusionD_zero_eq]; ring
    have e1 : (fun v => diffusionD a a 0 v * c0Shape a a v) =
        fun v => a / 2 * exp (4 / a * cos v ^ 2) := by
      funext v; simp [hD, c0Shape]
    rw [e1]
    have h0 : HasDerivAt cos (-sin u) u := Real.hasDerivAt_cos u
    have h1 := h0.fun_pow 2
    have h2 := ((h1.const_mul (4 / a)).exp).const_mul (a / 2)
    have hs : c0Shape a a u = exp (4 / a * cos u ^ 2) := by simp [c0Shape]
    convert h2 using 1
    rw [hs]
    simp only [mu]
    rw [sin_two_mul]
    field_simp
    ring
  · have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
    set w : ℝ → ℝ := fun v => a + b + (b - a) * cos (2 * v) with hw
    have hwpos : ∀ v, 0 < w v := c0Base_pos ha hb
    have e1 : (fun v => diffusionD a b 0 v * c0Shape a b v) =
        fun v => w v / 4 * w v ^ (4 / (b - a)) := by
      funext v
      simp only [c0Shape, hab, ite_false, diffusionD_zero_eq, hw]
    rw [e1]
    have hwd : HasDerivAt w (-(2 * (b - a)) * sin (2 * u)) u := by
      have h2 : HasDerivAt (fun v : ℝ => 2 * v) 2 u := by
        simpa using (hasDerivAt_id u).const_mul 2
      have := ((h2.cos).const_mul (b - a)).const_add (a + b)
      convert this using 1
      ring
    have hrp := hwd.rpow_const (p := 4 / (b - a)) (Or.inl (hwpos u).ne')
    have h3 := (hwd.div_const 4).mul hrp
    convert h3 using 1
    simp only [mu, c0Shape, hab, ite_false]
    have hwu : w u ≠ 0 := (hwpos u).ne'
    rw [rpow_sub_one hwu]
    generalize w u ^ (4 / (b - a)) = X
    generalize w u = W at hwu ⊢
    field_simp
    ring

/-- **Uniqueness of the stationary density for `c = 0`** (paper.tex:L1830-1838, (3.30)): for
`a, b > 0`, every admissible density is `Z⁻¹` times the explicit function `c0Shape a b`, with
`Z = ∫₀^{2π} c0Shape a b`. -/
theorem IsAdmissibleDensity.eq_c0Shape_div (ha : 0 < a) (hb : 0 < b) {p : ℝ → ℝ}
    (hp : IsAdmissibleDensity a b 0 p) :
    p = fun u => c0Shape a b u / ∫ v in (0)..(2 * π), c0Shape a b v := by
  obtain ⟨J, hJ⟩ := IsAdmissibleDensity.exists_hasDerivAt hp
  have hDpos : ∀ u, 0 < diffusionD a b 0 u :=
    diffusionD_pos ha hb (by simpa using mul_pos ha hb)
  obtain ⟨-, C, hC⟩ := eq_const_mul_of_hasDerivAt hDpos (diffusionD_periodic a b 0)
    (c0Shape_pos ha hb) (c0Shape_periodic a b) hp.2.2.1
    (hasDerivAt_diffusionD_mul_c0Shape ha hb) hJ
  have hint : ∫ u in (0)..(2 * π), p u = C * ∫ v in (0)..(2 * π), c0Shape a b v := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun u _ => hC u)
  have hnorm := hp.2.2.2.1
  have hZ := integral_c0Shape_pos ha hb
  have hCZ : C = (∫ v in (0)..(2 * π), c0Shape a b v)⁻¹ := by
    have h1 : C * ∫ v in (0)..(2 * π), c0Shape a b v = 1 := hint ▸ hnorm
    field_simp
    exact h1
  funext u
  rw [hC u, hCZ]
  ring

end ComplexSLE.Internal

end
