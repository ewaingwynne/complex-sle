/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsAdmissibleDensity
public import ComplexSLE.Internal.Density.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Lemma A.1: the hypotheses on the density and the integration by parts

Analytic part of the Kolmogorov forward equation for periodic one-dimensional diffusions
(paper.tex:L2318-2334, typo T12: `α, β` are real-valued).

* `IsKolmogorovDensity α β p`: the hypotheses of Lemma A.1 on the density `p` (continuous,
  non-negative, `π`-periodic, `∫₀^π p = 1`, `C²` off some lattice `x + πℤ` where it solves
  `-(αp)' + ½(β²p)'' = 0`, and `β²p` is `C¹` on `ℝ`).
* `IsAdmissibleDensity.isKolmogorovDensity`: the bridge used by Lemma 2.14
  (`step:stat-kolmogorov-normalization`, ruling R9): an admissible density `p` for `(a, b, c)`
  gives the Kolmogorov density `2p` for `α = µ` and any `β` with `β² = 2D`.
* `IsKolmogorovDensity.integral_generator_eq_zero`: `∫₀^π (f'α + ½f''β²) p = 0` for every `C²`
  `π`-periodic `f` (`step:kol-derivative-at-zero` and `step:kol-integration-by-parts`, (A.3)–(A.4)).
  The proof avoids differentiating `p` at the lattice points: with `G := β²p` (`C¹` on `ℝ`) the
  integrand is `½(f'G)' + f'·(αp - ½G')` everywhere, and `αp - ½G'` is constant on `(x, x + π)`
  by the ODE; both pieces integrate to zero over a period.
-/

public section

open Set Filter Topology MeasureTheory intervalIntegral Function Real
open scoped ContDiff Interval

namespace ComplexSLE.Internal

/-! ### Periodic functions: derivatives and shifted periods -/

/-- The derivative of a periodic function is periodic (no differentiability needed: `deriv` is
`0` where `f` is not differentiable, and translation preserves that). -/
theorem _root_.Function.Periodic.deriv_periodic {f : ℝ → ℝ} {c : ℝ} (hf : Periodic f c) :
    Periodic (deriv f) c := by
  intro u
  have h : (fun x => f (x + c)) = f := funext hf
  rw [← deriv_comp_add_const, h]

/-- Integral of a periodic function over `[0, T]` equals its integral over `[x, x + T]`. -/
theorem _root_.Function.Periodic.intervalIntegral_zero_eq {f : ℝ → ℝ} {T : ℝ} (hf : Periodic f T)
    (x : ℝ) :
    ∫ u in (0)..T, f u = ∫ u in x..x + T, f u := by
  have := hf.intervalIntegral_add_eq 0 x
  simpa using this

/-- A point strictly between `x` and `x + π` lies off the lattice `x + πℤ`. -/
theorem notMem_lattice_of_mem_Ioo {x u : ℝ} (hu : u ∈ Ioo x (x + π)) :
    ∀ n : ℤ, u ≠ x + n * π := by
  intro n hn
  obtain ⟨h1, h2⟩ := hu
  rw [hn] at h1 h2
  have hpos : (0 : ℝ) < n :=
    (mul_pos_iff_of_pos_right pi_pos).mp ((lt_add_iff_pos_right x).mp h1)
  have hlt : (n : ℝ) < 1 :=
    (mul_lt_iff_lt_one_left pi_pos).mp ((add_lt_add_iff_left x).mp h2)
  have h0 : (0 : ℤ) < n := by exact_mod_cast hpos
  have h1' : n < (1 : ℤ) := by exact_mod_cast hlt
  omega

/-- The complement of the lattice `x + πℤ` is open. -/
theorem isOpen_compl_lattice (x : ℝ) : IsOpen {u : ℝ | ∀ n : ℤ, u ≠ x + n * π} := by
  have hclosed : IsClosed ((fun u : ℝ => (u - x) / π) ⁻¹' range ((↑) : ℤ → ℝ)) :=
    Int.isClosedEmbedding_coe_real.isClosed_range.preimage (by fun_prop)
  convert hclosed.isOpen_compl using 1
  ext u
  simp only [mem_compl_iff, mem_preimage, mem_range, not_exists]
  constructor
  · intro h n hn
    apply h n
    field_simp at hn
    linarith
  · intro h n hn
    apply h n
    rw [hn]; field_simp; ring

/-! ### The hypotheses of Lemma A.1 on the density -/

/-- The hypotheses of Lemma A.1 (paper.tex:L2326-2333, T12) on the density `p` for the
coefficients `α, β`: `p` is continuous, non-negative, `π`-periodic with `∫₀^π p = 1`, and for
some `x` it is `C²` off `x + πℤ` and solves `-(αp)' + ½(β²p)'' = 0` there, while `β²p` is `C¹`
on all of `ℝ`. Only `β²` enters. -/
structure IsKolmogorovDensity (α β p : ℝ → ℝ) : Prop where
  continuous : Continuous p
  nonneg : ∀ u, 0 ≤ p u
  periodic : Periodic p π
  integral_eq_one : ∫ u in (0)..π, p u = 1
  exists_regular : ∃ x : ℝ,
    ContDiffOn ℝ 2 p {u | ∀ n : ℤ, u ≠ x + n * π} ∧
    (∀ u, (∀ n : ℤ, u ≠ x + n * π) →
      -deriv (fun v => α v * p v) u + (1 / 2) * deriv (deriv fun v => β v ^ 2 * p v) u = 0) ∧
    ContDiff ℝ 1 (fun u => β u ^ 2 * p u)

/-- Bridge for Lemma 2.14 (`step:stat-kolmogorov-normalization`, R9): an admissible density
`p` for `(a, b, c)` makes `2p` a Kolmogorov density for `α = µ` and any `β` with `β² = 2D`
(`∫₀^π 2p = ∫₀^{2π} p = 1`, and (2.13) is (A.2)). -/
theorem IsAdmissibleDensity.isKolmogorovDensity {a b c : ℝ} {p : ℝ → ℝ}
    (hp : IsAdmissibleDensity a b c p) {β : ℝ → ℝ}
    (hβ : ∀ u, β u ^ 2 = 2 * diffusionD a b c u) :
    IsKolmogorovDensity (mu a b c) β (fun u => 2 * p u) := by
  obtain ⟨hcont, hnonneg, hper, hint, x, hC2, hode, hC1⟩ := hp
  refine ⟨by fun_prop, fun u => by linarith [hnonneg u], fun u => by simp only [hper u],
    ?_, x, ?_, ?_, ?_⟩
  · -- `∫₀^π 2p = ∫₀^{2π} p = 1` by periodicity.
    have hsplit : ∫ u in (0)..(2 * π), p u =
        (∫ u in (0)..π, p u) + ∫ u in π..(2 * π), p u := by
      rw [integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
        (hcont.intervalIntegrable _ _)]
    have hshift : ∫ u in π..(2 * π), p u = ∫ u in (0)..π, p u := by
      have := hper.intervalIntegral_add_eq π 0
      rw [two_mul]
      simpa using this
    rw [intervalIntegral.integral_const_mul]
    linarith
  · exact contDiffOn_const.mul hC2
  · intro u hu
    have h1 : (fun v => mu a b c v * (2 * p v)) = fun v => 2 * (mu a b c v * p v) := by
      funext v; ring
    have h2 : (fun v => β v ^ 2 * (2 * p v)) = fun v => 4 * (diffusionD a b c v * p v) := by
      funext v; rw [hβ v]; ring
    rw [h1, h2]
    simp only [deriv_const_mul_field']
    have := hode u hu
    linear_combination 2 * this
  · have h2 : (fun u => β u ^ 2 * (2 * p u)) = fun u => 4 * (diffusionD a b c u * p u) := by
      funext v; rw [hβ v]; ring
    rw [h2]
    exact contDiff_const.mul hC1

/-! ### Integration by parts: (A.3) and (A.4) -/

namespace IsKolmogorovDensity

variable {α β p : ℝ → ℝ}

/-- The generator `Lf = f'α + ½f''β²` integrated against the density over a period vanishes:
`∫₀^π (f'(u)α(u) + ½f''(u)β(u)²) p(u) du = 0` for every `C²` `π`-periodic `f`
(paper.tex:L2376-2394, (A.3)–(A.4)). -/
theorem integral_generator_eq_zero (hp : IsKolmogorovDensity α β p)
    (hα : ContDiff ℝ 1 α) (hβ : ContDiff ℝ 2 β)
    (hαper : Periodic α π) (hβper : Periodic (fun u => β u ^ 2) π)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfper : Periodic f π) :
    ∫ u in (0)..π, (deriv f u * α u + (1 / 2) * deriv (deriv f) u * β u ^ 2) * p u = 0 := by
  obtain ⟨x, hC2, hode, hC1⟩ := hp.exists_regular
  have hpcont := hp.continuous
  have hpper := hp.periodic
  set G : ℝ → ℝ := fun v => β v ^ 2 * p v with hG
  set H : ℝ → ℝ := fun v => α v * p v - (1 / 2) * deriv G v with hH
  set S : Set ℝ := {u | ∀ n : ℤ, u ≠ x + n * π} with hS
  have hSopen : IsOpen S := isOpen_compl_lattice x
  -- regularity of the pieces
  have hf' : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hf'cont : Continuous (deriv f) := hf'.continuous
  have hf''cont : Continuous (deriv (deriv f)) := hf'.continuous_deriv_one
  have hGcont : Continuous G := hC1.continuous
  have hG'cont : Continuous (deriv G) := hC1.continuous_deriv_one
  have hGdiff : Differentiable ℝ G := hC1.differentiable one_ne_zero
  have hf'diff : Differentiable ℝ (deriv f) := hf'.differentiable one_ne_zero
  have hHcont : Continuous H := by
    simp only [hH]; fun_prop
  -- periodicity of the pieces
  have hf'per : Periodic (deriv f) π := hfper.deriv_periodic
  have hf''per : Periodic (deriv (deriv f)) π := hf'per.deriv_periodic
  have hβper' : ∀ u, β (u + π) ^ 2 = β u ^ 2 := fun u => hβper u
  have hGper : Periodic G π := fun u => by simp only [hG, hβper' u, hpper u]
  have hΦper : Periodic (fun u => (deriv f u * α u + (1 / 2) * deriv (deriv f) u * β u ^ 2) * p u)
      π := fun u => by
    simp only [hf'per u, hαper u, hf''per u, hpper u, hβper' u]
  -- the integrand is `½ (f'G)' + f' H` everywhere
  have hdecomp : ∀ u, (deriv f u * α u + (1 / 2) * deriv (deriv f) u * β u ^ 2) * p u =
      (1 / 2) * deriv (fun v => deriv f v * G v) u + deriv f u * H u := by
    intro u
    have hm : deriv (fun v => deriv f v * G v) u =
        deriv (deriv f) u * G u + deriv f u * deriv G u := deriv_mul (hf'diff u) (hGdiff u)
    rw [hm]
    simp only [hG, hH]
    ring
  -- `H` is constant on `(x, x + π)`
  have hI : Ioo x (x + π) ⊆ S := fun u hu => notMem_lattice_of_mem_Ioo hu
  have hpdiffS : DifferentiableOn ℝ p S := hC2.differentiableOn two_ne_zero
  have hG2 : ContDiffOn ℝ 2 G S := (hβ.pow 2).contDiffOn.mul hC2
  have hG'diffS : DifferentiableOn ℝ (deriv G) S :=
    (hG2.deriv_of_isOpen hSopen (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableOn
      one_ne_zero
  have hHdiff : DifferentiableOn ℝ H (Ioo x (x + π)) := by
    intro u hu
    have hu' := hI hu
    have h1 : DifferentiableAt ℝ (fun v => α v * p v) u :=
      (hα.differentiable one_ne_zero u).mul (hpdiffS.differentiableAt (hSopen.mem_nhds hu'))
    have h2 : DifferentiableAt ℝ (deriv G) u :=
      hG'diffS.differentiableAt (hSopen.mem_nhds hu')
    exact (h1.sub (h2.const_mul _)).differentiableWithinAt
  have hH' : (Ioo x (x + π)).EqOn (deriv H) 0 := by
    intro u hu
    have hu' := hI hu
    have h1 : DifferentiableAt ℝ (fun v => α v * p v) u :=
      (hα.differentiable one_ne_zero u).mul (hpdiffS.differentiableAt (hSopen.mem_nhds hu'))
    have h2 : DifferentiableAt ℝ (deriv G) u :=
      hG'diffS.differentiableAt (hSopen.mem_nhds hu')
    simp only [hH, Pi.zero_apply]
    have h3 : deriv (fun v => α v * p v - 1 / 2 * deriv G v) u =
        deriv (fun v => α v * p v) u - 1 / 2 * deriv (deriv G) u := by
      have := deriv_sub h1 (h2.const_mul (1 / 2 : ℝ))
      rw [deriv_const_mul _ h2] at this
      exact this
    rw [h3]
    have := hode u hu'
    linarith
  obtain ⟨K, hK⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo hHdiff hH'
  -- assemble
  rw [hΦper.intervalIntegral_zero_eq x]
  have hint1 : ∫ u in x..x + π, (1 / 2) * deriv (fun v => deriv f v * G v) u = 0 := by
    rw [intervalIntegral.integral_const_mul]
    have hcont : Continuous (deriv fun v => deriv f v * G v) := by
      have : (deriv fun v => deriv f v * G v) =
          fun v => deriv (deriv f) v * G v + deriv f v * deriv G v := by
        funext v; exact deriv_mul (hf'diff v) (hGdiff v)
      rw [this]; fun_prop
    rw [integral_deriv_eq_sub (f := fun v => deriv f v * G v)
      (fun v _ => (hf'diff v).mul (hGdiff v)) (hcont.intervalIntegrable _ _)]
    simp [hf'per x, hGper x]
  have hint2 : ∫ u in x..x + π, deriv f u * H u = 0 := by
    have hae : ∀ᵐ u ∂volume, u ∈ Ι x (x + π) → deriv f u * H u = deriv f u * K := by
      have h0 : ({x + π} : Set ℝ)ᶜ ∈ ae volume := compl_mem_ae_iff.mpr (measure_singleton _)
      filter_upwards [h0] with u hu hmem
      rw [uIoc_of_le (by linarith [pi_pos])] at hmem
      have hne : u ≠ x + π := by simpa using hu
      have hlt : u < x + π := lt_of_le_of_ne hmem.2 hne
      rw [hK u ⟨hmem.1, hlt⟩]
    rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_mul_const,
      integral_deriv_eq_sub (fun v _ => hf.differentiable two_ne_zero v)
        (hf'cont.intervalIntegrable _ _)]
    simp [hfper x]
  calc ∫ u in x..x + π, (deriv f u * α u + (1 / 2) * deriv (deriv f) u * β u ^ 2) * p u
      = ∫ u in x..x + π,
          ((1 / 2) * deriv (fun v => deriv f v * G v) u + deriv f u * H u) := by
        congr 1; funext u; exact hdecomp u
    _ = (∫ u in x..x + π, (1 / 2) * deriv (fun v => deriv f v * G v) u) +
          ∫ u in x..x + π, deriv f u * H u := by
        apply intervalIntegral.integral_add
        · have hcont : Continuous (deriv fun v => deriv f v * G v) := by
            have : (deriv fun v => deriv f v * G v) =
                fun v => deriv (deriv f) v * G v + deriv f v * deriv G v := by
              funext v; exact deriv_mul (hf'diff v) (hGdiff v)
            rw [this]; fun_prop
          exact (continuous_const.mul hcont).intervalIntegrable _ _
        · exact (hf'cont.mul hHcont).intervalIntegrable _ _
    _ = 0 := by rw [hint1, hint2, add_zero]

end IsKolmogorovDensity

end ComplexSLE.Internal

end
