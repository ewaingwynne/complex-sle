/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
Ported from leobon12/lean-formalizations @31e7483,
QuantumZipper/Proofs/Complex/KoebeBasic.lean;
trimmed and adapted to Lean v4.36 and the module system.
-/
module

public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Univalent maps: basic tools (EXT-CA, node A2 and helpers for the K nodes)

* `exists_log_of_ne_zero_ball`, `exists_sq_eq_of_ne_zero_ball`: holomorphic logarithms and square
  roots of nonvanishing holomorphic functions on a disk (from mathlib's continuous branches,
  `Complex.exists_continuousOn_eqOn_exp_comp`).
* `deriv_ne_zero_of_injOn`: an injective holomorphic map on an open set has nonvanishing
  derivative (Pommerenke, *Univalent Functions* (1975), §1.1; Ahlfors, *Complex Analysis*,
  Ch. 4, Thm. 11 corollary). Proof by local `n`-th roots and the inverse function theorem.
* `isOpen_image_of_injOn`: injective holomorphic maps are open.
-/

public section

open Set Metric Filter Complex
open scoped Topology Real

namespace QuantumZipper.CA.Koebe

/-- An open disk in `ℂ` is simply connected. -/
theorem isSimplyConnected_ball {c : ℂ} {r : ℝ} (hr : 0 < r) : IsSimplyConnected (ball c r) := by
  have := (convex_ball c r).contractibleSpace (nonempty_ball.2 hr)
  exact SimplyConnectedSpace.ofContractible _

/-- A nonvanishing holomorphic function on a disk has a holomorphic logarithm. -/
theorem exists_log_of_ne_zero_ball {h : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hd : DifferentiableOn ℂ h (ball c r)) (h0 : ∀ z ∈ ball c r, h z ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (ball c r) ∧ ∀ z ∈ ball c r, exp (L z) = h z := by
  rcases le_or_gt r 0 with hr | hr
  · refine ⟨0, ?_, ?_⟩ <;> simp [Metric.ball_eq_empty.2 hr]
  obtain ⟨L, hLc, hL⟩ := exists_continuousOn_eqOn_exp_comp (isSimplyConnected_ball (c := c) hr)
    isOpen_ball hd.continuousOn (fun ⟨z, hz, hz0⟩ => h0 z hz hz0)
  refine ⟨L, fun z hz => ?_, fun z hz => hL hz⟩
  have hU : ball c r ∈ 𝓝 z := isOpen_ball.mem_nhds hz
  have hLz : ContinuousAt L z := hLc.continuousAt hU
  have hev : L =ᶠ[𝓝 z] fun w => L z + log (h w / h z) := by
    filter_upwards [hLz.eventually (Metric.ball_mem_nhds (L z) Real.pi_pos), hU] with w hw hwU
    have hq : h w / h z = exp (L w - L z) := by
      rw [exp_sub]
      have e1 : exp (L w) = h w := hL hwU
      have e2 : exp (L z) = h z := hL hz
      rw [e1, e2]
    rw [Complex.dist_eq] at hw
    have him := abs_lt.1 (lt_of_le_of_lt (Complex.abs_im_le_norm (L w - L z)) hw)
    rw [hq, log_exp (by linarith [him.1]) (by linarith [him.2])]
    ring
  have hdiff : DifferentiableAt ℂ (fun w => L z + log (h w / h z)) z := by
    apply DifferentiableAt.const_add
    apply DifferentiableAt.clog ((hd.differentiableAt hU).div_const _)
    simp [div_self (h0 z hz)]
  exact (hdiff.congr_of_eventuallyEq hev).differentiableWithinAt

/-- A nonvanishing holomorphic function on a disk has a holomorphic square root. -/
theorem exists_sq_eq_of_ne_zero_ball {h : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hd : DifferentiableOn ℂ h (ball c r)) (h0 : ∀ z ∈ ball c r, h z ≠ 0) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball c r) ∧ ∀ z ∈ ball c r, G z ^ 2 = h z := by
  obtain ⟨L, hLd, hL⟩ := exists_log_of_ne_zero_ball hd h0
  refine ⟨fun z => exp (L z / 2), fun z hz => ?_, fun z hz => ?_⟩
  · exact ((hLd z hz).div_const 2).cexp
  · rw [← hL z hz, ← exp_nat_mul]
    congr 1
    push_cast
    ring

/-- An injective holomorphic map on an open set has nonvanishing derivative. -/
theorem deriv_ne_zero_of_injOn {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hinj : InjOn f U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    deriv f z₀ ≠ 0 := by
  have han : AnalyticAt ℂ (fun z => f z - f z₀) z₀ :=
    ((hd.analyticOnNhd hU) z₀ hz₀).sub analyticAt_const
  have hnot : ¬∀ᶠ z in 𝓝 z₀, f z - f z₀ = 0 := by
    intro hev
    have hF : ∀ᶠ z in 𝓝[≠] z₀, False := by
      filter_upwards [nhdsWithin_le_nhds (hev.and (hU.mem_nhds hz₀)), self_mem_nhdsWithin]
        with z h1 h3
      exact h3 (hinj h1.2 hz₀ (sub_eq_zero.1 h1.1))
    obtain ⟨_, h⟩ := hF.exists
    exact h
  obtain ⟨n, g, hg, hg0, hfg⟩ := han.exists_eventuallyEq_pow_smul_ne_zero_iff.2 hnot
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · have := hfg.self_of_nhds
      simp only [sub_self, pow_zero, one_smul] at this
      exact absurd this.symm hg0
    · have hderiv : HasDerivAt (fun z => f z₀ + (z - z₀) * g z) (g z₀) z₀ := by
        have := ((hasDerivAt_id z₀).sub_const z₀).mul hg.differentiableAt.hasDerivAt
        simpa using this.const_add (f z₀)
      have : HasDerivAt f (g z₀) z₀ := hderiv.congr_of_eventuallyEq (by
        filter_upwards [hfg] with z hz
        simp only [pow_one, smul_eq_mul] at hz
        linear_combination hz)
      rw [this.deriv]
      exact hg0
  · exfalso
    have hE : ∀ᶠ z in 𝓝 z₀, z ∈ U ∧ AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
        f z - f z₀ = (z - z₀) ^ n • g z :=
      (show ∀ᶠ z in 𝓝 z₀, z ∈ U from hU.mem_nhds hz₀).and (hg.eventually_analyticAt.and
        ((hg.continuousAt.eventually_ne hg0).and hfg))
    obtain ⟨ε, hε, hεE⟩ := Metric.eventually_nhds_iff_ball.1 hE
    obtain ⟨L, hLd, hL⟩ := exists_log_of_ne_zero_ball (c := z₀) (r := ε) (h := g)
      (fun z hz => (hεE z hz).2.1.differentiableAt.differentiableWithinAt)
      (fun z hz => (hεE z hz).2.2.1)
    set φ : ℂ → ℂ := fun z => (z - z₀) * exp (L z / n) with hφ
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hφpow : ∀ z ∈ ball z₀ ε, φ z ^ n = f z - f z₀ := by
      intro z hz
      rw [(hεE z hz).2.2.2, smul_eq_mul, ← hL z hz, hφ, mul_pow, ← exp_nat_mul,
        mul_div_cancel₀ _ hn0]
    have hz₀B : z₀ ∈ ball z₀ ε := mem_ball_self hε
    have hLz : DifferentiableAt ℂ L z₀ := hLd.differentiableAt (isOpen_ball.mem_nhds hz₀B)
    have hφd : DifferentiableOn ℂ φ (ball z₀ ε) := fun z hz =>
      (((differentiableAt_id.sub_const z₀).mul
        ((hLd.differentiableAt (isOpen_ball.mem_nhds hz)).div_const _).cexp)).differentiableWithinAt
    have hφder : HasDerivAt φ (exp (L z₀ / n)) z₀ := by
      have h' := ((hasDerivAt_id z₀).sub_const z₀).mul ((hLz.hasDerivAt.div_const (n : ℂ)).cexp)
      simp only [id, sub_self, zero_mul, one_mul, add_zero] at h'
      exact h'
    have hφstrict : HasStrictDerivAt φ (exp (L z₀ / n)) z₀ := by
      have := ((hφd.analyticOnNhd isOpen_ball) z₀ hz₀B).hasStrictDerivAt
      rwa [hφder.deriv] at this
    have hmap := hφstrict.map_nhds_eq (exp_ne_zero _)
    have hφ0 : φ z₀ = 0 := by simp [hφ]
    have himg : φ '' ball z₀ ε ∈ 𝓝 (0 : ℂ) := by
      rw [← hφ0, ← hmap]
      exact image_mem_map (isOpen_ball.mem_nhds hz₀B)
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 himg
    set ω : ℂ := exp (2 * π * I / n)
    have hω : IsPrimitiveRoot ω n := isPrimitiveRoot_exp n (by omega)
    have hωn : ‖ω‖ = 1 := hω.norm'_eq_one (by omega)
    set ζ : ℂ := ((δ / 2 : ℝ) : ℂ)
    have hζ : ‖ζ‖ = δ / 2 := by
      simp only [ζ, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_pos (by linarith)
    have h1 : ζ ∈ ball (0 : ℂ) δ := by
      rw [mem_ball, dist_zero_right, hζ]; linarith
    have h2 : ω * ζ ∈ ball (0 : ℂ) δ := by
      rw [mem_ball, dist_zero_right, norm_mul, hωn, one_mul, hζ]; linarith
    obtain ⟨z₁, hz₁, e₁⟩ := hδsub h1
    obtain ⟨z₂, hz₂, e₂⟩ := hδsub h2
    have hf : f z₁ = f z₂ := by
      have a1 := hφpow z₁ hz₁
      have a2 := hφpow z₂ hz₂
      rw [e₁] at a1
      rw [e₂, mul_pow, hω.pow_eq_one, one_mul] at a2
      linear_combination a2 - a1
    have hzz := hinj (hεE z₁ hz₁).1 (hεE z₂ hz₂).1 hf
    rw [hzz, e₂] at e₁
    have hζ0 : ζ ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hζ; linarith
    have : ω = 1 := by
      have := mul_right_cancel₀ hζ0 (e₁.trans (one_mul ζ).symm)
      exact this
    exact hω.ne_one (by omega) this

/-- Injective holomorphic maps on open sets are open. -/
theorem isOpen_image_of_injOn {f : ℂ → ℂ} {U V : Set ℂ} (hU : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hinj : InjOn f U) (hVU : V ⊆ U) (hV : IsOpen V) :
    IsOpen (f '' V) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨z, hz, rfl⟩
  have hf : HasStrictDerivAt f (deriv f z) z :=
    ((hd.analyticOnNhd hU) z (hVU hz)).hasStrictDerivAt
  rw [← hf.map_nhds_eq (deriv_ne_zero_of_injOn hU hd hinj (hVU hz))]
  exact image_mem_map (hV.mem_nhds hz)

end QuantumZipper.CA.Koebe
