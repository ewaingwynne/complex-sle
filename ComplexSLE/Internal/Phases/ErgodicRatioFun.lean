/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.ErgodicBirkhoff

/-!
# The cosine functional of a path observable (M7/D2, Lemma 3.6)

For the proof of Lemma 3.6 (paper.tex:L1430-1455) one needs the ergodic average
`(1/s) ∫₀ˢ cos 2θ̂_v dv` of the second additive functional of the polar chain. The integrals are
not measurable functionals of a general element of the observable space
`ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)` (product σ-algebra), so they are encoded through Riemann sums:

* `obsCos x r = Re (x₁ · exp (2i x₂(r)))`: for `x = Ξ_s = pathObsAt hU z s ω` this is
  `cos 2θ̂_{s + r}` (`obsCos_pathObsAt`);
* `rsumIv x n N` the `N`-th left Riemann sum of `r ↦ obsCos x r` over `[n, n + 1]`, and
  `cosIv x n` its `limsup` (a measurable function of `x`, `measurable_cosIv`);
* `cosLim x = limsup_N (1/N) ∑_{n<N} cosIv x n`, the Cesàro limit functional.

On the (a.s.) event on which `s ↦ θ̂_s` is continuous, `cosIv (Ξ_s) n` is the genuine integral
`∫_{s+n}^{s+n+1} cos 2θ̂_v dv` (`cosIv_pathObsAt`), the partial sums are
`C_{s+N} - C_s` with `C_t = ∫₀ᵗ cos 2θ̂` (`sum_cosIv_pathObsAt`), and, if `C_t / t → L` as
`t → ∞` along `ℝ≥0`, then `cosLim (Ξ_s) = L` for every `s` (`cosLim_pathObsAt`).
-/

@[expose] public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal

open Polar

/-- The cosine integrand of an observable: `Re (e^{2iθ̂_s} e^{2i(θ̂_{s+r} - θ̂_s)})`. -/
noncomputable def obsCos (x : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) (r : ℝ) : ℝ :=
  (x.1 * Complex.exp (2 * Complex.I * ((x.2.1 r.toNNReal : ℝ) : ℂ))).re

theorem measurable_obsCos (r : ℝ) : Measurable fun x : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => obsCos x r := by
  have h : Measurable fun x : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => x.2.1 r.toNNReal :=
    (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)
  unfold obsCos
  have h2 : Measurable fun x : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) =>
      x.1 * Complex.exp (2 * Complex.I * ((x.2.1 r.toNNReal : ℝ) : ℂ)) :=
    measurable_fst.mul (Complex.measurable_exp.comp
      (measurable_const.mul (Complex.measurable_ofReal.comp h)))
  exact Complex.measurable_re.comp h2

/-- The `N`-th left Riemann sum of `r ↦ obsCos x r` over `[n, n + 1]`. -/
noncomputable def rsumIv (x : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) (n N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, ((1 : ℝ) / N) * obsCos x ((n : ℝ) + (k : ℝ) / N)

/-- The integral of `obsCos x` over `[n, n + 1]`, encoded as the `limsup` of its Riemann sums. -/
noncomputable def cosIv (x : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) (n : ℕ) : ℝ :=
  limsup (fun N : ℕ => rsumIv x n N) atTop

/-- The sequence of unit-interval integrals. -/
noncomputable def cosSeq (x : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) : ℕ → ℝ := fun n => cosIv x n

/-- The Cesàro limit functional of the cosine integrals. -/
noncomputable def cosLim (x : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) : ℝ :=
  limsup (fun N : ℕ => (∑ n ∈ Finset.range N, cosIv x n) / (N : ℝ)) atTop

theorem measurable_rsumIv (n N : ℕ) : Measurable fun x => rsumIv x n N :=
  Finset.measurable_sum _ fun _ _ => measurable_const.mul (measurable_obsCos _)

theorem measurable_cosIv (n : ℕ) : Measurable fun x => cosIv x n :=
  Measurable.limsup fun N => measurable_rsumIv n N

theorem measurable_cosSeq : Measurable cosSeq :=
  measurable_pi_iff.2 fun n => measurable_cosIv n

theorem measurable_cosLim : Measurable cosLim :=
  Measurable.limsup fun _ =>
    (Finset.measurable_sum _ fun n _ => measurable_cosIv n).div_const _

section Obs

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ} (hU : IsSLEDriverAdapted a b c U P ℱ) {z : ℂ}

/-- For the path observable `Ξ_s`, `obsCos` is `cos 2θ̂_{s + r}`. -/
theorem obsCos_pathObsAt (s : ℝ≥0) (ω : Ω) (r : ℝ) :
    obsCos (pathObsAt hU z s ω) r = Real.cos (2 * thetaHat hU z (s + r.toNNReal) ω) := by
  simp only [obsCos, pathObsAt]
  rw [← Complex.exp_add]
  have : 2 * Complex.I * ((thetaHat hU z s ω : ℝ) : ℂ) +
      2 * Complex.I * ((thetaHat hU z (s + r.toNNReal) ω - thetaHat hU z s ω : ℝ) : ℂ) =
      ((2 * thetaHat hU z (s + r.toNNReal) ω : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

/-- The integrand `v ↦ cos 2θ̂_v` on the real line. -/
noncomputable def cosHatF (z : ℂ) (ω : Ω) (v : ℝ) : ℝ :=
  Real.cos (2 * thetaHat hU z v.toNNReal ω)

theorem continuous_cosHatF {ω : Ω}
    (hcont : Continuous fun s => thetaHat hU z s ω) : Continuous (cosHatF hU z ω) :=
  Real.continuous_cos.comp (continuous_const.mul (hcont.comp continuous_real_toNNReal))

/-- On a path with `θ̂` continuous, the Riemann sums of the cosine integrand of the observable
`Ξ_s` over `[n, n + 1]` converge to `∫_{s+n}^{s+n+1} cos 2θ̂_v dv`. -/
theorem tendsto_rsumIv_pathObsAt {ω : Ω} (hcont : Continuous fun s => thetaHat hU z s ω)
    (s : ℝ≥0) (n : ℕ) :
    Tendsto (fun N : ℕ => rsumIv (pathObsAt hU z s ω) n N) atTop
      (𝓝 (∫ v in ((s : ℝ) + n)..((s : ℝ) + n + 1), cosHatF hU z ω v)) := by
  set ψ : ℝ → ℝ := fun v => cosHatF hU z ω ((s : ℝ) + n + v) with hψ
  have hψc : Continuous ψ := (continuous_cosHatF hU hcont).comp (continuous_const.add continuous_id)
  have h := tendsto_riemannSum (φ := ψ) (t := 1) zero_le_one hψc.continuousOn
  have hint : (∫ v in (0 : ℝ)..1, ψ v) =
      ∫ v in ((s : ℝ) + n)..((s : ℝ) + n + 1), cosHatF hU z ω v := by
    simp only [hψ]
    rw [intervalIntegral.integral_comp_add_left (fun v => cosHatF hU z ω v) ((s : ℝ) + n)]
    simp
  rw [hint] at h
  refine h.congr fun N => ?_
  unfold rsumIv
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [obsCos_pathObsAt]
  simp only [hψ, cosHatF, mul_one]
  congr 4
  have h1 : (0 : ℝ) ≤ (n : ℝ) + (k : ℝ) / N := by positivity
  have h2 : (0 : ℝ) ≤ (s : ℝ) + n + (k : ℝ) / N := by positivity
  apply NNReal.coe_injective
  rw [NNReal.coe_add, Real.coe_toNNReal _ h1, Real.coe_toNNReal _ h2]
  ring

theorem cosIv_pathObsAt {ω : Ω} (hcont : Continuous fun s => thetaHat hU z s ω)
    (s : ℝ≥0) (n : ℕ) :
    cosIv (pathObsAt hU z s ω) n =
      ∫ v in ((s : ℝ) + n)..((s : ℝ) + n + 1), cosHatF hU z ω v :=
  (tendsto_rsumIv_pathObsAt hU hcont s n).limsup_eq

/-- Partial sums of the unit-interval cosine integrals of `Ξ_s`: `C_{s+N} - C_s`. -/
theorem sum_cosIv_pathObsAt {ω : Ω} (hcont : Continuous fun s => thetaHat hU z s ω)
    (s : ℝ≥0) (N : ℕ) :
    ∑ n ∈ Finset.range N, cosIv (pathObsAt hU z s ω) n =
      ∫ v in (s : ℝ)..((s : ℝ) + N), cosHatF hU z ω v := by
  have hc := continuous_cosHatF hU hcont
  simp only [cosIv_pathObsAt hU hcont s]
  have := intervalIntegral.sum_integral_adjacent_intervals (a := fun n : ℕ => (s : ℝ) + n)
    (f := fun v => cosHatF hU z ω v) (μ := volume) (n := N)
    (fun k _ => hc.intervalIntegrable _ _)
  simpa [add_assoc] using this

/-- The process `C_t = ∫₀ᵗ cos 2θ̂_v dv`. -/
noncomputable def cosInt (z : ℂ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  pathIntegral (fun v ω => Real.cos (2 * thetaHat hU z v ω)) t ω

theorem cosInt_eq {ω : Ω} (t : ℝ≥0) :
    cosInt hU z t ω = ∫ v in (0 : ℝ)..(t : ℝ), cosHatF hU z ω v := rfl

theorem abs_cosInt_sub_le {ω : Ω} (hcont : Continuous fun s => thetaHat hU z s ω) {r t : ℝ≥0}
    (hrt : r ≤ t) : |cosInt hU z t ω - cosInt hU z r ω| ≤ (t : ℝ) - r := by
  have hc := continuous_cosHatF hU hcont
  simp only [cosInt_eq]
  rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun v => cosHatF hU z ω v) (a := (r : ℝ)) (b := (t : ℝ)) (C := 1)
    fun v _ => by simpa [Real.norm_eq_abs, cosHatF] using Real.abs_cos_le_one _
  have hrt' : (r : ℝ) ≤ t := hrt
  simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hrt')] using this

theorem abs_cosInt_le {ω : Ω} (hcont : Continuous fun s => thetaHat hU z s ω) (t : ℝ≥0) :
    |cosInt hU z t ω| ≤ t := by
  have := abs_cosInt_sub_le hU hcont (zero_le : (0 : ℝ≥0) ≤ t)
  have h0 : cosInt hU z 0 ω = 0 := by simp [cosInt_eq]
  simpa [h0] using this

/-- **Cesàro limit of the observable after any time.** If `C_t / t → L` along `ℝ≥0` and `θ̂` is
continuous on the path, then `cosLim (Ξ_s) = L` for every `s`. -/
theorem cosLim_pathObsAt {ω : Ω} (hcont : Continuous fun s => thetaHat hU z s ω) {L : ℝ}
    (h : Tendsto (fun t : ℝ≥0 => cosInt hU z t ω / (t : ℝ)) atTop (𝓝 L)) (s : ℝ≥0) :
    cosLim (pathObsAt hU z s ω) = L := by
  unfold cosLim
  refine Tendsto.limsup_eq ?_
  have hsum : ∀ N : ℕ, ∑ n ∈ Finset.range N, cosIv (pathObsAt hU z s ω) n =
      cosInt hU z (s + N) ω - cosInt hU z s ω := fun N => by
    rw [sum_cosIv_pathObsAt hU hcont s N]
    have hc := continuous_cosHatF hU hcont
    simp only [cosInt_eq]
    rw [← intervalIntegral.integral_interval_sub_left (a := 0) (b := (s : ℝ) + N) (c := (s : ℝ))
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    simp
  have hn : Tendsto (fun n : ℕ => s + (n : ℝ≥0)) atTop atTop :=
    tendsto_atTop_mono (fun n => le_add_self) tendsto_natCast_atTop_atTop
  have h1 := h.comp hn
  have h2 : Tendsto (fun n : ℕ => ((s + (n : ℝ≥0) : ℝ≥0) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (s : ℝ)).add_const 1
    simp only [zero_add] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    push_cast
    field_simp
  have h3 : Tendsto (fun n : ℕ => cosInt hU z s ω / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have h4 := (h1.mul h2).sub h3
  simp only [mul_one, sub_zero] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < ((s + (n : ℝ≥0) : ℝ≥0) : ℝ) := by
    push_cast
    positivity
  simp only [Function.comp, hsum]
  field_simp

end Obs

end ComplexSLE.Internal

end
