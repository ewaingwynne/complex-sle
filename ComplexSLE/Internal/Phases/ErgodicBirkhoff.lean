/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.ErgodicStat

/-!
# Birkhoff for `log |f̂_t(𝐳)|` (M7/A5a, Lemma 3.4, first half)

On `(Ω × ℝ, P ⊗ ν)`, `ν = p(u) 1_{[0,2π]}(u) du`, `Y_t = log |f̂_t(e^{iu})|`
(`logFHat`), `ξ_n = Y_{n+1} - Y_n`:

* `exists_birkhoff_logFHat`: there is an integrable `L` with `∫ L = (I) = integralI a b c p` and
  `Y_n / n → L` almost surely. (`ξ_0` is integrable with mean `(I)` by
  `integrable_integral_logFHat`, `(ξ_n)` is stationary by `xiInc_stationary`, and the classical
  input `birkhoff_stationary` applies; `∑_{k<n} ξ_k = Y_n - Y_0` and `Y_0 = 0` a.s.)
* `exists_birkhoff_logFHat_real`: the same with, in addition, the limit along *real* times,
  fibrewise: for `ν`-a.e. `u`, almost surely `Y_s / s → L(ω, u)` as `s → ∞` in `ℝ≥0`.
* `exists_birkhoff_logFHat_ae`: the same with the real-time limit `P ⊗ ν`-almost surely (product
  form), through a measurable proxy event on the rational times (the paths `s ↦ Y_s` are
  continuous on `goodSet`).

Real times are reduced to integer times by `tendsto_div_of_floor`: `Y = D + M`
(`ae_log_norm_fHat_eq`), `D` is `C_ν`-Lipschitz and `M_s / s → 0` almost surely
(`fiber_sigmaLogMart`, i.e. the bounded-bracket martingale `M` of `BoundedBracket.lean`).

Uses the classical input `birkhoff_stationary` (E7) and everything used by `ErgodicStat.lean`.
-/

@[expose] public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal

open Polar

/-! ### From integer to real times (deterministic) -/

theorem tendsto_nat_floor_div_nnreal :
    Tendsto (fun s : ℝ≥0 => (⌊s⌋₊ : ℝ) / (s : ℝ)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun s : ℝ≥0 => 1 - 1 / (s : ℝ)) atTop (𝓝 1) := by
    have : Tendsto (fun s : ℝ≥0 => (s : ℝ)) atTop atTop := NNReal.tendsto_coe_atTop.2 tendsto_id
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (this.inv_tendsto_atTop.const_mul 1)
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ≥0)] with s hs
    have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have hpos : (0 : ℝ) < s := by linarith
    rw [one_sub_div hpos.ne', div_le_div_iff_of_pos_right hpos]
    have : (s : ℝ) < ⌊s⌋₊ + 1 := by exact_mod_cast Nat.lt_floor_add_one s
    linarith
  · filter_upwards [eventually_ge_atTop (1 : ℝ≥0)] with s hs
    have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have hpos : (0 : ℝ) < s := by linarith
    rw [div_le_one hpos]
    exact_mod_cast Nat.floor_le (zero_le : (0 : ℝ≥0) ≤ s)

/-- Real times from integer times. -/
theorem tendsto_div_of_floor {Y D M : ℝ≥0 → ℝ} {C L : ℝ} (hY : ∀ s, Y s = D s + M s)
    (hD : ∀ s : ℝ≥0, |D s - D (⌊s⌋₊ : ℝ≥0)| ≤ C)
    (hM : Tendsto (fun s : ℝ≥0 => M s / s) atTop (𝓝 0))
    (hn : Tendsto (fun n : ℕ => Y n / n) atTop (𝓝 L)) :
    Tendsto (fun s : ℝ≥0 => Y s / s) atTop (𝓝 L) := by
  have hfl : Tendsto (fun s : ℝ≥0 => ⌊s⌋₊) atTop atTop := tendsto_nat_floor_atTop
  have hu := tendsto_nat_floor_div_nnreal
  have hT1 : Tendsto (fun s : ℝ≥0 => (Y (⌊s⌋₊ : ℝ≥0) / (⌊s⌋₊ : ℝ)) * ((⌊s⌋₊ : ℝ) / s)) atTop
      (𝓝 (L * 1)) := (hn.comp hfl).mul hu
  have hMn : Tendsto (fun n : ℕ => M (n : ℝ≥0) / ((n : ℝ≥0) : ℝ)) atTop (𝓝 0) :=
    hM.comp tendsto_natCast_atTop_atTop
  have hT4 : Tendsto (fun s : ℝ≥0 => (M (⌊s⌋₊ : ℝ≥0) / (⌊s⌋₊ : ℝ)) * ((⌊s⌋₊ : ℝ) / s)) atTop
      (𝓝 (0 * 1)) := by
    have := (hMn.comp hfl).mul hu
    simpa using this
  have hT2 : Tendsto (fun s : ℝ≥0 => (D s - D (⌊s⌋₊ : ℝ≥0)) / (s : ℝ)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun s : ℝ≥0 => C / (s : ℝ)) atTop (𝓝 0) :=
      (NNReal.tendsto_coe_atTop.2 tendsto_id).const_div_atTop C
    refine squeeze_zero_norm' ?_ hinv
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with s hs
    have hpos : (0 : ℝ) < s := by exact_mod_cast hs
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos]
    exact div_le_div_of_nonneg_right (hD s) hpos.le
  have hsum := ((hT1.add hT2).add hM).sub hT4
  simp only [mul_one, add_zero, sub_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ≥0)] with s hs
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hpos : (0 : ℝ) < s := by linarith
  have hn1 : 1 ≤ ⌊s⌋₊ := Nat.le_floor (by simpa using hs)
  have hnpos : (0 : ℝ) < ⌊s⌋₊ := by exact_mod_cast hn1
  have e1 := hY s
  have e2 := hY (⌊s⌋₊ : ℝ≥0)
  rw [e1]
  field_simp
  rw [e2]
  ring

/-- A function continuous on `[1, ∞)` whose values at the rationals `≥ N` are eventually within
`ε` of `ℓ` (for every rational `ε`) tends to `ℓ`. -/
theorem tendsto_of_forall_rat {g : ℝ → ℝ} {ℓ : ℝ} (hg : ContinuousOn g (Ici 1))
    (h : ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧ ∀ r : ℚ, (N : ℝ) ≤ r → |g r - ℓ| ≤ ε) :
    Tendsto g atTop (𝓝 ℓ) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨ε, hε0, hεδ⟩ := exists_rat_btwn hδ
  obtain ⟨N, hN1, hN⟩ := h ε (by exact_mod_cast hε0)
  refine ⟨N, fun x hx => ?_⟩
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hcont : Continuous fun x : ℝ => |g (max x N) - ℓ| := by
    exact continuous_abs.comp ((hg.comp_continuous (continuous_id.max continuous_const)
      (fun x => le_trans hN1' (le_max_right _ _))).sub continuous_const)
  have hall : ∀ y : ℝ, |g (max y N) - ℓ| ≤ ε := fun y => by
    refine Rat.denseRange_cast.induction_on y (isClosed_le hcont continuous_const) fun r => ?_
    rcases le_total (N : ℝ) r with hr | hr
    · rw [max_eq_left hr]; exact hN r hr
    · rw [max_eq_right hr]
      have := hN (N : ℚ) (by simp)
      simpa using this
  have := hall x
  rw [max_eq_left hx] at this
  rw [Real.dist_eq]
  exact lt_of_le_of_lt this hεδ

section Birkhoff

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

theorem ae_logFHat_zero [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ)
    (ha : 0 < a) (hc : c ^ 2 ≤ a * b) {ν : Measure ℝ} [SFinite ν] :
    ∀ᵐ q ∂(P.prod ν), logFHat hU 0 q = 0 := by
  refine ae_prod_of_forall_ae (S := {q | logFHat hU 0 q = 0})
    (measurableSet_eq_fun (measurable_logFHat hU 0) measurable_const) fun u => ?_
  filter_upwards [ae_log_norm_fHat_eq hU ha hc (norm_unitPt u)] with ω hω
  show logFHat hU 0 (ω, u) = 0
  simp only [logFHat]
  rw [hω 0, sigmaLogMart_zero]
  simp [pathIntegral]

/-- **Birkhoff for `log |f̂|`** (M7/A5a). There is an integrable `L` on `(Ω × ℝ, P ⊗ ν)` with
`∫ L = (I)` and `log |f̂_n(e^{iu})| / n → L` almost surely along the integers. -/
theorem exists_birkhoff_logFHat [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) :
    ∃ L : Ω × ℝ → ℝ, Integrable L (P.prod (admissibleMeasure p)) ∧
      ∫ q, L q ∂(P.prod (admissibleMeasure p)) = integralI a b c p ∧
      ∀ᵐ q ∂(P.prod (admissibleMeasure p)),
        Tendsto (fun n : ℕ => logFHat hU (n : ℝ≥0) q / n) atTop (𝓝 (L q)) := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  obtain ⟨h1, e1⟩ := integrable_integral_logFHat hU ha hb hc hp 1
  obtain ⟨h0, e0⟩ := integrable_integral_logFHat hU ha hb hc hp 0
  have hint : Integrable (xiInc hU 0) (P.prod (admissibleMeasure p)) := by
    have e : xiInc hU 0 = logFHat hU 1 - logFHat hU 0 := by
      funext q; simp [xiInc]
    rw [e]; exact h1.sub h0
  have hmean : ∫ q, xiInc hU 0 q ∂(P.prod (admissibleMeasure p)) = integralI a b c p := by
    simp only [xiInc, Nat.cast_zero, zero_add]
    rw [integral_sub h1 h0, e1, e0]
    simp
  obtain ⟨L, hLint, hLmean, hLlim⟩ := External.birkhoff_stationary
    (P := P.prod (admissibleMeasure p)) (xiInc hU) (measurable_xiInc hU)
    (fun k => xiInc_stationary hU ha hb hc hp k) hint
  refine ⟨L, hLint, hLmean.trans hmean, ?_⟩
  filter_upwards [hLlim, ae_logFHat_zero hU ha hc (ν := admissibleMeasure p)] with q hq hq0
  refine hq.congr fun n => ?_
  have : ∑ k ∈ Finset.range n, xiInc hU k q = logFHat hU (n : ℝ≥0) q - logFHat hU 0 q := by
    have := Finset.sum_range_sub (fun k : ℕ => logFHat hU (k : ℝ≥0) q) n
    simpa [xiInc, Nat.cast_succ] using this
  rw [this, hq0, sub_zero]

/-- **Birkhoff for `log |f̂|`, real times** (M7/A5a). In addition to
`exists_birkhoff_logFHat`: for `ν`-a.e. `u`, almost surely
`log |f̂_s(e^{iu})| / s → L(ω, u)` as `s → ∞` along `ℝ≥0`. -/
theorem exists_birkhoff_logFHat_real [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) :
    ∃ L : Ω × ℝ → ℝ, Integrable L (P.prod (admissibleMeasure p)) ∧
      ∫ q, L q ∂(P.prod (admissibleMeasure p)) = integralI a b c p ∧
      (∀ᵐ q ∂(P.prod (admissibleMeasure p)),
        Tendsto (fun n : ℕ => logFHat hU (n : ℝ≥0) q / n) atTop (𝓝 (L q))) ∧
      ∀ᵐ u ∂(admissibleMeasure p), ∀ᵐ ω ∂P,
        Tendsto (fun s : ℝ≥0 => logFHat hU s (ω, u) / s) atTop (𝓝 (L (ω, u))) := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  obtain ⟨L, hLint, hLmean, hLlim⟩ := exists_birkhoff_logFHat hU ha hb hc hp
  refine ⟨L, hLint, hLmean, hLlim, ?_⟩
  filter_upwards [ae_ae_of_ae_prod_snd hLlim] with u hu
  have hz := unitPt_ne_zero u
  filter_upwards [hu, ae_log_norm_fHat_eq hU ha hc (norm_unitPt u),
    (fiber_sigmaLogMart hU ha hb hc hz).2.2.2] with ω h1 h2 h3
  refine tendsto_div_of_floor (D := fun s => pathIntegral
    (fun v ω => nu a b c (thetaHat hU (unitPt u) v ω)) s ω)
    (M := fun s => sigmaLogMart hU (unitPt u) s ω) (C := |2 - a / 2 + b / 2| + |c|)
    (fun s => h2 s) (fun s => ?_) h3 h1
  have hs : ((⌊s⌋₊ : ℝ≥0) : ℝ) ≤ s := by exact_mod_cast Nat.floor_le (zero_le : (0 : ℝ≥0) ≤ s)
  have hs1 : (s : ℝ) - ((⌊s⌋₊ : ℝ≥0) : ℝ) ≤ 1 := by
    have : (s : ℝ) < ⌊s⌋₊ + 1 := by exact_mod_cast Nat.lt_floor_add_one s
    simp only [NNReal.coe_natCast]
    linarith
  have hC : 0 ≤ |2 - a / 2 + b / 2| + |c| := by positivity
  calc |pathIntegral (fun v ω => nu a b c (thetaHat hU (unitPt u) v ω)) s ω -
        pathIntegral (fun v ω => nu a b c (thetaHat hU (unitPt u) v ω)) (⌊s⌋₊ : ℝ≥0) ω|
      ≤ (|2 - a / 2 + b / 2| + |c|) * ((s : ℝ) - ((⌊s⌋₊ : ℝ≥0) : ℝ)) :=
        abs_pathIntegral_comp_thetaHat_sub_le hU (continuous_nu a b c).measurable
          (fun x => abs_nu_le a b c x) ω (by exact_mod_cast Nat.floor_le (zero_le : (0 : ℝ≥0) ≤ s))
    _ ≤ (|2 - a / 2 + b / 2| + |c|) * 1 := mul_le_mul_of_nonneg_left hs1 hC
    _ = _ := mul_one _

/-- **Birkhoff for `log |f̂|`, real times, product form** (M7/A5a).
There is an integrable `L` on `(Ω × ℝ, P ⊗ ν)` with `∫ L = (I)` such that `P ⊗ ν`-almost surely
`log |f̂_s(e^{iu})| / s → L` as `s → ∞` along `ℝ≥0` (and along the integers). The exceptional
set is controlled through the measurable event on which the (continuous, on `goodSet`) paths
`s ↦ Y_s` have the limit along the rational times. -/
theorem exists_birkhoff_logFHat_ae [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) :
    ∃ L : Ω × ℝ → ℝ, Integrable L (P.prod (admissibleMeasure p)) ∧
      ∫ q, L q ∂(P.prod (admissibleMeasure p)) = integralI a b c p ∧
      (∀ᵐ q ∂(P.prod (admissibleMeasure p)),
        Tendsto (fun n : ℕ => logFHat hU (n : ℝ≥0) q / n) atTop (𝓝 (L q))) ∧
      ∀ᵐ q ∂(P.prod (admissibleMeasure p)),
        Tendsto (fun s : ℝ≥0 => logFHat hU s q / s) atTop (𝓝 (L q)) := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  obtain ⟨L, hLint, hLmean, hLn, hLfib⟩ := exists_birkhoff_logFHat_real hU ha hb hc hp
  refine ⟨L, hLint, hLmean, hLn, ?_⟩
  -- a measurable representative of `L`
  set L' : Ω × ℝ → ℝ := hLint.1.mk L with hL'
  have hL'm : Measurable L' := hLint.1.stronglyMeasurable_mk.measurable
  have hLL' : L =ᵐ[P.prod (admissibleMeasure p)] L' := hLint.1.ae_eq_mk
  -- the measurable proxy event
  set S : Set (Ω × ℝ) := {q | ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧ ∀ r : ℚ, (N : ℝ) ≤ r →
    |logFHat hU (r : ℝ).toNNReal q / (r : ℝ) - L' q| ≤ ε} with hSdef
  have hS : MeasurableSet S := by
    have e : S = ⋂ ε : ℚ, ⋂ (_ : 0 < ε), ⋃ N : ℕ, ⋃ (_ : 1 ≤ N), ⋂ r : ℚ, ⋂ (_ : (N : ℝ) ≤ r),
        {q | |logFHat hU (r : ℝ).toNNReal q / (r : ℝ) - L' q| ≤ (ε : ℝ)} := by
      ext q; simp [hSdef]
    rw [e]
    refine MeasurableSet.iInter fun ε => MeasurableSet.iInter fun _ => MeasurableSet.iUnion
      fun N => MeasurableSet.iUnion fun _ => MeasurableSet.iInter fun r =>
        MeasurableSet.iInter fun _ => ?_
    exact measurableSet_le (continuous_abs.measurable.comp
      (((measurable_logFHat hU _).div_const _).sub hL'm)) measurable_const
  have hSae : ∀ᵐ u ∂(admissibleMeasure p), ∀ᵐ ω ∂P, (ω, u) ∈ S := by
    filter_upwards [hLfib, ae_ae_of_ae_prod_snd hLL'] with u hu hLu
    filter_upwards [hu, hLu] with ω h1 h2 ε hε
    rw [h2] at h1
    obtain ⟨S0, hS0⟩ := Metric.tendsto_atTop.1 h1 (ε : ℝ) (by exact_mod_cast hε)
    refine ⟨max 1 ⌈(S0 : ℝ)⌉₊, le_max_left _ _, fun r hr => ?_⟩
    have hr0 : (0 : ℝ) ≤ r := le_trans (by positivity) hr
    have hS0r : S0 ≤ (r : ℝ).toNNReal := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0]
      calc (S0 : ℝ) ≤ ⌈(S0 : ℝ)⌉₊ := Nat.le_ceil _
        _ ≤ max 1 ⌈(S0 : ℝ)⌉₊ := by exact_mod_cast le_max_right _ _
        _ ≤ r := hr
    have := hS0 _ hS0r
    rw [Real.dist_eq, Real.coe_toNNReal _ hr0] at this
    exact this.le
  have hSprod := ae_prod_of_ae_ae_snd hS hSae
  filter_upwards [hSprod, ae_mem_goodSet hU ha hc (ν := admissibleMeasure p), hLL']
    with q hqS hqG hqL
  have hg : ContinuousOn (fun x : ℝ => logFHat hU x.toNNReal q / x) (Set.Ici 1) :=
    (((continuous_logFHat_time hU hqG).comp continuous_real_toNNReal).continuousOn).div
      continuousOn_id fun x hx => by
        have : (1 : ℝ) ≤ x := hx
        exact ne_of_gt (by linarith)
  have h := tendsto_of_forall_rat hg (ℓ := L' q) fun ε hε => by
    obtain ⟨N, hN1, hN⟩ := hqS ε hε
    exact ⟨N, hN1, hN⟩
  have h' : Tendsto (fun s : ℝ≥0 => logFHat hU s q / s) atTop (𝓝 (L' q)) := by
    have := h.comp (NNReal.tendsto_coe_atTop.2 tendsto_id)
    refine this.congr fun s => ?_
    simp [Function.comp]
  rwa [hqL]

end Birkhoff

end ComplexSLE.Internal

end
