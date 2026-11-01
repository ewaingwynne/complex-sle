/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.ErgodicRatioFun

/-!
# Birkhoff for `∫₀ˢ cos 2θ̂_v dv` (M7/D2, Lemma 3.7)

On `(Ω × ℝ, P ⊗ ν)`, `ν = p(u) 1_{[0,2π]}(u) du`, with `C_t(ω, u) = ∫₀ᵗ cos 2θ̂_v(e^{iu}) dv`
(`cosInt`) and the unit-interval increments `η_n = ∫_n^{n+1} cos 2θ̂_v dv`, encoded as the
measurable functional `cosIv (Ξ_n) 0` of the path observable (`etaSeq`):

* `etaSeq_stationary`: `(η_{n+k})_n` and `(η_n)_n` have the same law on `ℕ → ℝ`
  (`(η_{n+k})_n = cosSeq (Ξ_k)` and the law of `Ξ_k` does not depend on `k`, `map_pathObs_eq_zero`,
  modulo `hMO : MarkovOneDim`);
* `integral_etaSeq_zero`: `E η_0 = ∫ cos(2u) dν` (one-time stationarity of `e^{2iθ̂}`; Riemann sums
  and dominated convergence);
* `exists_birkhoff_cosInt`: there is an integrable `L` with `∫ L = ∫ cos(2u) dν` such that
  `P ⊗ ν`-a.s. `C_s / s → L` as `s → ∞` along `ℝ≥0` (EXTERNAL `birkhoff_stationary`; the real-time
  limit follows from the integer-time one since `|C_s - C_⌊s⌋| ≤ 1`, `tendsto_div_of_floor`).

Consumes the EXTERNAL `birkhoff_stationary` and everything consumed by `ErgodicStat.lean`.
-/

@[expose] public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal

open Polar

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-- The mean `∫ cos(2u) dν` of the cosine of the stationary angle. -/
noncomputable def cosMean (p : ℝ → ℝ) : ℝ := ∫ u, Real.cos (2 * u) ∂(admissibleMeasure p)

/-- `C_t(ω, u) = ∫₀ᵗ cos 2θ̂_v(e^{iu}) dv`. -/
noncomputable def cosIntU (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) (q : Ω × ℝ) : ℝ :=
  cosInt hU (unitPt q.2) t q.1

/-- The unit-interval increments `η_n = ∫_n^{n+1} cos 2θ̂_v dv` (via the observable). -/
noncomputable def etaSeq (hU : IsSLEDriverAdapted a b c U P ℱ) (n : ℕ) (q : Ω × ℝ) : ℝ :=
  cosIv (pathObs hU (n : ℝ≥0) q) 0

theorem measurable_etaSeq (hU : IsSLEDriverAdapted a b c U P ℱ) (n : ℕ) :
    Measurable (etaSeq hU n) :=
  (measurable_cosIv 0).comp (measurable_pathObs hU _)

/-- Shifting the time of the observable by `n` shifts the Riemann sums. -/
theorem rsumIv_pathObsAt_add (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) (s : ℝ≥0) (n N : ℕ)
    (ω : Ω) :
    rsumIv (pathObsAt hU z (s + (n : ℝ≥0)) ω) 0 N = rsumIv (pathObsAt hU z s ω) n N := by
  unfold rsumIv
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [obsCos_pathObsAt, obsCos_pathObsAt]
  congr 4
  have h1 : (0 : ℝ) ≤ ((0 : ℕ) : ℝ) + (k : ℝ) / N := by positivity
  have h2 : (0 : ℝ) ≤ (n : ℝ) + (k : ℝ) / N := by positivity
  apply NNReal.coe_injective
  simp only [NNReal.coe_add, Real.coe_toNNReal _ h1, Real.coe_toNNReal _ h2]
  push_cast
  ring

theorem cosIv_pathObsAt_add (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) (s : ℝ≥0) (n : ℕ)
    (ω : Ω) :
    cosIv (pathObsAt hU z (s + (n : ℝ≥0)) ω) 0 = cosIv (pathObsAt hU z s ω) n := by
  unfold cosIv
  simp only [rsumIv_pathObsAt_add]

theorem etaSeq_add (hU : IsSLEDriverAdapted a b c U P ℱ) (n k : ℕ) (q : Ω × ℝ) :
    etaSeq hU (n + k) q = cosSeq (pathObs hU (k : ℝ≥0) q) n := by
  unfold etaSeq cosSeq pathObs
  rw [show (((n + k : ℕ)) : ℝ≥0) = (k : ℝ≥0) + (n : ℝ≥0) by push_cast; ring]
  exact cosIv_pathObsAt_add hU _ _ _ _

theorem etaSeq_eq_cosSeq (hU : IsSLEDriverAdapted a b c U P ℱ) (n : ℕ) (q : Ω × ℝ) :
    etaSeq hU n q = cosSeq (pathObs hU 0 q) n := by
  have := etaSeq_add hU n 0 q
  simpa using this

/-- **Stationarity of `(η_n)`**: the laws of the shifted sequences on `ℕ → ℝ` agree. -/
theorem etaSeq_stationary [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (k : ℕ) :
    (P.prod (admissibleMeasure p)).map (fun q (n : ℕ) => etaSeq hU (n + k) q) =
      (P.prod (admissibleMeasure p)).map (fun q (n : ℕ) => etaSeq hU n q) := by
  have h1 : (fun q (n : ℕ) => etaSeq hU (n + k) q) = cosSeq ∘ pathObs hU (k : ℝ≥0) := by
    funext q n; exact etaSeq_add hU n k q
  have h2 : (fun q (n : ℕ) => etaSeq hU n q) = cosSeq ∘ pathObs hU 0 := by
    funext q n; exact etaSeq_eq_cosSeq hU n q
  rw [h1, h2, ← Measure.map_map measurable_cosSeq (measurable_pathObs hU _),
    ← Measure.map_map measurable_cosSeq (measurable_pathObs hU _)]
  congr 1
  exact map_pathObs_eq_zero hMO hU ha hb hc hp (k : ℝ≥0)

/-! ### On the good set -/

theorem continuous_thetaHat_of_mem_goodSet (hU : IsSLEDriverAdapted a b c U P ℱ) {q : Ω × ℝ}
    (hq : q ∈ goodSet hU) : Continuous fun s => thetaHat hU (unitPt q.2) s q.1 :=
  continuous_thetaHat_of_forall_mem hU (mem_sigmaDom_of_mem_goodSet hU hq)

/-- On the good set, the partial sums of `η` are the values `C_N`. -/
theorem sum_etaSeq_eq (hU : IsSLEDriverAdapted a b c U P ℱ) {q : Ω × ℝ} (hq : q ∈ goodSet hU)
    (N : ℕ) : ∑ n ∈ Finset.range N, etaSeq hU n q = cosIntU hU (N : ℝ≥0) q := by
  have hcont := continuous_thetaHat_of_mem_goodSet hU hq
  simp only [etaSeq_eq_cosSeq, cosSeq, pathObs]
  rw [sum_cosIv_pathObsAt hU hcont 0 N]
  simp [cosIntU, cosInt_eq]

theorem abs_etaSeq_zero_le (hU : IsSLEDriverAdapted a b c U P ℱ) {q : Ω × ℝ}
    (hq : q ∈ goodSet hU) : |etaSeq hU 0 q| ≤ 1 := by
  have h := sum_etaSeq_eq hU hq 1
  rw [Finset.sum_range_one] at h
  have h2 := abs_cosInt_le hU (continuous_thetaHat_of_mem_goodSet hU hq) 1
  rw [h]
  simpa [cosIntU] using h2

/-! ### The mean -/

theorem abs_rsumIv_pathObsAt_le (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) (s : ℝ≥0) (ω : Ω)
    (n N : ℕ) : |rsumIv (pathObsAt hU z s ω) n N| ≤ 1 := by
  unfold rsumIv
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  calc |∑ k ∈ Finset.range N, ((1 : ℝ) / N) * obsCos (pathObsAt hU z s ω) ((n : ℝ) + (k : ℝ) / N)|
      ≤ ∑ k ∈ Finset.range N, |((1 : ℝ) / N) * obsCos (pathObsAt hU z s ω)
          ((n : ℝ) + (k : ℝ) / N)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range N, ((1 : ℝ) / N) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / N)]
        refine mul_le_of_le_one_right (by positivity) ?_
        rw [obsCos_pathObsAt]
        exact Real.abs_cos_le_one _
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp


theorem integral_cos_thetaHat [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (s : ℝ≥0) :
    ∫ q, Real.cos (2 * thetaHat hU (unitPt q.2) s q.1) ∂(P.prod (admissibleMeasure p)) =
      cosMean p := by
  have hf : Continuous fun u : ℝ => Real.cos (2 * u) := by fun_prop
  have hper : Function.Periodic (fun u : ℝ => Real.cos (2 * u)) π := fun u => by
    have : 2 * (u + π) = 2 * u + 2 * π := by ring
    simp only [this, Real.cos_add_two_pi]
  exact integral_comp_thetaHat_prod_of_markovOneDim hMO hU ha hb hc hp s hf hper

/-- `E η_0 = ∫ cos(2u) dν`. -/
theorem integral_etaSeq_zero [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) :
    Integrable (etaSeq hU 0) (P.prod (admissibleMeasure p)) ∧
      ∫ q, etaSeq hU 0 q ∂(P.prod (admissibleMeasure p)) = cosMean p := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  have hm : Measurable (etaSeq hU 0) := measurable_etaSeq hU 0
  have hbd : ∀ᵐ q ∂(P.prod (admissibleMeasure p)), ‖etaSeq hU 0 q‖ ≤ 1 := by
    filter_upwards [ae_mem_goodSet hU ha hc (ν := admissibleMeasure p)] with q hq
    simpa [Real.norm_eq_abs] using abs_etaSeq_zero_le hU hq
  have hint : Integrable (etaSeq hU 0) (P.prod (admissibleMeasure p)) :=
    (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable hbd
  refine ⟨hint, ?_⟩
  -- the Riemann sums
  set R : ℕ → Ω × ℝ → ℝ := fun N q => rsumIv (pathObs hU 0 q) 0 N with hR
  have hRm : ∀ N, Measurable (R N) := fun N =>
    (measurable_rsumIv 0 N).comp (measurable_pathObs hU 0)
  have hlim : ∀ᵐ q ∂(P.prod (admissibleMeasure p)), Tendsto (fun N => R N q) atTop
      (𝓝 (etaSeq hU 0 q)) := by
    filter_upwards [ae_mem_goodSet hU ha hc (ν := admissibleMeasure p)] with q hq
    have hcont := continuous_thetaHat_of_mem_goodSet hU hq
    have h := tendsto_rsumIv_pathObsAt hU hcont (z := unitPt q.2) (ω := q.1) 0 0
    have h' := cosIv_pathObsAt hU hcont (z := unitPt q.2) (ω := q.1) 0 0
    simp only [hR, etaSeq, pathObs, Nat.cast_zero] at h h' ⊢
    rw [h']
    exact h
  have hRbd : ∀ N, ∀ᵐ q ∂(P.prod (admissibleMeasure p)), ‖R N q‖ ≤ 1 := fun N =>
    Eventually.of_forall fun q => by
      simpa [hR, Real.norm_eq_abs, pathObs] using abs_rsumIv_pathObsAt_le hU (unitPt q.2) 0 q.1 0 N
  have hobsint : ∀ (N : ℕ) (k : ℕ), Integrable (fun q : Ω × ℝ =>
      ((1 : ℝ) / N) * obsCos (pathObs hU 0 q) (((0 : ℕ) : ℝ) + (k : ℝ) / N))
      (P.prod (admissibleMeasure p)) := fun N k => by
    refine Integrable.const_mul ?_ _
    refine (integrable_const (1 : ℝ)).mono' ?_ (Eventually.of_forall fun q => ?_)
    · exact ((measurable_obsCos _).comp (measurable_pathObs hU 0)).aestronglyMeasurable
    · simp only [pathObs, obsCos_pathObsAt, Real.norm_eq_abs]
      exact Real.abs_cos_le_one _
  have hmean : ∀ N : ℕ, 0 < N → ∫ q, R N q ∂(P.prod (admissibleMeasure p)) = cosMean p :=
    fun N hN => by
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      simp only [hR, rsumIv]
      rw [integral_finsetSum _ fun k _ => hobsint N k]
      have hterm : ∀ k : ℕ, ∫ q, ((1 : ℝ) / N) * obsCos (pathObs hU 0 q)
          (((0 : ℕ) : ℝ) + (k : ℝ) / N) ∂(P.prod (admissibleMeasure p)) =
          ((1 : ℝ) / N) * cosMean p := fun k => by
        simp only [pathObs, obsCos_pathObsAt]
        rw [integral_const_mul]
        congr 1
        exact integral_cos_thetaHat hMO hU ha hb hc hp _
      simp only [hterm]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
  have hDCT := tendsto_integral_of_dominated_convergence
    (μ := P.prod (admissibleMeasure p)) (fun _ => (1 : ℝ))
    (fun N => (hRm N).aestronglyMeasurable) (integrable_const _) hRbd hlim
  have hev : ∀ᶠ N : ℕ in atTop, ∫ q, R N q ∂(P.prod (admissibleMeasure p)) = cosMean p := by
    filter_upwards [eventually_gt_atTop 0] with N hN using hmean N hN
  exact tendsto_nhds_unique hDCT (tendsto_const_nhds.congr' (hev.mono fun N h => h.symm))

/-! ### Birkhoff -/

/-- **Birkhoff for `∫₀ˢ cos 2θ̂`** (M7/D2). Under `hMO : MarkovOneDim`: there is an integrable `L`
on `(Ω × ℝ, P ⊗ ν)` with `∫ L = ∫ cos(2u) dν` such that `P ⊗ ν`-almost surely
`C_s / s → L` as `s → ∞` along `ℝ≥0`, `C_s = ∫₀ˢ cos 2θ̂_v(e^{iu}) dv`. -/
theorem exists_birkhoff_cosInt [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) :
    ∃ L : Ω × ℝ → ℝ, Integrable L (P.prod (admissibleMeasure p)) ∧
      ∫ q, L q ∂(P.prod (admissibleMeasure p)) = cosMean p ∧
      ∀ᵐ q ∂(P.prod (admissibleMeasure p)),
        Tendsto (fun s : ℝ≥0 => cosIntU hU s q / s) atTop (𝓝 (L q)) := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  obtain ⟨hint, hmean⟩ := integral_etaSeq_zero hMO hU ha hb hc hp
  obtain ⟨L, hLint, hLmean, hLlim⟩ := External.birkhoff_stationary
    (P := P.prod (admissibleMeasure p)) (etaSeq hU) (measurable_etaSeq hU)
    (fun k => etaSeq_stationary hMO hU ha hb hc hp k) hint
  refine ⟨L, hLint, hLmean.trans hmean, ?_⟩
  filter_upwards [hLlim, ae_mem_goodSet hU ha hc (ν := admissibleMeasure p)] with q hq hqG
  have hn : Tendsto (fun n : ℕ => cosIntU hU (n : ℝ≥0) q / n) atTop (𝓝 (L q)) :=
    hq.congr fun n => by rw [sum_etaSeq_eq hU hqG n]
  have hcont := continuous_thetaHat_of_mem_goodSet hU hqG
  refine tendsto_div_of_floor (Y := fun s => cosIntU hU s q) (D := fun s => cosIntU hU s q)
    (M := fun _ => 0) (C := 1) (L := L q) (fun s => by simp) (fun s => ?_) ?_ hn
  · have hs : ((⌊s⌋₊ : ℝ≥0) : ℝ) ≤ s := by exact_mod_cast Nat.floor_le (zero_le : (0 : ℝ≥0) ≤ s)
    have hs1 : (s : ℝ) - ((⌊s⌋₊ : ℝ≥0) : ℝ) ≤ 1 := by
      have : (s : ℝ) < ⌊s⌋₊ + 1 := by exact_mod_cast Nat.lt_floor_add_one s
      simp only [NNReal.coe_natCast]
      linarith
    have := abs_cosInt_sub_le hU hcont (z := unitPt q.2) (ω := q.1)
      (show ((⌊s⌋₊ : ℝ≥0)) ≤ s from by exact_mod_cast Nat.floor_le (zero_le : (0 : ℝ≥0) ≤ s))
    exact this.trans hs1
  · simp only [zero_div]
    exact tendsto_const_nhds

end ComplexSLE.Internal

end
