/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Doob's maximal inequality on dyadic grids and a strong law for `L²`-martingales

Source-independent probability. No external input is used; only Mathlib.

For a martingale `M : ℝ≥0 → Ω → ℝ` with square-integrable marginals:

* `Martingale.submartingale_sq_grid`: `k ↦ M_{kh}²` is a submartingale for `k ↦ ℱ_{kh}`
  (conditional Jensen, `Integrable.norm_condExp_rpow_le`);
* `Martingale.grid_maximal`: `lam² P(∃ k ≤ N, lam ≤ |M_{kh}|) ≤ E M_{Nh}²`
  (Mathlib's `maximal_ineq` for the nonnegative submartingale `M_{kh}²`);
* `Martingale.dyadic_maximal`: the same on the dyadic grid of `[0, T]` (monotone union over the
  mesh `T / 2^m`);
* `abs_le_of_dyadic`: a continuous function bounded on the dyadic grid of `[0, T]` is bounded
  on `[0, T]`;
* `ae_eventually_forall_abs_le`: if `E M_t² ≤ K t` and the paths are a.s. continuous then, for each
  `ε > 0`, a.s. eventually in `j`, `|M_s| ≤ ε 2^j` on `[0, 2^j]` (Borel–Cantelli along the dyadic
  scales: `P(sup_{s ≤ 2^j} |M_s| ≥ ε 2^j) ≤ K / (ε² 2^j)`);
* `ae_tendsto_div_of_second_moment`: `M_s / s → 0` almost surely.
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Finset

namespace ComplexSLE.Infrastructure

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}

/-- The filtration `k ↦ ℱ (k h)` along the grid of mesh `h`. -/
def gridFiltration (ℱ : Filtration ℝ≥0 m) (h : ℝ≥0) : Filtration ℕ m where
  seq k := ℱ (k * h)
  mono' _ _ hkl := ℱ.mono (by gcongr)
  le' k := ℱ.le _

theorem _root_.MeasureTheory.Martingale.submartingale_sq_grid [IsFiniteMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ P) (hsq : ∀ t, Integrable (fun ω => M t ω ^ 2) P) (h : ℝ≥0) :
    Submartingale (fun (k : ℕ) ω => M (k * h) ω ^ 2) (gridFiltration ℱ h) P := by
  refine ⟨fun k => (hM.stronglyAdapted (k * h)).pow 2, fun i j hij => ?_, fun k => hsq _⟩
  have hle : ((i : ℝ≥0) * h) ≤ (j : ℝ≥0) * h := by gcongr
  have hint : Integrable (fun x => ‖M (j * h) x‖ ^ (2 : ℝ)) P := by
    refine (hsq ((j : ℝ≥0) * h)).congr (Eventually.of_forall fun x => ?_)
    simp
  have h1 := Integrable.norm_condExp_rpow_le (m := ℱ (i * h)) (f := M (j * h)) (by norm_num) hint
  have h2 := hM.condExp_ae_eq hle
  have e : (fun x => ‖M (j * h) x‖ ^ (2 : ℝ)) = fun x => M (j * h) x ^ 2 := by
    funext x; simp
  rw [e] at h1
  filter_upwards [h1, h2] with x hx1 hx2
  change M (i * h) x ^ 2 ≤ (P[fun x => M (j * h) x ^ 2 | ℱ (i * h)]) x
  rw [← hx2] at *
  simpa [Real.rpow_two] using hx1


/-- **Doob's maximal inequality on a grid, `L²` form.** For a martingale with square-integrable
marginals and `lam : ℝ≥0`,
`lam² P{∃ k ≤ N, lam ≤ |M_{kh}|} ≤ E M_{Nh}²`. -/
theorem _root_.MeasureTheory.Martingale.grid_maximal [IsFiniteMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ P) (hsq : ∀ t, Integrable (fun ω => M t ω ^ 2) P) (h : ℝ≥0) (N : ℕ)
    (lam : ℝ≥0) :
    (lam : ℝ≥0∞) ^ 2 * P {ω | ∃ k : ℕ, k ≤ N ∧ (lam : ℝ) ≤ |M (k * h) ω|} ≤
      ENNReal.ofReal (∫ ω, M (N * h) ω ^ 2 ∂P) := by
  have hsub := hM.submartingale_sq_grid hsq h
  have hmax := maximal_ineq (𝒢 := gridFiltration ℱ h) hsub
    (f := fun (k : ℕ) ω => M (k * h) ω ^ 2) (fun k ω => sq_nonneg _) (ε := lam ^ 2) N
  have hset : {ω | ((lam ^ 2 : ℝ≥0) : ℝ) ≤ (range (N + 1)).sup' nonempty_range_add_one
      fun k => (fun (k : ℕ) ω => M (k * h) ω ^ 2) k ω} =
      {ω | ∃ k : ℕ, k ≤ N ∧ (lam : ℝ) ≤ |M (k * h) ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, le_sup'_iff, Finset.mem_range, Nat.lt_succ_iff, NNReal.coe_pow]
    refine exists_congr fun k => and_congr_right fun _ => ?_
    rw [← sq_abs (M _ ω), sq_le_sq₀ lam.coe_nonneg (abs_nonneg _)]
  rw [hset] at hmax
  have hle : ∫ ω in {ω | ∃ k : ℕ, k ≤ N ∧ (lam : ℝ) ≤ |M (k * h) ω|}, M (N * h) ω ^ 2 ∂P ≤
      ∫ ω, M (N * h) ω ^ 2 ∂P :=
    setIntegral_le_integral (hsq _) (Eventually.of_forall fun ω => sq_nonneg _)
  calc (lam : ℝ≥0∞) ^ 2 * P {ω | ∃ k : ℕ, k ≤ N ∧ (lam : ℝ) ≤ |M (k * h) ω|}
      = ((lam ^ 2 : ℝ≥0) : ℝ≥0∞) * P {ω | ∃ k : ℕ, k ≤ N ∧ (lam : ℝ) ≤ |M (k * h) ω|} := by
        push_cast; rfl
    _ ≤ _ := hmax.trans (ENNReal.ofReal_le_ofReal hle)


/-- **Doob's maximal inequality on the dyadic grid of `[0, T]`.** -/
theorem _root_.MeasureTheory.Martingale.dyadic_maximal [IsFiniteMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ P) (hsq : ∀ t, Integrable (fun ω => M t ω ^ 2) P) (T lam : ℝ≥0) :
    (lam : ℝ≥0∞) ^ 2 *
      P {ω | ∃ m : ℕ, ∃ k : ℕ, k ≤ 2 ^ m ∧ (lam : ℝ) ≤ |M (k * (T / 2 ^ m)) ω|} ≤
      ENNReal.ofReal (∫ ω, M T ω ^ 2 ∂P) := by
  set E : ℕ → Set Ω := fun m =>
    {ω | ∃ k : ℕ, k ≤ 2 ^ m ∧ (lam : ℝ) ≤ |M (k * (T / 2 ^ m)) ω|} with hE
  have hmono : Monotone E := by
    refine monotone_nat_of_le_succ fun m ω hω => ?_
    obtain ⟨k, hk, hkω⟩ := hω
    refine ⟨2 * k, by rw [pow_succ]; omega, ?_⟩
    have : ((2 * k : ℕ) : ℝ≥0) * (T / 2 ^ (m + 1)) = (k : ℝ≥0) * (T / 2 ^ m) := by
      push_cast; rw [pow_succ]; field_simp
    rw [this]; exact hkω
  have hU : {ω | ∃ m : ℕ, ∃ k : ℕ, k ≤ 2 ^ m ∧ (lam : ℝ) ≤ |M (k * (T / 2 ^ m)) ω|} = ⋃ m, E m := by
    ext ω; simp [hE]
  rw [hU, hmono.measure_iUnion, ENNReal.mul_iSup]
  refine iSup_le fun m => ?_
  have := hM.grid_maximal hsq (T / 2 ^ m) (2 ^ m) lam
  have e : ((2 ^ m : ℕ) : ℝ≥0) * (T / 2 ^ m) = T := by
    push_cast; field_simp
  rw [e] at this
  exact this


/-- A continuous function bounded by `b` on the dyadic grid of `[0, T]` is bounded by `b` on
`[0, T]`. -/
theorem abs_le_of_dyadic {f : ℝ≥0 → ℝ} (hf : Continuous f) {T : ℝ≥0} {b : ℝ}
    (hb : ∀ m : ℕ, ∀ k : ℕ, k ≤ 2 ^ m → |f (k * (T / 2 ^ m))| ≤ b) {s : ℝ≥0} (hs : s ≤ T) :
    |f s| ≤ b := by
  rcases eq_or_ne T 0 with rfl | hT
  · have : s = 0 := le_antisymm hs zero_le
    subst this
    simpa using hb 0 0 (by simp)
  have hTpos : 0 < T := pos_iff_ne_zero.2 hT
  -- the grid points `⌈2^m s / T⌉ T / 2^m` decrease to `s`
  set pt : ℕ → ℝ≥0 := fun m => (⌈2 ^ m * s / T⌉₊ : ℝ≥0) * (T / 2 ^ m) with hpt
  have hk : ∀ m : ℕ, ⌈(2 : ℝ≥0) ^ m * s / T⌉₊ ≤ 2 ^ m := fun m => by
    rw [Nat.ceil_le]
    push_cast
    rw [div_le_iff₀ hTpos]
    calc (2 : ℝ≥0) ^ m * s ≤ 2 ^ m * T := by gcongr
      _ = _ := by ring
  have hlim : Tendsto pt atTop (𝓝 s) := by
    have hup : ∀ m : ℕ, pt m ≤ s + T * ((2 : ℝ≥0)⁻¹) ^ m := fun m => by
      simp only [hpt]
      have h1 : (⌈(2 : ℝ≥0) ^ m * s / T⌉₊ : ℝ≥0) < 2 ^ m * s / T + 1 := Nat.ceil_lt_add_one zero_le
      calc (⌈(2 : ℝ≥0) ^ m * s / T⌉₊ : ℝ≥0) * (T / 2 ^ m)
          ≤ (2 ^ m * s / T + 1) * (T / 2 ^ m) := by gcongr
        _ = s + T * ((2 : ℝ≥0)⁻¹) ^ m := by
          rw [inv_pow]; field_simp
    have hlo : ∀ m : ℕ, s ≤ pt m := fun m => by
      simp only [hpt]
      have h1 : (2 : ℝ≥0) ^ m * s / T ≤ (⌈(2 : ℝ≥0) ^ m * s / T⌉₊ : ℝ≥0) := Nat.le_ceil _
      calc s = (2 ^ m * s / T) * (T / 2 ^ m) := by field_simp
        _ ≤ _ := by gcongr
    have hup' : Tendsto (fun m : ℕ => s + T * ((2 : ℝ≥0)⁻¹) ^ m) atTop (𝓝 (s + T * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (by simp [inv_lt_one_iff₀])))
    rw [mul_zero, add_zero] at hup'
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup' hlo hup
  have h2 : Tendsto (fun m => |f (pt m)|) atTop (𝓝 |f s|) :=
    ((hf.tendsto s).comp hlim).abs
  exact le_of_tendsto' h2 fun m => hb m _ (hk m)


/-- **Dyadic scales.** A continuous martingale with `E M_t² ≤ K t` is a.s. eventually bounded by
`ε 2^j` on `[0, 2^j]`, for every `ε > 0`. -/
theorem ae_eventually_forall_abs_le [IsProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ P) (hsq : ∀ t, Integrable (fun ω => M t ω ^ 2) P) {K : ℝ}
    (hK : ∀ t : ℝ≥0, ∫ ω, M t ω ^ 2 ∂P ≤ K * t)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => M t ω) {ε : ℝ≥0} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ᶠ j : ℕ in atTop, ∀ s : ℝ≥0, s ≤ 2 ^ j → |M s ω| ≤ ε * 2 ^ j := by
  set E : ℕ → Set Ω := fun j => {ω | ∃ m : ℕ, ∃ k : ℕ, k ≤ 2 ^ m ∧
    ((ε * 2 ^ j : ℝ≥0) : ℝ) ≤ |M (k * ((2 ^ j : ℝ≥0) / 2 ^ m)) ω|} with hE
  have hK0 : 0 ≤ K := by
    have := hK 1
    have h0 : 0 ≤ ∫ ω, M 1 ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
    simpa using h0.trans this
  -- the measure bound `P (E j) ≤ (K / ε²) (1/2)^j`
  have hbound : ∀ j : ℕ, (P (E j)).toReal ≤ K / (ε : ℝ) ^ 2 * (1 / 2) ^ j := fun j => by
    have h := hM.dyadic_maximal hsq ((2 : ℝ≥0) ^ j) (ε * 2 ^ j)
    have h1 : (((ε * 2 ^ j : ℝ≥0) : ℝ≥0∞) ^ 2 * P (E j)).toReal ≤
        (ENNReal.ofReal (∫ ω, M ((2 : ℝ≥0) ^ j) ω ^ 2 ∂P)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal
      (integral_nonneg fun ω => sq_nonneg _)] at h1
    simp only [ENNReal.coe_toReal, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat] at h1
    have h2 := (hK ((2 : ℝ≥0) ^ j))
    simp only [NNReal.coe_pow, NNReal.coe_ofNat] at h2
    have hεpos : (0 : ℝ) < ε := hε
    have h3 : ((ε : ℝ) * 2 ^ j) ^ 2 * (P (E j)).toReal ≤ K * 2 ^ j := h1.trans h2
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have ht : (0 : ℝ) < 2 ^ j := by positivity
    have h4 : (1 / 2 : ℝ) ^ j = (2 ^ j)⁻¹ := by rw [one_div, inv_pow]
    rw [h4, ← div_eq_mul_inv, le_div_iff₀ ht]
    refine le_of_mul_le_mul_left ?_ ht
    calc (2 : ℝ) ^ j * ((P (E j)).toReal * (ε : ℝ) ^ 2 * 2 ^ j)
        = ((ε : ℝ) * 2 ^ j) ^ 2 * (P (E j)).toReal := by ring
      _ ≤ K * 2 ^ j := h3
      _ = 2 ^ j * K := by ring
  have hsum : ∑' j, P (E j) ≠ ∞ := by
    have hs : Summable fun j : ℕ => K / (ε : ℝ) ^ 2 * (1 / 2 : ℝ) ^ j :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hs' : Summable fun j : ℕ => (P (E j)).toReal :=
      hs.of_nonneg_of_le (fun j => ENNReal.toReal_nonneg) hbound
    have e : ∑' j, P (E j) = ENNReal.ofReal (∑' j, (P (E j)).toReal) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun j => ENNReal.toReal_nonneg) hs']
      refine tsum_congr fun j => ?_
      rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [e]; exact ENNReal.ofReal_ne_top
  have hBC := ae_eventually_notMem hsum
  filter_upwards [hBC, hcont] with ω hω hc
  filter_upwards [hω] with j hj s hs
  have hj' : ∀ m : ℕ, ∀ k : ℕ, k ≤ 2 ^ m →
      |M (k * ((2 ^ j : ℝ≥0) / 2 ^ m)) ω| ≤ ε * 2 ^ j := fun m k hk => by
    by_contra hcon
    exact hj ⟨m, k, hk, by push_cast; exact (not_le.1 hcon).le⟩
  have := abs_le_of_dyadic hc (T := 2 ^ j) (b := (ε : ℝ) * 2 ^ j) (fun m k hk => hj' m k hk) hs
  simpa using this


/-- **Strong law for continuous `L²`-martingales with linearly growing second moment.** If `M` is a
continuous martingale with `E M_t² ≤ K t`, then `M_s / s → 0` almost surely as `s → ∞`. -/
theorem ae_tendsto_div_of_second_moment [IsProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ P) (hsq : ∀ t, Integrable (fun ω => M t ω ^ 2) P) {K : ℝ}
    (hK : ∀ t : ℝ≥0, ∫ ω, M t ω ^ 2 ∂P ≤ K * t)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => M t ω) :
    ∀ᵐ ω ∂P, Tendsto (fun s : ℝ≥0 => M s ω / s) atTop (𝓝 0) := by
  have hε : ∀ i : ℕ, 0 < ((i : ℝ≥0) + 1)⁻¹ := fun i => by positivity
  have h := ae_all_iff.2 fun i : ℕ =>
    ae_eventually_forall_abs_le hM hsq hK hcont (hε i)
  filter_upwards [h] with ω hω
  rw [Metric.tendsto_atTop]
  intro δ hδ
  -- choose `ε = (i+1)⁻¹ < δ / 2`
  obtain ⟨i, hi⟩ := exists_nat_one_div_lt (half_pos hδ)
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 (hω i)
  refine ⟨2 ^ j₀ + 1, fun s hs => ?_⟩
  have hs1 : (1 : ℝ) ≤ s := by
    have : (1 : ℝ≥0) ≤ 2 ^ j₀ + 1 := by simp
    exact_mod_cast this.trans hs
  have hsj : ((2 : ℝ) ^ j₀) ≤ s := by
    have : ((2 ^ j₀ + 1 : ℝ≥0) : ℝ) ≤ s := by exact_mod_cast hs
    push_cast at this; linarith
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hs1 (by norm_num : (1 : ℝ) < 2)
  have hnj : j₀ ≤ n + 1 := by
    have : (2 : ℝ) ^ j₀ < 2 ^ (n + 1) := hsj.trans_lt hn2
    exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 this |>.le
  have hs' : s ≤ 2 ^ (n + 1) := by
    have : (s : ℝ) ≤ 2 ^ (n + 1) := hn2.le
    exact_mod_cast this
  have hb := hj₀ (n + 1) hnj s hs'
  have hspos : (0 : ℝ) < s := by linarith
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hspos, div_lt_iff₀ hspos]
  have hb' : |M s ω| ≤ ((i : ℝ) + 1)⁻¹ * 2 ^ (n + 1) := by
    have := hb
    push_cast at this
    exact this
  calc |M s ω| ≤ ((i : ℝ) + 1)⁻¹ * 2 ^ (n + 1) := hb'
    _ = 2 * ((i : ℝ) + 1)⁻¹ * 2 ^ n := by ring
    _ ≤ 2 * ((i : ℝ) + 1)⁻¹ * s := by gcongr
    _ < δ * s := by
      have h2 : 2 * ((i : ℝ) + 1)⁻¹ < δ := by
        have := hi; rw [one_div] at this; linarith
      gcongr

end ComplexSLE.Infrastructure
