/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.Measurability
public import ComplexSLE.Internal.Polar.Argument
public import ComplexSLE.Internal.Polar.Riemann

/-!
# The clock and the argument at a fixed time are `ℱ t`-measurable (M6/S6)

For `t : ℝ≥0` and `z : ℂ`, on the event `{t < T_z}` the clock `A_t(z) = ∫₀ᵗ |f_s(z)|⁻² ds` and the
continuous argument `θ_t(z)` are limits of expressions in finitely many values
`f_{kt/N}(z)`, `k ≤ N`, each of which is `ℱ (kt/N) ⊆ ℱ t`-measurable by `measurable_centeredPath`:

* `A_t = lim_N ∑_{k<N} (t/N) |f_{kt/N}|⁻²` (`tendsto_riemannSum`);
* `θ_t = θ_0 + lim_N ∑_{k<N} arg (f_{(k+1)t/N} / f_{kt/N})`, the sum being eventually constant
  (`eventually_sum_arg_eq`), and `θ_0 = argInit` is the explicit function
  `arg (z - U_0)` shifted into `[0, 2π)`.

Hence both (set to `0` off `{t < T_z}`) are `ℱ t`-measurable, by
`measurable_of_tendsto_metrizable`.
-/

public section

open scoped NNReal ENNReal Real Topology
open Set MeasureTheory Filter Complex

namespace ComplexSLE.Internal.Polar

/-! ### The dyadic-type grid and `argInit` -/

/-- The grid point `k t / N`, as a nonnegative real. -/
@[expose] noncomputable def gridPt (t : ℝ≥0) (N k : ℕ) : ℝ≥0 := (k : ℝ≥0) * t / (N : ℝ≥0)

theorem coe_gridPt (t : ℝ≥0) (N k : ℕ) : ((gridPt t N k : ℝ≥0) : ℝ) = (k : ℝ) * t / N := by
  simp [gridPt]

theorem gridPt_le (t : ℝ≥0) {N k : ℕ} (hk : k ≤ N) : gridPt t N k ≤ t := by
  rw [← NNReal.coe_le_coe, coe_gridPt]
  by_cases hN : N = 0
  · simp [hN]
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
    rw [div_le_iff₀ hNpos]
    nlinarith [t.coe_nonneg]

variable {U : ℝ≥0 → ℂ}

theorem argInit_eq (hU : Continuous U) (z : ℂ) :
    argInit U hU z =
      if 0 ≤ arg (z - U 0) then arg (z - U 0) else arg (z - U 0) + 2 * π := by
  have hdir : Circle.exp (argInit U hU z) = Circle.exp (arg (z - U 0)) := by
    rw [circleExp_argInit]
    apply Circle.ext
    rw [coe_dirPath, Circle.coe_exp, fPath_zero]
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.1 hdir
  have h1 := arg_le_pi (z - U 0)
  have h2 := neg_pi_lt_arg (z - U 0)
  have h3 := argInit_mem_Ico hU z
  have hpos := Real.pi_pos
  split_ifs with h
  · have hn0 : n = 0 := by
      have a1 : (n : ℝ) < 1 := by
        by_contra hcon; push Not at hcon; nlinarith [h3.2]
      have a2 : (-1 : ℝ) < n := by
        by_contra hcon; push Not at hcon; nlinarith [h3.1]
      have a1' : n < 1 := by exact_mod_cast a1
      have a2' : -1 < n := by exact_mod_cast a2
      omega
    rw [hn, hn0]; simp
  · push Not at h
    have hn1 : n = 1 := by
      have a1 : (n : ℝ) < 2 := by
        by_contra hcon; push Not at hcon; nlinarith [h3.2]
      have a2 : (0 : ℝ) < n := by
        by_contra hcon; push Not at hcon; nlinarith [h3.1]
      have a1' : n < 2 := by exact_mod_cast a1
      have a2' : 0 < n := by exact_mod_cast a2
      omega
    rw [hn, hn1]; simp

/-! ### Measurability -/

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}

open Classical in
/-- `f_r(z)` on `{r < T_z}`, and `0` elsewhere. -/
@[expose] noncomputable def centeredOrZero (U : ℝ≥0 → Ω → ℂ) (hc : ∀ ω, Continuous fun t => U t ω)
    (z : ℂ) (r : ℝ≥0) (ω : Ω) : ℂ :=
  if (r : ℝ) ∈ lifeSet (fun s => U s ω) z then fPath (fun s => U s ω) (hc ω) z r else 0

theorem measurable_centeredOrZero {U : ℝ≥0 → Ω → ℂ} (hc : ∀ ω, Continuous fun t => U t ω)
    (had : Adapted ℱ U) (z : ℂ) (r : ℝ≥0) : Measurable[ℱ r] (centeredOrZero U hc z r) :=
  measurable_centeredPath hc had r z

theorem centeredOrZero_eq {U : ℝ≥0 → Ω → ℂ} (hc : ∀ ω, Continuous fun t => U t ω) (z : ℂ)
    {r : ℝ≥0} {ω : Ω} (h : (r : ℝ) ∈ lifeSet (fun s => U s ω) z) :
    centeredOrZero U hc z r ω = fPath (fun s => U s ω) (hc ω) z r := by
  simp [centeredOrZero, h]

open Classical in
/-- **The clock `A_t(z)` is `ℱ t`-measurable** (on `{t < T_z}`; `0` elsewhere). -/
theorem measurable_clock {U : ℝ≥0 → Ω → ℂ} (hc : ∀ ω, Continuous fun t => U t ω)
    (had : Adapted ℱ U) (t : ℝ≥0) (z : ℂ) :
    Measurable[ℱ t] fun ω =>
      if (t : ℝ) ∈ lifeSet (fun s => U s ω) z then clock (fun s => U s ω) (hc ω) z t else 0 := by
  let _ : MeasurableSpace Ω := ℱ t
  let G : ℕ → Ω → ℝ := fun N ω =>
    if (t : ℝ) ∈ lifeSet (fun s => U s ω) z then
      ∑ k ∈ Finset.range N, ((t : ℝ) / N) * (‖centeredOrZero U hc z (gridPt t N k) ω‖ ^ 2)⁻¹
    else 0
  have hG : ∀ N, Measurable (G N) := by
    intro N
    have hsum : Measurable fun ω => ∑ k ∈ Finset.range N,
        ((t : ℝ) / N) * (‖centeredOrZero U hc z (gridPt t N k) ω‖ ^ 2)⁻¹ := by
      refine Finset.measurable_sum _ fun k hk => ?_
      have hF : Measurable[ℱ t] (centeredOrZero U hc z (gridPt t N k)) :=
        (measurable_centeredOrZero hc had z _).mono
          (ℱ.mono (gridPt_le t (Finset.mem_range.1 hk).le)) le_rfl
      exact measurable_const.mul ((measurable_norm.comp hF).pow_const 2).inv
    exact Measurable.ite (measurableSet_mem_lifeSet hc had t z) hsum measurable_const
  refine measurable_of_tendsto_metrizable hG ?_
  rw [tendsto_pi_nhds]
  intro ω
  by_cases h : (t : ℝ) ∈ lifeSet (fun s => U s ω) z
  · simp only [G, h, ↓reduceIte]
    have hrs := tendsto_riemannSum (φ := clockRate (fun s => U s ω) (hc ω) z) t.coe_nonneg
      ((continuousOn_clockRate (hc ω) z).mono (Icc_subset_lifeSet h))
    refine (hrs.congr' ?_)
    filter_upwards with N
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkt : ((gridPt t N k : ℝ≥0) : ℝ) ∈ lifeSet (fun s => U s ω) z :=
      mem_lifeSet_of_le h (NNReal.coe_nonneg _) (NNReal.coe_le_coe.2
        (gridPt_le t (Finset.mem_range.1 hk).le))
    rw [centeredOrZero_eq hc z hkt, coe_gridPt]
    rfl
  · simp only [G, h, ↓reduceIte]
    exact tendsto_const_nhds

open Classical in
/-- **The argument `θ_t(z)` is `ℱ t`-measurable** (on `{t < T_z}`; `0` elsewhere). -/
theorem measurable_argPath {U : ℝ≥0 → Ω → ℂ} (hc : ∀ ω, Continuous fun t => U t ω)
    (had : Adapted ℱ U) (t : ℝ≥0) (z : ℂ) :
    Measurable[ℱ t] fun ω =>
      if (t : ℝ) ∈ lifeSet (fun s => U s ω) z then argPath (fun s => U s ω) (hc ω) z t
      else 0 := by
  let _ : MeasurableSpace Ω := ℱ t
  -- the initial value
  have hinit : Measurable fun ω => argInit (fun s => U s ω) (hc ω) z := by
    have h00 : Measurable[ℱ t] (U 0) := (had 0).mono (ℱ.mono (by simp : (0 : ℝ≥0) ≤ t)) le_rfl
    have h0 : Measurable[ℱ t] fun ω => arg (z - U 0 ω) :=
      Complex.measurable_arg.comp (measurable_const.sub h00)
    have : (fun ω => argInit (fun s => U s ω) (hc ω) z) =
        fun ω => if 0 ≤ arg (z - U 0 ω) then arg (z - U 0 ω) else arg (z - U 0 ω) + 2 * π := by
      funext ω; exact argInit_eq (hc ω) z
    rw [this]
    exact Measurable.ite (measurableSet_le measurable_const h0) h0 (h0.add_const _)
  let G : ℕ → Ω → ℝ := fun N ω =>
    if (t : ℝ) ∈ lifeSet (fun s => U s ω) z then
      argInit (fun s => U s ω) (hc ω) z + ∑ k ∈ Finset.range N,
        arg (centeredOrZero U hc z (gridPt t N (k + 1)) ω /
          centeredOrZero U hc z (gridPt t N k) ω)
    else 0
  have hG : ∀ N, Measurable (G N) := by
    intro N
    have hsum : Measurable fun ω => ∑ k ∈ Finset.range N,
        arg (centeredOrZero U hc z (gridPt t N (k + 1)) ω /
          centeredOrZero U hc z (gridPt t N k) ω) := by
      refine Finset.measurable_sum _ fun k hk => ?_
      have hk' : k < N := Finset.mem_range.1 hk
      have hF1 : Measurable[ℱ t] (centeredOrZero U hc z (gridPt t N (k + 1))) :=
        (measurable_centeredOrZero hc had z _).mono (ℱ.mono (gridPt_le t hk')) le_rfl
      have hF0 : Measurable[ℱ t] (centeredOrZero U hc z (gridPt t N k)) :=
        (measurable_centeredOrZero hc had z _).mono (ℱ.mono (gridPt_le t hk'.le)) le_rfl
      exact Complex.measurable_arg.comp (hF1.div hF0)
    exact Measurable.ite (measurableSet_mem_lifeSet hc had t z) (hinit.add hsum) measurable_const
  refine measurable_of_tendsto_metrizable hG ?_
  rw [tendsto_pi_nhds]
  intro ω
  by_cases h : (t : ℝ) ∈ lifeSet (fun s => U s ω) z
  · simp only [G, h, ↓reduceIte]
    have hev := eventually_sum_arg_eq (f := fPath (fun s => U s ω) (hc ω) z)
      (θ := argPath (fun s => U s ω) (hc ω) z) t.coe_nonneg
      ((continuousOn_argPath (hc ω) z).mono (Icc_subset_lifeSet h))
      (fun r hr => fPath_eq_norm_mul_exp (hc ω) (Icc_subset_lifeSet h hr))
      (fun r hr => fPath_ne_zero (hc ω) (Icc_subset_lifeSet h hr))
    refine (tendsto_const_nhds (x := argPath (fun s => U s ω) (hc ω) z t)).congr' ?_
    filter_upwards [hev] with N hN
    have hgrid : ∀ k ∈ Finset.range (N + 1), ((gridPt t N k : ℝ≥0) : ℝ) ∈
        lifeSet (fun s => U s ω) z := fun k hk =>
      mem_lifeSet_of_le h (NNReal.coe_nonneg _) (NNReal.coe_le_coe.2
        (gridPt_le t (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))))
    have hsum : ∑ k ∈ Finset.range N, arg (centeredOrZero U hc z (gridPt t N (k + 1)) ω /
        centeredOrZero U hc z (gridPt t N k) ω) = argPath (fun s => U s ω) (hc ω) z t -
          argPath (fun s => U s ω) (hc ω) z 0 := by
      rw [← hN]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < N := Finset.mem_range.1 hk
      rw [centeredOrZero_eq hc z (hgrid (k + 1) (Finset.mem_range.2 (Nat.succ_lt_succ hk'))),
        centeredOrZero_eq hc z (hgrid k (Finset.mem_range.2 (by omega))), coe_gridPt,
        coe_gridPt]
    rw [hsum, argPath_zero]
    ring
  · simp only [G, h, ↓reduceIte]
    exact tendsto_const_nhds

end ComplexSLE.Internal.Polar

end
