/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.ErgodicBirkhoff
public import ComplexSLE.External.RecurrenceStationary

/-!
# Recurrence of `log |f̂_s(𝐳)|` when `(I) = 0`, and the consumer shapes (M7/A5b, Lemma 3.3)

On `(Ω × ℝ, P ⊗ ν)`, `ν = p(u) 1_{[0,2π]}(u) du`, `Y_s = log |f̂_s(e^{iu})|` (`logFHat`),
`ξ_n = Y_{n+1} - Y_n` (`xiInc`). The a.s. constancy of the Birkhoff limit is taken as the explicit
hypothesis
`hconst : ∀ᵐ q ∂(P ⊗ ν), Y_s / s → (I)` (`s → ∞` in `ℝ≥0`),
proved elsewhere (`ErgodicConst*.lean`).

* `recurrent_logFHat_of_integralI_eq_zero` (paper.tex:L1384-1388, via `lem-recurrent`): if
  `(I) = 0`, a.s. for every `ε > 0` there are arbitrarily large `s` with `|Y_s| < ε`. The EXTERNAL
  `recurrence_stationary` applies to `(ξ_n)` (stationary: `xiInc_stationary`; integrable;
  `S_n / n = Y_n / n → 0` by `hconst`), and `∑_{k<n} ξ_k = Y_n` a.s.
* `not_tendsto_atBot_logFHat_of_integralI_nonneg` (Prop 3.1(a) shape): if `(I) ≥ 0`, a.s.
  `Y_s ↛ -∞`.
* `tendsto_atBot_logFHat_of_integralI_neg` (Prop 3.1(b) shape): if `(I) < 0`, a.s. `Y_s → -∞`
  (since `Y_s / s → (I)`).

Consumes the EXTERNALs `recurrence_stationary` (E7') and, through the stationarity layer,
`hormander_oneDim`, `ito_formula`, `timeChange_isContLocalMartingale`, `strongMarkov_sleDriver`,
and the EXTERNAL `markov_oneDim` (R29) as the hypothesis `hMO : MarkovOneDim`.
-/

@[expose] public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal

open Polar

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-! ### Recurrence when `(I) = 0` -/

/-- **Recurrence of `log |f̂|` when `(I) = 0`** (Lemma 3.3, last clause). Under `hMO : MarkovOneDim`
and the a.s. constancy `hconst` of the Birkhoff limit: if `(I) = 0`, then `P ⊗ ν`-a.s. for every
`ε > 0` and `S ≥ 0` there is `s ≥ S` with `|log |f̂_s(e^{iu})|| < ε`. -/
theorem recurrent_logFHat_of_integralI_eq_zero [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (hI : integralI a b c p = 0)
    (hconst : ∀ᵐ q ∂(P.prod (admissibleMeasure p)),
      Tendsto (fun s : ℝ≥0 => logFHat hU s q / s) atTop (𝓝 (integralI a b c p))) :
    ∀ᵐ q ∂(P.prod (admissibleMeasure p)), ∀ ε : ℝ, 0 < ε → ∀ S : ℝ≥0,
      ∃ s : ℝ≥0, S ≤ s ∧ |logFHat hU s q| < ε := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  -- integrability of `ξ 0`
  obtain ⟨h1, -⟩ := integrable_integral_logFHat hMO hU ha hb hc hp 1
  obtain ⟨h0, -⟩ := integrable_integral_logFHat hMO hU ha hb hc hp 0
  have hint : Integrable (xiInc hU 0) (P.prod (admissibleMeasure p)) := by
    have e : xiInc hU 0 = logFHat hU 1 - logFHat hU 0 := by
      funext q; simp [xiInc]
    rw [e]; exact h1.sub h0
  -- the partial sums are `Y_n` a.s.
  have hsum : ∀ᵐ q ∂(P.prod (admissibleMeasure p)), ∀ n : ℕ,
      ∑ k ∈ Finset.range n, xiInc hU k q = logFHat hU (n : ℝ≥0) q := by
    filter_upwards [ae_logFHat_zero hU ha hc (ν := admissibleMeasure p)] with q hq0 n
    have := Finset.sum_range_sub (fun k : ℕ => logFHat hU (k : ℝ≥0) q) n
    have e : ∑ k ∈ Finset.range n, xiInc hU k q = logFHat hU (n : ℝ≥0) q - logFHat hU 0 q := by
      simpa [xiInc, Nat.cast_succ] using this
    rw [e, hq0, sub_zero]
  -- Cesàro limit `0`
  have hlim : ∀ᵐ q ∂(P.prod (admissibleMeasure p)),
      Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, xiInc hU k q) / n) atTop (𝓝 0) := by
    filter_upwards [hconst, hsum] with q hq hs
    have h := hq.comp tendsto_natCast_atTop_atTop
    rw [hI] at h
    refine h.congr fun n => ?_
    simp [Function.comp, hs n]
  have hrec := External.recurrence_stationary (P := P.prod (admissibleMeasure p)) (xiInc hU)
    (measurable_xiInc hU) (fun k => xiInc_stationary hMO hU ha hb hc hp k) hint hlim
  filter_upwards [hrec, hsum] with q hq hs ε hε S
  obtain ⟨n, hn1, hn2⟩ := ((hq ε hε).and_eventually (eventually_ge_atTop ⌈S⌉₊)).exists
  refine ⟨(n : ℝ≥0), le_trans (Nat.le_ceil S) (by exact_mod_cast hn2), ?_⟩
  rw [← hs n]
  exact hn1

/-! ### Consumer shapes (Proposition 3.1) -/

/-- **Prop 3.1(a) shape.** If `(I) ≥ 0`, then `P ⊗ ν`-a.s. `log |f̂_s(e^{iu})|` does not tend to
`-∞` as `s → ∞`. -/
theorem not_tendsto_atBot_logFHat_of_integralI_nonneg [IsProbabilityMeasure P]
    (hMO : MarkovOneDim) (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b)
    (hc : c ^ 2 ≤ a * b) {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p)
    (hI : 0 ≤ integralI a b c p)
    (hconst : ∀ᵐ q ∂(P.prod (admissibleMeasure p)),
      Tendsto (fun s : ℝ≥0 => logFHat hU s q / s) atTop (𝓝 (integralI a b c p))) :
    ∀ᵐ q ∂(P.prod (admissibleMeasure p)),
      ¬ Tendsto (fun s : ℝ≥0 => logFHat hU s q) atTop atBot := by
  rcases hI.lt_or_eq with hpos | hzero
  · -- `Y_s / s → (I) > 0` forces `Y_s > 0` eventually
    filter_upwards [hconst] with q hq hbot
    have h1 : ∀ᶠ s : ℝ≥0 in atTop, 0 < logFHat hU s q / s :=
      hq.eventually (lt_mem_nhds hpos)
    have h2 : ∀ᶠ s : ℝ≥0 in atTop, logFHat hU s q < 0 := hbot.eventually (eventually_lt_atBot 0)
    have h3 : ∀ᶠ s : ℝ≥0 in atTop, 0 < s := eventually_gt_atTop 0
    obtain ⟨s, hs1, hs2, hs3⟩ := (h1.and (h2.and h3)).exists
    have hs3' : (0 : ℝ) < s := by exact_mod_cast hs3
    have := (div_pos_iff_of_pos_right hs3').1 hs1
    linarith
  · -- `(I) = 0`: recurrence
    have hrec := recurrent_logFHat_of_integralI_eq_zero hMO hU ha hb hc hp hzero.symm hconst
    filter_upwards [hrec] with q hq hbot
    obtain ⟨S, hS⟩ := eventually_atTop.1 (hbot.eventually (eventually_le_atBot (-1)))
    obtain ⟨s, hsS, hs⟩ := hq 1 one_pos S
    have h1 := hS s hsS
    have h2 := (abs_lt.1 hs).1
    linarith

/-- **Prop 3.1(b) shape.** If `(I) < 0`, then `P ⊗ ν`-a.s. `log |f̂_s(e^{iu})| → -∞` as `s → ∞`
(indeed `Y_s / s → (I) < 0`). -/
theorem tendsto_atBot_logFHat_of_integralI_neg (hU : IsSLEDriverAdapted a b c U P ℱ)
    {p : ℝ → ℝ} (hI : integralI a b c p < 0)
    (hconst : ∀ᵐ q ∂(P.prod (admissibleMeasure p)),
      Tendsto (fun s : ℝ≥0 => logFHat hU s q / s) atTop (𝓝 (integralI a b c p))) :
    ∀ᵐ q ∂(P.prod (admissibleMeasure p)),
      Tendsto (fun s : ℝ≥0 => logFHat hU s q) atTop atBot := by
  filter_upwards [hconst] with q hq
  have hneg : integralI a b c p / 2 < 0 := by linarith
  have hlt : ∀ᶠ s : ℝ≥0 in atTop, logFHat hU s q / s < integralI a b c p / 2 :=
    hq.eventually (gt_mem_nhds (by linarith))
  have hbot : Tendsto (fun s : ℝ≥0 => integralI a b c p / 2 * (s : ℝ)) atTop atBot :=
    Tendsto.const_mul_atTop_of_neg hneg (NNReal.tendsto_coe_atTop.2 tendsto_id)
  refine tendsto_atBot_mono' _ ?_ hbot
  filter_upwards [hlt, eventually_gt_atTop (0 : ℝ≥0)] with s hs hs0
  have hs0' : (0 : ℝ) < s := by exact_mod_cast hs0
  rw [div_lt_iff₀ hs0'] at hs
  linarith

end ComplexSLE.Internal

end
