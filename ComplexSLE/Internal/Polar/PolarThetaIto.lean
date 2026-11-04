/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.PolarThetaSector
public import ComplexSLE.Internal.Polar.PolarThetaCalculus
public import ComplexSLE.External.ItoFormula

/-!
# Itô's formula for the argument between two successive sector times (M6/S11;
`step:polar-real-imag`, imaginary part)

For an adapted `SLE_Σ` driver (`0 < a`, `c² ≤ ab`), `z ≠ 0` and a sector index `k`, let
`ρ = S_k ≤ σ = S_{k+1} ≤ τ_n` be the sector times of `PolarThetaSector.lean`. We apply the external
Itô formula E1 (`External.ito_formula`) to the `ℝ⁴`-valued state

  `X_t = (Re f_{t ∧ σ}, Im f_{t ∧ σ}, Re f_{t ∧ ρ}, Im f_{t ∧ ρ})`

with the function `argProd (w, v) = Arg (w v̄)`. Since `|θ_{t ∧ σ} - θ_{t ∧ ρ}| ≤ π/2`, the path of `X`
stays in the open set `argDomain` where `argProd` is smooth, and `argProd (X_t) = θ_{t ∧ σ} - θ_{t ∧ ρ}`
exactly. The characteristics of `X` are those of `(Re f, Im f)` stopped at `σ` and at `ρ`; the
cross brackets between the two blocks are `Σ (t ∧ ρ)` (`isContLocalMartingale_min_mul_min`,
which needs the bound `|U_{t ∧ τ_n} - U_0| ≤ 2n² + 2n`). The Itô integrand evaluates to
`1_{ρ < s ≤ σ} µ(θ_s)|f_s|⁻²` (the `v`-terms cancel the `w`-terms before `ρ`), so that

  `Θ^n_{t ∧ S_{k+1}} - Θ^n_{t ∧ S_k}` is a continuous local martingale
  (`isContLocalMartingale_sectorIncrement`).
-/

public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal.Polar

section

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

variable (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) (n : ℕ)

/-! ### A deterministic bound on the driver on `[0, τ_n]` -/

/-- `|f_s(z)| ≤ n` for `s ∈ [0, τ_n]` when `τ_n > 0` (by continuity at `τ_n`). -/
theorem norm_fPath_le_of_le_exitR {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) {s : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ exitR hU z n ω) (hpos : 0 < exitR hU z n ω) :
    ‖fPath (fun r => U r ω) (hU.cont ω) z s‖ ≤ n := by
  rcases lt_or_eq_of_le hs with hlt | heq
  · exact (norm_fPath_mem_Ioo_of_lt_exitTime (hU.cont ω) hs0 hlt).1.2.le
  · subst heq
    have hsub : Ico (0 : ℝ) (exitR hU z n ω) ⊆ lifeSet (fun r => U r ω) z := fun y hy =>
      mem_lifeSet_of_le (exitR_mem_lifeSet hU z n hz) hy.1 hy.2.le
    have hcl : exitR hU z n ω ∈ closure (Ico (0 : ℝ) (exitR hU z n ω)) := by
      rw [closure_Ico hpos.ne]; exact right_mem_Icc.2 hpos.le
    have hcw : ContinuousWithinAt (fun y => ‖fPath (fun r => U r ω) (hU.cont ω) z y‖)
        (Ico (0 : ℝ) (exitR hU z n ω)) (exitR hU z n ω) :=
      ((continuousOn_norm_fPath (hU.cont ω) z) _ (exitR_mem_lifeSet hU z n hz)).mono hsub
    exact hcw.closure_le hcl continuousWithinAt_const fun y hy =>
      (norm_fPath_mem_Ioo_of_lt_exitTime (hU.cont ω) hy.1 hy.2).1.2.le

/-- **The driver is bounded before `τ_n`:** `|U_{t ∧ τ_n} - U_0| ≤ 2n² + 2n` for every `ω`, `t`. -/
theorem norm_U_min_exitNN_sub_le (ω : Ω) (t : ℝ≥0) :
    ‖U (min t (exitNN hU z n ω)) ω - U 0 ω‖ ≤ 2 * (n : ℝ) ^ 2 + 2 * n := by
  have hC : (0 : ℝ) ≤ 2 * (n : ℝ) ^ 2 + 2 * n := by positivity
  by_cases hz : 0 < absorbingTime (fun s => U s ω) z
  swap
  · have h0 : exitNN hU z n ω = 0 := by
      rw [exitNN, exitR_eq_zero hU z n hz, Real.toNNReal_zero]
    simp only [h0, min_eq_right zero_le, sub_self, norm_zero]
    exact hC
  rcases eq_or_lt_of_le (exitR_nonneg hU z n ω) with h0 | hpos
  · have h0' : exitNN hU z n ω = 0 := by rw [exitNN, ← h0, Real.toNNReal_zero]
    simp only [h0', min_eq_right zero_le, sub_self, norm_zero]
    exact hC
  have hn : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · exfalso
      have hmem : (0 : ℝ) ∈ exitSet (fun r => U r ω) (hU.cont ω) z n :=
        ⟨zero_mem_lifeSet_iff.2 hz, Or.inr (Or.inl (by simp [hn0]))⟩
      exact absurd (exitTime_le_of_mem (hU.cont ω) hmem) (not_le.2 hpos)
    · exact_mod_cast hn0
  set s : ℝ≥0 := min t (exitNN hU z n ω) with hs
  have hsR : (s : ℝ) ≤ exitR hU z n ω := by
    rw [← coe_exitNN hU z n ω]; exact NNReal.coe_le_coe.2 (min_le_right _ _)
  have hsl : (s : ℝ) ∈ lifeSet (fun r => U r ω) z :=
    mem_lifeSet_of_le (exitR_mem_lifeSet hU z n hz) s.coe_nonneg hsR
  have hkey := fPath_sub_fPath_zero (hU.cont ω) hsl (z := z)
  rw [Real.toNNReal_coe] at hkey
  have hU' : U s ω - U 0 ω = (∫ r in (0 : ℝ)..s, 2 / fPath (fun r => U r ω) (hU.cont ω) z r) -
      (fPath (fun r => U r ω) (hU.cont ω) z s - fPath (fun r => U r ω) (hU.cont ω) z 0) := by
    linear_combination hkey
  have hint_bd : ‖∫ r in (0 : ℝ)..s, 2 / fPath (fun r => U r ω) (hU.cont ω) z r‖ ≤
      2 * n * |(s : ℝ) - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const_ae ?_
    have hae : ∀ᵐ x : ℝ, x ≠ exitR hU z n ω := by
      rw [ae_iff]
      simp only [not_not, Set.ofPred_eq_eq_singleton, measure_singleton]
    filter_upwards [hae] with x hx hxI
    rw [uIoc_of_le s.coe_nonneg] at hxI
    have hxlt : x < exitR hU z n ω := lt_of_le_of_ne (hxI.2.trans hsR) hx
    have hf := (norm_fPath_mem_Ioo_of_lt_exitTime (hU.cont ω) hxI.1.le hxlt).1.1
    have hfpos : 0 < ‖fPath (fun r => U r ω) (hU.cont ω) z x‖ := lt_trans (by positivity) hf
    rw [norm_div, RCLike.norm_two, div_le_iff₀ hfpos]
    rw [div_lt_iff₀ hn] at hf
    nlinarith
  have hfs := norm_fPath_le_of_le_exitR hU z n hz s.coe_nonneg hsR hpos
  have hf0 := norm_fPath_le_of_le_exitR hU z n hz le_rfl (exitR_nonneg hU z n ω) hpos
  have hsn : (s : ℝ) ≤ n := hsR.trans (exitTime_le_nat (hU.cont ω) hz n)
  have hprod : 2 * (n : ℝ) * s ≤ 2 * n * n :=
    mul_le_mul_of_nonneg_left hsn (by positivity)
  calc ‖U s ω - U 0 ω‖ = ‖(∫ r in (0 : ℝ)..s, 2 / fPath (fun r => U r ω) (hU.cont ω) z r) -
        (fPath (fun r => U r ω) (hU.cont ω) z s - fPath (fun r => U r ω) (hU.cont ω) z 0)‖ := by
        rw [hU']
    _ ≤ ‖∫ r in (0 : ℝ)..s, 2 / fPath (fun r => U r ω) (hU.cont ω) z r‖ +
        ‖fPath (fun r => U r ω) (hU.cont ω) z s - fPath (fun r => U r ω) (hU.cont ω) z 0‖ :=
        norm_sub_le _ _
    _ ≤ 2 * n * |(s : ℝ) - 0| + (‖fPath (fun r => U r ω) (hU.cont ω) z s‖ +
        ‖fPath (fun r => U r ω) (hU.cont ω) z 0‖) := add_le_add hint_bd (norm_sub_le _ _)
    _ ≤ 2 * (n : ℝ) ^ 2 + 2 * n := by
        rw [sub_zero, abs_of_nonneg s.coe_nonneg]
        nlinarith

/-! ### The martingale parts of the Itô state, bounded and continuous -/

/-- The martingale part `Mⁱ_t = Xⁱ_t - Xⁱ_0 - ∫₀ᵗ Aⁱ` of the Itô state `(Re f, Im f)` stopped at
`τ_n` (`= -(Uⁱ_{t ∧ τ_n} - Uⁱ_0)`). -/
@[expose] noncomputable def stateMart (i : Fin 2) (t : ℝ≥0) (ω : Ω) : ℝ :=
  itoState hU z n t ω i - itoState hU z n 0 ω i -
    pathIntegral (fun s ω => itoDrift hU z n s ω i) t ω

theorem stateMart_eq (i : Fin 2) (t : ℝ≥0) (ω : Ω) :
    stateMart hU z n i t ω = -(reIm (U (min t (exitNN hU z n ω)) ω) i - reIm (U 0 ω) i) :=
  itoState_sub_eq hU z n t ω i

theorem abs_stateMart_le (i : Fin 2) (t : ℝ≥0) (ω : Ω) :
    |stateMart hU z n i t ω| ≤ 2 * (n : ℝ) ^ 2 + 2 * n := by
  rw [stateMart_eq, abs_neg, ← Pi.sub_apply, ← reIm_sub]
  refine le_trans ?_ (norm_U_min_exitNN_sub_le hU z n ω t)
  fin_cases i
  · exact Complex.abs_re_le_norm _
  · exact Complex.abs_im_le_norm _

theorem continuous_stateMart (i : Fin 2) (ω : Ω) : Continuous fun t => stateMart hU z n i t ω := by
  simp only [stateMart_eq]
  exact (((continuous_apply i).comp (continuous_reIm.comp
    ((hU.cont ω).comp (continuous_id.min continuous_const)))).sub continuous_const).neg

theorem isStronglyProgressive_stateMart (i : Fin 2) :
    IsStronglyProgressive ℱ (stateMart hU z n i) := by
  have hU' : IsStronglyProgressive ℱ U :=
    StronglyAdapted.isStronglyProgressive_of_continuous
      (fun t => (hU.adapted t).stronglyMeasurable) hU.cont
  have h1 := hU'.stoppedProcess (isStoppingTime_exitNN hU z n)
  simp only [funext fun t => funext fun ω => stoppedProcess_coe_min U (exitNN hU z n) t ω] at h1
  have h2 : IsStronglyProgressive ℱ fun t ω => reIm (U (min t (exitNN hU z n ω)) ω) i := fun j =>
    ((continuous_apply i).comp continuous_reIm).comp_stronglyMeasurable (h1 j)
  have h3 : IsStronglyProgressive ℱ fun (_ : ℝ≥0) ω => reIm (U 0 ω) i :=
    StronglyAdapted.isStronglyProgressive_of_continuous
      (fun t => (stronglyMeasurable_reIm_U hU 0 i).mono (ℱ.mono bot_le)) fun _ => continuous_const
  have : stateMart hU z n i =
      fun t ω => -(reIm (U (min t (exitNN hU z n ω)) ω) i - reIm (U 0 ω) i) :=
    funext fun t => funext fun ω => stateMart_eq hU z n i t ω
  rw [this]
  exact fun j => ((h2 j).sub (h3 j)).neg

/-- The bracket `A^{ij}_t = Σⁱʲ (t ∧ τ_n)` of the martingale parts. -/
@[expose] noncomputable def stateBracket (i j : Fin 2) (t : ℝ≥0) (ω : Ω) : ℝ :=
  covMatrix a b c i j * min (t : ℝ) (exitR hU z n ω)

theorem continuous_stateMart_mul_sub (i j : Fin 2) (ω : Ω) :
    Continuous fun t => stateMart hU z n i t ω * stateMart hU z n j t ω -
      stateBracket hU z n i j t ω :=
  ((continuous_stateMart hU z n i ω).mul (continuous_stateMart hU z n j ω)).sub
    (continuous_const.mul (NNReal.continuous_coe.min continuous_const))

theorem covMatrix_comm (i j : Fin 2) : covMatrix a b c i j = covMatrix a b c j i := by
  fin_cases i <;> fin_cases j <;> rfl

section Martingales

variable [IsProbabilityMeasure P]

theorem isContLocalMartingale_stateMart (i : Fin 2) :
    IsContLocalMartingale ℱ (stateMart hU z n i) P :=
  isContLocalMartingale_itoState_sub hU z n i

theorem isContLocalMartingale_stateMart_mul (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (i j : Fin 2) :
    IsContLocalMartingale ℱ (fun t ω => stateMart hU z n i t ω * stateMart hU z n j t ω -
      stateBracket hU z n i j t ω) P := by
  have h := isContLocalMartingale_itoState_mul_sub hU z n ha hc i j
  refine h.congr_fun' fun t ω => ?_
  simp only [stateMart, stateBracket, pathIntegral_itoQ]

end Martingales

/-! ### Indicators of stochastic intervals `[0, S]` -/

/-- The indicator `1_{t ≤ S}` of a finite random time. -/
@[expose] noncomputable def beforeTime (S : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if t ≤ S ω then 1 else 0

theorem isStronglyProgressive_beforeTime {S : Ω → ℝ≥0}
    (hS : IsStoppingTime ℱ fun ω => (S ω : WithTop ℝ≥0)) :
    IsStronglyProgressive ℱ (beforeTime S) :=
  Infrastructure.isStronglyProgressive_indicator_le_nnreal hS

theorem beforeTime_toNNReal (S : Ω → ℝ≥0) (ω : Ω) (s : ℝ) :
    beforeTime S s.toNNReal ω = (Iic (S ω : ℝ)).indicator (fun _ => (1 : ℝ)) s := by
  have key : s.toNNReal ≤ S ω ↔ s ≤ (S ω : ℝ) := Real.toNNReal_le_iff_le_coe
  simp only [beforeTime, key, indicator, mem_Iic]

/-- `∫₀ᵗ 1_{s ≤ S} ξ_s ds = ∫₀^{t ∧ S} ξ_s ds`. -/
theorem pathIntegral_beforeTime_mul (S : Ω → ℝ≥0) {ξ : ℝ≥0 → Ω → ℝ} (ω : Ω) (t : ℝ≥0) :
    pathIntegral (fun s ω => beforeTime S s ω * ξ s ω) t ω = pathIntegral ξ (min t (S ω)) ω := by
  simp only [pathIntegral, beforeTime_toNNReal, NNReal.coe_min]
  rw [← integral_indicator_Iic_eq (S ω).coe_nonneg t.coe_nonneg]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [indicator]
  split_ifs <;> simp

theorem intervalIntegrable_beforeTime_mul (S : Ω → ℝ≥0) (ω : Ω) {φ : ℝ → ℝ} {t : ℝ≥0}
    (hφ : IntervalIntegrable φ volume 0 t) :
    IntervalIntegrable (fun s => beforeTime S s.toNNReal ω * φ s) volume 0 t := by
  simp only [beforeTime_toNNReal]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg] at hφ ⊢
  refine hφ.bdd_mul (c := 1) (measurable_const.indicator measurableSet_Iic).aestronglyMeasurable
    (ae_of_all _ fun s => ?_)
  simp only [indicator]
  split_ifs <;> simp

theorem pathIntegral_sub {ξ η : ℝ≥0 → Ω → ℝ} {ω : Ω} {t : ℝ≥0}
    (hξ : IntervalIntegrable (fun s : ℝ => ξ s.toNNReal ω) volume 0 t)
    (hη : IntervalIntegrable (fun s : ℝ => η s.toNNReal ω) volume 0 t) :
    pathIntegral (fun s ω => ξ s ω - η s ω) t ω = pathIntegral ξ t ω - pathIntegral η t ω :=
  intervalIntegral.integral_sub hξ hη

/-! ### The sector state -/

variable (k : ℕ)

/-- Coordinate bookkeeping: coordinates `0, 1` of the sector state carry `(Re, Im)` of `f` stopped
at `S_{k+1}`, coordinates `2, 3` carry `f` stopped at `S_k`. -/
@[expose] def toFin2 : Fin 4 → Fin 2 := ![0, 1, 0, 1]

/-- The stopping time attached to the coordinate `i`: `S_{k+1}` for `i < 2`, `S_k` otherwise. -/
@[expose] noncomputable def secStop (i : Fin 4) (ω : Ω) : ℝ≥0 :=
  ![sectorTime hU z n (k + 1) ω, sectorTime hU z n (k + 1) ω, sectorTime hU z n k ω,
    sectorTime hU z n k ω] i

/-- **The sector state** `X_t = (Re f_{t ∧ S_{k+1}}, Im f_{t ∧ S_{k+1}}, Re f_{t ∧ S_k}, Im f_{t ∧ S_k})`. -/
@[expose] noncomputable def secState (t : ℝ≥0) (ω : Ω) (i : Fin 4) : ℝ :=
  itoState hU z n (min t (secStop hU z n k i ω)) ω (toFin2 i)

/-- The drift of the sector state: `1_{t ≤ S} A_t` coordinatewise. -/
@[expose] noncomputable def secDrift (t : ℝ≥0) (ω : Ω) (i : Fin 4) : ℝ :=
  beforeTime (secStop hU z n k i) t ω * itoDrift hU z n t ω (toFin2 i)

/-- The diffusion matrix of the sector state: `Σ` on the `(i, j)`-block, times the indicator of
`[0, S_{k+1} ∧ S_k]` for mixed or lower blocks and of `[0, S_{k+1}]` on the upper block. -/
@[expose] noncomputable def secQ (t : ℝ≥0) (ω : Ω) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => beforeTime (fun ω => min (secStop hU z n k i ω) (secStop hU z n k j ω)) t ω *
    covMatrix a b c (toFin2 i) (toFin2 j)

theorem secQ_apply (t : ℝ≥0) (ω : Ω) (i j : Fin 4) :
    secQ hU z n k t ω i j =
      beforeTime (fun ω => min (secStop hU z n k i ω) (secStop hU z n k j ω)) t ω *
        covMatrix a b c (toFin2 i) (toFin2 j) := rfl

@[simp] theorem toFin2_zero : toFin2 0 = 0 := rfl
@[simp] theorem toFin2_one : toFin2 1 = 1 := rfl
@[simp] theorem toFin2_two : toFin2 2 = 0 := rfl
@[simp] theorem toFin2_three : toFin2 3 = 1 := rfl

theorem secStop_of_lt {i : Fin 4} (hi : (i : ℕ) < 2) (ω : Ω) :
    secStop hU z n k i ω = sectorTime hU z n (k + 1) ω := by
  fin_cases i <;> first | rfl | exact absurd hi (by decide)

theorem secStop_of_not_lt {i : Fin 4} (hi : ¬ (i : ℕ) < 2) (ω : Ω) :
    secStop hU z n k i ω = sectorTime hU z n k ω := by
  fin_cases i <;> first | rfl | exact absurd (by decide) hi

theorem isStoppingTime_secStop (i : Fin 4) :
    IsStoppingTime ℱ fun ω => (secStop hU z n k i ω : WithTop ℝ≥0) := by
  by_cases hi : (i : ℕ) < 2
  · simp only [secStop_of_lt hU z n k hi]; exact isStoppingTime_sectorTime hU z n _
  · simp only [secStop_of_not_lt hU z n k hi]; exact isStoppingTime_sectorTime hU z n _

/-- `min (S_i, S_j)` is `S_{k+1}` on the upper block and `S_k` elsewhere. -/
theorem min_secStop_of_lt {i j : Fin 4} (hi : (i : ℕ) < 2) (hj : (j : ℕ) < 2) (ω : Ω) :
    min (secStop hU z n k i ω) (secStop hU z n k j ω) = sectorTime hU z n (k + 1) ω := by
  rw [secStop_of_lt hU z n k hi, secStop_of_lt hU z n k hj, min_self]

theorem min_secStop_of_not_lt_left {i j : Fin 4} (hi : ¬ (i : ℕ) < 2) (ω : Ω) :
    min (secStop hU z n k i ω) (secStop hU z n k j ω) = sectorTime hU z n k ω := by
  rw [secStop_of_not_lt hU z n k hi]
  refine min_eq_left ?_
  by_cases hj : (j : ℕ) < 2
  · rw [secStop_of_lt hU z n k hj]; exact sectorTime_le_succ hU z n k ω
  · rw [secStop_of_not_lt hU z n k hj]

theorem min_secStop_of_not_lt_right {i j : Fin 4} (hj : ¬ (j : ℕ) < 2) (ω : Ω) :
    min (secStop hU z n k i ω) (secStop hU z n k j ω) = sectorTime hU z n k ω := by
  rw [min_comm]; exact min_secStop_of_not_lt_left hU z n k hj ω

/-! #### Measurability, continuity, integrability of the sector state -/

theorem isStronglyProgressive_itoState_min {S : Ω → ℝ≥0}
    (hS : IsStoppingTime ℱ fun ω => (S ω : WithTop ℝ≥0)) (i : Fin 2) :
    IsStronglyProgressive ℱ fun t ω => itoState hU z n (min t (S ω)) ω i := by
  have h := (isStronglyProgressive_itoState hU z n).stoppedProcess hS
  simp only [funext fun t => funext fun ω => stoppedProcess_coe_min (itoState hU z n) S t ω] at h
  exact fun j => (continuous_apply i).comp_stronglyMeasurable (h j)

theorem continuous_vec4 :
    Continuous fun q : ℝ × ℝ × ℝ × ℝ => (![q.1, q.2.1, q.2.2.1, q.2.2.2] : Fin 4 → ℝ) := by
  refine continuous_pi fun j => ?_
  fin_cases j
  · exact continuous_fst
  · exact continuous_snd.fst
  · exact continuous_snd.snd.fst
  · exact continuous_snd.snd.snd

theorem isStronglyProgressive_secState : IsStronglyProgressive ℱ (secState hU z n k) := by
  intro j
  have h : ∀ i : Fin 4, StronglyMeasurable[Subtype.instMeasurableSpace.prod (ℱ j)]
      fun p : Iic j × Ω => secState hU z n k p.1 p.2 i := fun i =>
    isStronglyProgressive_itoState_min hU z n (isStoppingTime_secStop hU z n k i) (toFin2 i) j
  have : (fun p : Iic j × Ω => secState hU z n k p.1 p.2) = fun p =>
      ![secState hU z n k p.1 p.2 0, secState hU z n k p.1 p.2 1, secState hU z n k p.1 p.2 2,
        secState hU z n k p.1 p.2 3] := by
    funext p; ext i; fin_cases i <;> rfl
  rw [this]
  exact continuous_vec4.comp_stronglyMeasurable ((h 0).prodMk ((h 1).prodMk ((h 2).prodMk (h 3))))

theorem continuous_secState (ω : Ω) : Continuous fun t => secState hU z n k t ω := by
  refine continuous_pi fun i => ?_
  exact (continuous_apply (toFin2 i)).comp
    ((continuous_itoState hU z n ω).comp (continuous_id.min continuous_const))

theorem isStronglyProgressive_secDrift : IsStronglyProgressive ℱ (secDrift hU z n k) := by
  intro j
  have h : ∀ i : Fin 4, StronglyMeasurable[Subtype.instMeasurableSpace.prod (ℱ j)]
      fun p : Iic j × Ω => secDrift hU z n k p.1 p.2 i := fun i =>
    (isStronglyProgressive_beforeTime (isStoppingTime_secStop hU z n k i) j).mul
      ((continuous_apply (toFin2 i)).comp_stronglyMeasurable
        (isStronglyProgressive_itoDrift hU z n j))
  have : (fun p : Iic j × Ω => secDrift hU z n k p.1 p.2) = fun p =>
      ![secDrift hU z n k p.1 p.2 0, secDrift hU z n k p.1 p.2 1, secDrift hU z n k p.1 p.2 2,
        secDrift hU z n k p.1 p.2 3] := by
    funext p; ext i; fin_cases i <;> rfl
  rw [this]
  exact continuous_vec4.comp_stronglyMeasurable ((h 0).prodMk ((h 1).prodMk ((h 2).prodMk (h 3))))

theorem intervalIntegrable_secDrift (ω : Ω) (i : Fin 4) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => secDrift hU z n k s.toNNReal ω i) volume 0 t :=
  intervalIntegrable_beforeTime_mul _ ω (intervalIntegrable_itoDrift hU z n ω (toFin2 i) t)

/-- The entries of `secQ`, as a matrix-valued process, assemble continuously from the two
indicators. -/
theorem secQ_eq (t : ℝ≥0) (ω : Ω) :
    secQ hU z n k t ω = Matrix.of fun (i j : Fin 4) =>
      (if (i : ℕ) < 2 ∧ (j : ℕ) < 2 then beforeTime (sectorTime hU z n (k + 1)) t ω
        else beforeTime (sectorTime hU z n k) t ω) * covMatrix a b c (toFin2 i) (toFin2 j) := by
  ext i j
  rw [secQ_apply, Matrix.of_apply]
  congr 1
  by_cases hij : (i : ℕ) < 2 ∧ (j : ℕ) < 2
  · rw [if_pos hij]
    simp only [beforeTime, min_secStop_of_lt hU z n k hij.1 hij.2]
  · rw [if_neg hij]
    rcases not_and_or.1 hij with hi | hj
    · simp only [beforeTime, min_secStop_of_not_lt_left hU z n k hi]
    · simp only [beforeTime, min_secStop_of_not_lt_right hU z n k hj]

theorem continuous_matrixOf_ite :
    Continuous fun q : ℝ × ℝ => (Matrix.of fun (i j : Fin 4) =>
      (if (i : ℕ) < 2 ∧ (j : ℕ) < 2 then q.1 else q.2) * covMatrix a b c (toFin2 i) (toFin2 j)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.of_apply]
  split_ifs
  · exact continuous_fst.mul continuous_const
  · exact continuous_snd.mul continuous_const

theorem isStronglyProgressive_secQ : IsStronglyProgressive ℱ (secQ hU z n k) := by
  intro j
  have h1 := isStronglyProgressive_beforeTime (isStoppingTime_sectorTime hU z n (k + 1)) j
  have h2 := isStronglyProgressive_beforeTime (isStoppingTime_sectorTime hU z n k) j
  have : (fun p : Iic j × Ω => secQ hU z n k p.1 p.2) =
      (fun q : ℝ × ℝ => (Matrix.of fun (i j : Fin 4) =>
        (if (i : ℕ) < 2 ∧ (j : ℕ) < 2 then q.1 else q.2) * covMatrix a b c (toFin2 i) (toFin2 j))) ∘
      fun p : Iic j × Ω => (beforeTime (sectorTime hU z n (k + 1)) p.1 p.2,
        beforeTime (sectorTime hU z n k) p.1 p.2) := by
    funext p
    exact secQ_eq hU z n k p.1 p.2
  rw [this]
  exact (continuous_matrixOf_ite (a := a) (b := b) (c := c)).comp_stronglyMeasurable (h1.prodMk h2)

theorem intervalIntegrable_secQ (ω : Ω) (i j : Fin 4) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => secQ hU z n k s.toNNReal ω i j) volume 0 t := by
  simp only [secQ_apply]
  exact intervalIntegrable_beforeTime_mul _ ω intervalIntegrable_const

/-! #### The martingale hypotheses of Itô's formula for the sector state -/

theorem secState_sub_eq (t : ℝ≥0) (ω : Ω) (i : Fin 4) :
    secState hU z n k t ω i - secState hU z n k 0 ω i -
        pathIntegral (fun s ω => secDrift hU z n k s ω i) t ω =
      stateMart hU z n (toFin2 i) (min t (secStop hU z n k i ω)) ω := by
  simp only [secState, secDrift, stateMart, min_eq_left (zero_le : (0 : ℝ≥0) ≤ secStop hU z n k i ω)]
  rw [pathIntegral_beforeTime_mul]

theorem pathIntegral_secQ (ω : Ω) (i j : Fin 4) (t : ℝ≥0) :
    pathIntegral (fun s ω => secQ hU z n k s ω i j) t ω =
      covMatrix a b c (toFin2 i) (toFin2 j) *
        ((min t (min (secStop hU z n k i ω) (secStop hU z n k j ω)) : ℝ≥0) : ℝ) := by
  have : (fun s ω => secQ hU z n k s ω i j) = fun s ω =>
      beforeTime (fun ω => min (secStop hU z n k i ω) (secStop hU z n k j ω)) s ω *
        covMatrix a b c (toFin2 i) (toFin2 j) := funext fun s => funext fun ω => secQ_apply _ _ _ _ _ _ _ _
  rw [this, pathIntegral_beforeTime_mul]
  simp [pathIntegral, mul_comm]

theorem coe_min_le_exitR {S : Ω → ℝ≥0} (hS : ∀ ω, S ω ≤ exitNN hU z n ω) (t : ℝ≥0) (ω : Ω) :
    ((min t (S ω) : ℝ≥0) : ℝ) ≤ exitR hU z n ω :=
  (le_exitNN_iff hU z n).1 (le_trans (min_le_right _ _) (hS ω))

section Martingales

variable [IsProbabilityMeasure P]

/-- **Hypothesis `hM` of Itô's formula** for the sector state. -/
theorem ito_hM_sec (i : Fin 4) :
    IsContLocalMartingale ℱ (fun t ω => secState hU z n k t ω i - secState hU z n k 0 ω i -
      pathIntegral (fun s ω => secDrift hU z n k s ω i) t ω) P := by
  have h := (isContLocalMartingale_stateMart hU z n (toFin2 i)).stopped_min_of_continuous ℱ
    (continuous_stateMart hU z n (toFin2 i)) (isStoppingTime_secStop hU z n k i)
  exact h.congr_fun' fun t ω => (secState_sub_eq hU z n k t ω i).symm

/-- **Hypothesis `hMM` of Itô's formula** for the sector state: the brackets within a block are
those of the stopped state; the cross brackets are `Σ (t ∧ S_k)`. -/
theorem ito_hMM_sec (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (i j : Fin 4) :
    IsContLocalMartingale ℱ (fun t ω =>
      (secState hU z n k t ω i - secState hU z n k 0 ω i -
          pathIntegral (fun s ω => secDrift hU z n k s ω i) t ω) *
        (secState hU z n k t ω j - secState hU z n k 0 ω j -
          pathIntegral (fun s ω => secDrift hU z n k s ω j) t ω) -
        pathIntegral (fun s ω => secQ hU z n k s ω i j) t ω) P := by
  have hρσ : ∀ ω, sectorTime hU z n k ω ≤ sectorTime hU z n (k + 1) ω :=
    sectorTime_le_succ hU z n k
  have hσ := isStoppingTime_sectorTime hU z n (k + 1)
  have hρ := isStoppingTime_sectorTime hU z n k
  have hσle := sectorTime_le_exitNN hU z n (k + 1)
  have hρle := sectorTime_le_exitNN hU z n k
  have key : ∀ t ω, (secState hU z n k t ω i - secState hU z n k 0 ω i -
          pathIntegral (fun s ω => secDrift hU z n k s ω i) t ω) *
        (secState hU z n k t ω j - secState hU z n k 0 ω j -
          pathIntegral (fun s ω => secDrift hU z n k s ω j) t ω) -
        pathIntegral (fun s ω => secQ hU z n k s ω i j) t ω =
      stateMart hU z n (toFin2 i) (min t (secStop hU z n k i ω)) ω *
        stateMart hU z n (toFin2 j) (min t (secStop hU z n k j ω)) ω -
        covMatrix a b c (toFin2 i) (toFin2 j) *
          ((min t (min (secStop hU z n k i ω) (secStop hU z n k j ω)) : ℝ≥0) : ℝ) := by
    intro t ω
    rw [secState_sub_eq, secState_sub_eq, pathIntegral_secQ]
  refine IsContLocalMartingale.congr_fun' ?_ fun t ω => (key t ω).symm
  by_cases hi : (i : ℕ) < 2 <;> by_cases hj : (j : ℕ) < 2
  · -- upper block: both stopped at `S_{k+1}`
    simp only [secStop_of_lt hU z n k hi, secStop_of_lt hU z n k hj, min_self]
    have h := (isContLocalMartingale_stateMart_mul hU z n ha hc (toFin2 i) (toFin2 j))
      |>.stopped_min_of_continuous ℱ (continuous_stateMart_mul_sub hU z n _ _) hσ
    refine h.congr_fun' fun t ω => ?_
    simp only [stateBracket, min_eq_left (coe_min_le_exitR hU z n hσle t ω)]
  · -- `i` upper, `j` lower: cross bracket
    simp only [secStop_of_lt hU z n k hi, secStop_of_not_lt hU z n k hj,
      min_eq_right (hρσ _)]
    have h := isContLocalMartingale_min_mul_min (isContLocalMartingale_stateMart hU z n (toFin2 i))
      (continuous_stateMart hU z n (toFin2 i)) (isStronglyProgressive_stateMart hU z n (toFin2 j))
      (continuous_stateMart hU z n (toFin2 j)) (abs_stateMart_le hU z n (toFin2 j))
      (isContLocalMartingale_stateMart_mul hU z n ha hc (toFin2 i) (toFin2 j))
      (continuous_stateMart_mul_sub hU z n _ _) hρ hσ hρσ
    refine h.congr_fun' fun t ω => ?_
    simp only [stateBracket, min_eq_left (coe_min_le_exitR hU z n hρle t ω)]
  · -- `i` lower, `j` upper: cross bracket with the roles exchanged
    simp only [secStop_of_not_lt hU z n k hi, secStop_of_lt hU z n k hj,
      min_eq_left (hρσ _)]
    have h := isContLocalMartingale_min_mul_min (isContLocalMartingale_stateMart hU z n (toFin2 j))
      (continuous_stateMart hU z n (toFin2 j)) (isStronglyProgressive_stateMart hU z n (toFin2 i))
      (continuous_stateMart hU z n (toFin2 i)) (abs_stateMart_le hU z n (toFin2 i))
      (isContLocalMartingale_stateMart_mul hU z n ha hc (toFin2 j) (toFin2 i))
      (continuous_stateMart_mul_sub hU z n _ _) hρ hσ hρσ
    refine h.congr_fun' fun t ω => ?_
    simp only [stateBracket, min_eq_left (coe_min_le_exitR hU z n hρle t ω)]
    rw [mul_comm (stateMart hU z n (toFin2 j) _ ω), covMatrix_comm]
  · -- lower block: both stopped at `S_k`
    simp only [secStop_of_not_lt hU z n k hi, secStop_of_not_lt hU z n k hj, min_self]
    have h := (isContLocalMartingale_stateMart_mul hU z n ha hc (toFin2 i) (toFin2 j))
      |>.stopped_min_of_continuous ℱ (continuous_stateMart_mul_sub hU z n _ _) hρ
    refine h.congr_fun' fun t ω => ?_
    simp only [stateBracket, min_eq_left (coe_min_le_exitR hU z n hρle t ω)]

end Martingales

/-! #### The path stays in `argDomain`, and `argProd (X_t) = θ_{t ∧ S_{k+1}} - θ_{t ∧ S_k}` -/

theorem abs_argStopped_min_sub_le (t : ℝ≥0) (ω : Ω) :
    |argStopped hU z n (min t (sectorTime hU z n (k + 1) ω)) ω -
      argStopped hU z n (min t (sectorTime hU z n k ω)) ω| ≤ π / 2 := by
  by_cases h : t ≤ sectorTime hU z n k ω
  · rw [min_eq_left h, min_eq_left (le_trans h (sectorTime_le_succ hU z n k ω)), sub_self,
      abs_zero]
    positivity
  · have h' : sectorTime hU z n k ω < t := lt_of_not_ge h
    rw [min_eq_right (le_of_lt h')]
    exact abs_argStopped_sub_le hU z n (le_min (le_of_lt h') (sectorTime_le_succ hU z n k ω))
      (min_le_right _ _)

theorem secState_eq_polar {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) (t : ℝ≥0) :
    secState hU z n k t ω =
      ![‖stoppedF hU z n (min t (sectorTime hU z n (k + 1) ω)) ω‖ *
          Real.cos (argStopped hU z n (min t (sectorTime hU z n (k + 1) ω)) ω),
        ‖stoppedF hU z n (min t (sectorTime hU z n (k + 1) ω)) ω‖ *
          Real.sin (argStopped hU z n (min t (sectorTime hU z n (k + 1) ω)) ω),
        ‖stoppedF hU z n (min t (sectorTime hU z n k ω)) ω‖ *
          Real.cos (argStopped hU z n (min t (sectorTime hU z n k ω)) ω),
        ‖stoppedF hU z n (min t (sectorTime hU z n k ω)) ω‖ *
          Real.sin (argStopped hU z n (min t (sectorTime hU z n k ω)) ω)] := by
  ext i
  fin_cases i <;>
    simp [secState, secStop, itoState_eq_polar hU z n hz, argStopped_eq hU z n hz]

theorem prodConj_secState {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) (t : ℝ≥0) :
    prodConj (secState hU z n k t ω) =
      ((‖stoppedF hU z n (min t (sectorTime hU z n (k + 1) ω)) ω‖ *
        ‖stoppedF hU z n (min t (sectorTime hU z n k ω)) ω‖ : ℝ) : ℂ) *
        Complex.exp (((argStopped hU z n (min t (sectorTime hU z n (k + 1) ω)) ω -
          argStopped hU z n (min t (sectorTime hU z n k ω)) ω : ℝ) : ℂ) * Complex.I) := by
  rw [secState_eq_polar hU z n k hz t, prodConj_polar]

theorem norm_mul_norm_pos {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) (t : ℝ≥0) :
    0 < ‖stoppedF hU z n (min t (sectorTime hU z n (k + 1) ω)) ω‖ *
      ‖stoppedF hU z n (min t (sectorTime hU z n k ω)) ω‖ :=
  mul_pos (norm_pos_iff.2 (stoppedF_ne_zero hU z n hz _))
    (norm_pos_iff.2 (stoppedF_ne_zero hU z n hz _))

theorem secState_mem_argDomain {ω : Ω} (hz : 0 < absorbingTime (fun s => U s ω) z) (t : ℝ≥0) :
    secState hU z n k t ω ∈ argDomain := by
  change prodConj (secState hU z n k t ω) ∈ Complex.slitPlane
  rw [prodConj_secState hU z n k hz t]
  exact real_mul_exp_mem_slitPlane (norm_mul_norm_pos hU z n k hz t)
    (abs_argStopped_min_sub_le hU z n k t ω)

/-- **The pathwise identity** `argProd (X_t) = θ̃_{t ∧ S_{k+1}} - θ̃_{t ∧ S_k}`. -/
theorem argProd_secState (t : ℝ≥0) (ω : Ω) :
    argProd (secState hU z n k t ω) =
      argStopped hU z n (min t (sectorTime hU z n (k + 1) ω)) ω -
        argStopped hU z n (min t (sectorTime hU z n k ω)) ω := by
  by_cases hz : 0 < absorbingTime (fun s => U s ω) z
  · rw [argProd, prodConj_secState hU z n k hz t]
    exact arg_real_mul_exp (norm_mul_norm_pos hU z n k hz t)
      (lt_of_le_of_lt (abs_argStopped_min_sub_le hU z n k t ω) (by linarith [Real.pi_pos]))
  · have hX : secState hU z n k t ω = 0 := by
      ext i; simp [secState, itoState_eq_zero hU z n hz]
    rw [hX, argStopped_eq_zero hU z n hz, argStopped_eq_zero hU z n hz, sub_zero]
    simp [argProd, prodConj]

/-! #### The Itô integrand -/

/-- **The Itô integrand of `argProd`** at the sector state is `(1_{s ≤ S_{k+1}} - 1_{s ≤ S_k})`
times the drift density `thetaDrift` (`eqn-theta-t-op`): before `S_k` the `v`-terms cancel the
`w`-terms, between `S_k` and `S_{k+1}` only the `w`-terms survive. -/
theorem ito_integrand_argProd (ω : Ω) (s : ℝ≥0)
    (hs : 0 < absorbingTime (fun r => U r ω) z ∨ 0 < s) :
    ∑ i, fderiv ℝ argProd (secState hU z n k s ω) (Pi.single i 1) * secDrift hU z n k s ω i +
      (1 / 2) * ∑ i, ∑ j, iteratedFDeriv ℝ 2 argProd (secState hU z n k s ω)
        ![Pi.single i 1, Pi.single j 1] * secQ hU z n k s ω i j =
      beforeTime (sectorTime hU z n (k + 1)) s ω * thetaDrift hU z n s ω -
        beforeTime (sectorTime hU z n k) s ω * thetaDrift hU z n s ω := by
  by_cases hz : 0 < absorbingTime (fun r => U r ω) z
  · have hD := secState_mem_argDomain hU z n k hz s
    simp only [fderiv_argProd_single hD, iteratedFDeriv_argProd hD, Fin.sum_univ_four, secQ_apply]
    have hq : ∀ r : ℝ≥0, (stoppedF hU z n r ω).re ^ 2 + (stoppedF hU z n r ω).im ^ 2 ≠ 0 :=
      fun r => ne_of_gt (itoState_mem_posSet₂ hU z n hz r)
    have hq' : ∀ r : ℝ≥0, (stoppedF hU z n r ω).re * (stoppedF hU z n r ω).re +
        (stoppedF hU z n r ω).im * (stoppedF hU z n r ω).im ≠ 0 := fun r => by
      rw [← sq, ← sq]; exact hq r
    by_cases hsσ : s ≤ sectorTime hU z n (k + 1) ω
    · have hsτ : s ≤ exitNN hU z n ω := le_trans hsσ (sectorTime_le_exitNN hU z n _ ω)
      have hγ : beforeExit hU z n s ω = 1 := by simp [beforeExit, hsτ]
      have e1 : min s (sectorTime hU z n (k + 1) ω) = s := min_eq_left hsσ
      by_cases hsρ : s ≤ sectorTime hU z n k ω
      · have e2 : min s (sectorTime hU z n k ω) = s := min_eq_left hsρ
        have hs2 := hq s
        have hs2' := hq' s
        simp [secDrift, secState, secStop, beforeTime, hsσ, hsρ, e1, e2, gradArg, hessArg,
          itoDrift, thetaDrift, hγ, muFn, covMatrix, itoState, reIm, Complex.div_re,
          Complex.div_im, Complex.normSq_apply, Pi.single_apply]
        field_simp
        ring
      · have hρs : sectorTime hU z n k ω < s := lt_of_not_ge hsρ
        have e2 : min s (sectorTime hU z n k ω) = sectorTime hU z n k ω :=
          min_eq_right (le_of_lt hρs)
        have hs2 := hq s
        have hs2' := hq' s
        have hρ2 := hq (sectorTime hU z n k ω)
        have hρ2' := hq' (sectorTime hU z n k ω)
        simp [secDrift, secState, secStop, beforeTime, hsσ, hsρ, e1, e2, gradArg, hessArg,
          itoDrift, thetaDrift, hγ, muFn, covMatrix, itoState, reIm, Complex.div_re,
          Complex.div_im, Complex.normSq_apply, Pi.single_apply]
        field_simp
        ring
    · have hsρ : ¬ s ≤ sectorTime hU z n k ω := fun h =>
        hsσ (le_trans h (sectorTime_le_succ hU z n k ω))
      simp [secDrift, beforeTime, hsσ, hsρ, secStop]
  · have hs' : 0 < s := hs.resolve_left hz
    have hτ0 : exitNN hU z n ω = 0 := by
      rw [exitNN, exitR_eq_zero hU z n hz, Real.toNNReal_zero]
    have hσ0 : sectorTime hU z n (k + 1) ω = 0 :=
      le_antisymm (hτ0 ▸ sectorTime_le_exitNN hU z n _ ω) zero_le
    have hρ0 : sectorTime hU z n k ω = 0 :=
      le_antisymm (hτ0 ▸ sectorTime_le_exitNN hU z n _ ω) zero_le
    have hns : ¬ s ≤ (0 : ℝ≥0) := not_le.2 hs'
    simp [Fin.sum_univ_four, secDrift, secQ_apply, beforeTime, secStop, hσ0, hρ0, hns]

/-! ### Applying Itô's formula -/

variable [IsProbabilityMeasure P]

/-- **The increment of `Θ^n` over the sector `[S_k, S_{k+1}]` is a continuous local martingale**
(`step:polar-real-imag`, imaginary part, between two sector times). For `0 < a`, `c² ≤ ab`,
`z ≠ 0`: `t ↦ Θ^n_{t ∧ S_{k+1}} - Θ^n_{t ∧ S_k}` is a continuous `ℱ`-local martingale. -/
theorem isContLocalMartingale_sectorIncrement (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0) :
    IsContLocalMartingale ℱ (fun t ω =>
      thetaMart hU z n (min t (sectorTime hU z n (k + 1) ω)) ω -
        thetaMart hU z n (min t (sectorTime hU z n k ω)) ω) P := by
  have hAint : ∀ᵐ ω ∂P, ∀ (i : Fin 4) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => secDrift hU z n k (Real.toNNReal s) ω i) volume 0 t :=
    Eventually.of_forall fun ω i t => intervalIntegrable_secDrift hU z n k ω i t
  have hQint : ∀ᵐ ω ∂P, ∀ (i j : Fin 4) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => secQ hU z n k (Real.toNNReal s) ω i j) volume 0 t :=
    Eventually.of_forall fun ω i j t => intervalIntegrable_secQ hU z n k ω i j t
  have hXD : ∀ᵐ ω ∂P, ∀ t, secState hU z n k t ω ∈ argDomain := by
    filter_upwards [ae_pos_absorbingTime hU z hz] with ω hω
    exact fun t => secState_mem_argDomain hU z n k hω t
  have h := External.ito_formula ℱ (secState hU z n k) (secDrift hU z n k) (secQ hU z n k)
    (isStronglyProgressive_secState hU z n k) (continuous_secState hU z n k)
    (isStronglyProgressive_secDrift hU z n k) hAint (isStronglyProgressive_secQ hU z n k) hQint
    (ito_hM_sec hU z n k) (ito_hMM_sec hU z n k ha hc)
    argDomain isOpen_argDomain argProd measurable_argProd contDiffOn_argProd hXD
  refine h.congr_fun' fun t ω => ?_
  rw [argProd_secState, argProd_secState, min_eq_left zero_le, min_eq_left zero_le,
    sub_self, sub_zero]
  have hint : pathIntegral (fun s ω =>
      ∑ i, fderiv ℝ argProd (secState hU z n k s ω) (Pi.single i 1) * secDrift hU z n k s ω i +
        (1 / 2) * ∑ i, ∑ j, iteratedFDeriv ℝ 2 argProd (secState hU z n k s ω)
          ![Pi.single i 1, Pi.single j 1] * secQ hU z n k s ω i j) t ω =
      pathIntegral (fun s ω => beforeTime (sectorTime hU z n (k + 1)) s ω * thetaDrift hU z n s ω -
        beforeTime (sectorTime hU z n k) s ω * thetaDrift hU z n s ω) t ω :=
    pathIntegral_congr_pos (fun s hs => ito_integrand_argProd hU z n k ω s (Or.inr hs)) t
  rw [hint, pathIntegral_sub (intervalIntegrable_beforeTime_mul _ ω
    (intervalIntegrable_thetaDrift hU z n ω t)) (intervalIntegrable_beforeTime_mul _ ω
    (intervalIntegrable_thetaDrift hU z n ω t)), pathIntegral_beforeTime_mul,
    pathIntegral_beforeTime_mul]
  simp only [thetaMart]
  ring

end

end ComplexSLE.Internal.Polar

end
