/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.Lemma38Meas
public import ComplexSLE.Internal.Stationary.PathStatMarkov
public import ComplexSLE.Internal.Polar.PolarSigmaTop

/-!
# Lemma 3.10, the stopping times and the strong Markov step (M7/E2)

Fix an adapted `SLE_Σ` driver `U`, a point `z`, a level `t̃` and put `θ = σ_z(t̃)`
(`sigmaTop`, an a.s. finite stopping time). For `k : ℕ` let

* `hitK k = hitTime U z (lvl k)` (the paper's `τ_k`, with `lvl k = 16^{-k}` there),
  `tauHat k = min (hitK k) θ` (an a.s. finite `ℱ`-stopping time);
* `rhoK k = |f_{τ̂_k}(z)|` and `Yk k = 1_{τ_k ≤ θ} exp (-A(τ̂_k))`, where `A` is the clock; the pair
  `(rhoK k, Yk k)` is measurable for the σ-algebra `ℱ_{τ̂_k}`.

The strong Markov step (`lintegral_gset_mul_Yk`): for the good set
`𝒢 = {v ∈ CPath | |v_s| ≤ 1/16 for s ≤ u₀}` of paths with small oscillation,

  `E[ 1_𝒢(V_k) · Y_k ] = Λ(𝒢) · E[Y_k]`,

where `V_k` is the post-`τ̂_k` driver rescaled by `|f_{τ̂_k}(z)|⁻¹` and `Λ` the law of the driver. This
is `lintegral_comp_scale_postPath` with the `ℱ_{τ̂_k}`-measurable pair `(rhoK k, Yk k)`.
Uses the EXTERNAL `strongMarkov_sleDriver` (through `lintegral_comp_scale_postPath`).
-/

public section

open scoped NNReal ENNReal Topology Real
open Set Metric Filter MeasureTheory ProbabilityTheory

namespace ComplexSLE.Internal

open Polar

section Defs

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

variable (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) (tt : ℝ≥0)

/-- The first time at which `dist(z, L_t) ≤ lvl k` (the paper's `τ_k`). -/
@[expose] noncomputable def hitK (k : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  hitTime (fun s => U s ω) z (lvl k)

/-- `τ̂_k = τ_k ∧ σ_z(t̃)`, an a.s. finite stopping time. -/
@[expose] noncomputable def tauHat (k : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  min (hitK (U := U) z k ω) (sigmaTop hU z tt ω)

include hU in
theorem isStoppingTime_hitK (k : ℕ) : IsStoppingTime ℱ (hitK (U := U) z k) :=
  isStoppingTime_hitTime hU.cont hU.adapted z (lvl k)

theorem isStoppingTime_tauHat (k : ℕ) : IsStoppingTime ℱ (tauHat hU z tt k) :=
  (isStoppingTime_hitK hU z k).min (isStoppingTime_sigmaTop hU z tt)

/-- `|f_{τ̂_k}(z)|` (the restart scale). -/
@[expose] noncomputable def rhoK (k : ℕ) (ω : Ω) : ℝ≥0 :=
  ‖centeredOrZero U hU.cont z (tauHat hU z tt k ω).untopA ω‖₊

/-- The clock at `τ̂_k`. -/
@[expose] noncomputable def cK (k : ℕ) (ω : Ω) : ℝ :=
  clockOrZero U hU.cont z (tauHat hU z tt k ω).untopA ω

open Classical in
/-- `Y_k = 1_{τ_k ≤ θ} exp (-A(τ̂_k))`. -/
@[expose] noncomputable def Yk (k : ℕ) (ω : Ω) : ℝ :=
  (if hitK (U := U) z k ω ≤ sigmaTop hU z tt ω then (1 : ℝ) else 0) * Real.exp (-cK hU z tt k ω)

theorem measurable_rhoK_Yk (k : ℕ) :
    Measurable[(isStoppingTime_tauHat hU z tt k).measurableSpace]
      fun ω => (rhoK hU z tt k ω, Yk hU z tt k ω) := by
  have hτ := isStoppingTime_tauHat hU z tt k
  have h1 := measurable_stoppedValue (isStronglyProgressive_centeredOrZero hU.cont hU.adapted z) hτ
  have h2 := measurable_stoppedValue (isStronglyProgressive_clockOrZero hU.cont hU.adapted z) hτ
  have h3 : MeasurableSet[hτ.measurableSpace]
      {ω | hitK (U := U) z k ω ≤ sigmaTop hU z tt ω} :=
    IsStoppingTime.measurableSet_stopping_time_le_min (isStoppingTime_hitK hU z k)
      (isStoppingTime_sigmaTop hU z tt)
  refine Measurable.prodMk ?_ ?_
  · exact measurable_nnnorm.comp h1
  · have h4 : Measurable[hτ.measurableSpace] (fun ω => Real.exp (-cK hU z tt k ω)) :=
      Real.measurable_exp.comp h2.neg
    have h5 : Measurable[hτ.measurableSpace]
        (fun ω => if hitK (U := U) z k ω ≤ sigmaTop hU z tt ω then (1 : ℝ) else 0) :=
      Measurable.ite h3 measurable_const measurable_const
    exact h5.mul h4

theorem cK_nonneg (k : ℕ) (ω : Ω) : 0 ≤ cK hU z tt k ω := by
  unfold cK clockOrZero
  split_ifs with h
  · exact clock_nonneg (hU.cont ω) h
  · exact le_rfl

theorem Yk_nonneg (k : ℕ) (ω : Ω) : 0 ≤ Yk hU z tt k ω := by
  unfold Yk
  split_ifs <;> simp [Real.exp_nonneg]

theorem Yk_le_one (k : ℕ) (ω : Ω) : Yk hU z tt k ω ≤ 1 := by
  unfold Yk
  have : Real.exp (-cK hU z tt k ω) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith [cK_nonneg hU z tt k ω]
  split_ifs <;> simp [this]

/-! ### The good set of small-oscillation paths -/

/-- The paths `v` with `|v_s| ≤ 1/16` for all `s ≤ u₀`. -/
@[expose] def Gset (u₀ : ℝ≥0) : Set CPath := {v | ∀ s : ℝ≥0, s ≤ u₀ → ‖v.1 s‖ ≤ 1 / 16}

theorem measurableSet_Gset (u₀ : ℝ≥0) : MeasurableSet (Gset u₀) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  set S : Set ℝ≥0 := {u₀} ∪ (D ∩ Iio u₀) with hS
  have hSc : S.Countable := (countable_singleton _).union (hDc.mono inter_subset_left)
  have key : Gset u₀ = ⋂ q ∈ S, {v : CPath | ‖v.1 q‖ ≤ 1 / 16} := by
    ext v
    simp only [Gset, mem_ofPred_eq, mem_iInter]
    constructor
    · intro h q hq
      rcases hq with hq | hq
      · rw [mem_singleton_iff.1 hq]; exact h _ le_rfl
      · exact h q hq.2.le
    · intro h s hs
      rcases hs.eq_or_lt with hs | hs
      · exact h u₀ (Or.inl rfl) |> fun h' => by rw [hs]; exact h'
      · have hcl : IsClosed {s' : ℝ≥0 | ‖v.1 s'‖ ≤ 1 / 16} :=
          isClosed_le (continuous_norm.comp v.2) continuous_const
        have hsub : S ⊆ {s' : ℝ≥0 | ‖v.1 s'‖ ≤ 1 / 16} := fun q hq => h q hq
        have hmem : s ∈ closure (Iio u₀ ∩ D) := hDd.open_subset_closure_inter isOpen_Iio hs
        refine closure_minimal ?_ hcl hmem
        intro q hq
        exact hsub (Or.inr ⟨hq.2, hq.1⟩)
  rw [key]
  exact MeasurableSet.biInter hSc fun q _ =>
    measurableSet_le (measurable_norm.comp (CPath.measurable_eval q)) measurable_const

/-! ### The rescaled post-`τ` path is the restarted driver -/

theorem scale_postPath_apply (hU : IsSLEDriverAdapted a b c U P ℱ) (τ : Ω → WithTop ℝ≥0)
    (ρ : ℝ≥0) (ω : Ω) (s : ℝ≥0) :
    (CPath.scale ρ⁻¹ (postPath hU τ ω)).1 s =
      restartDriver (fun r => U r ω) (τ ω).untopA ρ s := by
  simp only [CPath.scale, postPath, CPath.ofDriver, postDriver, restartDriver]
  have h1 : s / (ρ⁻¹) ^ 2 = ρ ^ 2 * s := by
    rw [inv_pow, div_inv_eq_mul, mul_comm]
  rw [h1, add_comm ((τ ω).untopA) (ρ ^ 2 * s)]
  congr 1
  rw [show (((ρ⁻¹ : ℝ≥0) : ℝ) : ℂ) = ((ρ : ℝ) : ℂ)⁻¹ by
    rw [NNReal.coe_inv, Complex.ofReal_inv]]

/-! ### The strong Markov step -/

/-- On the almost sure event `{σ_z = [0, ∞)}`, `τ̂_k` is finite and `τ̂_k ∈ [0, T_z)`. -/
theorem tauHat_untopA_mem {ω : Ω}
    (hω : sigmaDom (fun s => U s ω) (hU.cont ω) z = Ici 0) (k : ℕ) :
    tauHat hU z tt k ω = (((tauHat hU z tt k ω).untopA : ℝ≥0) : WithTop ℝ≥0) ∧
      (((tauHat hU z tt k ω).untopA : ℝ≥0) : ℝ) ∈ lifeSet (fun s => U s ω) z := by
  have hmem : (tt : ℝ) ∈ sigmaDom (fun s => U s ω) (hU.cont ω) z := by
    rw [hω]; exact tt.coe_nonneg
  have hθ := sigmaTop_of_mem hU hmem
  have hle : tauHat hU z tt k ω ≤ sigmaTop hU z tt ω := min_le_right _ _
  rw [hθ] at hle
  have hne : tauHat hU z tt k ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hle
  have hcoe : tauHat hU z tt k ω = (((tauHat hU z tt k ω).untopA : ℝ≥0) : WithTop ℝ≥0) := by
    obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 hne
    rw [← hx]
    exact congrArg _ (WithTop.untopD_coe _ _).symm
  refine ⟨hcoe, ?_⟩
  rw [hcoe, WithTop.coe_le_coe] at hle
  have hσ := sigmaTime_mem_lifeSet (hU.cont ω) hmem
  refine mem_lifeSet_of_le hσ (NNReal.coe_nonneg _) ?_
  have h1 : (((sigmaTime (fun s => U s ω) (hU.cont ω) z tt).toNNReal : ℝ≥0) : ℝ) =
      sigmaTime (fun s => U s ω) (hU.cont ω) z tt := Real.coe_toNNReal _ hσ.1
  rw [← h1]
  exact_mod_cast hle

theorem measurable_Yk (k : ℕ) : Measurable (Yk hU z tt k) := by
  have := (measurable_rhoK_Yk hU z tt k)
  have h2 : Measurable fun ω => (rhoK hU z tt k ω, Yk hU z tt k ω) :=
    this.mono (isStoppingTime_tauHat hU z tt k).measurableSpace_le le_rfl
  exact measurable_snd.comp h2

/-- **The strong Markov step at `τ̂_k`:** `E[1_𝒢(V_k) Y_k] = Λ(𝒢) E[Y_k]`. -/
theorem lintegral_Gset_mul_Yk [IsProbabilityMeasure P] (ha : 0 < a) (hc : c ^ 2 ≤ a * b)
    (hz : z ≠ 0) (u₀ : ℝ≥0) (k : ℕ) :
    ∫⁻ ω, (Gset u₀).indicator (fun _ => (1 : ℝ≥0∞))
        (CPath.scale (rhoK hU z tt k ω)⁻¹ (postPath hU (tauHat hU z tt k) ω)) *
        ENNReal.ofReal (Yk hU z tt k ω) ∂P =
      P.map (CPath.ofDriver U hU.cont) (Gset u₀) * ∫⁻ ω, ENNReal.ofReal (Yk hU z tt k ω) ∂P := by
  have hgood := Polar.ae_sigmaDom_eq_Ici hU z ha hc hz
  have hτ := isStoppingTime_tauHat hU z tt k
  have hfin : ∀ᵐ ω ∂P, tauHat hU z tt k ω ≠ ⊤ := by
    filter_upwards [hgood] with ω hω
    rw [(tauHat_untopA_mem hU z tt hω k).1]
    exact WithTop.coe_ne_top
  have hρ : ∀ᵐ ω ∂P, 0 < (rhoK hU z tt k ω, Yk hU z tt k ω).1 := by
    filter_upwards [hgood] with ω hω
    obtain ⟨-, hlife⟩ := tauHat_untopA_mem hU z tt hω k
    unfold rhoK
    rw [centeredOrZero_eq hU.cont z hlife]
    exact nnnorm_pos.2 (fPath_ne_zero (hU.cont ω) hlife)
  set F : CPath × ℝ → ℝ≥0∞ := fun p =>
    (Gset u₀).indicator (fun _ => (1 : ℝ≥0∞)) p.1 * ENNReal.ofReal p.2 with hF
  have hFm : Measurable F :=
    ((measurable_const.indicator (measurableSet_Gset u₀)).comp measurable_fst).mul
      (ENNReal.measurable_ofReal.comp measurable_snd)
  have key := lintegral_comp_scale_postPath hU hτ hfin (measurable_rhoK_Yk hU z tt k) hρ hFm
  have hYm := measurable_Yk hU z tt k
  calc _ = ∫⁻ ω, F (CPath.scale (rhoK hU z tt k ω)⁻¹ (postPath hU (tauHat hU z tt k) ω),
        Yk hU z tt k ω) ∂P := rfl
    _ = _ := key
    _ = ∫⁻ ω, ENNReal.ofReal (Yk hU z tt k ω) *
        P.map (CPath.ofDriver U hU.cont) (Gset u₀) ∂P := by
      refine lintegral_congr fun ω => ?_
      simp only [hF]
      rw [lintegral_mul_const _ (measurable_const.indicator (measurableSet_Gset u₀)),
        lintegral_indicator_const (measurableSet_Gset u₀), one_mul, mul_comm]
    _ = _ := by
      rw [lintegral_mul_const' _ _ (measure_ne_top _ _), mul_comm]

end Defs

end ComplexSLE.Internal

end
