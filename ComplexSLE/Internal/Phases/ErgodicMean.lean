/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.ErgodicDecomp
public import ComplexSLE.Internal.Stationary.PathStat
public import ComplexSLE.Frozen.Defs.IntegralI

/-!
# The mean of `log |f̂_t(𝐳)|` on `Ω × ℝ` (M7/A5a)

On `(Ω × ℝ, P ⊗ ν)`, `ν = p(u) 1_{[0,2π]}(u) du` (`admissibleMeasure p`), with the random point
`𝐳 = e^{iu}`, let `Y_t(ω, u) = log |f̂_t(e^{iu})(ω)|` (`logFHat`) and
`D_t(ω, u) = ∫₀ᵗ ν(θ̂_v(e^{iu})(ω)) dv` (`driftInt`).

* `integral_nu_comp_thetaHat`: `E ν(θ̂_t) = ∫ ν dν = integralI` (one-time stationarity of
  `θ̂ mod π` (`integral_comp_thetaHat_prod_admissible`), `ν` is `π`-periodic);
* `integral_driftInt`: `E D_t = t · integralI` (Riemann sums, dominated convergence along the
  a.s. event `goodSet` on which every path of `θ̂` is continuous);
* `integrable_logFHat_sub_driftInt`: `Y_t - D_t` is integrable with mean zero (fibrewise it is the
  `L²`-martingale `M_t`, `ae_logFHat_sub_driftInt`; Fubini);
* `integrable_integral_logFHat`: `Y_t` is integrable and `E Y_t = t · integralI`.
-/

@[expose] public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal

open Polar

theorem periodic_nu (a b c : ℝ) : Function.Periodic (nu a b c) π := fun u => by
  unfold nu
  have h1 : 2 * (u + π) = 2 * u + 2 * π := by ring
  rw [h1, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem integral_nu_admissibleMeasure {a b c : ℝ} {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) :
    ∫ u, nu a b c u ∂(admissibleMeasure p) = integralI a b c p :=
  integral_admissibleMeasure hp

section Mean

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-- `Y_t(ω, u) = log |f̂_t(e^{iu})(ω)|`. -/
noncomputable def logFHat (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) (q : Ω × ℝ) : ℝ :=
  Real.log ‖fHat hU (unitPt q.2) t q.1‖

/-- `D_t(ω, u) = ∫₀ᵗ ν(θ̂_v(e^{iu})(ω)) dv`. -/
noncomputable def driftInt (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) (q : Ω × ℝ) : ℝ :=
  pathIntegral (fun v ω => nu a b c (thetaHat hU (unitPt q.2) v ω)) t q.1

theorem measurable_logFHat (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) :
    Measurable (logFHat hU t) :=
  measurable_log_norm_fHat_unit hU t

/-- The event on which `sigmaDom = [0, ∞)` (all `σ_z(s)` are defined) for `z = e^{iu}`. -/
def goodSet (hU : IsSLEDriverAdapted a b c U P ℱ) : Set (Ω × ℝ) :=
  ⋂ n : ℕ, sigmaDomUnit hU n

theorem measurableSet_goodSet (hU : IsSLEDriverAdapted a b c U P ℱ) :
    MeasurableSet (goodSet hU) :=
  MeasurableSet.iInter fun n => measurableSet_sigmaDomUnit hU n

theorem mem_sigmaDom_of_mem_goodSet (hU : IsSLEDriverAdapted a b c U P ℱ) {q : Ω × ℝ}
    (hq : q ∈ goodSet hU) (s : ℝ≥0) :
    (s : ℝ) ∈ sigmaDom (fun r => U r q.1) (hU.cont q.1) (unitPt q.2) := by
  have hn : q ∈ sigmaDomUnit hU (⌈s⌉₊ : ℝ) := mem_iInter.1 hq ⌈s⌉₊
  exact mem_sigmaDom_of_le hn s.coe_nonneg (Nat.le_ceil s)

theorem continuous_thetaHat_of_forall_mem (hU : IsSLEDriverAdapted a b c U P ℱ) {z : ℂ} {ω : Ω}
    (hmem : ∀ s : ℝ≥0, (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z) :
    Continuous fun s => thetaHat hU z s ω := by
  have e : (fun s => thetaHat hU z s ω) = fun s : ℝ≥0 => argPath (fun r => U r ω) (hU.cont ω) z
      (sigmaTime (fun r => U r ω) (hU.cont ω) z s) := funext fun s => thetaHat_of_mem hU (hmem s)
  rw [e]
  exact ((continuousOn_argPath (hU.cont ω) z).comp (continuousOn_sigmaTime (hU.cont ω) z)
    fun _ hv => sigmaTime_mem_lifeSet (hU.cont ω) hv).comp_continuous NNReal.continuous_coe hmem

/-- On the good set, `s ↦ log |f̂_s(e^{iu})(ω)|` is continuous. -/
theorem continuous_logFHat_time (hU : IsSLEDriverAdapted a b c U P ℱ) {q : Ω × ℝ}
    (hq : q ∈ goodSet hU) : Continuous fun s : ℝ≥0 => logFHat hU s q := by
  have hmem := mem_sigmaDom_of_mem_goodSet hU hq
  have hV := hU.cont q.1
  have h1 : ContinuousOn (fun v : ℝ => fPath (fun r => U r q.1) hV (unitPt q.2)
      (sigmaTime (fun r => U r q.1) hV (unitPt q.2) v))
      (sigmaDom (fun r => U r q.1) hV (unitPt q.2)) :=
    (continuousOn_fPath hV (unitPt q.2)).comp (continuousOn_sigmaTime hV (unitPt q.2))
      fun v hv => sigmaTime_mem_lifeSet hV hv
  have h2 : ContinuousOn (fun v : ℝ => Real.log ‖fPath (fun r => U r q.1) hV (unitPt q.2)
      (sigmaTime (fun r => U r q.1) hV (unitPt q.2) v)‖)
      (sigmaDom (fun r => U r q.1) hV (unitPt q.2)) :=
    h1.norm.log fun v hv => norm_ne_zero_iff.2 (fPath_sigmaTime_ne_zero hV hv)
  have e : (fun s : ℝ≥0 => logFHat hU s q) = fun s : ℝ≥0 => Real.log ‖fPath
      (fun r => U r q.1) hV (unitPt q.2)
      (sigmaTime (fun r => U r q.1) hV (unitPt q.2) (s : ℝ))‖ := by
    funext s
    simp only [logFHat, fHat_of_mem hU (hmem s)]
  rw [e]
  exact h2.comp_continuous NNReal.continuous_coe hmem

/-- A statement holding a.s. for every fibre `u` holds `P ⊗ ν`-a.e. on a measurable set. -/
theorem ae_prod_of_forall_ae [SFinite P] {ν : Measure ℝ} [SFinite ν] {S : Set (Ω × ℝ)}
    (hS : MeasurableSet S) (h : ∀ u, ∀ᵐ ω ∂P, (ω, u) ∈ S) : ∀ᵐ q ∂(P.prod ν), q ∈ S := by
  have h0 : (P.prod ν) Sᶜ = 0 := by
    rw [Measure.prod_apply_symm hS.compl]
    have : ∀ u, P ((fun x => (x, u)) ⁻¹' Sᶜ) = 0 := fun u => ae_iff.1 (h u)
    exact (lintegral_congr this).trans lintegral_zero
  exact ae_iff.2 h0

/-- A statement holding a.s. for `ν`-a.e. fibre `u` holds `P ⊗ ν`-a.e. on a measurable set. -/
theorem ae_prod_of_ae_ae_snd [SFinite P] {ν : Measure ℝ} [SFinite ν] {S : Set (Ω × ℝ)}
    (hS : MeasurableSet S) (h : ∀ᵐ u ∂ν, ∀ᵐ ω ∂P, (ω, u) ∈ S) : ∀ᵐ q ∂(P.prod ν), q ∈ S := by
  have h0 : (P.prod ν) Sᶜ = 0 := by
    rw [Measure.prod_apply_symm hS.compl]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [h] with u hu
    exact ae_iff.1 hu
  exact ae_iff.2 h0

theorem ae_mem_goodSet [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ)
    (ha : 0 < a) (hc : c ^ 2 ≤ a * b) {ν : Measure ℝ} [SFinite ν] :
    ∀ᵐ q ∂(P.prod ν), q ∈ goodSet hU := by
  refine ae_prod_of_forall_ae (measurableSet_goodSet hU) fun u => ?_
  filter_upwards [ae_sigmaDom_eq_Ici hU (unitPt u) ha hc (unitPt_ne_zero u)] with ω hω
  refine mem_iInter.2 fun n => ?_
  change (n : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) (unitPt u)
  rw [hω]; exact Nat.cast_nonneg n

/-- `E ν(θ̂_s(e^{iu})) = ∫ ν dν = (I)` for every `s ≥ 0`. -/
theorem integral_nu_comp_thetaHat [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (s : ℝ≥0) :
    ∫ q, nu a b c (thetaHat hU (unitPt q.2) s q.1) ∂(P.prod (admissibleMeasure p)) =
      integralI a b c p := by
  rw [integral_comp_thetaHat_prod_admissible hU ha hb hc hp s (continuous_nu a b c)
    (periodic_nu a b c)]
  exact integral_nu_admissibleMeasure hp

/-- The Riemann sums of the drift integral. -/
noncomputable def driftRiemann (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) (N : ℕ)
    (q : Ω × ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, ((t : ℝ) / N) *
    nu a b c (thetaHat hU (unitPt q.2) (((k : ℝ) * t / N).toNNReal) q.1)

theorem measurable_driftRiemann (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) (N : ℕ) :
    Measurable (driftRiemann hU t N) :=
  Finset.measurable_sum _ fun _ _ =>
    measurable_const.mul ((continuous_nu a b c).measurable.comp (measurable_thetaHat_unit hU _))

theorem abs_driftRiemann_le (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) (N : ℕ)
    (q : Ω × ℝ) : |driftRiemann hU t N q| ≤ (|2 - a / 2 + b / 2| + |c|) * t := by
  unfold driftRiemann
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Finset.range_zero, Finset.sum_empty, abs_zero]; positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  calc |∑ k ∈ Finset.range N, ((t : ℝ) / N) *
        nu a b c (thetaHat hU (unitPt q.2) (((k : ℝ) * t / N).toNNReal) q.1)|
      ≤ ∑ k ∈ Finset.range N, |((t : ℝ) / N) *
        nu a b c (thetaHat hU (unitPt q.2) (((k : ℝ) * t / N).toNNReal) q.1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range N, ((t : ℝ) / N) * (|2 - a / 2 + b / 2| + |c|) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t : ℝ) / N)]
        exact mul_le_mul_of_nonneg_left (abs_nu_le _ _ _ _) (by positivity)
    _ = (|2 - a / 2 + b / 2| + |c|) * t := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

theorem tendsto_driftRiemann (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) {q : Ω × ℝ}
    (hq : q ∈ goodSet hU) :
    Tendsto (fun N : ℕ => driftRiemann hU t N q) atTop (𝓝 (driftInt hU t q)) := by
  have hmem := mem_sigmaDom_of_mem_goodSet hU hq
  have hc : Continuous fun s : ℝ => nu a b c (thetaHat hU (unitPt q.2) s.toNNReal q.1) :=
    (continuous_nu a b c).comp
      ((continuous_thetaHat_of_forall_mem hU hmem).comp continuous_real_toNNReal)
  exact tendsto_riemannSum (φ := fun s : ℝ => nu a b c (thetaHat hU (unitPt q.2) s.toNNReal q.1))
    t.coe_nonneg hc.continuousOn

theorem integrable_nu_comp_thetaHat [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (s : ℝ≥0) :
    Integrable (fun q : Ω × ℝ => nu a b c (thetaHat hU (unitPt q.2) s q.1)) (P.prod ν) :=
  (integrable_const (|2 - a / 2 + b / 2| + |c|)).mono'
    ((continuous_nu a b c).measurable.comp (measurable_thetaHat_unit hU s)).aestronglyMeasurable
    (Eventually.of_forall fun q => by
      simpa [Real.norm_eq_abs] using abs_nu_le a b c _)

/-- **The mean of the drift integral**: `E D_t = t · (I)`; `D_t` is a.e. strongly measurable. -/
theorem integral_driftInt [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (t : ℝ≥0) :
    AEStronglyMeasurable (driftInt hU t) (P.prod (admissibleMeasure p)) ∧
      ∫ q, driftInt hU t q ∂(P.prod (admissibleMeasure p)) = t * integralI a b c p := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  have hlim : ∀ᵐ q ∂(P.prod (admissibleMeasure p)),
      Tendsto (fun N : ℕ => driftRiemann hU t N q) atTop (𝓝 (driftInt hU t q)) :=
    (ae_mem_goodSet hU ha hc).mono fun q hq => tendsto_driftRiemann hU t hq
  have hm : ∀ N, AEStronglyMeasurable (driftRiemann hU t N) (P.prod (admissibleMeasure p)) :=
    fun N => (measurable_driftRiemann hU t N).aestronglyMeasurable
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop hm hlim, ?_⟩
  have hDCT := tendsto_integral_of_dominated_convergence
    (μ := P.prod (admissibleMeasure p)) (fun _ => (|2 - a / 2 + b / 2| + |c|) * t) hm
    (integrable_const _) (fun N => Eventually.of_forall fun q => by
      simpa [Real.norm_eq_abs] using abs_driftRiemann_le hU t N q) hlim
  have hmean : ∀ N : ℕ, 0 < N → ∫ q, driftRiemann hU t N q ∂(P.prod (admissibleMeasure p)) =
      t * integralI a b c p := fun N hN => by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    unfold driftRiemann
    rw [integral_finsetSum _ fun k _ => (integrable_nu_comp_thetaHat hU _).const_mul _]
    simp only [integral_const_mul, integral_nu_comp_thetaHat hU ha hb hc hp]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have hev : ∀ᶠ N : ℕ in atTop, ∫ q, driftRiemann hU t N q ∂(P.prod (admissibleMeasure p)) =
      t * integralI a b c p := by
    filter_upwards [eventually_gt_atTop 0] with N hN using hmean N hN
  exact tendsto_nhds_unique hDCT (tendsto_const_nhds.congr' (hev.mono fun N h => h.symm))

/-- Fibrewise, `Y_t - D_t = M_t` almost surely. -/
theorem ae_logFHat_sub_driftInt [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ)
    (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (t : ℝ≥0) (u : ℝ) :
    (fun ω => logFHat hU t (ω, u) - driftInt hU t (ω, u)) =ᵐ[P]
      sigmaLogMart hU (unitPt u) t := by
  filter_upwards [ae_log_norm_fHat_eq hU ha hc (norm_unitPt u)] with ω hω
  simp only [logFHat, driftInt]
  rw [hω t]; ring

/-- **`Y_t - D_t` is integrable on `Ω × ℝ` with mean zero.** -/
theorem integrable_logFHat_sub_driftInt [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (t : ℝ≥0) :
    Integrable (fun q => logFHat hU t q - driftInt hU t q) (P.prod (admissibleMeasure p)) ∧
      ∫ q, (logFHat hU t q - driftInt hU t q) ∂(P.prod (admissibleMeasure p)) = 0 := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  set F : Ω × ℝ → ℝ := fun q => logFHat hU t q - driftInt hU t q with hF
  have hFm : AEStronglyMeasurable F (P.prod (admissibleMeasure p)) :=
    (measurable_logFHat hU t).aestronglyMeasurable.sub
      (integral_driftInt hU ha hb hc hp t).1
  have hfib := ae_logFHat_sub_driftInt hU ha hc t
  have hint : Integrable F (P.prod (admissibleMeasure p)) := by
    refine ⟨hFm, ?_⟩
    rw [HasFiniteIntegral, lintegral_prod_symm _ hFm.enorm]
    have hbd : ∀ u : ℝ, ∫⁻ ω, ‖F (ω, u)‖ₑ ∂P ≤ ENNReal.ofReal (1 + (a + b + |c|) * t) := fun u => by
      have hz := unitPt_ne_zero u
      obtain ⟨hsq, hK, -, -⟩ := fiber_sigmaLogMart hU ha hb hc hz
      calc ∫⁻ ω, ‖F (ω, u)‖ₑ ∂P = ∫⁻ ω, ‖sigmaLogMart hU (unitPt u) t ω‖ₑ ∂P :=
            lintegral_congr_ae (by
              filter_upwards [hfib u] with ω hω
              rw [show F (ω, u) = _ from hω])
        _ ≤ ∫⁻ ω, ENNReal.ofReal (1 + sigmaLogMart hU (unitPt u) t ω ^ 2) ∂P := by
            refine lintegral_mono fun ω => ?_
            rw [← ofReal_norm]
            refine ENNReal.ofReal_le_ofReal ?_
            rw [Real.norm_eq_abs]
            nlinarith [sq_abs (sigmaLogMart hU (unitPt u) t ω),
              sq_nonneg (|sigmaLogMart hU (unitPt u) t ω| - 1)]
        _ = ENNReal.ofReal (∫ ω, (1 + sigmaLogMart hU (unitPt u) t ω ^ 2) ∂P) :=
            (ofReal_integral_eq_lintegral_ofReal ((integrable_const _).add (hsq t))
              (Eventually.of_forall fun ω => add_nonneg zero_le_one (sq_nonneg _))).symm
        _ ≤ ENNReal.ofReal (1 + (a + b + |c|) * t) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [integral_add (integrable_const _) (hsq t)]
            simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
            linarith [hK t]
    calc ∫⁻ y, ∫⁻ x, ‖F (x, y)‖ₑ ∂P ∂(admissibleMeasure p)
        ≤ ∫⁻ y, ENNReal.ofReal (1 + (a + b + |c|) * t) ∂(admissibleMeasure p) :=
          lintegral_mono hbd
      _ < ⊤ := by simp
  refine ⟨hint, ?_⟩
  rw [integral_prod_symm F hint]
  have : ∀ u : ℝ, ∫ ω, F (ω, u) ∂P = 0 := fun u => by
    rw [integral_congr_ae (hfib u)]
    exact (fiber_sigmaLogMart hU ha hb hc (unitPt_ne_zero u)).2.2.1 t
  simp [this]

theorem abs_driftInt_le (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) (q : Ω × ℝ) :
    |driftInt hU t q| ≤ (|2 - a / 2 + b / 2| + |c|) * t :=
  Infrastructure.abs_pathIntegral_le_of_bound
    (Γ := fun v ω => nu a b c (thetaHat hU (unitPt q.2) v ω)) (ω := q.1)
    (fun _ => abs_nu_le a b c _) t

/-- **`E Y_t = t · (I)`**: `Y_t = log |f̂_t(𝐳)|` is integrable on `(Ω × ℝ, P ⊗ ν)` with mean
`t ∫₀^{2π} ν p` (paper.tex:L440, eqn-integral-nu). -/
theorem integrable_integral_logFHat [IsProbabilityMeasure P]
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (t : ℝ≥0) :
    Integrable (logFHat hU t) (P.prod (admissibleMeasure p)) ∧
      ∫ q, logFHat hU t q ∂(P.prod (admissibleMeasure p)) = t * integralI a b c p := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  obtain ⟨hMint, hM0⟩ := integrable_logFHat_sub_driftInt hU ha hb hc hp t
  obtain ⟨hDm, hD⟩ := integral_driftInt hU ha hb hc hp t
  have hDint : Integrable (driftInt hU t) (P.prod (admissibleMeasure p)) :=
    (integrable_const ((|2 - a / 2 + b / 2| + |c|) * t)).mono' hDm
      (Eventually.of_forall fun q => by simpa [Real.norm_eq_abs] using abs_driftInt_le hU t q)
  have e : logFHat hU t = fun q => (logFHat hU t q - driftInt hU t q) + driftInt hU t q := by
    funext q; ring
  have hint : Integrable (logFHat hU t) (P.prod (admissibleMeasure p)) := by
    rw [e]; exact hMint.add hDint
  refine ⟨hint, ?_⟩
  rw [e, integral_add hMint hDint, hM0, hD, zero_add]

end Mean

end ComplexSLE.Internal

end
