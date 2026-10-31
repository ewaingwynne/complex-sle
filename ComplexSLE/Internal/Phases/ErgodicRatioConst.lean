/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.ErgodicRatioBirkhoff
public import ComplexSLE.Internal.Phases.ErgodicRatioRegen
public import ComplexSLE.Internal.Phases.ErgodicConst

/-!
# The Birkhoff limit of `∫₀ˢ cos 2θ̂` is a.s. constant (M7/D2, Lemma 3.6)

The 0-1 law of `ErgodicConstFibre.lean` (paper.tex:L1361-1372, regeneration at the times where
`e^{2iθ̂} = 1`), generalised from `log |f̂_s(z)|` to an arbitrary measurable functional `Φ` of the
path observable `Ξ_s = pathObsAt hU z s` that recovers the limit `L` from the observable after
every time `s₀`:

* `lintegral_mul_comp_limit_gen`: for every `ℱ_S`-measurable weight `G` and measurable `ψ`,
  `E[G ψ(L)] = E[G] · ∫ ψ(Φ(obsC (w, 0))) dΛ(w)`;
* `fibre_law_and_const_gen`: for every sequence `A_n` of past functionals (`A_n` measurable for the
  regeneration σ-algebra of level `n`) with `A_n / n → L` a.s., the law of `L` is the `Λ`-image of
  `Φ ∘ obsC (·, 0)` (independent of the point) and `L` is a.s. constant;
* `birkhoff_cosInt_const`: with `Φ = cosLim` (`ErgodicRatioFun.lean`) and `A_n = C_n`, the limit
  `L` of `exists_birkhoff_cosInt` is a.s. equal to `∫ cos(2u) dν`: `P ⊗ ν`-a.s.
  `C_s / s → ∫ cos(2u) dν`.

Consumes the EXTERNALs `strongMarkov_sleDriver` and `birkhoff_stationary` (and, through the
stationarity layer, `hormander_oneDim`, `ito_formula`, `timeChange_isContLocalMartingale`); the
EXTERNAL `markov_oneDim` (R29) is the hypothesis `hMO : MarkovOneDim`.
-/

@[expose] public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal

open Polar

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-! ### The regeneration step for a general observable functional -/

section Regeneration

variable [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ) {z : ℂ} {k : ℕ}

/-- **The regeneration step for a general functional `Φ` of the observable** (paper.tex:L1368-1372).
Let `D` be a regeneration datum at level `k` and `L` a function with `Φ(Ξ_{s₀}) = L` a.s. for
every `s₀`. For every `ℱ_S`-measurable weight `G` and every measurable `ψ`,
`E[G ψ(L)] = E[G] · ∫ ψ(Φ(obsC (w, 0))) dΛ(w)`. -/
theorem lintegral_mul_comp_limit_gen (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (D : RegenDatum hU z k)
    {Φ : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ} (hΦ : Measurable Φ) {L : Ω → ℝ}
    (hrec : ∀ᵐ ω ∂P, ∀ s₀ : ℝ≥0, Φ (pathObsAt hU z s₀ ω) = L ω)
    {G : Ω → ℝ≥0∞} (hG : Measurable[D.hS.measurableSpace] G) {ψ : ℝ → ℝ≥0∞}
    (hψ : Measurable ψ) :
    ∫⁻ ω, G ω * ψ (L ω) ∂P =
      (∫⁻ ω, G ω ∂P) * ∫⁻ w, ψ (Φ (obsC (w, 0))) ∂(driverLaw hU) := by
  set F : CPath × ℝ → ℝ≥0∞ := fun q => ψ (Φ (obsC q)) with hFdef
  have hFm : Measurable F := hψ.comp (hΦ.comp (measurable_obsC hU))
  set X : Ω → ℝ≥0 × ℝ := fun ω => (‖fHat hU z (D.τ ω) ω‖₊, thetaHat hU z (D.τ ω) ω) with hXdef
  have step1 : ∫⁻ ω, G ω * ψ (L ω) ∂P =
      ∫⁻ ω, G ω * F (CPath.scale (X ω).1⁻¹ (postPath hU D.S ω), (X ω).2) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hrec, D.hobs] with ω h1 h2
    congr 1
    simp only [hFdef, hXdef]
    rw [← h2, h1 (D.τ ω)]
  have step2 := lintegral_mul_comp_scale_postPath hU D.hS D.hfin D.hX D.hpos hG hFm
  set K : ℝ → ℝ≥0∞ := obsKernel (driverLaw hU) (fun ξ => ψ (Φ ξ)) with hKdef
  have hKF : ∀ β : ℝ, ∫⁻ w, F (w, β) ∂(P.map (CPath.ofDriver U hU.cont)) = K β := fun β => rfl
  have hper : Function.Periodic K π :=
    obsKernel_periodic hU ha hc (hψ.comp hΦ)
  have hK0 : ∀ᵐ ω ∂P, K (thetaHat hU z (D.τ ω) ω) = K 0 := by
    filter_upwards [D.hstate] with ω hω
    rw [periodic_eq_comp_exp hper, hω, Complex.arg_one, zero_div]
  have hGm : Measurable G := hG.mono D.hS.measurableSpace_le le_rfl
  rw [step1, step2]
  simp only [hKF]
  calc ∫⁻ ω, G ω * K (X ω).2 ∂P = ∫⁻ ω, G ω * K 0 ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hK0] with ω hω
        simp only [hXdef]
        rw [hω]
    _ = (∫⁻ ω, G ω ∂P) * K 0 := lintegral_mul_const _ hGm

end Regeneration

/-! ### The fibre law and the 0-1 law for a general functional -/

section ZeroOne

variable [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ) {z : ℂ}

/-- **The fibre law and the 0-1 law for a general observable functional** (paper.tex:L1361-1372).
Given regeneration data at every level `k`, a measurable `L` and a measurable functional `Φ` of the
observable with `Φ(Ξ_{s₀}) = L` a.s. for every `s₀`, and past functionals `A_n` measurable for the
level-`n` regeneration σ-algebra with `A_n / n → L` a.s.: the law of `L` is the image of the driver
law `Λ` under `w ↦ Φ (obsC (w, 0))` (independent of `z`), and `L` is a.s. constant. -/
theorem fibre_law_and_const_gen (ha : 0 < a) (hc : c ^ 2 ≤ a * b)
    (D : ∀ k : ℕ, RegenDatum hU z k) {Φ : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ} (hΦ : Measurable Φ)
    {L : Ω → ℝ} (hL : Measurable L)
    (hrec : ∀ᵐ ω ∂P, ∀ s₀ : ℝ≥0, Φ (pathObsAt hU z s₀ ω) = L ω) {A : ℕ → Ω → ℝ}
    (hpast : ∀ n : ℕ, Measurable[(D n).hS.measurableSpace] (A n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => A n ω / (n : ℝ)) atTop (𝓝 (L ω))) :
    P.map L = (driverLaw hU).map (fun w : CPath => Φ (obsC (w, 0))) ∧
      ∃ c₀ : ℝ, ∀ᵐ ω ∂P, L ω = c₀ := by
  have hΛm : Measurable fun w : CPath => Φ (obsC (w, 0)) :=
    hΦ.comp ((measurable_obsC hU).comp (measurable_id.prodMk measurable_const))
  refine ⟨?_, ?_⟩
  · refine Measure.ext_of_lintegral _ fun ψ hψ => ?_
    rw [lintegral_map hψ hL, lintegral_map hψ hΛm]
    have := lintegral_mul_comp_limit_gen hU ha hc (D 0) hΦ hrec (G := fun _ => 1)
      measurable_const hψ
    simpa using this
  -- the constancy
  set φ : ℝ → ℝ := fun x => Real.arctan x + π / 2 with hφdef
  have hφc : Continuous φ := Real.continuous_arctan.add continuous_const
  have hφpos : ∀ x, 0 ≤ φ x := fun x => by
    have := Real.neg_pi_div_two_lt_arctan x
    simp only [hφdef]; linarith
  have hφle : ∀ x, φ x ≤ π := fun x => by
    have := Real.arctan_lt_pi_div_two x
    simp only [hφdef]; linarith
  set Ψ : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (φ x) with hΨdef
  have hΨc : Continuous Ψ := ENNReal.continuous_ofReal.comp hφc
  have hΨm : Measurable Ψ := hΨc.measurable
  have hΨle : ∀ x, Ψ x ≤ ENNReal.ofReal π := fun x => ENNReal.ofReal_le_ofReal (hφle x)
  set κ : ℝ≥0∞ := ∫⁻ w, Ψ (Φ (obsC (w, 0))) ∂(driverLaw hU) with hκdef
  have hκ : ∫⁻ ω, Ψ (L ω) ∂P = κ := by
    have := lintegral_mul_comp_limit_gen hU ha hc (D 0) hΦ hrec (G := fun _ => 1)
      measurable_const hΨm
    simpa using this
  have hκfin : κ ≠ ∞ := by
    rw [← hκ]
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun ω => hΨle (L ω)) ?_)
    simp
  -- the weights
  set G : ℕ → Ω → ℝ≥0∞ := fun n ω => Ψ (A n ω / (n : ℝ)) with hGdef
  have hGmeas : ∀ n, Measurable[(D n).hS.measurableSpace] (G n) := fun n =>
    hΨm.comp ((hpast n).div_const _)
  have hGm : ∀ n, Measurable (G n) := fun n =>
    (hGmeas n).mono (D n).hS.measurableSpace_le le_rfl
  have hGle : ∀ n ω, G n ω ≤ ENNReal.ofReal π := fun n ω => hΨle _
  have hG : ∀ n, ∫⁻ ω, G n ω * Ψ (L ω) ∂P = (∫⁻ ω, G n ω ∂P) * κ := fun n =>
    lintegral_mul_comp_limit_gen hU ha hc (D n) hΦ hrec (hGmeas n) hΨm
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun n => G n ω) atTop (𝓝 (Ψ (L ω))) := by
    filter_upwards [hlim] with ω hω
    exact (hΨc.tendsto _).comp hω
  have hfinπ : ∫⁻ _ : Ω, ENNReal.ofReal π ∂P ≠ ∞ := by simp
  have hT2 : Tendsto (fun n => ∫⁻ ω, G n ω ∂P) atTop (𝓝 (∫⁻ ω, Ψ (L ω) ∂P)) :=
    tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal π) hGm
      (fun n => Eventually.of_forall (hGle n)) hfinπ hconv
  have hfin2 : ∫⁻ _ : Ω, ENNReal.ofReal π * ENNReal.ofReal π ∂P ≠ ∞ := by
    rw [lintegral_const, measure_univ, mul_one]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hT1 : Tendsto (fun n => ∫⁻ ω, G n ω * Ψ (L ω) ∂P) atTop
      (𝓝 (∫⁻ ω, Ψ (L ω) * Ψ (L ω) ∂P)) :=
    tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal π * ENNReal.ofReal π)
      (fun n => (hGm n).mul (hΨm.comp hL))
      (fun n => Eventually.of_forall fun ω => mul_le_mul' (hGle n ω) (hΨle _)) hfin2
      (hconv.mono fun ω hω => ENNReal.Tendsto.mul_const hω (Or.inr ENNReal.ofReal_ne_top))
  have hT2' : Tendsto (fun n => (∫⁻ ω, G n ω ∂P) * κ) atTop
      (𝓝 ((∫⁻ ω, Ψ (L ω) ∂P) * κ)) := ENNReal.Tendsto.mul_const hT2 (Or.inr hκfin)
  have hsq : ∫⁻ ω, Ψ (L ω) * Ψ (L ω) ∂P = κ * κ := by
    have := tendsto_nhds_unique (hT1.congr hG) hT2'
    rwa [hκ] at this
  -- to real integrals
  set f : Ω → ℝ := fun ω => φ (L ω) with hfdef
  have hfm : Measurable f := hφc.measurable.comp hL
  have hfnn : ∀ ω, 0 ≤ f ω := fun ω => hφpos _
  have hfint : Integrable f P :=
    Integrable.of_bound hfm.aestronglyMeasurable π (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hfnn ω)]; exact hφle _)
  have hf2int : Integrable (fun ω => f ω ^ 2) P :=
    Integrable.of_bound (hfm.pow_const 2).aestronglyMeasurable (π ^ 2)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (hfnn ω) (hφle _) 2)
  have e1 : ENNReal.ofReal (∫ ω, f ω ∂P) = κ := by
    rw [ofReal_integral_eq_lintegral_ofReal hfint (Eventually.of_forall hfnn), ← hκ]
  have e2 : ENNReal.ofReal (∫ ω, f ω ^ 2 ∂P) = κ * κ := by
    rw [ofReal_integral_eq_lintegral_ofReal hf2int (Eventually.of_forall fun ω => sq_nonneg _),
      ← hsq]
    refine lintegral_congr fun ω => ?_
    rw [sq, ENNReal.ofReal_mul (hfnn ω)]
  have h3 : ∫ ω, f ω ^ 2 ∂P = (∫ ω, f ω ∂P) ^ 2 := by
    have hm0 : 0 ≤ ∫ ω, f ω ∂P := integral_nonneg hfnn
    have h4 : ENNReal.ofReal (∫ ω, f ω ^ 2 ∂P) = ENNReal.ofReal ((∫ ω, f ω ∂P) ^ 2) := by
      rw [e2, sq, ENNReal.ofReal_mul hm0, e1]
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun ω => sq_nonneg _)
      (sq_nonneg _)).1 h4
  obtain ⟨c₁, hc₁⟩ := ae_const_of_integral_sq_eq hfm (C := π)
    (fun ω => by rw [abs_of_nonneg (hfnn ω)]; exact hφle _) h3
  refine ⟨Real.tan (c₁ - π / 2), ?_⟩
  filter_upwards [hc₁] with ω hω
  have : Real.arctan (L ω) = c₁ - π / 2 := by
    simp only [hfdef, hφdef] at hω
    linarith
  rw [← this, Real.tan_arctan]

end ZeroOne

/-! ### The constant limit of `C_s / s` -/

section Main

/-- **Lemma 3.6, ergodic input: the Birkhoff limit of `∫₀ˢ cos 2θ̂` is a.s. constant, equal to
`∫ cos(2u) dν`.** Under `hMO : MarkovOneDim`: `P ⊗ ν`-a.s., `C_s / s → ∫ cos(2u) dν` as
`s → ∞` along `ℝ≥0`, `C_s = ∫₀ˢ cos 2θ̂_v(e^{iu}) dv`. -/
theorem birkhoff_cosInt_const [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) :
    ∀ᵐ q ∂(P.prod (admissibleMeasure p)),
      Tendsto (fun s : ℝ≥0 => cosIntU hU s q / s) atTop (𝓝 (cosMean p)) := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  -- complete the filtration so that the null sets lie in time `0`
  have hnull : ∀ N : Set Ω, MeasurableSet N → P N = 0 →
      MeasurableSet[nullFiltration ℱ P 0] N := fun N hN hN0 =>
    (le_sup_right : _ ≤ ℱ 0 ⊔ MeasurableSpace.generateFrom
      {N : Set Ω | MeasurableSet[m] N ∧ P N = 0}) _
      (MeasurableSpace.measurableSet_generateFrom ⟨hN, hN0⟩)
  have hU' : IsSLEDriverAdapted a b c U P (nullFiltration ℱ P) :=
    hU.of_le_sup_null (fun t => le_sup_left) (fun t => le_rfl)
  suffices h : ∀ᵐ q ∂(P.prod (admissibleMeasure p)),
      Tendsto (fun s : ℝ≥0 => cosIntU hU' s q / s) atTop (𝓝 (cosMean p)) from h
  -- the Birkhoff limit, with a measurable representative
  obtain ⟨L, hLint, hLmean, hLreal⟩ := exists_birkhoff_cosInt hMO hU' ha hb hc hp
  set L' : Ω × ℝ → ℝ := hLint.1.mk L with hL'
  have hL'm : Measurable L' := hLint.1.stronglyMeasurable_mk.measurable
  have hLL' : L =ᵐ[P.prod (admissibleMeasure p)] L' := hLint.1.ae_eq_mk
  have hLreal' : ∀ᵐ q ∂(P.prod (admissibleMeasure p)),
      Tendsto (fun s : ℝ≥0 => cosIntU hU' s q / s) atTop (𝓝 (L' q)) := by
    filter_upwards [hLreal, hLL'] with q h1 h2
    rwa [← h2]
  -- the constant on each good fibre
  set κ : ℝ := ∫ x, x ∂((driverLaw hU').map (fun w : CPath => cosLim (obsC (w, 0))))
    with hκ
  have hfib : ∀ᵐ u ∂(admissibleMeasure p), ∀ᵐ ω ∂P, L' (ω, u) = κ := by
    filter_upwards [ae_ae_of_ae_prod_snd hLreal', ae_recurrent_unit hMO hU' ha hb hc hp] with u
      h1 h2
    have hz := unitPt_ne_zero u
    have D : ∀ k : ℕ, ∃ D : RegenDatum hU' (unitPt u) k,
        sigmaFiltration hU' (unitPt u) (k : ℝ≥0) ≤ D.hS.measurableSpace := fun k =>
      nonempty_regenDatum_le hU' hnull ha hc hz h2 k
    choose D hDle using D
    have hLm : Measurable fun ω => L' (ω, u) := hL'm.comp measurable_prodMk_right
    -- `Φ(Ξ_{s₀}) = L` for every `s₀`
    have hrec : ∀ᵐ ω ∂P, ∀ s₀ : ℝ≥0, cosLim (pathObsAt hU' (unitPt u) s₀ ω) = L' (ω, u) := by
      filter_upwards [h1, ae_sigmaDom_eq_Ici hU' (unitPt u) ha hc hz] with ω hω hdom s₀
      have hmem : ∀ s : ℝ≥0, (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU'.cont ω) (unitPt u) :=
        fun s => by rw [hdom]; exact s.coe_nonneg
      exact cosLim_pathObsAt hU' (continuous_thetaHat_of_forall_mem hU' hmem) hω s₀
    -- the past functionals `C_n` are `ℱ_S`-measurable
    have hprog := isStronglyProgressive_thetaHat hU' (z := unitPt u)
    have hΓp : IsStronglyProgressive (sigmaFiltration hU' (unitPt u))
        fun s ω => Real.cos (2 * thetaHat hU' (unitPt u) s ω) := fun i =>
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).comp_stronglyMeasurable
        (hprog i)
    have hpast : ∀ n : ℕ, Measurable[(D n).hS.measurableSpace]
        (fun ω => cosInt hU' (unitPt u) (n : ℝ≥0) ω) := fun n =>
      ((isStronglyProgressive_pathIntegral' hΓp).stronglyAdapted (n : ℝ≥0)).measurable.mono
        (hDle n) le_rfl
    have hlimn : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => cosInt hU' (unitPt u) (n : ℝ≥0) ω / (n : ℝ))
        atTop (𝓝 (L' (ω, u))) := by
      filter_upwards [h1] with ω hω
      have := hω.comp tendsto_natCast_atTop_atTop
      refine this.congr fun n => ?_
      simp [cosIntU]
    obtain ⟨hlaw, c₀, hc₀⟩ := fibre_law_and_const_gen hU' ha hc D measurable_cosLim hLm hrec hpast
      hlimn
    -- `κ = ∫ L'(·, u) = c₀`
    have h3 : ∫ ω, L' (ω, u) ∂P = κ := by
      rw [hκ, ← hlaw]
      exact (integral_map (f := fun x : ℝ => x) hLm.aemeasurable
        measurable_id.aestronglyMeasurable).symm
    have h4 : ∫ ω, L' (ω, u) ∂P = c₀ := by
      rw [integral_congr_ae hc₀]; simp
    filter_upwards [hc₀] with ω hω
    rw [hω, ← h4, h3]
  -- the product statement
  have hS : MeasurableSet {q : Ω × ℝ | L' q = κ} := measurableSet_eq_fun hL'm measurable_const
  have hprod : ∀ᵐ q ∂(P.prod (admissibleMeasure p)), L' q = κ := ae_prod_of_ae_ae_snd hS hfib
  -- `κ = ∫ cos(2u) dν`
  have hκI : κ = cosMean p := by
    rw [← hLmean, integral_congr_ae hLL', integral_congr_ae hprod]
    simp
  filter_upwards [hLreal', hprod] with q h1 h2
  rwa [h2, hκI] at h1

end Main

end ComplexSLE.Internal

end
