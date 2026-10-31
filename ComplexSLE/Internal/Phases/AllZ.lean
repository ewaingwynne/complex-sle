/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.AllZEvents
public import ComplexSLE.Internal.Phases.AllZFHat
public import ComplexSLE.Internal.Phases.AllZDensity
public import ComplexSLE.Internal.Phases.AllZLebesgue
public import ComplexSLE.Internal.Polar.PolarSigmaTop

/-!
# Lemma 3.2 (`lem-all-z`): from the random point `𝐳` to every `z`

Source: paper.tex:L1294-1325. Let `{𝓔(z)}` be an event family with scale invariance and future
dependence (`ScaleInvariantEvents`, `FutureDependentEvents`, measurable in the sense of
`MeasurableEvents`). If `P(𝓔(𝐳)) = 1` for the random point `𝐳 = e^{i𝐮}`, `𝐮 ∼ p 1_{[0,2π]} du`
independent of the driver, then `P(𝓔(z)) = 1` for every `z ≠ 0`.

* `ae_mem_of_ae_unit` (core): for an adapted driver, if for Lebesgue-a.e. `u` the event holds a.s.
  at `e^{iu}`, it holds a.s. at every `z ≠ 0`.
  Proof (a simplification of the source's stopping-time choice, which is one-sided in the critical
  case): `τ = σ_z(1)` is an a.s. finite `ℱ`-stopping time lying in the life set of `z`. By future
  dependence (pathwise, at `s = τ`), `𝓔(z)` holds iff `𝓔(f_τ(z))` holds for the post-`τ` driver
  `V = U_{τ+·} - U_τ`. By the strong Markov property (EXTERNAL `strongMarkov_sleDriver`) `V` is an
  `SLE_Σ` driver independent of `ℱ_τ ∋ f_τ(z)` (`ae_mem_postDriver`), and by scale invariance
  and the equality of laws it suffices that `f_τ(z)/|f_τ(z)| = e^{iθ̂_1(z)}` lie in the set `Λ` of
  good unit points. `θ̂_1(z)` has a Lebesgue density (EXTERNAL `hormander_oneDim`,
  `map_thetaHat_absolutelyContinuous`), and `Λ` is conull, so `e^{iθ̂_1} ∈ Λ` a.s.
* `lemma_3_2`: the statement with the product extension: `P(𝓔(𝐳)) = 1` for `𝐳` on
  `Ω × ℝ` with measure `P.prod (admissibleLaw p)`, together with the positivity of the admissible
  density (`IsAdmissibleDensity.ae_pos`), gives `P(𝓔(z)) = 1` for every `z ≠ 0`.

Uses the EXTERNALs `strongMarkov_sleDriver`, `hormander_oneDim` (and `ito_formula`, `timeChange`
upstream through the polar layer).
-/

public section

open scoped NNReal ENNReal Real
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Internal

section Core

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- **Core of Lemma 3.2.** For an adapted `SLE_Σ` driver and an event family `E` (scale
invariant, future dependent, measurable section `M`): if for Lebesgue-a.e. `u ∈ ℝ` the event holds
a.s. at the unit point `e^{iu}`, then it holds a.s. at every `z ≠ 0`. -/
theorem ae_mem_of_ae_unit [IsProbabilityMeasure P] (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (hU : IsSLEDriverAdapted a b c U P ℱ) {E : (ℝ≥0 → ℂ) → ℂ → Prop}
    (hEs : ScaleInvariantEvents E) (hEf : FutureDependentEvents E)
    {M : Set ((ℝ≥0 → ℂ) × ℂ)} (hMm : MeasurableSet M)
    (hEM : ∀ (u : ℝ≥0 → ℂ) (z : ℂ), Continuous u → (E u z ↔ (u, z) ∈ M))
    (hΛ : ∀ᵐ u : ℝ ∂(volume : Measure ℝ),
      ∀ᵐ ω ∂P, ((fun t => U t ω), Complex.exp ((u : ℂ) * Complex.I)) ∈ M)
    {z : ℂ} (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, ((fun t => U t ω), z) ∈ M := by
  -- the set of good points
  set Z : Set ℂ := {ξ | ∀ᵐ ω ∂P, ((fun t => U t ω), ξ) ∈ M} with hZdef
  -- the stopping time `τ = σ_z(1)`
  set τ : Ω → WithTop ℝ≥0 := Polar.sigmaTop hU z 1 with hτdef
  have hτ : IsStoppingTime ℱ τ := Polar.isStoppingTime_sigmaTop hU z 1
  have hgood := Polar.ae_thetaHat_eq_and_continuous hU ha hc hz
  have hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤ := by
    filter_upwards [hgood] with ω hω
    rw [hτdef, Polar.sigmaTop_of_mem hU (hω.1 1)]
    exact WithTop.coe_ne_top
  -- `f_τ(z)` is `ℱ_τ`-measurable
  have hX : Measurable[hτ.measurableSpace] (Polar.fHat hU z 1) := Polar.measurable_fHat hU 1
  -- the direction `e^{iθ̂_1}` is a.s. a good point
  have hθmeas : Measurable (Polar.thetaHat hU z 1) :=
    (((Polar.isStronglyProgressive_thetaHat hU (z := z)).stronglyAdapted 1).mono
      ((Polar.sigmaFiltration hU z).le 1)).measurable
  have hac := map_thetaHat_absolutelyContinuous hU ha hb hc hz (s := 1) one_pos
  have hdirZ : ∀ᵐ ω ∂P, Complex.exp ((Polar.thetaHat hU z 1 ω : ℂ) * Complex.I) ∈ Z := by
    obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null
      (ae_iff.1 hΛ)
    have hPN : P ((Polar.thetaHat hU z 1) ⁻¹' N) = 0 := by
      rw [← Measure.map_apply hθmeas hNm]
      exact hac hN0
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) hPN
    apply hNsub
    exact hω
  -- `f_τ(z)` is a.s. a good point (scale invariance)
  have hXZ : ∀ᵐ ω ∂P, Polar.fHat hU z 1 ω ∈ Z := by
    filter_upwards [hgood, hdirZ] with ω hω hZω
    have hmem := hω.1 1
    have hlife := Polar.sigmaTime_mem_lifeSet (hU.cont ω) hmem
    have hne := Polar.fPath_ne_zero (hU.cont ω) hlife
    have hexp := Polar.exp_argPath_mul_I (hU.cont ω) hlife
    rw [Polar.thetaHat_of_mem hU hmem, hexp] at hZω
    rw [Polar.fHat_of_mem hU hmem]
    exact mem_cone_of_direction hU hEs hMm hEM hne hZω
  have hZ' : ∀ ξ ∈ Z, ∀ᵐ ω ∂P, ((fun t => U t ω), ξ) ∈ M := fun ξ hξ => hξ
  have hmark := ae_mem_postDriver hU hτ hfin hX hMm hZ' hXZ
  filter_upwards [hmark, hgood] with ω hω hgω
  -- the pathwise identification `E z ↔ E (f_τ z)` for the post-`τ` driver
  have hmem := hgω.1 1
  have hlife := Polar.sigmaTime_mem_lifeSet (hU.cont ω) hmem
  set σ := Polar.sigmaTime (fun t => U t ω) (hU.cont ω) z 1 with hσ
  have hσ0 : 0 ≤ σ := Polar.sigmaTime_nonneg (hU.cont ω) hmem
  have hτω : τ ω = ((σ.toNNReal : ℝ≥0) : WithTop ℝ≥0) := Polar.sigmaTop_of_mem hU hmem
  have hs : (τ ω).untopA = σ.toNNReal := by rw [hτω]; rfl
  set s : ℝ≥0 := σ.toNNReal with hsdef
  have hsσ : (s : ℝ) = σ := Real.coe_toNNReal σ hσ0
  have hz' : z ∈ (leftHull (fun t => U t ω) s)ᶜ := by
    rw [← Polar.coe_mem_lifeSet_iff, hsσ]; exact hlife
  have hfut := hEf (fun t => U t ω) (hU.cont ω) s z hz'
  have hcl : centeredLoewnerMap (fun t => U t ω) (hU.cont ω) s ⟨z, hz'⟩ = Polar.fHat hU z 1 ω := by
    rw [Polar.centeredLoewnerMap_eq_fPath (hU.cont ω) s hz', Polar.fHat_of_mem hU hmem, hsσ]
    rfl
  have hpath : (fun r => (fun t => U t ω) (r + s) - (fun t => U t ω) s) =
      fun r => postDriver U τ r ω := by
    funext r
    simp only [postDriver, hs, add_comm r]
  rw [hcl, hpath] at hfut
  have hV : E (fun r => postDriver U τ r ω) (Polar.fHat hU z 1 ω) :=
    (hEM _ _ (continuous_postDriver hU τ ω)).2 hω
  exact (hEM _ _ (hU.cont ω)).1 (hfut.2 hV)

end Core

section Main

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- **Lemma 3.2 (`lem-all-z`)** (paper.tex:L1294-1325). Let `a, b > 0`, `c² ≤ ab`, `U` an `SLE_Σ`
driver on an arbitrary probability space and `p` an admissible density. Let `E` be an event family
(a predicate of a continuous driver path and a point) that is scale invariant, future dependent
and measurable (`ScaleInvariantEvents`, `FutureDependentEvents`, `MeasurableEvents`). If
`P(𝓔(𝐳)) = 1` for the random point `𝐳 = e^{i𝐮}` of the product extension `Ω × ℝ` with
`𝐮 ∼ p 1_{[0,2π]} du` independent of the driver, then `P(𝓔(z)) = 1` for every `z ≠ 0`. -/
theorem lemma_3_2 (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (hU : IsSLEDriver a b c U P) {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p)
    {E : (ℝ≥0 → ℂ) → ℂ → Prop} (hEm : MeasurableEvents E) (hEs : ScaleInvariantEvents E)
    (hEf : FutureDependentEvents E)
    (hrand : ∀ᵐ x ∂(P.prod (admissibleLaw p) : Measure (Ω × ℝ)),
      E (fun t => U t x.1) (Complex.exp ((x.2 : ℂ) * Complex.I))) :
    ∀ z : ℂ, z ≠ 0 → ∀ᵐ ω ∂P, E (fun t => U t ω) z := by
  have hPprob : IsProbabilityMeasure P := hU.isProbabilityMeasure
  have : IsProbabilityMeasure (admissibleLaw p) := isProbabilityMeasure_admissibleLaw hp
  obtain ⟨ℱ, U', hUU', -, -, hU'⟩ := hU.exists_adapted
  obtain ⟨M, hMm, hM⟩ := hEm
  -- Fubini: for `ν`-a.e. `u`, the event holds a.s. at `e^{iu}`
  have hFub := ae_ae_of_ae_prod_snd hrand
  have hΛν : ∀ᵐ u : ℝ ∂(admissibleLaw p), ∀ᵐ ω ∂P,
      ((fun t => U' t ω), Complex.exp ((u : ℂ) * Complex.I)) ∈ M := by
    filter_upwards [hFub] with u hu
    filter_upwards [hu, hUU'] with ω h1 h2
    have e : (fun t => U' t ω) = fun t => U t ω := funext h2
    refine (hM _ _ (hU'.cont ω)).1 ?_
    rw [e]
    exact h1
  -- positivity of `p`: Lebesgue-a.e. on `[0, 2π]`, then on `ℝ` by periodicity
  have hΛI := ae_volume_restrict_of_ae_admissibleLaw ha hb hc hp hΛν
  have hexp : ∀ u : ℝ, Complex.exp (((u + 2 * π : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((u : ℂ) * Complex.I) := by
    intro u
    have : (((u + 2 * π : ℝ) : ℂ) * Complex.I) = (u : ℂ) * Complex.I + 2 * π * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hper : Function.Periodic (fun u : ℝ => ∀ᵐ ω ∂P,
      ((fun t => U' t ω), Complex.exp ((u : ℂ) * Complex.I)) ∈ M) (2 * π) := by
    intro u
    simp only [hexp u]
  have hΛ := ae_volume_of_ae_restrict_Icc hper hΛI
  intro z hz
  have hcore := ae_mem_of_ae_unit ha hb hc hU' hEs hEf hMm hM hΛ hz
  filter_upwards [hcore, hUU'] with ω h1 h2
  have e : (fun t => U' t ω) = fun t => U t ω := funext h2
  have h3 : E (fun t => U' t ω) z := (hM _ _ (hU'.cont ω)).2 h1
  rw [e] at h3
  exact h3

end Main

end ComplexSLE.Internal

end
