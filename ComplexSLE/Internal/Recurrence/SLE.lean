/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Recurrence.ScaleFunction
public import ComplexSLE.Internal.Recurrence.Renewal
public import ComplexSLE.Internal.Stationary.Coefficients

/-!
# The hitting lemma of R27 and claim (2.45) for the argument diffusion of SLE_Σ

Specialisation of `exists_uniform_hit` to the coefficients `α = µ`, `β² = 2D` of the SDE (2.30)
for `θ̂` (any continuous `β` with `β² = 2D`: `√(2D)` in the noncritical case, `betaCrit` in the
critical one).

* `mu_neg_of_sq_eq_zero`: hypothesis (H) for `c ≥ 0`, `c² ≤ ab`: at a zero of `β` (only possible
  when `c² = ab`, at `x + πℤ`) the drift is `µ = -4c/(a+b) < 0` (paper.tex:L993,
  `step:p-case2-welldefined`).
* `sle_hits_lower` (R27, "θ̂ started at any `y` hits every level `θ* < y` with positive
  probability", `c ≥ 0`), with a uniform bound in time and in the starting point `X₀ ∈ [θ*, y]`;
  `sle_hits_upper` is the reflected statement for `c ≤ 0` (`θ ↦ -θ`, `c ↦ -c`,
  `step:wlog-c-nonneg-arg`), so for `c² < ab` both directions hold.
* `sle_angle_hit_unif`: claim (2.45) of Lemma 2.16 (paper.tex:L1167-1171,
  `step:rec-angle-hit-unif`): for `c ≥ 0` and every `ε ∈ (0, π]` there are `T, δ > 0` with
  `P^y(∃ t ≤ T, θ̂_t = x) ≥ δ` for all `y ∈ [x, x+π-ε]`, stated for every solution started in
  that interval. Here `x` is arbitrary (in the critical case the paper takes the zero of `D`).

* `sle_recurrence`: Lemma 2.16 (paper.tex:L1155-1163) for `c ≥ 0`, in the form "a.s. there are
  arbitrarily large `t` with `e^{2iX_t} = e^{2ix}`", from (2.45) and the renewal argument
  (`ae_frequently_mem_latticeSet`), given the stationarity input `hstat` (Lemma 2.14 + density)
  and the hypothesis `hMarkov` that the Markov property at a fixed time `s` transports the
  (2.45) bound to the conditional bound on `{X_s ∈ C_ε}` given `ℱ_s`. For `c² < ab` the point `x`
  is arbitrary (first bullet, `w = e^{2ix}`); for `c² = ab` any `x` works too, in particular
  the zero of `D` (second bullet, R19 sign).

The hitting results use no Markov property; everything uses `ito_formula` (proved in-project)
(`sle_recurrence` additionally takes `hMarkov` as a hypothesis).
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
open ComplexSLE.Internal

namespace ComplexSLE.Recurrence

variable {a b c : ℝ} {β : ℝ → ℝ}

/-- **Hypothesis (H) for SLE_Σ, `c ≥ 0`.** If `β² = 2D` and `β v = 0`, then `µ v < 0`. -/
theorem mu_neg_of_sq_eq_zero (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b) (hc0 : 0 ≤ c)
    (hβ2 : ∀ v, β v ^ 2 = 2 * diffusionD a b c v) {v : ℝ} (hv : β v = 0) : mu a b c v < 0 := by
  have hD : diffusionD a b c v = 0 := by
    have := hβ2 v
    rw [hv] at this
    linarith
  rcases hc.lt_or_eq with hlt | heq
  · exact absurd hD (diffusionD_pos ha hb hlt v).ne'
  · have hcpos : 0 < c := by
      rcases hc0.lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h, zero_pow two_ne_zero] at heq
        have := mul_pos ha hb
        linarith
    have hβc : betaCrit a c v = 0 := by
      have := sq_betaCrit ha heq v
      rw [hD, mul_zero] at this
      exact pow_eq_zero_iff two_ne_zero |>.1 this
    rw [mu_eq_of_betaCrit_eq_zero ha hb heq hβc]
    have : 0 < a + b := by positivity
    exact div_neg_of_neg_of_pos (by linarith) this

/-! ### Reflection `X ↦ -X` -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {α : ℝ → ℝ} {X : ℝ≥0 → Ω → ℝ}

/-- `-X` solves the martingale problem with coefficients `(-α(-·), β(-·))`. -/
theorem isDiffusionSolution_neg (hX : IsDiffusionSolution ℱ α β X P) :
    IsDiffusionSolution ℱ (fun v => -α (-v)) (fun v => β (-v)) (fun t ω => -X t ω) P := by
  obtain ⟨hprog, hcont, hM, hMM⟩ := hX
  have hpi : ∀ t ω, pathIntegral (fun s ω => -α (X s ω)) t ω =
      -pathIntegral (fun s ω => α (X s ω)) t ω := by
    intro t ω
    simp only [pathIntegral]
    exact intervalIntegral.integral_neg
  refine ⟨fun i => (hprog i).neg, ?_, ?_, ?_⟩
  · filter_upwards [hcont] with ω h using h.neg
  · have := hM.neg
    convert this using 1
    funext t ω
    simp only [neg_neg, hpi, Pi.neg_apply]
    ring
  · convert hMM using 1
    funext t ω
    simp only [neg_neg, hpi]
    ring

/-! ### The hitting lemma of R27 -/

/-- **Hitting lemma (R27), lower levels, `c ≥ 0`.** For `θ* < y` there are `T, δ > 0` such that
every solution of the `θ̂`-SDE (martingale form, everywhere-continuous paths) started in
`[θ*, y]` hits `θ*` by time `T` with probability `≥ δ`. -/
theorem sle_hits_lower (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b) (hc0 : 0 ≤ c)
    (hβc : Continuous β) (hβ2 : ∀ v, β v ^ 2 = 2 * diffusionD a b c v) {y θ : ℝ} (hθ : θ < y) :
    ∃ (T : ℝ≥0) (δ : ℝ), 0 < T ∧ 0 < δ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ≥0 ‹_›) (X : ℝ≥0 → Ω → ℝ), IsDiffusionSolution ℱ (mu a b c) β X P →
        (∀ ω, Continuous fun t => X t ω) → (∀ᵐ ω ∂P, X 0 ω ∈ Icc θ y) →
        δ ≤ P.real {ω | ∃ t : ℝ≥0, t ≤ T ∧ X t ω = θ} :=
  exists_uniform_hit (continuous_mu a b c) hβc
    (fun _ _ hv => mu_neg_of_sq_eq_zero ha hb hc hc0 hβ2 hv) hθ.le (lt_add_one y)

/-- **Hitting lemma (R27), upper levels, `c ≤ 0`** (by reflection `θ ↦ -θ`, `c ↦ -c`). -/
theorem sle_hits_upper (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b) (hc0 : c ≤ 0)
    (hβc : Continuous β) (hβ2 : ∀ v, β v ^ 2 = 2 * diffusionD a b c v) {y θ : ℝ} (hθ : y < θ) :
    ∃ (T : ℝ≥0) (δ : ℝ), 0 < T ∧ 0 < δ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ≥0 ‹_›) (X : ℝ≥0 → Ω → ℝ), IsDiffusionSolution ℱ (mu a b c) β X P →
        (∀ ω, Continuous fun t => X t ω) → (∀ᵐ ω ∂P, X 0 ω ∈ Icc y θ) →
        δ ≤ P.real {ω | ∃ t : ℝ≥0, t ≤ T ∧ X t ω = θ} := by
  have hc' : (-c) ^ 2 ≤ a * b := by rwa [neg_sq]
  have hβ2' : ∀ v, β (-v) ^ 2 = 2 * diffusionD a b (-c) v := fun v => by
    rw [diffusionD_neg_c, hβ2]
  obtain ⟨T, δ, hT, hδ, h⟩ := sle_hits_lower ha hb hc' (neg_nonneg.2 hc0) (hβc.comp continuous_neg)
    hβ2' (neg_lt_neg hθ)
  refine ⟨T, δ, hT, hδ, fun Ω _ P _ ℱ X hX hXc h0 => ?_⟩
  have hX' : IsDiffusionSolution ℱ (mu a b (-c)) (fun v => β (-v)) (fun t ω => -X t ω) P := by
    have := isDiffusionSolution_neg hX
    have e : (fun v => -mu a b c (-v)) = mu a b (-c) := funext fun v => (mu_neg_c a b c v).symm
    rwa [e] at this
  have := h Ω P ℱ (fun t ω => -X t ω) hX' (fun ω => (hXc ω).neg)
    (by filter_upwards [h0] with ω hω; exact ⟨neg_le_neg hω.2, neg_le_neg hω.1⟩)
  simpa only [neg_inj] using this

/-- Positive probability of ever hitting a lower level (`c ≥ 0`): the qualitative form of R27. -/
theorem sle_hits_lower_pos (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b) (hc0 : 0 ≤ c)
    (hβc : Continuous β) (hβ2 : ∀ v, β v ^ 2 = 2 * diffusionD a b c v) {y θ : ℝ} (hθ : θ < y)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ≥0 ‹_›} {X : ℝ≥0 → Ω → ℝ} (hX : IsDiffusionSolution ℱ (mu a b c) β X P)
    (hXc : ∀ ω, Continuous fun t => X t ω) (h0 : ∀ᵐ ω ∂P, X 0 ω ∈ Icc θ y) :
    0 < P.real {ω | ∃ t : ℝ≥0, X t ω = θ} := by
  obtain ⟨T, δ, -, hδ, h⟩ := sle_hits_lower ha hb hc hc0 hβc hβ2 hθ
  refine lt_of_lt_of_le hδ ((h Ω P ℱ X hX hXc h0).trans (measureReal_mono ?_))
  rintro ω ⟨t, -, ht⟩
  exact ⟨t, ht⟩

/-! ### Claim (2.45) of Lemma 2.16 -/

/-- **Claim (2.45), paper.tex:L1167-1171** (`step:rec-angle-hit-unif`), for `c ≥ 0`: for every
`ε ∈ (0, π]` there are `T, δ > 0` such that every solution of the `θ̂`-SDE started in
`[x, x+π-ε]` hits `x` by time `T` with probability at least `δ`. -/
theorem sle_angle_hit_unif (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b) (hc0 : 0 ≤ c)
    (hβc : Continuous β) (hβ2 : ∀ v, β v ^ 2 = 2 * diffusionD a b c v) (x : ℝ) {ε : ℝ}
    (hε : 0 < ε) (hεπ : ε ≤ π) :
    ∃ (T : ℝ≥0) (δ : ℝ), 0 < T ∧ 0 < δ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ≥0 ‹_›) (X : ℝ≥0 → Ω → ℝ), IsDiffusionSolution ℱ (mu a b c) β X P →
        (∀ ω, Continuous fun t => X t ω) → (∀ᵐ ω ∂P, X 0 ω ∈ Icc x (x + π - ε)) →
        δ ≤ P.real {ω | ∃ t : ℝ≥0, t ≤ T ∧ X t ω = x} :=
  exists_uniform_hit (u := x + π) (continuous_mu a b c) hβc
    (fun _ _ hv => mu_neg_of_sq_eq_zero ha hb hc hc0 hβ2 hv) (by linarith) (by linarith)

/-! ### Lemma 2.16 for SLE_Σ, modulo the Markov transport of (2.45) -/

/-- **Lemma 2.16 (recurrence), `c ≥ 0`, modulo the Markov property.** Let `X` solve the
`θ̂`-SDE with everywhere-continuous paths. Assume the stationarity input `hstat` (for every
`η > 0` some `ε > 0` has `P(X_t ∉ C_ε) ≤ η` for all `t`) and the Markov transport `hMarkov`: any
uniform bound `δ ≤ P'(∃ t ≤ T, X'_t = x)` valid for all solutions started in `[x, x+π-ε]` yields
`δ · P(A ∩ {X_s ∈ C_ε}) ≤ P(A ∩ {X_s ∈ C_ε} ∩ {∃ t ≤ T, X_{s+t} ∈ x+πℤ})` for all `s` and
`A ∈ ℱ_s`. Then a.s. there are arbitrarily large `t` with `e^{2iX_t} = e^{2ix}`. -/
theorem sle_recurrence (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b) (hc0 : 0 ≤ c)
    (hβc : Continuous β) (hβ2 : ∀ v, β v ^ 2 = 2 * diffusionD a b c v)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ≥0 ‹_›} {X : ℝ≥0 → Ω → ℝ} (hX : IsDiffusionSolution ℱ (mu a b c) β X P)
    (hXc : ∀ ω, Continuous fun t => X t ω) (x : ℝ)
    (hstat : ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ≥0, P.real {ω | X t ω ∉ goodSet x ε} ≤ η)
    (hMarkov : ∀ (ε : ℝ) (T : ℝ≥0) (δ : ℝ), 0 < ε → 0 < T → 0 < δ →
      (∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (ℱ' : Filtration ℝ≥0 ‹_›) (X' : ℝ≥0 → Ω' → ℝ), IsDiffusionSolution ℱ' (mu a b c) β X' P' →
        (∀ ω, Continuous fun t => X' t ω) → (∀ᵐ ω ∂P', X' 0 ω ∈ Icc x (x + π - ε)) →
        δ ≤ P'.real {ω | ∃ t : ℝ≥0, t ≤ T ∧ X' t ω = x}) →
      ∀ (s : ℝ≥0) (A : Set Ω), MeasurableSet[ℱ s] A →
        δ * P.real (A ∩ {ω | X s ω ∈ goodSet x ε}) ≤
          P.real (A ∩ {ω | X s ω ∈ goodSet x ε} ∩
            {ω | ∃ t ≤ T, X (s + t) ω ∈ latticeSet x})) :
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0, ∃ t : ℝ≥0, s ≤ t ∧
      Complex.exp (2 * Complex.I * X t ω) = Complex.exp (2 * Complex.I * x) := by
  have h := ae_frequently_mem_latticeSet hX.1.stronglyAdapted hXc hstat ?_
  · filter_upwards [h] with ω hω s
    obtain ⟨t, hst, ht⟩ := hω s
    exact ⟨t, hst, mem_latticeSet_iff_exp.1 ht⟩
  · intro ε hε
    -- shrink `ε` to `ε' ≤ π`; `C_ε ⊆ C_{ε'}`
    have hε'pos : 0 < min ε π := lt_min hε Real.pi_pos
    obtain ⟨T, δ, hT, hδ, h245⟩ :=
      sle_angle_hit_unif ha hb hc hc0 hβc hβ2 x hε'pos (min_le_right _ _)
    refine ⟨T, δ, hT, hδ, fun s A hA => ?_⟩
    have hM := hMarkov (min ε π) T δ hε'pos hT hδ h245
    have hsub : goodSet x ε ⊆ goodSet x (min ε π) := goodSet_subset_goodSet (min_le_left ε π)
    have hA' : MeasurableSet[ℱ s] (A ∩ {ω | X s ω ∈ goodSet x ε}) :=
      hA.inter ((hX.1.stronglyAdapted s).measurable (measurableSet_goodSet x ε))
    have := hM s _ hA'
    have e1 : A ∩ {ω | X s ω ∈ goodSet x ε} ∩ {ω | X s ω ∈ goodSet x (min ε π)} =
        A ∩ {ω | X s ω ∈ goodSet x ε} := by
      rw [inter_eq_left]
      rintro ω ⟨-, h⟩
      exact hsub h
    rwa [e1] at this

end ComplexSLE.Recurrence

end
