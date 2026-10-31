/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.Kolmogorov
public import ComplexSLE.Infrastructure.Stochastic.ContinuousModification

/-!
# Lemma A.1 in kernel form: the transition kernel of a periodic diffusion

Let `α, β` be the coefficients of Lemma A.1 and `p : ℝ≥0 → ℝ → ℝ → ℝ` a transition kernel
`p t u v` representing the time-`t` law of every solution of `dX = α(X) dt + β(X) dB` started at
`u`. The structure `IsDiffusionKernel α β p` collects, in consumer-side form, the properties of such
a kernel that the stationarity argument uses:

* `nonneg`, `continuous`, `law_eq`: the representation clause of `External.hormander_oneDim`
  (and the hypotheses `hp0`, `hpc`, `hp` of the pending external `markov_oneDim`,
  `review/approvals/drafts/MarkovOneDim.lean.txt`);
* `smooth`: `u ↦ ∫ f(v) p t u v dv` is `C²` for bounded measurable `f` and `t > 0`
  (`External.hormander_oneDim`, third clause, which gives `C^∞`);
* `exists_solution`: a solution from every starting point `u` exists on some probability space
  (for `θ̂` this is supplied by `isDiffusionSolution_thetaHat`);
* `equivariant` and `markov`: the two conclusions of the pending external `markov_oneDim`
  (`π`-equivariance of `p`, and the Markov property in conditional-expectation form).

None of these is assumed from an external here; they are explicit hypotheses of the consumer.

The semigroup is `kernelOp p t f u = ∫ f(v) p t u v dv` for `t > 0`, and the identity for `t = 0`
(the kernel `p 0` is unconstrained by the representation clause).

Main results:

* `IsDiffusionKernel.integral_comp_eq`: `E f(X_t) = (T_t f)(u)` for a solution `X` started at `u`;
* `IsDiffusionKernel.kernelOp_add`: the semigroup identity `T_{t+s} = T_t ∘ T_s`
  (from the Markov property and the representation clause);
* `IsDiffusionKernel.abs_kernelOp_sub_le`: `|T_t g(u) - T_s g(u)| ≤ C_L |t - s|` uniformly in `u`
  for `g ∈ C²` with bounded generator (Itô in expectation);
* `IsDiffusionKernel.hasDerivWithinAt_kernelOp`: the right derivative at `0` of
  `t ↦ T_t g(u)` is `Lg(u)`.

Everything consumes `ito_formula` through `ItoReal.lean`, so is `PROVED_REL{ito_formula}`.
-/

public section

open scoped NNReal Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set Function Real

namespace ComplexSLE.Internal

/-- The properties of a transition kernel `p t u v` for the diffusion `dX = α(X) dt + β(X) dB`
used by the kernel form of Lemma A.1 (see the module docstring for the provenance of each field). -/
structure IsDiffusionKernel (α β : ℝ → ℝ) (p : ℝ≥0 → ℝ → ℝ → ℝ) : Prop where
  /-- `p ≥ 0` (`hp0` of `markov_oneDim`; the second clause of `hormander_oneDim`). -/
  nonneg : ∀ t u v, 0 ≤ p t u v
  /-- `p t u` is continuous in `v` for `t > 0` (`hpc` of `markov_oneDim`). -/
  continuous : ∀ t : ℝ≥0, 0 < t → ∀ u, Continuous (p t u)
  /-- The representation clause: every solution started at `u` has time-`t` law `p t u v dv`
  (`hp` of `markov_oneDim`; the last clause of `hormander_oneDim`). -/
  law_eq : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ≥0 ‹_›) (X : ℝ≥0 → Ω → ℝ) (u : ℝ),
      IsDiffusionSolution ℱ α β X P → (∀ᵐ ω ∂P, X 0 ω = u) →
        ∀ t : ℝ≥0, 0 < t →
          P.map (X t) = volume.withDensity fun v => ENNReal.ofReal (p t u v)
  /-- Existence of a solution started at every `u`, on some probability space. -/
  exists_solution : ∀ u : ℝ, ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P) (ℱ : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ),
      IsDiffusionSolution ℱ α β X P ∧ ∀ᵐ ω ∂P, X 0 ω = u
  /-- `T_t f` is `C²` for bounded measurable `f` and `t > 0` (third clause of
  `hormander_oneDim`, which gives `C^∞`). -/
  smooth : ∀ t : ℝ≥0, 0 < t → ∀ f : ℝ → ℝ, Measurable f → (∃ C : ℝ, ∀ v, |f v| ≤ C) →
    ContDiff ℝ 2 fun u => ∫ v, f v * p t u v
  /-- `π`-equivariance of the kernel (first conclusion of `markov_oneDim`). -/
  equivariant : ∀ t : ℝ≥0, 0 < t → ∀ u v, p t (u + π) (v + π) = p t u v
  /-- The Markov property (second conclusion of `markov_oneDim`):
  `E[f(X_{t+s}) | ℱ_t] = (T_s f)(X_t)` for every solution, on any filtered probability space. -/
  markov : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ≥0 ‹_›) (X : ℝ≥0 → Ω → ℝ), IsDiffusionSolution ℱ α β X P →
        ∀ t s : ℝ≥0, 0 < s → ∀ f : ℝ → ℝ, Measurable f → (∃ C : ℝ, ∀ v, |f v| ≤ C) →
          P[fun ω => f (X (t + s) ω) | ℱ t] =ᵐ[P] fun ω => ∫ v, f v * p s (X t ω) v

/-- The semigroup `T_t f(u) = ∫ f(v) p t u v dv` of the kernel for `t > 0`, and `T_0 = id`. -/
@[expose] noncomputable def kernelOp (p : ℝ≥0 → ℝ → ℝ → ℝ) (t : ℝ≥0) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  if t = 0 then f u else ∫ v, f v * p t u v

@[simp] theorem kernelOp_zero (p : ℝ≥0 → ℝ → ℝ → ℝ) (f : ℝ → ℝ) : kernelOp p 0 f = f := by
  funext u; simp [kernelOp]

theorem kernelOp_of_pos {p : ℝ≥0 → ℝ → ℝ → ℝ} {t : ℝ≥0} (ht : 0 < t) (f : ℝ → ℝ) :
    kernelOp p t f = fun u => ∫ v, f v * p t u v := by
  funext u; simp [kernelOp, ht.ne']

variable {α β : ℝ → ℝ} {p : ℝ≥0 → ℝ → ℝ → ℝ}

namespace IsDiffusionKernel

/-- A solution from `u` with *every* path continuous (a continuous version on the completed
filtration), obtained from `exists_solution`. -/
theorem exists_continuous_solution (K : IsDiffusionKernel α β p) (u : ℝ) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ℱ : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ),
      IsDiffusionSolution ℱ α β X P ∧ (∀ ω, Continuous fun t => X t ω) ∧
        ∀ᵐ ω ∂P, X 0 ω = u := by
  obtain ⟨Ω, mΩ, P, hP, ℱ, X, hX, h0⟩ := K.exists_solution u
  let 𝒢 : Filtration ℝ≥0 mΩ :=
    { seq := fun t => ℱ t ⊔
        MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet[mΩ] N ∧ P N = 0}
      mono' := fun _ _ hst => sup_le_sup_right (ℱ.mono hst) _
      le' := fun t => sup_le (ℱ.le t)
        (MeasurableSpace.generateFrom_le fun _ hN => hN.1) }
  obtain ⟨X', hae, hcont, hX'⟩ := hX.exists_continuous_version 𝒢 fun t => rfl
  refine ⟨Ω, mΩ, P, hP, 𝒢, X', hX', hcont, ?_⟩
  filter_upwards [hae, h0] with ω h1 h2
  rw [h1 0, h2]

/-- `E g(X_t) = ∫ g(v) p t u v dv` for a solution started at `u` and `t > 0`. -/
theorem integral_comp_eq_integral (K : IsDiffusionKernel α β p) {Ω : Type} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {u : ℝ}
    (hX : IsDiffusionSolution ℱ α β X P) (h0 : ∀ᵐ ω ∂P, X 0 ω = u) {t : ℝ≥0} (ht : 0 < t)
    {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ ω, g (X t ω) ∂P = ∫ v, g v * p t u v := by
  rw [← integral_map (IsDiffusionSolution.measurable hX t).aemeasurable hg.aestronglyMeasurable,
    K.law_eq Ω P ℱ X u hX h0 t ht,
    integral_withDensity_eq_integral_toReal_smul (f := fun v => ENNReal.ofReal (p t u v))
      (ENNReal.measurable_ofReal.comp (K.continuous t ht u).measurable)
      (Eventually.of_forall fun v => ENNReal.ofReal_lt_top)]
  congr 1
  funext v
  rw [ENNReal.toReal_ofReal (K.nonneg t u v), smul_eq_mul, mul_comm]

/-- `E g(X_t) = (T_t g)(u)` for every `t ≥ 0`, with `T_0 = id`. -/
theorem integral_comp_eq_kernelOp (K : IsDiffusionKernel α β p) {Ω : Type}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ≥0 mΩ}
    {X : ℝ≥0 → Ω → ℝ} {u : ℝ} (hX : IsDiffusionSolution ℱ α β X P) (h0 : ∀ᵐ ω ∂P, X 0 ω = u)
    (t : ℝ≥0) {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ ω, g (X t ω) ∂P = kernelOp p t g u := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [kernelOp_zero, integral_congr_ae (g := fun _ => g u)
      (by filter_upwards [h0] with ω hω; simp only [hω]), integral_const]
    simp
  · rw [kernelOp_of_pos (pos_iff_ne_zero.mpr ht)]
    exact K.integral_comp_eq_integral hX h0 (pos_iff_ne_zero.mpr ht) hg

/-- The time-`t` law of a solution is a probability measure, so `volume.withDensity (p t u)` is. -/
theorem isProbabilityMeasure_withDensity (K : IsDiffusionKernel α β p) {t : ℝ≥0} (ht : 0 < t)
    (u : ℝ) : IsProbabilityMeasure (volume.withDensity fun v => ENNReal.ofReal (p t u v)) := by
  obtain ⟨Ω, mΩ, P, hP, ℱ, X, hX, h0⟩ := K.exists_solution u
  rw [← K.law_eq Ω P ℱ X u hX h0 t ht]
  infer_instance

/-- `T_t` is a contraction for the sup norm. -/
theorem abs_kernelOp_le (K : IsDiffusionKernel α β p) (t : ℝ≥0) {g : ℝ → ℝ}
    (hg : Measurable g) {C : ℝ} (hC : ∀ v, |g v| ≤ C) (u : ℝ) : |kernelOp p t g u| ≤ C := by
  obtain ⟨Ω, mΩ, P, hP, ℱ, X, hX, h0⟩ := K.exists_solution u
  rw [← K.integral_comp_eq_kernelOp hX h0 t hg]
  have := norm_integral_le_of_norm_le_const (μ := P) (f := fun ω => g (X t ω)) (C := C)
    (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hC (X t ω))
  simpa [Real.norm_eq_abs, abs_of_nonneg (le_trans (abs_nonneg _) (hC 0))] using this

/-- **The semigroup identity** `T_{t+s} f(u) = ∫ (T_s f)(w) p t u w dw` for `t, s > 0`: the Markov
property for a solution started at `u`, integrated against the representation clause. -/
theorem integral_transition_add (K : IsDiffusionKernel α β p) {t s : ℝ≥0} (ht : 0 < t)
    (hs : 0 < s) {f : ℝ → ℝ} (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ v, |f v| ≤ C) (u : ℝ) :
    ∫ v, f v * p (t + s) u v = ∫ w, (∫ v, f v * p s w v) * p t u w := by
  obtain ⟨Ω, mΩ, P, hP, ℱ, X, hX, h0⟩ := K.exists_solution u
  have hgm : Measurable fun w => ∫ v, f v * p s w v :=
    (K.smooth s hs f hf hfb).continuous.measurable
  calc ∫ v, f v * p (t + s) u v = ∫ ω, f (X (t + s) ω) ∂P :=
        (K.integral_comp_eq_integral hX h0 (add_pos_of_pos_of_nonneg ht s.2) hf).symm
    _ = ∫ ω, (P[fun ω => f (X (t + s) ω) | ℱ t]) ω ∂P := (integral_condExp (ℱ.le t)).symm
    _ = ∫ ω, (∫ v, f v * p s (X t ω) v) ∂P :=
        integral_congr_ae (K.markov Ω P ℱ X hX t s hs f hf hfb)
    _ = ∫ w, (∫ v, f v * p s w v) * p t u w := K.integral_comp_eq_integral hX h0 ht hgm

/-- The semigroup identity `T_{t+s} = T_t ∘ T_s` (`T_0 = id`). -/
theorem kernelOp_add (K : IsDiffusionKernel α β p) (t s : ℝ≥0) {f : ℝ → ℝ} (hf : Measurable f)
    (hfb : ∃ C : ℝ, ∀ v, |f v| ≤ C) :
    kernelOp p (t + s) f = kernelOp p t (kernelOp p s f) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  have ht' := pos_iff_ne_zero.mpr ht
  have hs' := pos_iff_ne_zero.mpr hs
  funext u
  rw [kernelOp_of_pos (add_pos ht' hs'), kernelOp_of_pos ht', kernelOp_of_pos hs']
  exact K.integral_transition_add ht' hs' hf hfb u

/-! ### Itô in expectation for the kernel -/

/-- `|T_t g(u) - T_s g(u)| ≤ C_L |t - s|` for `g ∈ C²` bounded with bounded generator,
uniformly in the starting point `u`. -/
theorem abs_kernelOp_sub_le (K : IsDiffusionKernel α β p) (hα : Continuous α)
    (hβ : Continuous β) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {Cg CL : ℝ} (hgb : ∀ u, |g u| ≤ Cg)
    (hLb : ∀ u, |generator α β g u| ≤ CL) (u : ℝ) (s t : ℝ≥0) :
    |kernelOp p t g u - kernelOp p s g u| ≤ CL * |(t : ℝ) - s| := by
  obtain ⟨Ω, mΩ, P, hP, ℱ, X, hX, hXc, h0⟩ := K.exists_continuous_solution u
  rw [← K.integral_comp_eq_kernelOp hX h0 t hg.continuous.measurable,
    ← K.integral_comp_eq_kernelOp hX h0 s hg.continuous.measurable]
  exact IsDiffusionSolution.abs_integral_sub_integral_le hX hXc hα hβ hg hgb hLb s t

/-- The right derivative at `0` of `t ↦ T_t g(u)` is `Lg(u)`, where
`Lg = g'α + ½g''β²` is the generator (`generator α β g`). -/
theorem hasDerivWithinAt_kernelOp (K : IsDiffusionKernel α β p) (hα : Continuous α)
    (hβ : Continuous β) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {Cg CL : ℝ} (hgb : ∀ u, |g u| ≤ Cg)
    (hLb : ∀ u, |generator α β g u| ≤ CL) (u : ℝ) :
    HasDerivWithinAt (fun t : ℝ => kernelOp p (Real.toNNReal t) g u) (generator α β g u)
      (Ici 0) 0 := by
  obtain ⟨Ω, mΩ, P, hP, ℱ, X, hX, hXc, h0⟩ := K.exists_continuous_solution u
  have h := IsDiffusionSolution.hasDerivWithinAt_integral_comp hX hXc hα hβ hg hgb hLb
  have e : ∀ t : ℝ, kernelOp p (Real.toNNReal t) g u = ∫ ω, g (X (Real.toNNReal t) ω) ∂P :=
    fun t => (K.integral_comp_eq_kernelOp hX h0 _ hg.continuous.measurable).symm
  have e0 : ∫ ω, generator α β g (X 0 ω) ∂P = generator α β g u := by
    rw [integral_congr_ae (g := fun _ => generator α β g u)
      (by filter_upwards [h0] with ω hω; simp only [hω]), integral_const]
    simp
  rw [e0] at h
  simpa only [e] using h

end IsDiffusionKernel

end ComplexSLE.Internal

end
