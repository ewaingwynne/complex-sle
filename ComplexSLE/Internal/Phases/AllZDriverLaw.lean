/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Driver.Shift
public import ComplexSLE.Internal.Driver.Chain
public import ComplexSLE.Internal.Driver.Transform
public import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# The path law of an `SLE_Σ` driver depends only on `(a, b, c)`

Two `SLE_Σ` drivers `U`, `U'` with the same parameters, living on possibly different probability
spaces, have the same law as random elements of the path space `ℝ≥0 → ℂ` (product σ-algebra):

* `IsSLEDriver.map_finite_eq_of_chain`: for a finite set `S` of times lying on a monotone chain
  `p`, the law of `(U s)_{s ∈ S}` is the image of the product of the increment laws
  `N(0, (p_{n+1} - p_n) Σ)` under the partial-sum map;
* `IsSLEDriver.map_path_eq`: the laws of the paths coincide (uniqueness of projective limits);
* `IsSLEDriver.measure_path_preimage_eq`: for a measurable set `A ⊆ (ℝ≥0 → ℂ)` of paths,
  `P {ω | (U · ω) ∈ A} = P' {ω | (U' · ω) ∈ A}`.

This is the identification of laws needed to transfer an a.s. event of an `SLE_Σ` driver to the
post-stopping-time driver of the strong Markov property (`lem-all-z`).
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ComplexSLE.IsSLEDriver

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ} {U' : ℝ≥0 → Ω' → ℂ}

theorem sum_fin_ite_lt' (M i : ℕ) (hi : i ≤ M) (F : ℕ → ℂ) :
    ∑ n : Fin M, (if (n : ℕ) < i then F n else 0) = ∑ j ∈ Finset.range i, F j := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if j < i then F j else 0) M, ← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- The partial-sum map from the increments along a chain to the values at the times of `S`. -/
noncomputable def partialSums (M : ℕ) (S : Finset ℝ≥0) (iS : S → ℕ) : (Fin M → ℂ) → (S → ℂ) :=
  fun x s => ∑ n : Fin M, if (n : ℕ) < iS s then x n else 0

theorem measurable_partialSums (M : ℕ) (S : Finset ℝ≥0) (iS : S → ℕ) :
    Measurable (partialSums M S iS) := by
  refine measurable_pi_iff.2 fun s => Finset.measurable_sum _ fun j _ => ?_
  by_cases h : (j : ℕ) < iS s <;> simp only [h, ite_true, ite_false] <;> fun_prop

/-- **Finite-dimensional law of the driver along a chain.** -/
theorem map_finite_eq_of_chain (hU : IsSLEDriver a b c U P) (S : Finset ℝ≥0) (p : ℕ → ℝ≥0)
    (M : ℕ) (hmono : Monotone p) (hp0 : p 0 = 0) (iS : S → ℕ) (hiM : ∀ s, iS s ≤ M)
    (hpi : ∀ s, p (iS s) = s) :
    P.map (fun ω (s : S) => U (s : ℝ≥0) ω) =
      (Measure.pi fun n : Fin M => complexGaussian
        ((((p (n + 1) : ℝ≥0) : ℝ) - (p n : ℝ≥0)) • covMatrix a b c)).map (partialSums M S iS) := by
  have := hU.isProbabilityMeasure
  let Δ : ℕ → Ω → ℂ := fun j ω => U (p (j + 1)) ω - U (p j) ω
  have mΔ : ∀ n : Fin M, AEMeasurable (Δ n) P := fun n =>
    (hU.aemeasurable _).sub (hU.aemeasurable _)
  have hΔind : iIndepFun (fun n : Fin M => Δ n) P :=
    (hU.indepIncrements.nat hmono).precomp Fin.val_injective
  have hΔlaw : ∀ n : Fin M, HasLaw (Δ n)
      (complexGaussian ((((p (n + 1) : ℝ≥0) : ℝ) - (p n : ℝ≥0)) • covMatrix a b c)) P :=
    fun n => hU.law_increment (p n) (p (n + 1)) (hmono (Nat.le_succ _))
  have hvec : P.map (fun ω (n : Fin M) => Δ n ω) = Measure.pi fun n : Fin M => complexGaussian
      ((((p (n + 1) : ℝ≥0) : ℝ) - (p n : ℝ≥0)) • covMatrix a b c) := by
    rw [hΔind.map_fun_eq_pi_map mΔ]
    congr 1
    funext n
    exact (hΔlaw n).map_eq
  have e1 : (fun ω (s : S) => U (s : ℝ≥0) ω) =ᵐ[P] partialSums M S iS ∘
      (fun ω (n : Fin M) => Δ n ω) := by
    filter_upwards [hU.zero] with ω h0
    funext s
    simp only [partialSums, Function.comp_apply]
    rw [sum_fin_ite_lt' M (iS s) (hiM s) (fun j => Δ j ω)]
    have e2 := Finset.sum_range_sub (fun j => U (p j) ω) (iS s)
    simp only [Δ]
    rw [e2, hpi s, hp0, h0, sub_zero]
  rw [Measure.map_congr e1,
    ← AEMeasurable.map_map_of_aemeasurable (measurable_partialSums M S iS).aemeasurable
      (.of_eval mΔ), hvec]

/-- **Finite-dimensional laws of an `SLE_Σ` driver.** Two `SLE_Σ` drivers with the same
parameters have the same law on `S → ℂ` for every finite set `S` of times. -/
theorem map_finite_eq (hU : IsSLEDriver a b c U P) (hU' : IsSLEDriver a b c U' P')
    (S : Finset ℝ≥0) :
    P.map (fun ω (s : S) => U (s : ℝ≥0) ω) = P'.map (fun ω (s : S) => U' (s : ℝ≥0) ω) := by
  classical
  obtain ⟨p, M, hmono, hp0, hcov, -, -⟩ := Internal.exists_chain S
  have hS' : ∀ s : S, ∃ i, i ≤ M ∧ p i = s := fun s => hcov s s.2
  choose iS hiM hpi using hS'
  rw [hU.map_finite_eq_of_chain S p M hmono hp0 iS hiM hpi,
    hU'.map_finite_eq_of_chain S p M hmono hp0 iS hiM hpi]

theorem measurable_path (hm : ∀ t, Measurable (U t)) :
    Measurable (fun ω (t : ℝ≥0) => U t ω) :=
  measurable_pi_iff.2 hm

/-- **Uniqueness of the path law.** Two `SLE_Σ` drivers with the same `(a, b, c)` and measurable
coordinates have the same law as random elements of the path space `ℝ≥0 → ℂ` (product
σ-algebra). -/
theorem map_path_eq (hU : IsSLEDriver a b c U P) (hU' : IsSLEDriver a b c U' P')
    (hm : ∀ t, Measurable (U t)) (hm' : ∀ t, Measurable (U' t)) :
    P.map (fun ω (t : ℝ≥0) => U t ω) = P'.map (fun ω (t : ℝ≥0) => U' t ω) := by
  have hP := hU.isProbabilityMeasure
  have hP' := hU'.isProbabilityMeasure
  have h1 := isProjectiveLimit_map (P := P) (X := U) (measurable_path hm).aemeasurable
  have h2 := isProjectiveLimit_map (P := P') (X := U') (measurable_path hm').aemeasurable
  have hI : ∀ I : Finset ℝ≥0, P.map (fun ω ↦ I.restrict (U · ω)) =
      P'.map (fun ω ↦ I.restrict (U' · ω)) := fun I => hU.map_finite_eq hU' I
  have h1' : IsProjectiveLimit (P.map (fun ω (t : ℝ≥0) => U t ω))
      (fun I ↦ P'.map (fun ω ↦ I.restrict (U' · ω))) := fun I => (h1 I).trans (hI I)
  exact h1'.unique h2

/-- **Measurable path events have the same probability for any two `SLE_Σ` drivers.** -/
theorem measure_path_preimage_eq (hU : IsSLEDriver a b c U P) (hU' : IsSLEDriver a b c U' P')
    (hm : ∀ t, Measurable (U t)) (hm' : ∀ t, Measurable (U' t))
    {A : Set (ℝ≥0 → ℂ)} (hA : MeasurableSet A) :
    P {ω | (fun t => U t ω) ∈ A} = P' {ω | (fun t => U' t ω) ∈ A} := by
  have h := congrArg (fun μ => μ A) (hU.map_path_eq hU' hm hm')
  simp only [Measure.map_apply (measurable_path hm) hA,
    Measure.map_apply (measurable_path hm') hA] at h
  exact h

end ComplexSLE.IsSLEDriver

end
