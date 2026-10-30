/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsSLEDriver
import ComplexSLE.Internal.Driver.Chain
import ComplexSLE.Internal.Driver.GaussianMap
import ComplexSLE.Internal.Driver.Shift
import ComplexSLE.Internal.Driver.Transform

/-!
# Time reversal of the driver on `[0, T]`

For an `SLE_Σ` driver `U` and `T ≥ 0`, the process `s ↦ U (T - s) - U T` (truncated subtraction
in `ℝ≥0`, i.e. `U ((T - s)⁺) - U T`) has on `[0, T]` the same finite-dimensional laws as `U`
(paper.tex:L796: `B_t` and `B_{T-t} - B_T` are equal in law). This is
`IsSLEDriver.map_timeReversal`.

Proof: put the finite set of times `S ∪ {T}` on a monotone chain `0 = p₀ ≤ … ≤ p_M = T`. The
increments `Δ_n = U(p_{n+1}) - U(p_n)` are independent, `N(0, (p_{n+1} - p_n) Σ)`; the increments
of the reversed process are `Δ̃_n = U(T - p_{n+1}) - U(T - p_n)`, which are the negatives of the
increments `U(u_{m+1}) - U(u_m)` of `U` along the reversed chain `u_m = T - p_{M-m}`
(`m = M - 1 - n`), hence independent with the same laws `N(0, (p_{n+1} - p_n) Σ)` since
`complexGaussian` is symmetric under `x ↦ -x`. The two vectors of increments have the same law
(product of the same marginals), and the values at the times of `S` are the same measurable
function of the vector of increments.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ComplexSLE.IsSLEDriver

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

private theorem sum_fin_ite_lt (M i : ℕ) (hi : i ≤ M) (F : ℕ → ℂ) :
    ∑ n : Fin M, (if (n : ℕ) < i then F n else 0) = ∑ j ∈ Finset.range i, F j := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if j < i then F j else 0) M, ← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- **Time reversal on `[0, T]`, finite-dimensional laws.** For an `SLE_Σ` driver `U`, `T ≥ 0` and
a finite set `S ⊆ [0, T]` of times, the joint law on `S → ℂ` of
`(U (T - s) - U T)_{s ∈ S}` (with `T - s` the truncated subtraction of `ℝ≥0`) equals the joint law
of `(U s)_{s ∈ S}`. -/
theorem map_timeReversal (hU : IsSLEDriver a b c U P) (T : ℝ≥0) (S : Finset ℝ≥0)
    (hS : ∀ s ∈ S, s ≤ T) :
    P.map (fun ω (s : S) => U (T - (s : ℝ≥0)) ω - U T ω) =
      P.map (fun ω (s : S) => U (s : ℝ≥0) ω) := by
  classical
  have := hU.isProbabilityMeasure
  obtain ⟨p, M, hmono, hp0, hcov, hmem, hle⟩ := Internal.exists_chain (insert T S)
  have hpT : ∀ n, p n ≤ T := by
    intro n
    rcases Finset.mem_insert.1 (hmem n) with h | h
    · rw [h]; exact zero_le
    · rcases Finset.mem_insert.1 h with h | h
      · rw [h]
      · exact hS _ h
  have hpM : p M = T := by
    obtain ⟨i, _, hi⟩ := hcov T (Finset.mem_insert_self _ _)
    exact le_antisymm (hpT M) (hi ▸ hle i)
  -- the reversed chain
  let u : ℕ → ℝ≥0 := fun m => T - p (M - m)
  have humono : Monotone u := fun m m' h => tsub_le_tsub_left (hmono (by omega)) T
  -- increments
  let Δ : ℕ → Ω → ℂ := fun j ω => U (p (j + 1)) ω - U (p j) ω
  let Δ' : ℕ → Ω → ℂ := fun j ω => U (u (j + 1)) ω - U (u j) ω
  let Ut : ℝ≥0 → Ω → ℂ := fun s ω => U (T - s) ω - U T ω
  let Δt : ℕ → Ω → ℂ := fun j ω => Ut (p (j + 1)) ω - Ut (p j) ω
  have mΔ : ∀ n : Fin M, AEMeasurable (Δ n) P := fun n =>
    (hU.aemeasurable _).sub (hU.aemeasurable _)
  have mΔt : ∀ n : Fin M, AEMeasurable (Δt n) P := fun n =>
    ((hU.aemeasurable _).sub (hU.aemeasurable _)).sub
      ((hU.aemeasurable _).sub (hU.aemeasurable _))
  -- identification of the reversed increments
  have hΔt_eq : ∀ n : Fin M, Δt n = fun ω => -(Δ' (Fin.rev n).val ω) := by
    intro n
    have hn := n.isLt
    have e1 : M - ((M - (n + 1)) + 1) = n := by omega
    have e2 : M - (M - (n + 1)) = n + 1 := by omega
    funext ω
    simp only [Δt, Ut, Δ', u, Fin.val_rev, e1, e2]
    ring
  -- independence
  have hΔind : iIndepFun (fun n : Fin M => Δ n) P :=
    (hU.indepIncrements.nat hmono).precomp Fin.val_injective
  have hΔtind : iIndepFun (fun n : Fin M => Δt n) P := by
    have h1 := (hU.indepIncrements.nat humono).precomp
      (g := fun n : Fin M => (Fin.rev n).val) (Fin.val_injective.comp Fin.rev_injective)
    have h2 := h1.comp (fun _ => Neg.neg) (fun _ => measurable_neg)
    refine (iIndepFun_congr (fun n => ?_)).1 h2
    rw [hΔt_eq n]
    rfl
  -- marginal laws
  have hΔlaw : ∀ n : Fin M, HasLaw (Δ n)
      (complexGaussian ((((p (n + 1) : ℝ≥0) : ℝ) - (p n : ℝ≥0)) • covMatrix a b c)) P :=
    fun n => hU.law_increment (p n) (p (n + 1)) (hmono (Nat.le_succ _))
  have hΔtlaw : ∀ n : Fin M, HasLaw (Δt n)
      (complexGaussian ((((p (n + 1) : ℝ≥0) : ℝ) - (p n : ℝ≥0)) • covMatrix a b c)) P := by
    intro n
    have hn := n.isLt
    have h1 := (hU.law_increment (u ((Fin.rev n).val)) (u ((Fin.rev n).val + 1))
      (humono (Nat.le_succ _))).neg_complexGaussian
    rw [hΔt_eq n]
    have e1 : M - ((M - (n + 1)) + 1) = n := by omega
    have e2 : M - (M - (n + 1)) = n + 1 := by omega
    have hc : (((u ((Fin.rev n).val + 1) : ℝ≥0) : ℝ) - (u (Fin.rev n).val : ℝ≥0)) =
        (((p (n + 1) : ℝ≥0) : ℝ) - (p n : ℝ≥0)) := by
      simp only [u, Fin.val_rev, e1, e2]
      rw [NNReal.coe_sub (hpT _), NNReal.coe_sub (hpT _)]
      ring
    rw [hc] at h1
    exact h1
  -- the vectors of increments have the same law
  have hvec : P.map (fun ω (n : Fin M) => Δt n ω) = P.map (fun ω (n : Fin M) => Δ n ω) := by
    rw [hΔtind.map_fun_eq_pi_map mΔt, hΔind.map_fun_eq_pi_map mΔ]
    congr 1
    funext n
    rw [(hΔtlaw n).map_eq, (hΔlaw n).map_eq]
  -- the values at the times of `S` as a function of the vector of increments
  have hS' : ∀ s : S, ∃ i, i ≤ M ∧ p i = s := fun s => hcov s (Finset.mem_insert_of_mem s.2)
  choose iS hiM hpi using hS'
  let g : (Fin M → ℂ) → (S → ℂ) := fun x s =>
    ∑ n : Fin M, if (n : ℕ) < iS s then x n else 0
  have hg : Measurable g := by
    refine measurable_pi_iff.2 fun s => Finset.measurable_sum _ fun j _ => ?_
    by_cases h : (j : ℕ) < iS s <;> simp only [h, ite_true, ite_false] <;> fun_prop
  have e1 : (fun ω (s : S) => U (s : ℝ≥0) ω) =ᵐ[P] g ∘ (fun ω (n : Fin M) => Δ n ω) := by
    filter_upwards [hU.zero] with ω h0
    funext s
    simp only [g, Function.comp_apply]
    rw [sum_fin_ite_lt M (iS s) (hiM s) (fun j => Δ j ω)]
    have e2 := Finset.sum_range_sub (fun j => U (p j) ω) (iS s)
    simp only [Δ]
    rw [e2, hpi s, hp0, h0, sub_zero]
  have e2 : (fun ω (s : S) => U (T - (s : ℝ≥0)) ω - U T ω) =ᵐ[P]
      g ∘ (fun ω (n : Fin M) => Δt n ω) := by
    filter_upwards with ω
    funext s
    simp only [g, Function.comp_apply]
    rw [sum_fin_ite_lt M (iS s) (hiM s) (fun j => Δt j ω)]
    have e2 := Finset.sum_range_sub (fun j => Ut (p j) ω) (iS s)
    simp only [Δt]
    rw [e2, hpi s, hp0]
    simp [Ut]
  rw [Measure.map_congr e2, Measure.map_congr e1,
    ← AEMeasurable.map_map_of_aemeasurable hg.aemeasurable (.of_eval mΔt),
    ← AEMeasurable.map_map_of_aemeasurable hg.aemeasurable (.of_eval mΔ), hvec]

end ComplexSLE.IsSLEDriver

end
