/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Process.Adapted
public import Mathlib.MeasureTheory.Constructions.Cylinders

import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Strong Markov property, step 1: the whole future after a deterministic time

Source-independent probability. No external input is used; only Mathlib.

Let `U : ℝ≥0 → Ω → E` be adapted to a filtration `ℱ` and suppose that
* (single increments) for `s ≤ t` the increment `U t - U s` is independent of `ℱ s`, and
* (stationarity) the law of `U (t + r) - U (s + r)` does not depend on `r`.

Put `smPath U T ω = (s ↦ U (T ω + s) ω - U (T ω) ω)`, the process restarted at the time `T`. We show
for a deterministic time `t` (so `T = fun _ => t`):

* `indep_smPath_const`: the whole restarted path `smPath U (fun _ => t)` is independent of `ℱ t`;
* `map_smPath_const_eq`: its law (on `ℝ≥0 → E` with the product σ-algebra) is the law of
  `smPath U (fun _ => 0)`, i.e. of `U - U 0`.

The proof is an induction over the finite set `I` of observation times (added from the top, with
`Finset.induction_on_max`): the vector of restarted values at the times of `I` is `ℱ (t + sup I)`-
measurable, and the next increment is independent of that σ-algebra, so independence and law
extend one time at a time (`indep_sup_right_of_indep`). A π-system argument over cylinder sets
passes from finite sets of times to the whole path.

The restarted-process notation `smShift`/`smPath` follows `QuantumZipper.StrongMarkov`
(leobon12/lean-formalizations @31e7483), whose route this file generalizes.
-/

public section

open scoped NNReal
open MeasureTheory ProbabilityTheory

namespace ComplexSLE.Infrastructure.StrongMarkov

/-! ### Independence of three σ-algebras -/

/-- Independent σ-algebras: product formula on measurable events. -/
theorem measure_inter_of_indep {Ω : Type*} {m₁ m₂ : MeasurableSpace Ω} [MeasurableSpace Ω]
    {P : Measure Ω} (h : Indep m₁ m₂ P) {s t : Set Ω} (hs : MeasurableSet[m₁] s)
    (ht : MeasurableSet[m₂] t) : P (s ∩ t) = P s * P t :=
  (Indep_iff m₁ m₂ P).1 h s t hs ht

/-- If `m₀ ⟂ m₁` and `(m₀ ⊔ m₁) ⟂ m₂`, then `m₀ ⟂ (m₁ ⊔ m₂)`. -/
theorem indep_sup_right_of_indep {Ω : Type*} {m₀ m₁ m₂ : MeasurableSpace Ω} [m : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (h₀ : m₀ ≤ m) (h₁ : m₁ ≤ m) (h₂ : m₂ ≤ m)
    (h01 : Indep m₀ m₁ P) (h012 : Indep (m₀ ⊔ m₁) m₂ P) : Indep m₀ (m₁ ⊔ m₂) P := by
  let p₂ : Set (Set Ω) := {s | ∃ F G, MeasurableSet[m₁] F ∧ MeasurableSet[m₂] G ∧ s = F ∩ G}
  have hp₂ : IsPiSystem p₂ := by
    rintro _ ⟨F, G, hF, hG, rfl⟩ _ ⟨F', G', hF', hG', rfl⟩ -
    exact ⟨F ∩ F', G ∩ G', hF.inter hF', hG.inter hG', by ext; simp; tauto⟩
  have hgen : m₁ ⊔ m₂ = MeasurableSpace.generateFrom p₂ := by
    refine le_antisymm (sup_le ?_ ?_) (MeasurableSpace.generateFrom_le ?_)
    · intro F hF
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨F, Set.univ, hF, @MeasurableSet.univ _ m₂, by simp⟩
    · intro G hG
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨Set.univ, G, @MeasurableSet.univ _ m₁, hG, by simp⟩
    · rintro _ ⟨F, G, hF, hG, rfl⟩
      exact (le_sup_left (a := m₁) (b := m₂) F hF).inter (le_sup_right (a := m₁) (b := m₂) G hG)
  refine IndepSets.indep h₀ (sup_le h₁ h₂) (p1 := {s | MeasurableSet[m₀] s}) (p2 := p₂)
    (@MeasurableSpace.isPiSystem_measurableSet _ m₀) hp₂
    (@MeasurableSpace.generateFrom_measurableSet _ m₀).symm hgen ((IndepSets_iff _ _ _).2 ?_)
  rintro E _ hE ⟨F, G, hF, hG, rfl⟩
  have hEF : MeasurableSet[m₀ ⊔ m₁] (E ∩ F) := (le_sup_left (a := m₀) (b := m₁) E hE).inter
    (le_sup_right (a := m₀) (b := m₁) F hF)
  have hF' : MeasurableSet[m₀ ⊔ m₁] F := le_sup_right (a := m₀) (b := m₁) F hF
  rw [← Set.inter_assoc, measure_inter_of_indep h012 hEF hG, measure_inter_of_indep h012 hF' hG,
    measure_inter_of_indep h01 hE hF]
  ring

/-! ### The restarted process and its truncations -/

section Algebra

variable {Ω E : Type*} [AddCommGroup E] {U : ℝ≥0 → Ω → E}

/-- The process `U` restarted at the random time `T`: `s ↦ U (T + s) - U T`. -/
@[expose] def smShift (U : ℝ≥0 → Ω → E) (T : Ω → ℝ≥0) (s : ℝ≥0) (ω : Ω) : E :=
  U (T ω + s) ω - U (T ω) ω

/-- The path of the restarted process, as an element of `ℝ≥0 → E`. -/
@[expose] def smPath (U : ℝ≥0 → Ω → E) (T : Ω → ℝ≥0) (ω : Ω) : ℝ≥0 → E :=
  fun s => smShift U T s ω

/-- Truncation of a path to the finite set of times `I` (zero outside `I`). -/
noncomputable def trunc (I : Finset ℝ≥0) (y : ℝ≥0 → E) : ℝ≥0 → E :=
  fun s => if s ∈ I then y s else 0

theorem trunc_insert {I : Finset ℝ≥0} {a : ℝ≥0} (ha : a ∉ I) (y : ℝ≥0 → E) :
    trunc (insert a I) y = Function.update (trunc I y) a (y a) := by
  funext s
  by_cases hs : s = a
  · subst hs; simp [trunc]
  · simp [trunc, hs]

theorem restrict_trunc (I : Finset ℝ≥0) (y : ℝ≥0 → E) : I.restrict (trunc I y) = I.restrict y := by
  funext s; simp [trunc, Finset.restrict]

theorem preimage_cylinder_smPath (I : Finset ℝ≥0) (S : Set (I → E)) (r : ℝ≥0) :
    smPath U (fun _ => r) ⁻¹' cylinder I S =
      (fun ω => trunc I (smPath U (fun _ => r) ω)) ⁻¹' (I.restrict ⁻¹' S) := by
  ext ω; simp [cylinder, restrict_trunc]

/-- One induction step: the restarted path truncated to `insert a I`, where `a` exceeds `I` and
`b = sup I`, is a function of the path truncated to `I` and of the increment
`U (r + a) - U (r + b)`. -/
theorem trunc_smPath_insert (r : ℝ≥0) {I : Finset ℝ≥0} {a : ℝ≥0} (ha : ∀ x ∈ I, x < a) (ω : Ω) :
    trunc (insert a I) (smPath U (fun _ => r) ω) =
      Function.update (trunc I (smPath U (fun _ => r) ω)) a
        ((U (r + a) ω - U (r + I.sup id) ω) + trunc I (smPath U (fun _ => r) ω) (I.sup id)) := by
  have haI : a ∉ I := fun h => lt_irrefl _ (ha a h)
  rw [trunc_insert haI]
  congr 1
  have hb : trunc I (smPath U (fun _ => r) ω) (I.sup id) = U (r + I.sup id) ω - U r ω := by
    by_cases hI : I = ∅
    · subst hI; simp [trunc]
    · have hmem : I.sup id ∈ I := by
        obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup I (Finset.nonempty_iff_ne_empty.2 hI) id
        simpa [hsup] using hi
      simp [trunc, smPath, smShift, hmem]
  rw [hb]
  simp [smPath, smShift]

end Algebra

/-! ### Measurability -/

section Measurability

variable {Ω E : Type*} [AddCommGroup E] [MeasurableSpace E] {mΩ : MeasurableSpace Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {U : ℝ≥0 → Ω → E}

omit [AddCommGroup E] in
/-- An adapted process is measurable at every time. -/
theorem measurable_of_adapted (hU : Adapted ℱ U) (t : ℝ≥0) : Measurable (U t) :=
  (hU t).mono (ℱ.le t) le_rfl

/-- Truncation to a finite set of times is measurable. -/
theorem measurable_trunc (I : Finset ℝ≥0) : Measurable (trunc (E := E) I) :=
  measurable_pi_iff.2 fun s => by
    by_cases hs : s ∈ I
    · simpa [trunc, hs] using measurable_pi_apply s
    · simp [trunc, hs]

end Measurability

/-! ### The simple Markov property at a deterministic time -/

section Future

variable {Ω E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {U : ℝ≥0 → Ω → E}

/-- The restarted path at a deterministic time is measurable. -/
theorem measurable_smPath_const (hUm : ∀ t, Measurable (U t)) (t : ℝ≥0) :
    Measurable (smPath U (fun _ => t)) :=
  measurable_pi_iff.2 fun s => (hUm (t + s)).sub (hUm t)

/-- Measurability of the truncated restarted path with respect to `ℱ (r + b)` when all times of
`I` are at most `b`. -/
theorem measurable_trunc_smPath (hU : Adapted ℱ U) (r : ℝ≥0) (I : Finset ℝ≥0) {b : ℝ≥0}
    (hb : ∀ x ∈ I, x ≤ b) :
    Measurable[ℱ (r + b)] (fun ω => trunc I (smPath U (fun _ => r) ω)) := by
  refine @measurable_pi_iff _ _ _ (ℱ (r + b)) _ _ |>.2 fun s => ?_
  by_cases hs : s ∈ I
  · have h1 : Measurable[ℱ (r + b)] (U (r + s)) :=
      (hU (r + s)).mono (ℱ.mono (add_le_add_right (hb s hs) r)) le_rfl
    have h2 : Measurable[ℱ (r + b)] (U r) := (hU r).mono (ℱ.mono le_self_add) le_rfl
    simpa [trunc, smPath, smShift, hs] using h1.fun_sub h2
  · simp [trunc, hs]

/-- **Simple Markov property at a deterministic time, finite-dimensional form** (by induction on
the finite set `I` of times). The restarted path at time `t`, truncated to `I`, is independent
of `ℱ t` and has the same law as the restarted path at time `0`. -/
theorem trunc_claim [IsProbabilityMeasure P] (hU : Adapted ℱ U)
    (hind : ∀ s t : ℝ≥0, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => U t ω - U s ω) inferInstance) (ℱ s) P)
    (hinc : ∀ s t r : ℝ≥0, s ≤ t →
      P.map (fun ω => U (t + r) ω - U (s + r) ω) = P.map (fun ω => U t ω - U s ω))
    (t : ℝ≥0) (I : Finset ℝ≥0) :
    Indep (ℱ t) (MeasurableSpace.comap (fun ω => trunc I (smPath U (fun _ => t) ω))
      MeasurableSpace.pi) P ∧
    P.map (fun ω => trunc I (smPath U (fun _ => t) ω)) =
      P.map (fun ω => trunc I (smPath U (fun _ => 0) ω)) := by
  have hUm : ∀ t, Measurable (U t) := measurable_of_adapted hU
  induction I using Finset.induction_on_max with
  | empty =>
    have h0 : ∀ r : ℝ≥0, (fun ω => trunc (∅ : Finset ℝ≥0) (smPath U (fun _ => r) ω)) =
        fun _ => (0 : ℝ≥0 → E) := by
      intro r; funext ω s; simp [trunc]
    rw [h0 t, h0 0]
    refine ⟨?_, rfl⟩
    exact indep_of_indep_of_le_right (indep_bot_right _)
      (Measurable.comap_le (measurable_const : Measurable[⊥] (fun _ : Ω => (0 : ℝ≥0 → E))))
  | insert a I ha ih =>
    obtain ⟨ihI, ihL⟩ := ih
    set b : ℝ≥0 := I.sup id with hb
    have hb1 : ∀ x ∈ I, x ≤ b := fun x hx => Finset.le_sup (f := id) hx
    have hb2 : b ≤ a := Finset.sup_le fun x hx => (ha x hx).le
    set Z : ℝ≥0 → Ω → (ℝ≥0 → E) := fun r ω => trunc I (smPath U (fun _ => r) ω) with hZdef
    set X : ℝ≥0 → Ω → E := fun r ω => U (r + a) ω - U (r + b) ω with hXdef
    have hZm : ∀ r, Measurable[ℱ (r + b)] (Z r) := fun r => measurable_trunc_smPath hU r I hb1
    have hZmeas : ∀ r, Measurable (Z r) := fun r => (hZm r).mono (ℱ.le _) le_rfl
    have hXmeas : ∀ r, Measurable (X r) := fun r => (hUm (r + a)).fun_sub (hUm (r + b))
    have hXind : ∀ r, Indep (ℱ (r + b)) (MeasurableSpace.comap (X r) inferInstance) P :=
      fun r => (hind (r + b) (r + a) (add_le_add_right hb2 r)).symm
    have hZX : ∀ r, IndepFun (Z r) (X r) P := fun r => by
      rw [IndepFun_iff_Indep]
      exact indep_of_indep_of_le_left (hXind r) (hZm r).comap_le
    -- the step map
    let G : (ℝ≥0 → E) × E → (ℝ≥0 → E) := fun p => Function.update p.1 a (p.2 + p.1 b)
    have hG : Measurable G :=
      (measurable_update' (a := a)).comp (measurable_fst.prodMk
        (measurable_snd.add ((measurable_pi_apply b).comp measurable_fst)))
    have hstep : ∀ r, (fun ω => trunc (insert a I) (smPath U (fun _ => r) ω)) =
        G ∘ fun ω => (Z r ω, X r ω) := fun r => by
      funext ω; exact trunc_smPath_insert r ha ω
    have hlawX : P.map (X t) = P.map (X 0) := by
      have h := hinc b a t hb2
      simp only [hXdef, add_comm t a, add_comm t b, zero_add]
      exact h
    refine ⟨?_, ?_⟩
    · rw [hstep t]
      have h₁ : MeasurableSpace.comap (Z t) MeasurableSpace.pi ≤ mΩ := (hZmeas t).comap_le
      have h₂ : MeasurableSpace.comap (X t) inferInstance ≤ mΩ := (hXmeas t).comap_le
      have h012 : Indep (ℱ t ⊔ MeasurableSpace.comap (Z t) MeasurableSpace.pi)
          (MeasurableSpace.comap (X t) inferInstance) P :=
        indep_of_indep_of_le_left (hXind t) (sup_le (ℱ.mono le_self_add) (hZm t).comap_le)
      refine indep_of_indep_of_le_right (indep_sup_right_of_indep (ℱ.le t) h₁ h₂ ihI h012) ?_
      refine Measurable.comap_le ?_
      have hZ' : Measurable[MeasurableSpace.comap (Z t) MeasurableSpace.pi ⊔
          MeasurableSpace.comap (X t) inferInstance] (Z t) :=
        (comap_measurable (Z t)).mono le_sup_left le_rfl
      have hX' : Measurable[MeasurableSpace.comap (Z t) MeasurableSpace.pi ⊔
          MeasurableSpace.comap (X t) inferInstance] (X t) :=
        (comap_measurable (X t)).mono le_sup_right le_rfl
      exact hG.comp (hZ'.prodMk hX')
    · rw [hstep t, hstep 0]
      have hmap : ∀ r, P.map (G ∘ fun ω => (Z r ω, X r ω)) =
          ((P.map (Z r)).prod (P.map (X r))).map G := fun r => by
        rw [← (indepFun_iff_map_prod_eq_prod_map_map (hZmeas r).aemeasurable
          (hXmeas r).aemeasurable).1 (hZX r), Measure.map_map hG ((hZmeas r).prodMk (hXmeas r))]
      rw [hmap t, hmap 0, ihL, hlawX]

/-- **Whole-future independence at a deterministic time.** The restarted path
`s ↦ U (t + s) - U t` is independent of `ℱ t`. -/
theorem indep_smPath_const [IsProbabilityMeasure P] (hU : Adapted ℱ U)
    (hind : ∀ s t : ℝ≥0, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => U t ω - U s ω) inferInstance) (ℱ s) P)
    (hinc : ∀ s t r : ℝ≥0, s ≤ t →
      P.map (fun ω => U (t + r) ω - U (s + r) ω) = P.map (fun ω => U t ω - U s ω))
    (t : ℝ≥0) :
    Indep (ℱ t) (MeasurableSpace.comap (smPath U (fun _ => t)) MeasurableSpace.pi) P := by
  have hsm := measurable_smPath_const (measurable_of_adapted hU) t
  have hgen : MeasurableSpace.comap (smPath U (fun _ => t)) MeasurableSpace.pi =
      MeasurableSpace.generateFrom
        {s | ∃ c ∈ measurableCylinders (fun _ : ℝ≥0 => E), smPath U (fun _ => t) ⁻¹' c = s} := by
    rw [← generateFrom_measurableCylinders, MeasurableSpace.comap_generateFrom]
    rfl
  refine IndepSets.indep (ℱ.le t) hsm.comap_le (p1 := {s | MeasurableSet[ℱ t] s})
    (p2 := {s | ∃ c ∈ measurableCylinders (fun _ : ℝ≥0 => E), smPath U (fun _ => t) ⁻¹' c = s})
    (@MeasurableSpace.isPiSystem_measurableSet _ (ℱ t))
    (isPiSystem_measurableCylinders.comap _)
    (@MeasurableSpace.generateFrom_measurableSet _ (ℱ t)).symm hgen ((IndepSets_iff _ _ _).2 ?_)
  rintro F _ hF ⟨c, hc, rfl⟩
  obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders c).1 hc
  have hmeas : MeasurableSet[MeasurableSpace.comap (fun ω => trunc I (smPath U (fun _ => t) ω))
      MeasurableSpace.pi] (smPath U (fun _ => t) ⁻¹' cylinder I S) := by
    rw [preimage_cylinder_smPath]
    exact ⟨_, (Finset.measurable_restrict (X := fun _ : ℝ≥0 => E) I) hS, rfl⟩
  exact measure_inter_of_indep (trunc_claim hU hind hinc t I).1 hF hmeas

/-- **Law of the restarted path at a deterministic time.** The law on `ℝ≥0 → E` of
`s ↦ U (t + s) - U t` does not depend on `t`. -/
theorem map_smPath_const_eq [IsProbabilityMeasure P] (hU : Adapted ℱ U)
    (hind : ∀ s t : ℝ≥0, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => U t ω - U s ω) inferInstance) (ℱ s) P)
    (hinc : ∀ s t r : ℝ≥0, s ≤ t →
      P.map (fun ω => U (t + r) ω - U (s + r) ω) = P.map (fun ω => U t ω - U s ω))
    (t : ℝ≥0) :
    P.map (smPath U (fun _ => t)) = P.map (smPath U (fun _ => 0)) := by
  have hs : ∀ r, Measurable (smPath U (fun _ => r)) :=
    measurable_smPath_const (measurable_of_adapted hU)
  have hT : ∀ (r : ℝ≥0) (I : Finset ℝ≥0), Measurable fun ω => trunc I (smPath U (fun _ => r) ω) :=
    fun r I => (measurable_trunc I).comp (hs r)
  refine ext_of_generate_finite (measurableCylinders fun _ : ℝ≥0 => E)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders (fun c hc => ?_) ?_
  · obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders c).1 hc
    have hcyl := MeasurableSet.cylinder (α := fun _ : ℝ≥0 => E) I hS
    have hS' : MeasurableSet (I.restrict ⁻¹' S) :=
      (Finset.measurable_restrict (X := fun _ : ℝ≥0 => E) I) hS
    rw [Measure.map_apply (hs t) hcyl, Measure.map_apply (hs 0) hcyl, preimage_cylinder_smPath,
      preimage_cylinder_smPath, ← Measure.map_apply (hT t I) hS', ← Measure.map_apply (hT 0 I) hS',
      (trunc_claim hU hind hinc t I).2]
  · rw [Measure.map_apply (hs t) MeasurableSet.univ, Measure.map_apply (hs 0) MeasurableSet.univ]
    simp

end Future

end ComplexSLE.Infrastructure.StrongMarkov

end
