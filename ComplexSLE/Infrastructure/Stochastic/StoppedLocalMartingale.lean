/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsContLocalMartingale
public import ComplexSLE.External.TimeChangeIsContLocalMartingale

/-!
# Stopping a continuous local martingale

Source-independent stochastic calculus. Mathlib's optional stopping theorems are stated for
discrete or countable-range stopping times; for the continuous-time processes of this project we
obtain the stopped process `M^ρ = M (· ∧ ρ)` of a continuous local martingale `M` at a finite
stopping time `ρ` as a continuous local martingale from the external time-change input E2c
(`timeChange_isContLocalMartingale`) with the time change `σ s = s ∧ ρ`, which yields a local
martingale with respect to the *stopped* filtration `𝒢_s = ℱ_{s ∧ ρ}`. The elementary transfer
lemma `isContLocalMartingale_of_min_const` then upgrades this to the original filtration `ℱ`:
for `A ∈ ℱ_s`, split `A = (A ∩ {ρ ≤ s}) ∪ (A ∩ {s < ρ})`; on the first piece the stopped process
is constant between `s` and `t`, and the second piece belongs to `ℱ_{s ∧ ρ}`.

Everything that consumes `IsContLocalMartingale.stopped_min` is `PROVED_REL{E2c}`.
-/

public section

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### Transfer from the stopped filtration `ℱ_{· ∧ ρ}` to `ℱ` -/

section Transfer

variable (ℱ : Filtration ℝ≥0 mΩ) {ρ : Ω → ℝ≥0}

/-- Monotonicity of the product σ-algebra. -/
theorem measurableSpace_prod_mono {α β : Type*} {m₁ m₁' : MeasurableSpace α}
    {m₂ m₂' : MeasurableSpace β} (h₁ : m₁ ≤ m₁') (h₂ : m₂ ≤ m₂') :
    m₁.prod m₂ ≤ m₁'.prod m₂' :=
  sup_le_sup (MeasurableSpace.comap_mono h₁) (MeasurableSpace.comap_mono h₂)

/-- The σ-algebra of a stopping time only depends on the stopping time as a function. -/
theorem _root_.MeasureTheory.IsStoppingTime.measurableSpace_congr {τ₁ τ₂ : Ω → WithTop ℝ≥0}
    (h₁ : IsStoppingTime ℱ τ₁) (h₂ : IsStoppingTime ℱ τ₂) (h : τ₁ = τ₂) :
    h₁.measurableSpace = h₂.measurableSpace := by
  subst h; rfl

theorem measurableSet_le_const_of_isStoppingTime
    (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0)) (s : ℝ≥0) :
    MeasurableSet[ℱ s] {ω | ρ ω ≤ s} := by
  have : {ω | ρ ω ≤ s} = {ω | (ρ ω : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0)} := by
    ext ω
    simp only [mem_ofPred_eq]
    exact WithTop.coe_le_coe.symm
  rw [this]
  exact hρ s

theorem measurableSet_lt_const_of_isStoppingTime
    (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0)) (s : ℝ≥0) :
    MeasurableSet[ℱ s] {ω | s < ρ ω} := by
  have : {ω | s < ρ ω} = {ω | ρ ω ≤ s}ᶜ := by ext ω; simp
  rw [this]
  exact (measurableSet_le_const_of_isStoppingTime ℱ hρ s).compl

/-- For `A ∈ ℱ_s`, the set `A ∩ {s < ρ}` is `ℱ_{ρ ∧ s}`-measurable. -/
theorem measurableSet_inter_lt_min_const (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0))
    {s : ℝ≥0} {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    MeasurableSet[(hρ.min_const s).measurableSpace] (A ∩ {ω | s < ρ ω}) := by
  rw [IsStoppingTime.measurableSet]
  have hAs : MeasurableSet[ℱ s] (A ∩ {ω | s < ρ ω}) :=
    hA.inter (measurableSet_lt_const_of_isStoppingTime ℱ hρ s)
  refine ⟨le_iSup (fun t => ℱ t) s _ hAs, fun u => ?_⟩
  by_cases hus : s ≤ u
  · have : A ∩ {ω | s < ρ ω} ∩ {ω | min ((ρ ω : WithTop ℝ≥0)) (s : WithTop ℝ≥0) ≤ u} =
        A ∩ {ω | s < ρ ω} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, and_iff_left_iff_imp]
      intro _
      exact le_trans (min_le_right _ _) (by exact_mod_cast hus)
    rw [this]
    exact ℱ.mono hus _ hAs
  · push Not at hus
    have : A ∩ {ω | s < ρ ω} ∩ {ω | min ((ρ ω : WithTop ℝ≥0)) (s : WithTop ℝ≥0) ≤ u} = ∅ := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      rintro ⟨-, hlt⟩ hle
      have h1 : min ((ρ ω : WithTop ℝ≥0)) (s : WithTop ℝ≥0) = s :=
        min_eq_right (by exact_mod_cast hlt.le)
      rw [h1] at hle
      exact absurd (by exact_mod_cast hle : s ≤ u) (not_le.2 hus)
    rw [this]
    exact @MeasurableSet.empty _ (ℱ u)

/-- **Filtration transfer.** A continuous local martingale with respect to the stopped
filtration `𝒢_s = ℱ_{ρ ∧ s}` that is constant on `[ρ, ∞)` is a continuous local martingale with
respect to `ℱ`. -/
theorem isContLocalMartingale_of_min_const (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0))
    (𝒢 : Filtration ℝ≥0 mΩ) (h𝒢 : ∀ s, 𝒢 s = (hρ.min_const s).measurableSpace)
    {N : ℝ≥0 → Ω → ℝ} (hN : IsContLocalMartingale 𝒢 N P)
    (hconst : ∀ ω (s t : ℝ≥0), s ≤ t → ρ ω ≤ s → N t ω = N s ω) :
    IsContLocalMartingale ℱ N P := by
  have h𝒢le : ∀ s, 𝒢 s ≤ ℱ s := fun s => by
    rw [h𝒢]
    exact (hρ.min_const s).measurableSpace_le_of_le_const fun ω => min_le_right _ _
  obtain ⟨hprog, hcont, τ, hτ, hτev, hmart⟩ := hN
  refine ⟨fun i => (hprog i).mono (measurableSpace_prod_mono le_rfl (h𝒢le i)), hcont, τ,
    fun n i => h𝒢le i _ (hτ n i), hτev, fun n => ?_⟩
  set Y := stoppedProcess N (τ n) with hYdef
  have hY : Martingale Y 𝒢 P := hmart n
  refine ⟨fun i => (hY.stronglyAdapted i).mono (h𝒢le i), fun s t hst => ?_⟩
  -- `Y` is constant between `s` and `t` on `{ρ ≤ s}`
  have hYconst : ∀ ω, ρ ω ≤ s → Y t ω = Y s ω := by
    intro ω hρs
    simp only [hYdef, stoppedProcess]
    rcases le_total (τ n ω) (ρ ω : WithTop ℝ≥0) with hτρ | hρτ
    · -- `τ n ω ≤ ρ ω ≤ s ≤ t`: both minima are `τ n ω`
      have h1 : min (t : WithTop ℝ≥0) (τ n ω) = τ n ω :=
        min_eq_right (hτρ.trans (by exact_mod_cast hρs.trans hst))
      have h2 : min (s : WithTop ℝ≥0) (τ n ω) = τ n ω :=
        min_eq_right (hτρ.trans (by exact_mod_cast hρs))
      rw [h1, h2]
    · -- `ρ ω ≤ τ n ω`: both minima are `≥ ρ ω`, so `N` is constant between them
      have hρs' : (ρ ω : WithTop ℝ≥0) ≤ s := by exact_mod_cast hρs
      have hst' : (s : WithTop ℝ≥0) ≤ t := by exact_mod_cast hst
      have hmin_s : min (s : WithTop ℝ≥0) (τ n ω) ≠ ⊤ := by
        exact ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
      have hmin_t : min (t : WithTop ℝ≥0) (τ n ω) ≠ ⊤ := by
        exact ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
      have hle : (min (s : WithTop ℝ≥0) (τ n ω)).untopA ≤
          (min (t : WithTop ℝ≥0) (τ n ω)).untopA := by
        rw [WithTop.untopA_eq_untop hmin_s, WithTop.untopA_eq_untop hmin_t, ← WithTop.coe_le_coe,
          WithTop.coe_untop, WithTop.coe_untop]
        exact min_le_min_right _ hst'
      have hρle : ρ ω ≤ (min (s : WithTop ℝ≥0) (τ n ω)).untopA := by
        rw [WithTop.untopA_eq_untop hmin_s, ← WithTop.coe_le_coe, WithTop.coe_untop]
        exact le_min hρs' hρτ
      exact hconst ω _ _ hle hρle
  have : SigmaFiniteFiltration P 𝒢 := inferInstance
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) (hY.integrable t)
    (fun A _ _ => (hY.integrable s).integrableOn) (fun A hA _ => ?_)
    ((hY.stronglyAdapted s).mono (h𝒢le s)).aestronglyMeasurable).symm
  have hA' : MeasurableSet A := ℱ.le s A hA
  have hle_meas : MeasurableSet {ω | ρ ω ≤ s} :=
    ℱ.le s _ (measurableSet_le_const_of_isStoppingTime ℱ hρ s)
  have hlt_meas : MeasurableSet {ω | s < ρ ω} :=
    ℱ.le s _ (measurableSet_lt_const_of_isStoppingTime ℱ hρ s)
  have hsplit : A = (A ∩ {ω | ρ ω ≤ s}) ∪ (A ∩ {ω | s < ρ ω}) := by
    ext ω
    simp only [mem_union, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro hω
      rcases le_or_gt (ρ ω) s with h | h
      · exact Or.inl ⟨hω, h⟩
      · exact Or.inr ⟨hω, h⟩
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  have hdisj : Disjoint (A ∩ {ω | ρ ω ≤ s}) (A ∩ {ω | s < ρ ω}) := by
    rw [Set.disjoint_left]
    rintro ω ⟨-, h1⟩ ⟨-, h2⟩
    exact absurd h1 (not_le.2 h2)
  rw [hsplit, setIntegral_union hdisj (hA'.inter hlt_meas) (hY.integrable s).integrableOn
    (hY.integrable s).integrableOn, setIntegral_union hdisj (hA'.inter hlt_meas)
    (hY.integrable t).integrableOn (hY.integrable t).integrableOn]
  congr 1
  · exact setIntegral_congr_fun (hA'.inter hle_meas) fun ω hω => (hYconst ω hω.2).symm
  · refine hY.setIntegral_eq hst ?_
    rw [h𝒢]
    exact measurableSet_inter_lt_min_const ℱ hρ hA

end Transfer

/-! ### Stopping at a finite stopping time -/

/-- **Stopped continuous local martingale** (via E2c). If `M` is an everywhere-continuous
`ℱ`-local martingale and `ρ` is a finite `ℱ`-stopping time, then `t ↦ M (t ∧ ρ)` is a continuous
`ℱ`-local martingale. -/
theorem IsContLocalMartingale.stopped_min (ℱ : Filtration ℝ≥0 mΩ) {M : ℝ≥0 → Ω → ℝ}
    (hM : IsContLocalMartingale ℱ M P) (hMc : ∀ ω, Continuous fun t => M t ω) {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0)) :
    IsContLocalMartingale ℱ (fun t ω => M (min t (ρ ω)) ω) P := by
  set σ : ℝ≥0 → Ω → ℝ≥0 := fun s ω => min s (ρ ω) with hσdef
  have hσeq : ∀ s, (fun ω => (σ s ω : WithTop ℝ≥0)) =
      fun ω => min ((ρ ω : WithTop ℝ≥0)) (s : WithTop ℝ≥0) := by
    intro s; funext ω
    simp only [hσdef, WithTop.coe_min, min_comm]
  have hσ : ∀ s, IsStoppingTime ℱ fun ω => (σ s ω : WithTop ℝ≥0) := fun s => by
    rw [hσeq s]; exact hρ.min_const s
  let 𝒢 : Filtration ℝ≥0 mΩ :=
    { seq := fun s => (hσ s).measurableSpace
      mono' := fun s t hst => IsStoppingTime.measurableSpace_mono _ _ fun ω => by
        simp only [hσdef, WithTop.coe_min]
        exact min_le_min_right _ (by exact_mod_cast hst)
      le' := fun s => (hσ s).measurableSpace_le }
  have h := External.timeChange_isContLocalMartingale ℱ M hM hMc σ hσ
    (fun ω => by simp [hσdef])
    (fun ω => ⟨continuous_id.min continuous_const, fun s t hst => min_le_min_right _ hst⟩)
    𝒢 (fun s => rfl)
  refine isContLocalMartingale_of_min_const ℱ hρ 𝒢 (fun s => ?_) h ?_
  · exact IsStoppingTime.measurableSpace_congr ℱ (hσ s) (hρ.min_const s) (hσeq s)
  · intro ω s t hst hρs
    simp only [min_eq_right hρs, min_eq_right (hρs.trans hst)]

end ComplexSLE

end
