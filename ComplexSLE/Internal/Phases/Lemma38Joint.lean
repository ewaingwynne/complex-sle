/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.Lemma38Step
public import ComplexSLE.Internal.Phases.EventMeasDist
public import ComplexSLE.Internal.Polar.PolarContMeas
public import ComplexSLE.Internal.Stationary.PathStatCanon

/-!
# Lemma 3.10, joint measurability of `dist(e^{iu}, L_{σ_{e^{iu}}(t̃)})` on `Ω × ℝ` (M7/E2)

For an adapted driver `U` (continuous paths) put `ddU t (ω, u) = dist(e^{iu}, L_t(U(ω)))` and
`distSigma t̃ (ω, u) = dist(e^{iu}, L_{σ_{e^{iu}}(t̃)}(U(ω)))`.

* `measurable_ddU`: `ddU t` is measurable on `Ω × ℝ` for each `t`
  (`measurable_infDist_leftHull`, composed with `(ω, u) ↦ (U(ω), e^{iu})`);
* `measurableSet_distSigma_le`: for every `r`, `{(ω, u) | t̃ ∈ sigmaDom ∧ distSigma ≤ r}` is
  measurable. Since `t ↦ dist(z, L_t)` is non-increasing and right-continuous
  (`Lemma38Hull.lean`), and `σ_z(t̃) ≥ q ⟺ A_q ≤ t̃`, this set equals
  `{t̃ ∈ sigmaDom} ∩ ⋂_{q ∈ D} {dist(z, L_q) > r → (q < T_z ∧ A_q ≤ t̃)}` for a countable dense `D`;
* `measurable_distSigmaTilde`: `distSigma` with the junk value `0` off the (a.s. full) domain is
  measurable.
-/

public section

open scoped NNReal ENNReal Topology Real
open Set Metric Filter MeasureTheory

namespace ComplexSLE.Internal

open Polar

section Joint

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-- `dist(e^{iu}, L_t(U(ω)))`. -/
@[expose] noncomputable def ddU (U : ℝ≥0 → Ω → ℂ) (t : ℝ≥0) (p : Ω × ℝ) : ℝ :=
  infDist (unitPt p.2) (leftHull (fun s => U s p.1) t)

/-- `dist(e^{iu}, L_{σ_{e^{iu}}(t̃)}(U(ω)))` (junk off the domain of `σ`). -/
@[expose] noncomputable def distSigma (hU : IsSLEDriverAdapted a b c U P ℱ) (tt : ℝ≥0)
    (p : Ω × ℝ) : ℝ :=
  infDist (unitPt p.2) (leftHull (fun s => U s p.1)
    (sigmaTime (fun s => U s p.1) (hU.cont p.1) (unitPt p.2) tt).toNNReal)

theorem measurable_ddU (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) :
    Measurable (ddU U t) := by
  have hUm : ∀ s, Measurable (U s) := fun s => hU.adapted.measurable
  have h1 : Measurable fun ω : Ω => (CPath.ofDriver U hU.cont ω : ContPath) :=
    CPath.measurable_ofDriver hU.cont hUm
  have h2 : Measurable fun u : ℝ => unitPt u := continuous_unitPt.measurable
  have h3 : Measurable fun p : Ω × ℝ =>
      ((CPath.ofDriver U hU.cont p.1 : ContPath), unitPt p.2) :=
    (h1.comp measurable_fst).prodMk (h2.comp measurable_snd)
  have h4 := (measurable_infDist_leftHull t).comp h3
  exact h4

open Classical in
theorem measurableSet_distSigma_le (hU : IsSLEDriverAdapted a b c U P ℱ) (tt : ℝ≥0) (r : ℝ) :
    MeasurableSet {p : Ω × ℝ | (tt : ℝ) ∈ sigmaDom (fun s => U s p.1) (hU.cont p.1) (unitPt p.2) ∧
      distSigma hU tt p ≤ r} := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hunit : ∀ u : ℝ, unitPt u = Complex.exp ((u : ℂ) * Complex.I) := fun u => rfl
  set dom : Set (Ω × ℝ) :=
    {p | (tt : ℝ) ∈ sigmaDom (fun s => U s p.1) (hU.cont p.1) (unitPt p.2)} with hdom
  have hdomm : MeasurableSet dom := measurableSet_sigmaDom_unit hU.cont hU.adapted tt
  have key : {p : Ω × ℝ | (tt : ℝ) ∈ sigmaDom (fun s => U s p.1) (hU.cont p.1) (unitPt p.2) ∧
      distSigma hU tt p ≤ r} = dom ∩ ⋂ q ∈ D,
        ({p : Ω × ℝ | ddU U q p ≤ r} ∪
          ({p : Ω × ℝ | (q : ℝ) ∈ lifeSet (fun s => U s p.1) (unitPt p.2)} ∩
            {p : Ω × ℝ | (if (q : ℝ) ∈ lifeSet (fun s => U s p.1) (unitPt p.2) then
              clock (fun s => U s p.1) (hU.cont p.1) (unitPt p.2) q else 0) ≤ tt})) := by
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_union]
    constructor
    · rintro ⟨hp, hd⟩
      refine ⟨hp, fun q hq => ?_⟩
      by_cases hqr : ddU U q p ≤ r
      · exact Or.inl hqr
      · right
        push Not at hqr
        set σ := sigmaTime (fun s => U s p.1) (hU.cont p.1) (unitPt p.2) tt with hσ
        have hσlife : σ ∈ lifeSet (fun s => U s p.1) (unitPt p.2) :=
          sigmaTime_mem_lifeSet (hU.cont p.1) hp
        have hσ0 : ((σ.toNNReal : ℝ≥0) : ℝ) = σ := Real.coe_toNNReal _ hσlife.1
        have hqσ : q < σ.toNNReal := by
          by_contra hcon
          push Not at hcon
          have h1 := infDist_leftHull_anti (U := fun s => U s p.1) (unitPt p.2) hcon
          have h2 : ddU U q p ≤ distSigma hU tt p := h1
          linarith
        have hqlife : (q : ℝ) ∈ lifeSet (fun s => U s p.1) (unitPt p.2) :=
          mem_lifeSet_of_le hσlife q.coe_nonneg (by
            rw [← hσ0]; exact_mod_cast hqσ.le)
        refine ⟨hqlife, ?_⟩
        simp only [hqlife, ↓reduceIte]
        have := clock_monotoneOn (hU.cont p.1) (unitPt p.2) hqlife hσlife (by
          rw [← hσ0]; exact_mod_cast hqσ.le)
        rwa [clock_sigmaTime (hU.cont p.1) hp] at this
    · rintro ⟨hp, h⟩
      refine ⟨hp, ?_⟩
      by_contra hcon
      push Not at hcon
      set σ := sigmaTime (fun s => U s p.1) (hU.cont p.1) (unitPt p.2) tt with hσ
      have hσlife : σ ∈ lifeSet (fun s => U s p.1) (unitPt p.2) :=
        sigmaTime_mem_lifeSet (hU.cont p.1) hp
      have hσ0 : ((σ.toNNReal : ℝ≥0) : ℝ) = σ := Real.coe_toNNReal _ hσlife.1
      set ε := distSigma hU tt p - r with hε
      have hεpos : 0 < ε / 2 := by rw [hε]; linarith
      obtain ⟨δ, hδ, hδ'⟩ := exists_forall_sub_le_infDist_leftHull (hU.cont p.1) (unitPt p.2)
        σ.toNNReal hεpos
      obtain ⟨q, hqD, hq1, hq2⟩ := hDd.exists_between (lt_add_of_pos_right σ.toNNReal hδ)
      have hqdd : r < ddU U q p := by
        have := hδ' q hq1 hq2
        have h2 : distSigma hU tt p - ε / 2 ≤ ddU U q p := this
        linarith
      rcases h q hqD with h1 | ⟨hqlife, hqclock⟩
      · linarith
      · simp only [hqlife, ↓reduceIte] at hqclock
        have hle := le_of_clock_le_clock (hU.cont p.1) hqlife hσlife (by
          rw [clock_sigmaTime (hU.cont p.1) hp]; exact hqclock)
        have : (σ.toNNReal : ℝ) < q := by exact_mod_cast hq1
        rw [hσ0] at this
        linarith
  rw [key]
  refine hdomm.inter (MeasurableSet.biInter hDc fun q _ => ?_)
  refine (measurableSet_le (measurable_ddU hU q) measurable_const).union ?_
  refine (measurableSet_mem_lifeSet_unit hU.cont hU.adapted q).inter ?_
  exact measurableSet_le (measurable_clock_unit hU.cont hU.adapted q) measurable_const

open Classical in
/-- `distSigma`, with the junk value `0` off the domain of `σ`; measurable. -/
@[expose] noncomputable def distSigmaTilde (hU : IsSLEDriverAdapted a b c U P ℱ) (tt : ℝ≥0)
    (p : Ω × ℝ) : ℝ :=
  if (tt : ℝ) ∈ sigmaDom (fun s => U s p.1) (hU.cont p.1) (unitPt p.2) then distSigma hU tt p
  else 0

theorem measurable_distSigmaTilde (hU : IsSLEDriverAdapted a b c U P ℱ) (tt : ℝ≥0) :
    Measurable (distSigmaTilde hU tt) := by
  refine measurable_of_Iic fun r => ?_
  have hdomm : MeasurableSet {p : Ω × ℝ |
      (tt : ℝ) ∈ sigmaDom (fun s => U s p.1) (hU.cont p.1) (unitPt p.2)} :=
    measurableSet_sigmaDom_unit hU.cont hU.adapted tt
  by_cases hr : 0 ≤ r
  · have : distSigmaTilde hU tt ⁻¹' Iic r =
        {p : Ω × ℝ | (tt : ℝ) ∈ sigmaDom (fun s => U s p.1) (hU.cont p.1) (unitPt p.2)}ᶜ ∪
          {p : Ω × ℝ | (tt : ℝ) ∈ sigmaDom (fun s => U s p.1) (hU.cont p.1) (unitPt p.2) ∧
            distSigma hU tt p ≤ r} := by
      ext p
      by_cases hp : (tt : ℝ) ∈ sigmaDom (fun s => U s p.1) (hU.cont p.1) (unitPt p.2)
      · simp [distSigmaTilde, hp]
      · simp [distSigmaTilde, hp, hr]
    rw [this]
    exact hdomm.compl.union (measurableSet_distSigma_le hU tt r)
  · have : distSigmaTilde hU tt ⁻¹' Iic r = {p : Ω × ℝ |
        (tt : ℝ) ∈ sigmaDom (fun s => U s p.1) (hU.cont p.1) (unitPt p.2) ∧
          distSigma hU tt p ≤ r} := by
      ext p
      by_cases hp : (tt : ℝ) ∈ sigmaDom (fun s => U s p.1) (hU.cont p.1) (unitPt p.2)
      · simp only [mem_preimage, mem_Iic, mem_ofPred_eq, distSigmaTilde, hp, ↓reduceIte, true_and]
      · simp only [mem_preimage, mem_Iic, mem_ofPred_eq, distSigmaTilde, hp, ↓reduceIte,
          false_and, iff_false]
        exact hr
    rw [this]
    exact measurableSet_distSigma_le hU tt r

end Joint

end ComplexSLE.Internal

end
