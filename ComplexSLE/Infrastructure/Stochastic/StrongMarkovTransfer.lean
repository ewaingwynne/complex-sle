/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic

import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Strong Markov property: transfer along equality of path laws

Source-independent probability. No external input is used; only Mathlib.

Two small tools used to read off the properties of a restarted process from the law of its path.

* `map_sub_eq_of_map_path_eq`, `hasIndepIncrements_of_map_path_eq`: if the laws on `ℝ≥0 → E` of
  the paths of `V` and `W` coincide (and the coordinates are measurable) then increments of `V`
  and `W` have the same laws, and `V` has independent increments as soon as `W` has.
* `indep_comap_of_ae_eq_comp`: a measurable function of a process that is independent of a
  σ-algebra, modified on a null set, is still independent of it.
-/

public section

open scoped NNReal
open MeasureTheory ProbabilityTheory

namespace ComplexSLE.Infrastructure.StrongMarkov

/-- If `f` is a.e. equal to `g ∘ h` with `g` measurable and `h` independent of `m₂`, then `f` is
independent of `m₂`. -/
theorem indep_comap_of_ae_eq_comp {Ω β γ : Type*} {m₂ : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ] {P : Measure Ω}
    {h : Ω → β} {g : β → γ} {f : Ω → γ} (hg : Measurable g) (hfg : f =ᵐ[P] g ∘ h)
    (hI : Indep (MeasurableSpace.comap h mβ) m₂ P) :
    Indep (MeasurableSpace.comap f mγ) m₂ P := by
  rw [Indep_iff]
  rintro t1 t2 ⟨S, hS, rfl⟩ ht2
  have hae : f ⁻¹' S =ᵐ[P] h ⁻¹' (g ⁻¹' S) := by
    filter_upwards [hfg] with ω hω
    exact propext (by simp [hω])
  have hB : MeasurableSet[MeasurableSpace.comap h mβ] (h ⁻¹' (g ⁻¹' S)) :=
    ⟨g ⁻¹' S, hg hS, rfl⟩
  have hae2 : f ⁻¹' S ∩ t2 =ᵐ[P] h ⁻¹' (g ⁻¹' S) ∩ t2 := by
    filter_upwards [hfg] with ω hω
    exact propext (by simp [hω])
  rw [measure_congr hae2, measure_congr hae]
  exact (Indep_iff _ _ _).1 hI _ _ hB ht2

section Transfer

variable {Ω E : Type*} [AddCommGroup E] [MeasurableSpace E] [MeasurableSub₂ E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The law of an increment is a function of the law of the whole path. -/
theorem map_sub_eq_of_map_path_eq {V W : ℝ≥0 → Ω → E} (hV : ∀ t, Measurable (V t))
    (hW : ∀ t, Measurable (W t)) (h : P.map (fun ω t => V t ω) = P.map (fun ω t => W t ω))
    (s t : ℝ≥0) :
    P.map (fun ω => V t ω - V s ω) = P.map (fun ω => W t ω - W s ω) := by
  have hΨ : Measurable fun x : ℝ≥0 → E => x t - x s :=
    (measurable_pi_apply t).sub (measurable_pi_apply s)
  have h1 : (fun ω => V t ω - V s ω) = (fun x : ℝ≥0 → E => x t - x s) ∘ fun ω t => V t ω := rfl
  have h2 : (fun ω => W t ω - W s ω) = (fun x : ℝ≥0 → E => x t - x s) ∘ fun ω t => W t ω := rfl
  rw [h1, h2, ← Measure.map_map hΨ (measurable_pi_iff.2 hV),
    ← Measure.map_map hΨ (measurable_pi_iff.2 hW), h]

/-- Independence of increments depends only on the law of the path. -/
theorem hasIndepIncrements_of_map_path_eq [IsProbabilityMeasure P] {V W : ℝ≥0 → Ω → E}
    (hV : ∀ t, Measurable (V t)) (hW : ∀ t, Measurable (W t))
    (h : P.map (fun ω t => V t ω) = P.map (fun ω t => W t ω))
    (hW' : HasIndepIncrements W P) : HasIndepIncrements V P := by
  intro n t ht
  have hI := hW' n t ht
  have hΦ : Measurable fun x : ℝ≥0 → E => fun i : Fin n => x (t i.succ) - x (t i.castSucc) :=
    measurable_pi_iff.2 fun i => (measurable_pi_apply _).sub (measurable_pi_apply _)
  have hvec : P.map (fun ω (i : Fin n) => V (t i.succ) ω - V (t i.castSucc) ω) =
      P.map (fun ω (i : Fin n) => W (t i.succ) ω - W (t i.castSucc) ω) := by
    have h1 : (fun ω (i : Fin n) => V (t i.succ) ω - V (t i.castSucc) ω) =
        (fun x : ℝ≥0 → E => fun i : Fin n => x (t i.succ) - x (t i.castSucc)) ∘
          fun ω t => V t ω := rfl
    have h2 : (fun ω (i : Fin n) => W (t i.succ) ω - W (t i.castSucc) ω) =
        (fun x : ℝ≥0 → E => fun i : Fin n => x (t i.succ) - x (t i.castSucc)) ∘
          fun ω t => W t ω := rfl
    rw [h1, h2, ← Measure.map_map hΦ (measurable_pi_iff.2 hV),
      ← Measure.map_map hΦ (measurable_pi_iff.2 hW), h]
  have hmarg := fun i : Fin n => map_sub_eq_of_map_path_eq hV hW h (t i.castSucc) (t i.succ)
  have hVm : ∀ i : Fin n, AEMeasurable (fun ω => V (t i.succ) ω - V (t i.castSucc) ω) P :=
    fun i => ((hV _).sub (hV _)).aemeasurable
  have hWm : ∀ i : Fin n, AEMeasurable (fun ω => W (t i.succ) ω - W (t i.castSucc) ω) P :=
    fun i => ((hW _).sub (hW _)).aemeasurable
  rw [iIndepFun_iff_map_fun_eq_pi_map hWm] at hI
  rw [iIndepFun_iff_map_fun_eq_pi_map hVm, hvec, hI]
  congr 1
  funext i
  exact (hmarg i).symm

end Transfer

end ComplexSLE.Infrastructure.StrongMarkov

end
