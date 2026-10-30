/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsSLEDriver
import ComplexSLE.Internal.Driver.TimeReversal
import ComplexSLE.Internal.Driver.Shift
import ComplexSLE.Internal.Driver.Transform

/-!
# Finite-dimensional laws and the driver part of Proposition 1.5

For an `SLE_Σ` driver `U` and `t : ℝ≥0` put
`Y s = (U (t - s) - U t) + (U (max s t) - U t)` (truncated subtraction in `ℝ≥0`).

* `map_reversed_restrict`: for a finite set `I` of times, `(U (t - s) - U t)_{s ∈ I}` has the law of
  `(U (min s t))_{s ∈ I}` (this is `map_timeReversal` on `[0, t]` applied to the times `min s t`).
* `map_dual_restrict`: `Y` has the same finite-dimensional laws as `U`. Both are the same
  measurable function of the pair (future `s ↦ U (s + t) - U t`, a past vector), the future being
  independent of the past (`indepFun_shift_past`), and the two past vectors having the same law.
* `of_fdd_eq`: a process with a.s. continuous paths, `V 0 = 0` a.s. and the same finite-dimensional
  laws as an `SLE_Σ` driver is an `SLE_Σ` driver. (Only finite-dimensional laws are used, so no
  measurability of the path map is needed.)
* `dual`: `Ũ = i Y` is an `SLE_{Σ̃}` driver, `Σ̃ = [[b, -c], [-c, a]]`.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ComplexSLE.IsSLEDriver

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- For a finite set `I` of times, `(U (t - s) - U t)_{s ∈ I}` has the law of
`(U (min s t))_{s ∈ I}`. -/
theorem map_reversed_restrict (hU : IsSLEDriver a b c U P) (t : ℝ≥0) (I : Finset ℝ≥0) :
    P.map (fun ω (s : I) => U (t - (s : ℝ≥0)) ω - U t ω) =
      P.map (fun ω (s : I) => U (min (s : ℝ≥0) t) ω) := by
  classical
  have mU := hU.aemeasurable
  set S' : Finset ℝ≥0 := I.image (fun s => min s t) with hS'def
  have hS' : ∀ s ∈ S', s ≤ t := by
    intro s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
    exact min_le_right _ _
  have h := hU.map_timeReversal t S' hS'
  let ψ : (S' → ℂ) → (I → ℂ) := fun x i => x ⟨min i t, Finset.mem_image_of_mem _ i.2⟩
  have hψ : Measurable ψ := Measurable.of_eval fun i => measurable_pi_apply _
  have hXS : AEMeasurable (fun ω (s : S') => U (t - (s : ℝ≥0)) ω - U t ω) P :=
    aemeasurable_pi_iff.2 fun s => (mU _).sub (mU _)
  have hYS : AEMeasurable (fun ω (s : S') => U (s : ℝ≥0) ω) P :=
    aemeasurable_pi_iff.2 fun s => mU _
  have e1 : (fun ω (s : I) => U (t - (s : ℝ≥0)) ω - U t ω) =
      ψ ∘ (fun ω (s : S') => U (t - (s : ℝ≥0)) ω - U t ω) := by
    funext ω i
    simp only [Function.comp_apply, ψ]
    have : t - min (i : ℝ≥0) t = t - i := by
      rcases le_total (i : ℝ≥0) t with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h, tsub_self, tsub_eq_zero_of_le h]
    rw [this]
  have e2 : (fun ω (s : I) => U (min (s : ℝ≥0) t) ω) =
      ψ ∘ (fun ω (s : S') => U (s : ℝ≥0) ω) := by
    funext ω i
    simp only [Function.comp_apply, ψ]
  rw [e1, e2, ← AEMeasurable.map_map_of_aemeasurable hψ.aemeasurable hXS,
    ← AEMeasurable.map_map_of_aemeasurable hψ.aemeasurable hYS, h]

private theorem eq_min_add_max_sub (U : ℝ≥0 → ℂ) (s t : ℝ≥0) :
    U s = U (min s t) + (U (max s t) - U t) := by
  rcases le_total s t with h | h
  · rw [min_eq_left h, max_eq_right h]; ring
  · rw [min_eq_right h, max_eq_left h]; ring

/-- `Y` has the same finite-dimensional laws as `U`. -/
theorem map_dual_restrict (hU : IsSLEDriver a b c U P) (t : ℝ≥0) (S : Finset ℝ≥0) :
    P.map (fun ω (s : S) => (U (t - (s : ℝ≥0)) ω - U t ω) + (U (max (s : ℝ≥0) t) ω - U t ω)) =
      P.map (fun ω (s : S) => U (s : ℝ≥0) ω) := by
  have := hU.isProbabilityMeasure
  have mU := hU.aemeasurable
  have hind := hU.indepFun_shift_past t
  -- the future and the three past vectors
  let gF : (ℝ≥0 → ℂ) → (S → ℂ) := fun f s => f ((s : ℝ≥0) - t)
  let gP : (Set.Iic t → ℂ) → (S → ℂ) := fun p s =>
    p ⟨min (s : ℝ≥0) t, Set.mem_Iic.2 (min_le_right _ _)⟩
  let gP' : (Set.Iic t → ℂ) → (S → ℂ) := fun p s =>
    p ⟨t - (s : ℝ≥0), Set.mem_Iic.2 tsub_le_self⟩ - p ⟨t, Set.mem_Iic.2 le_rfl⟩
  have hgF : Measurable gF := Measurable.of_eval fun s => measurable_pi_apply _
  have hgP : Measurable gP := Measurable.of_eval fun s => measurable_pi_apply _
  have hgP' : Measurable gP' :=
    Measurable.of_eval fun s => (measurable_pi_apply _).sub (measurable_pi_apply _)
  let Fut : Ω → ℝ≥0 → ℂ := fun ω s => U (s + t) ω - U t ω
  let Past : Ω → Set.Iic t → ℂ := fun ω r => U (r : ℝ≥0) ω
  have hA_eq : ∀ ω, gF (Fut ω) = fun s : S => U (max (s : ℝ≥0) t) ω - U t ω := by
    intro ω
    funext s
    simp only [gF, Fut, tsub_add_eq_max]
  have hB_eq : ∀ ω, gP (Past ω) = fun s : S => U (min (s : ℝ≥0) t) ω := fun ω => rfl
  have hB'_eq : ∀ ω, gP' (Past ω) = fun s : S => U (t - (s : ℝ≥0)) ω - U t ω := fun ω => rfl
  have hA : AEMeasurable (fun ω => gF (Fut ω)) P := by
    simp only [hA_eq]
    exact aemeasurable_pi_iff.2 fun s => (mU _).sub (mU _)
  have hB : AEMeasurable (fun ω => gP (Past ω)) P := by
    simp only [hB_eq]
    exact aemeasurable_pi_iff.2 fun s => mU _
  have hB' : AEMeasurable (fun ω => gP' (Past ω)) P := by
    simp only [hB'_eq]
    exact aemeasurable_pi_iff.2 fun s => (mU _).sub (mU _)
  have i1 : IndepFun (fun ω => gF (Fut ω)) (fun ω => gP (Past ω)) P := hind.comp hgF hgP
  have i2 : IndepFun (fun ω => gF (Fut ω)) (fun ω => gP' (Past ω)) P := hind.comp hgF hgP'
  rw [indepFun_iff_map_prod_eq_prod_map_map hA hB] at i1
  rw [indepFun_iff_map_prod_eq_prod_map_map hA hB'] at i2
  have hlaw : P.map (fun ω => gP' (Past ω)) = P.map (fun ω => gP (Past ω)) := by
    simp only [hB_eq, hB'_eq]
    exact hU.map_reversed_restrict t S
  let Φ : (S → ℂ) × (S → ℂ) → (S → ℂ) := fun p => p.2 + p.1
  have hΦ : Measurable Φ := by fun_prop
  have hpair' : AEMeasurable (fun ω => (gF (Fut ω), gP' (Past ω))) P := hA.prodMk hB'
  have hpair : AEMeasurable (fun ω => (gF (Fut ω), gP (Past ω))) P := hA.prodMk hB
  have key : P.map (fun ω => (gF (Fut ω), gP' (Past ω))) =
      P.map (fun ω => (gF (Fut ω), gP (Past ω))) := by
    rw [i1, i2, hlaw]
  have eY : (fun ω (s : S) => (U (t - (s : ℝ≥0)) ω - U t ω) + (U (max (s : ℝ≥0) t) ω - U t ω)) =
      Φ ∘ (fun ω => (gF (Fut ω), gP' (Past ω))) := by
    funext ω
    simp only [Function.comp_apply, Φ, hA_eq, hB'_eq]
    rfl
  have eU : (fun ω (s : S) => U (s : ℝ≥0) ω) = Φ ∘ (fun ω => (gF (Fut ω), gP (Past ω))) := by
    funext ω s
    simp only [Function.comp_apply, Φ, hA_eq, hB_eq, Pi.add_apply]
    exact eq_min_add_max_sub (U · ω) s t
  rw [eY, eU, ← AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable hpair',
    ← AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable hpair, key]

/-- A process with a.s. continuous paths, `V 0 = 0` a.s., and the finite-dimensional laws of an
`SLE_Σ` driver is an `SLE_Σ` driver. -/
theorem of_fdd_eq (hU : IsSLEDriver a b c U P) {V : ℝ≥0 → Ω → ℂ}
    (hcont : ∀ᵐ ω ∂P, Continuous fun s => V s ω) (hzero : ∀ᵐ ω ∂P, V 0 ω = 0)
    (hmeas : ∀ s, AEMeasurable (V s) P)
    (hfdd : ∀ S : Finset ℝ≥0,
      P.map (fun ω (s : S) => V s ω) = P.map (fun ω (s : S) => U s ω)) :
    IsSLEDriver a b c V P := by
  classical
  have := hU.isProbabilityMeasure
  have mU := hU.aemeasurable
  -- functions of the finite-dimensional vectors have the same law
  have hG : ∀ (S : Finset ℝ≥0) {E : Type} [MeasurableSpace E] {G : (S → ℂ) → E},
      Measurable G → P.map (fun ω => G (fun s : S => V s ω)) =
        P.map (fun ω => G (fun s : S => U s ω)) := by
    intro S E _ G hG
    have hVS : AEMeasurable (fun ω (s : S) => V s ω) P := aemeasurable_pi_iff.2 fun s => hmeas _
    have hUS : AEMeasurable (fun ω (s : S) => U s ω) P := aemeasurable_pi_iff.2 fun s => mU _
    have e1 := AEMeasurable.map_map_of_aemeasurable hG.aemeasurable hVS
    have e2 := AEMeasurable.map_map_of_aemeasurable hG.aemeasurable hUS
    rw [hfdd S] at e1
    exact e1.symm.trans e2
  refine ⟨hcont, hzero, ?_, ?_⟩
  · intro n tt htt
    set S : Finset ℝ≥0 := Finset.univ.image tt with hS
    have hmem : ∀ j, tt j ∈ S := fun j => Finset.mem_image_of_mem tt (Finset.mem_univ j)
    let Θ : (S → ℂ) → (Fin n → ℂ) := fun x i =>
      x ⟨tt i.succ, hmem _⟩ - x ⟨tt i.castSucc, hmem _⟩
    have hΘ : Measurable Θ :=
      Measurable.of_eval fun i => (measurable_pi_apply _).sub (measurable_pi_apply _)
    have hvec := hG S hΘ
    have hUi := hU.indepIncrements n tt htt
    rw [iIndepFun_iff_map_fun_eq_pi_map
      (f := fun (i : Fin n) ω => U (tt i.succ) ω - U (tt i.castSucc) ω)
      (fun i => (mU _).sub (mU _))] at hUi
    rw [iIndepFun_iff_map_fun_eq_pi_map
      (f := fun (i : Fin n) ω => V (tt i.succ) ω - V (tt i.castSucc) ω)
      (fun i => (hmeas _).sub (hmeas _))]
    have hmarg : ∀ i : Fin n, P.map (fun ω => V (tt i.succ) ω - V (tt i.castSucc) ω) =
        P.map (fun ω => U (tt i.succ) ω - U (tt i.castSucc) ω) := fun i =>
      hG S (G := fun x => x ⟨tt i.succ, hmem _⟩ - x ⟨tt i.castSucc, hmem _⟩)
        ((measurable_pi_apply _).sub (measurable_pi_apply _))
    have hvec' : P.map (fun ω (i : Fin n) => V (tt i.succ) ω - V (tt i.castSucc) ω) =
        P.map (fun ω (i : Fin n) => U (tt i.succ) ω - U (tt i.castSucc) ω) := hvec
    rw [hvec', hUi]
    congr 1
    funext i
    exact (hmarg i).symm
  · intro s t hst
    have hS : s ∈ ({s, t} : Finset ℝ≥0) := by simp
    have hT : t ∈ ({s, t} : Finset ℝ≥0) := by simp
    refine ⟨(hmeas t).sub (hmeas s), ?_⟩
    have h := hG {s, t} (G := fun x => x ⟨t, hT⟩ - x ⟨s, hS⟩)
      ((measurable_pi_apply _).sub (measurable_pi_apply _))
    exact h.trans (hU.law_increment s t hst).map_eq

/-- **Driver part of Proposition 1.5.** If `U` is an `SLE_Σ` driver and `t : ℝ≥0`, then
`s ↦ i (U (t - s) - U t) + i (U (max s t) - U t)` is an `SLE_{Σ̃}` driver with
`Σ̃ = [[b, -c], [-c, a]]`. -/
theorem dual (hU : IsSLEDriver a b c U P) (t : ℝ≥0) :
    IsSLEDriver b a (-c)
      (fun s ω => Complex.I * (U (t - s) ω - U t ω) + Complex.I * (U (max s t) ω - U t ω)) P := by
  have mU := hU.aemeasurable
  have hY : IsSLEDriver a b c
      (fun s ω => (U (t - s) ω - U t ω) + (U (max s t) ω - U t ω)) P := by
    refine hU.of_fdd_eq ?_ ?_ (fun s => ((mU _).sub (mU _)).add ((mU _).sub (mU _)))
      (fun S => hU.map_dual_restrict t S)
    · filter_upwards [hU.cont] with ω hω
      fun_prop
    · exact Filter.Eventually.of_forall fun ω => by simp
  have := hY.mul_I
  simpa only [mul_add] using this

end ComplexSLE.IsSLEDriver

end
