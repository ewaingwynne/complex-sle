/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Ito.LocalizeBV
public import ComplexSLE.Infrastructure.Ito.LocalizeProcess
public import ComplexSLE.Infrastructure.Ito.LocalizeVariation

/-!
# Itô's formula for locally integrable drift and diffusion densities

Reduction of the exact statement of `ComplexSLE.External.ito_formula` (almost surely locally
integrable `A`, `Q`, almost surely `X ∈ D`) to the everywhere bounded variation case
(`isContLocalMartingale_itoProc_of_bounded_variation`).

Let `φ = ∑ |Aⁱ| + ∑ |Qⁱʲ|` and `ρ n = variationTime φ n` (`LocalizeVariation.lean`), a genuine
stopping time with `∫⁻_{(0, ρ n]} φ̃ ≤ n` for *every* `ω`, where `φ̃ = 1_{lintPath φ < ∞} φ`. The
data `(X_{· ∧ ρ n}, A', Q')` with `A' = A 1_{lintPath φ < ∞} 1_{s ≤ ρ n}` (and `Q'` likewise) have
bounded variation `≤ n` everywhere, and on the almost sure set where `lintPath φ < ∞` identically
their martingale parts and brackets are `(Mⁱ)^{ρ n}`, `(Nⁱʲ)^{ρ n}`, local martingales by
`isContLocalMartingale_stoppedProcess_of_ae_continuous`. Hence `Y^{ρ n}` is a local martingale for
every `n` and, since `ρ n → ∞` almost surely, so is `Y`
(`isContLocalMartingale_itoProc`).
-/

@[expose] public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Infrastructure.Ito

open ComplexSLE.Infrastructure

section Lintegral

variable {Ω : Type*}

/-- `∫⁻_{(0,t]} 1_{s ≤ T} ξ_s = ∫⁻_{(0, t ∧ T]} ξ_s`. -/
theorem lintPath_stopInd (ξ : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    lintPath (fun s ω => stopInd T s ω * ξ s ω) t ω = lintPath ξ (min t (T ω)) ω := by
  unfold lintPath
  have h : (fun s : ℝ => ENNReal.ofReal (stopInd T s.toNNReal ω * ξ s.toNNReal ω)) =
      (Iic ((T ω : ℝ≥0) : ℝ)).indicator fun s : ℝ => ENNReal.ofReal (ξ s.toNNReal ω) := by
    funext s
    by_cases hs : s.toNNReal ≤ T ω
    · have hs' : s ∈ Iic ((T ω : ℝ≥0) : ℝ) := by
        rw [mem_Iic]; exact Real.toNNReal_le_iff_le_coe.1 hs
      simp [stopInd, hs, hs']
    · have hs' : s ∉ Iic ((T ω : ℝ≥0) : ℝ) := fun h' =>
        hs (Real.toNNReal_le_iff_le_coe.2 (mem_Iic.1 h'))
      simp [stopInd, hs, hs']
  have hset : Iic ((T ω : ℝ≥0) : ℝ) ∩ Ioc (0 : ℝ) (t : ℝ) =
      Ioc (0 : ℝ) ((min t (T ω) : ℝ≥0) : ℝ) := by
    ext s
    simp [and_comm, and_left_comm, and_assoc]
  rw [h, setLIntegral_indicator measurableSet_Iic, hset]

/-- From a bound on the lintegral of `|ξ|` to interval integrability and a bound on `∫ |ξ|`. -/
theorem intervalIntegrable_and_abs_le_of_lintPath {ξ : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hmeas : Measurable fun r : ℝ => ξ r.toNNReal ω) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (h : ∀ t : ℝ≥0, lintPath (fun s ω => |ξ s ω|) t ω ≤ c) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => ξ s.toNNReal ω) volume 0 t ∧
      ∫ s in (0 : ℝ)..(t : ℝ), |ξ s.toNNReal ω| ≤ c.toReal := by
  have hlt : lintPath (fun s ω => |ξ s ω|) t ω < ⊤ := (h t).trans_lt hc.lt_top
  have hint : IntegrableOn (fun s : ℝ => ξ s.toNNReal ω) (Ioc 0 (t : ℝ)) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simp only [Real.enorm_eq_ofReal_abs]
    exact hlt
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).2 hint, ?_⟩
  rw [intervalIntegral.integral_of_le t.coe_nonneg]
  have hint' : IntegrableOn (fun s : ℝ => |ξ s.toNNReal ω|) (Ioc 0 (t : ℝ)) := hint.abs
  have := ofReal_integral_eq_lintegral_ofReal hint' (Eventually.of_forall fun s => abs_nonneg _)
  rw [← ENNReal.ofReal_le_iff_le_toReal hc, this]
  exact h t

end Lintegral


section Reduction

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m0} {d : ℕ}
  {A : ℝ≥0 → Ω → (Fin d → ℝ)} {Q : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ}

/-- `φ = ∑ᵢ |Aⁱ| + ∑ᵢⱼ |Qⁱʲ|`, the total size of the drift and diffusion densities. -/
noncomputable def varDensity (A : ℝ≥0 → Ω → (Fin d → ℝ))
    (Q : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i, |A s ω i| + ∑ i, ∑ j, |Q s ω i j|

theorem varDensity_nonneg (s : ℝ≥0) (ω : Ω) : 0 ≤ varDensity A Q s ω := by
  unfold varDensity; positivity

theorem abs_apply_le_varDensity (s : ℝ≥0) (ω : Ω) (i : Fin d) :
    |A s ω i| ≤ varDensity A Q s ω := by
  have h1 : |A s ω i| ≤ ∑ i, |A s ω i| :=
    Finset.single_le_sum (f := fun i => |A s ω i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have h2 : 0 ≤ ∑ i, ∑ j, |Q s ω i j| := by positivity
  unfold varDensity; linarith

theorem abs_matrix_apply_le_varDensity (s : ℝ≥0) (ω : Ω) (i j : Fin d) :
    |Q s ω i j| ≤ varDensity A Q s ω := by
  have h1 : |Q s ω i j| ≤ ∑ j, |Q s ω i j| :=
    Finset.single_le_sum (f := fun j => |Q s ω i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j, |Q s ω i j| ≤ ∑ i, ∑ j, |Q s ω i j| :=
    Finset.single_le_sum (f := fun i => ∑ j, |Q s ω i j|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have h3 : 0 ≤ ∑ i, |A s ω i| := by positivity
  unfold varDensity; linarith

theorem isStronglyProgressive_abs {ξ : ℝ≥0 → Ω → ℝ} (h : IsStronglyProgressive ℱ ξ) :
    IsStronglyProgressive ℱ fun s ω => |ξ s ω| := fun i =>
  continuous_abs.comp_stronglyMeasurable (h i)

theorem isStronglyProgressive_varDensity (hA : IsStronglyProgressive ℱ A)
    (hQ : IsStronglyProgressive ℱ Q) : IsStronglyProgressive ℱ (varDensity A Q) :=
  (IsStronglyProgressive.finsetSum fun i _ => isStronglyProgressive_abs
      (isStronglyProgressive_apply hA i)).add
    (IsStronglyProgressive.finsetSum fun i _ => IsStronglyProgressive.finsetSum fun j _ =>
      isStronglyProgressive_abs (isStronglyProgressive_matrix_apply hQ i j))

/-- Along a path with locally integrable densities, `lintPath φ` is finite. -/
theorem lintPath_varDensity_lt_top {ω : Ω}
    (hA : ∀ (i : Fin d) (t : ℝ≥0), IntervalIntegrable (fun s : ℝ => A s.toNNReal ω i) volume 0 t)
    (hQ : ∀ (i j : Fin d) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => Q s.toNNReal ω i j) volume 0 t) (t : ℝ≥0) :
    lintPath (varDensity A Q) t ω < ⊤ := by
  have hI : IntervalIntegrable (fun s : ℝ => varDensity A Q s.toNNReal ω) volume 0 t :=
    (intervalIntegrable_sum' Finset.univ fun i _ => (hA i t).abs).add
      (intervalIntegrable_sum' Finset.univ fun i _ =>
        intervalIntegrable_sum' Finset.univ fun j _ => (hQ i j t).abs)
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).1 hI).lintegral_lt_top

theorem gate_eq_one {φ : ℝ≥0 → Ω → ℝ} {s : ℝ≥0} {ω : Ω} (h : lintPath φ s ω < ⊤) :
    gate φ s ω = 1 := by
  simp [gate, h]

/-- The drift density switched off from the time its total variation becomes infinite. -/
noncomputable def gateSmul (φ : ℝ≥0 → Ω → ℝ) {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (A : ℝ≥0 → Ω → E) (s : ℝ≥0) (ω : Ω) : E := gate φ s ω • A s ω

theorem isStronglyProgressive_gateSmul {φ : ℝ≥0 → Ω → ℝ} (hφ : IsStronglyProgressive ℱ φ)
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] {A : ℝ≥0 → Ω → E} (hA : IsStronglyProgressive ℱ A) :
    IsStronglyProgressive ℱ (gateSmul φ A) := fun i =>
  ((isStronglyProgressive_gate hφ) i).smul (hA i)

theorem gateSmul_eq {φ : ℝ≥0 → Ω → ℝ} {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {A : ℝ≥0 → Ω → E} {s : ℝ≥0} {ω : Ω} (h : lintPath φ s ω < ⊤) : gateSmul φ A s ω = A s ω := by
  simp [gateSmul, gate_eq_one h]

/-- Pointwise bound of the switched-off, stopped drift density by `1_{s ≤ T} φ̃`. -/
theorem abs_stopSmul_gateSmul_le (T : Ω → ℝ≥0) (s : ℝ≥0) (ω : Ω) (i : Fin d) :
    |stopSmul T (gateSmul (varDensity A Q) A) s ω i| ≤
      stopInd T s ω * tilde (varDensity A Q) s ω := by
  have h := abs_apply_le_varDensity (A := A) (Q := Q) s ω i
  by_cases h1 : s ≤ T ω <;> by_cases h2 : lintPath (varDensity A Q) s ω < ⊤ <;>
    simp [stopSmul, stopInd, gateSmul, gate, tilde, h1, h2, h]

theorem abs_stopSmul_gateSmul_matrix_le (T : Ω → ℝ≥0) (s : ℝ≥0) (ω : Ω) (i j : Fin d) :
    |stopSmul T (gateSmul (varDensity A Q) Q) s ω i j| ≤
      stopInd T s ω * tilde (varDensity A Q) s ω := by
  have h := abs_matrix_apply_le_varDensity (A := A) (Q := Q) s ω i j
  by_cases h1 : s ≤ T ω <;> by_cases h2 : lintPath (varDensity A Q) s ω < ⊤ <;>
    simp [stopSmul, stopInd, gateSmul, gate, tilde, h1, h2, h]

/-- The total variation of the stopped, switched-off densities is at most `n`, for every `ω`. -/
theorem lintPath_abs_stopSmul_gateSmul_le (T : Ω → ℝ≥0) (n : ℕ) (ω : Ω)
    (hT : lintPath (tilde (varDensity A Q)) (T ω) ω ≤ n) (t : ℝ≥0) :
    lintPath (fun s ω => stopInd T s ω * tilde (varDensity A Q) s ω) t ω ≤ n := by
  rw [lintPath_stopInd]
  exact (lintPath_mono _ ω (min_le_right t (T ω))).trans hT

section GateEq

variable {X : ℝ≥0 → Ω → (Fin d → ℝ)} {φ : ℝ≥0 → Ω → ℝ} {ω : Ω}

theorem Mp_gateSmul (h : ∀ s, lintPath φ s ω < ⊤) (i : Fin d) (u : ℝ≥0) :
    Mp X (gateSmul φ A) i u ω = Mp X A i u ω := by
  simp only [Mp, pathIntegral, gateSmul_eq, h]

theorem Np_gateSmul (h : ∀ s, lintPath φ s ω < ⊤) (i j : Fin d) (u : ℝ≥0) :
    Np X (gateSmul φ A) (gateSmul φ Q) i j u ω = Np X A Q i j u ω := by
  simp only [Np, Mp_gateSmul h, pathIntegral, gateSmul_eq, h]

theorem itoProc_gateSmul {F : (Fin d → ℝ) → ℝ} (h : ∀ s, lintPath φ s ω < ⊤) (u : ℝ≥0) :
    itoProc F X (gateSmul φ A) (gateSmul φ Q) u ω = itoProc F X A Q u ω := by
  simp only [itoProc, itoDrift, pathIntegral, gateSmul_eq, h]

end GateEq

end Reduction



section Main

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m0} {d : ℕ}
  {X A : ℝ≥0 → Ω → (Fin d → ℝ)} {Q : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ}

/-- **Itô's formula (martingale form) for almost surely locally integrable densities.** The
statement of `ComplexSLE.External.ito_formula`, in terms of `Mp`, `Np`, `itoProc`. -/
theorem isContLocalMartingale_itoProc {P : Measure Ω} [IsProbabilityMeasure P]
    (hX : IsStronglyProgressive ℱ X) (hXc : ∀ ω, Continuous fun t => X t ω)
    (hA : IsStronglyProgressive ℱ A) (hQ : IsStronglyProgressive ℱ Q)
    (hAint : ∀ᵐ ω ∂P, ∀ (i : Fin d) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => A s.toNNReal ω i) volume 0 t)
    (hQint : ∀ᵐ ω ∂P, ∀ (i j : Fin d) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => Q s.toNNReal ω i j) volume 0 t)
    (hM : ∀ i, IsContLocalMartingale ℱ (Mp X A i) P)
    (hMM : ∀ i j, IsContLocalMartingale ℱ (Np X A Q i j) P)
    {D : Set (Fin d → ℝ)} (hD : IsOpen D) {F : (Fin d → ℝ) → ℝ} (hFm : Measurable F)
    (hF : ContDiffOn ℝ 2 F D) (hXD : ∀ᵐ ω ∂P, ∀ t, X t ω ∈ D) :
    IsContLocalMartingale ℱ (itoProc F X A Q) P := by
  set φ := varDensity A Q with hφdef
  have hφ : IsStronglyProgressive ℱ φ := isStronglyProgressive_varDensity hA hQ
  set ρ : ℕ → Ω → ℝ≥0 := variationTime φ with hρdef
  have hρ : ∀ n, IsStoppingTime ℱ fun ω => (ρ n ω : WithTop ℝ≥0) :=
    isStoppingTime_variationTime hφ
  have hgood : ∀ᵐ ω ∂P, (∀ (i : Fin d) (t : ℝ≥0),
        IntervalIntegrable (fun s : ℝ => A s.toNNReal ω i) volume 0 t) ∧
      (∀ (i j : Fin d) (t : ℝ≥0),
        IntervalIntegrable (fun s : ℝ => Q s.toNNReal ω i j) volume 0 t) ∧
      (∀ t, X t ω ∈ D) ∧ (∀ t, lintPath φ t ω < ⊤) := by
    filter_upwards [hAint, hQint, hXD] with ω h1 h2 h3
    exact ⟨h1, h2, h3, lintPath_varDensity_lt_top h1 h2⟩
  have hprog := isStronglyProgressive_itoProc hX hA hQ hFm
  have hcont : ∀ᵐ ω ∂P, Continuous fun t => itoProc F X A Q t ω := by
    filter_upwards [hgood] with ω h
    exact continuous_itoProc hXc h.1 h.2.1 hD hF h.2.2.1
  refine IsContLocalMartingale.of_stopped_seq hprog hcont
    (ρ := fun n ω => (ρ n ω : WithTop ℝ≥0)) hρ ?_ fun n => ?_
  · -- the variation times are eventually above every level
    filter_upwards [hgood] with ω h t
    have hfin := h.2.2.2 t
    obtain ⟨N, hN⟩ := exists_nat_gt (max (t : ℝ) (lintPath φ t ω).toReal)
    rw [eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
    have htn : t ≤ (n : ℝ≥0) := by
      have : (t : ℝ) ≤ n := ((le_max_left _ _).trans_lt hN).le.trans hnR
      exact_mod_cast this
    have hJ : lintPath φ t ω < (n : ℝ≥0∞) := by
      have h1 : (lintPath φ t ω).toReal < n := ((le_max_right _ _).trans_lt hN).trans_le hnR
      exact (ENNReal.toReal_lt_toReal hfin.ne (ENNReal.natCast_ne_top n)).1 (by simpa using h1)
    exact WithTop.coe_le_coe.2 (le_variationTime htn hJ)
  · -- the stopped Itô process is a continuous local martingale
    set T := ρ n with hT
    have hTst : IsStoppingTime ℱ fun ω => (T ω : WithTop ℝ≥0) := hρ n
    have hAg : IsStronglyProgressive ℱ (gateSmul φ A) := isStronglyProgressive_gateSmul hφ hA
    have hQg : IsStronglyProgressive ℱ (gateSmul φ Q) := isStronglyProgressive_gateSmul hφ hQ
    have hA' : IsStronglyProgressive ℱ (stopSmul T (gateSmul φ A)) :=
      isStronglyProgressive_stopSmul hTst hAg
    have hQ' : IsStronglyProgressive ℱ (stopSmul T (gateSmul φ Q)) :=
      isStronglyProgressive_stopSmul hTst hQg
    have hX'p : IsStronglyProgressive ℱ (frozenStop (Set.univ : Set (Fin d → ℝ)) 0 T X) :=
      isStronglyProgressive_frozenStop MeasurableSet.univ 0 hTst hX
    have hX'c : ∀ ω, Continuous fun t => frozenStop (Set.univ : Set (Fin d → ℝ)) 0 T X t ω :=
      fun ω => by
        simp only [frozenStop, mem_univ, ite_true]
        exact (hXc ω).comp (continuous_id.min continuous_const)
    have hT0 : ∀ ω, X 0 ω ∉ (Set.univ : Set (Fin d → ℝ)) → T ω = 0 :=
      fun ω h => absurd (mem_univ _) h
    have hvar : ∀ ω, lintPath (tilde φ) (T ω) ω ≤ n :=
      fun ω => lintPath_tilde_variationTime_le φ n ω
    have hAbd : ∀ ω (i : Fin d) (t : ℝ≥0),
        IntervalIntegrable (fun s : ℝ => stopSmul T (gateSmul φ A) s.toNNReal ω i) volume 0 t ∧
          ∫ s in (0 : ℝ)..(t : ℝ), |stopSmul T (gateSmul φ A) s.toNNReal ω i| ≤ (n : ℝ) :=
      fun ω i t => by
        have := intervalIntegrable_and_abs_le_of_lintPath
          (ξ := fun s ω => stopSmul T (gateSmul φ A) s ω i) (ω := ω)
          (measurable_toNNReal_section (isStronglyProgressive_apply hA' i) ω)
          (c := (n : ℝ≥0∞)) (ENNReal.natCast_ne_top n) (fun t => ?_) t
        · simpa using this
        · calc lintPath (fun s ω => |stopSmul T (gateSmul φ A) s ω i|) t ω
              ≤ lintPath (fun s ω => stopInd T s ω * tilde φ s ω) t ω :=
                lintegral_mono fun r => ENNReal.ofReal_le_ofReal
                  (abs_stopSmul_gateSmul_le (A := A) (Q := Q) T _ ω i)
            _ ≤ n := lintPath_abs_stopSmul_gateSmul_le T n ω (hvar ω) t
    have hQbd : ∀ ω (i j : Fin d) (t : ℝ≥0),
        IntervalIntegrable (fun s : ℝ => stopSmul T (gateSmul φ Q) s.toNNReal ω i j) volume 0 t ∧
          ∫ s in (0 : ℝ)..(t : ℝ), |stopSmul T (gateSmul φ Q) s.toNNReal ω i j| ≤ (n : ℝ) :=
      fun ω i j t => by
        have := intervalIntegrable_and_abs_le_of_lintPath
          (ξ := fun s ω => stopSmul T (gateSmul φ Q) s ω i j) (ω := ω)
          (measurable_toNNReal_section (isStronglyProgressive_matrix_apply hQ' i j) ω)
          (c := (n : ℝ≥0∞)) (ENNReal.natCast_ne_top n) (fun t => ?_) t
        · simpa using this
        · calc lintPath (fun s ω => |stopSmul T (gateSmul φ Q) s ω i j|) t ω
              ≤ lintPath (fun s ω => stopInd T s ω * tilde φ s ω) t ω :=
                lintegral_mono fun r => ENNReal.ofReal_le_ofReal
                  (abs_stopSmul_gateSmul_matrix_le (A := A) (Q := Q) T _ ω i j)
            _ ≤ n := lintPath_abs_stopSmul_gateSmul_le T n ω (hvar ω) t
    -- the martingale parts and brackets of the new data are the stopped ones, a.s.
    have hMeq : ∀ᵐ ω ∂P, ∀ (i : Fin d) (t : ℝ≥0),
        Mp (frozenStop (Set.univ : Set (Fin d → ℝ)) 0 T X) (stopSmul T (gateSmul φ A)) i t ω =
          stoppedProcess (Mp X A i) (fun ω => (T ω : WithTop ℝ≥0)) t ω := by
      filter_upwards [hgood] with ω h i t
      rw [stoppedProcess_coe, Mp_frozenStop hT0, Mp_gateSmul h.2.2.2]
    have hNeq : ∀ᵐ ω ∂P, ∀ (i j : Fin d) (t : ℝ≥0),
        Np (frozenStop (Set.univ : Set (Fin d → ℝ)) 0 T X) (stopSmul T (gateSmul φ A))
          (stopSmul T (gateSmul φ Q)) i j t ω =
          stoppedProcess (Np X A Q i j) (fun ω => (T ω : WithTop ℝ≥0)) t ω := by
      filter_upwards [hgood] with ω h i j t
      rw [stoppedProcess_coe, Np_frozenStop hT0, Np_gateSmul h.2.2.2]
    have hYeq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        itoProc F (frozenStop (Set.univ : Set (Fin d → ℝ)) 0 T X) (stopSmul T (gateSmul φ A))
          (stopSmul T (gateSmul φ Q)) t ω =
          stoppedProcess (itoProc F X A Q) (fun ω => (T ω : WithTop ℝ≥0)) t ω := by
      filter_upwards [hgood] with ω h t
      rw [stoppedProcess_coe, itoProc_frozenStop hT0, itoProc_gateSmul h.2.2.2]
    have hM' : ∀ i, IsContLocalMartingale ℱ
        (Mp (frozenStop (Set.univ : Set (Fin d → ℝ)) 0 T X) (stopSmul T (gateSmul φ A)) i) P :=
      fun i => (isContLocalMartingale_stoppedProcess_of_ae_continuous (hM i) hTst).congr_ae
        (isStronglyProgressive_Mp hX'p hA' i) (by filter_upwards [hMeq] with ω h t using h i t)
    have hMM' : ∀ i j, IsContLocalMartingale ℱ
        (Np (frozenStop (Set.univ : Set (Fin d → ℝ)) 0 T X) (stopSmul T (gateSmul φ A))
          (stopSmul T (gateSmul φ Q)) i j) P :=
      fun i j => (isContLocalMartingale_stoppedProcess_of_ae_continuous (hMM i j) hTst).congr_ae
        (isStronglyProgressive_Np hX'p hA' hQ' i j)
        (by filter_upwards [hNeq] with ω h t using h i j t)
    have hXD' : ∀ᵐ ω ∂P, ∀ t, frozenStop (Set.univ : Set (Fin d → ℝ)) 0 T X t ω ∈ D := by
      filter_upwards [hXD] with ω h t
      simp only [frozenStop, mem_univ, ite_true]
      exact h _
    have hL1 := isContLocalMartingale_itoProc_of_bounded_variation (ℱ := ℱ)
      (X := frozenStop (Set.univ : Set (Fin d → ℝ)) 0 T X) (A := stopSmul T (gateSmul φ A))
      (Q := stopSmul T (gateSmul φ Q)) hX'p hX'c hA' hQ' (C₀ := (n : ℝ))
      (fun ω i t => (hAbd ω i t).1) (fun ω i t => (hAbd ω i t).2)
      (fun ω i j t => (hQbd ω i j t).1) (fun ω i j t => (hQbd ω i j t).2) hM' hMM' hD hFm hF hXD'
    exact hL1.congr_ae (hprog.stoppedProcess hTst)
      (by filter_upwards [hYeq] with ω h t using (h t).symm)

end Main

end ComplexSLE.Infrastructure.Ito

end
