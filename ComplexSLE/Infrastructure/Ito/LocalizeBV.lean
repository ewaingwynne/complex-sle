/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Ito.Bounded
public import ComplexSLE.Infrastructure.Ito.LocalizeData
public import ComplexSLE.Infrastructure.Ito.LocalizeExit
public import ComplexSLE.Infrastructure.Ito.LocalizeProcess
public import ComplexSLE.Infrastructure.Ito.LocalizeStopping
public import ComplexSLE.Infrastructure.Stochastic.TimeChangeExitTimes

/-!
# Itô's formula for data of everywhere bounded variation

The bounded core `martingale_ito_bounded` needs a compact set, bounded drift and bracket densities,
bounded martingale parts and true martingales. This file reduces to it, for data whose drift and
diffusion densities have *everywhere* bounded total variation (so that `Mⁱ`, `Nⁱʲ` have everywhere
continuous paths and exit times of them are genuine stopping times of an arbitrary filtration).

* `martingale_stopped_itoProc`: for a stopping time `T` that keeps `X` in `closure U` (and is `0`
  when `X₀ ∉ U`) and keeps `|Mⁱ| ≤ C`, the stopped Itô process `Y^T` is a martingale. The data are
  frozen on `{X₀ ∉ U}` (`frozenStop`) so that `X` stays in a compact subset of `D`.
* `isContLocalMartingale_itoProc_of_bounded_variation`: Itô's formula for data of everywhere
  bounded variation. The stopping times are `T n = min (capExitTime (∑ᵢ |Mⁱ|) n)
  (exhaustionExitTime X D n)`, the exit of `∑ᵢ |Mⁱ|` from `[-n, n]` and of `X` from `expU D n`;
  they are genuine stopping times because `Mⁱ` and `X` are everywhere continuous.
-/

@[expose] public section

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Infrastructure.Ito

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

theorem stoppedProcess_coe {E : Type*} (Y : ℝ≥0 → Ω → E) (T : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    stoppedProcess Y (fun ω => (T ω : WithTop ℝ≥0)) t ω = Y (min t (T ω)) ω := by
  simp only [stoppedProcess]
  rw [← WithTop.coe_min]
  rfl

/-- **The stopped Itô process is a martingale.** Let `(X, A, Q)` be Itô data with everywhere
integrable densities of everywhere bounded variation, `Mⁱ`, `Nⁱʲ` continuous local martingales. Let
`T` be a stopping time, `U` an open set with compact closure inside the open set `D` such that,
when `X₀ ∈ U`, `X` stays in `closure U` up to `T`, `T = 0` when `X₀ ∉ U`, and `|Mⁱ| ≤ C` up to `T`.
Then `Y^T` is a martingale. -/
theorem martingale_stopped_itoProc {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ≥0 m0} {d : ℕ} {X A : ℝ≥0 → Ω → (Fin d → ℝ)}
    {Q : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ}
    (hX : IsStronglyProgressive ℱ X) (hXc : ∀ ω, Continuous fun t => X t ω)
    (hA : IsStronglyProgressive ℱ A) (hQ : IsStronglyProgressive ℱ Q) {C₀ : ℝ}
    (hAint : ∀ ω (i : Fin d) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => A s.toNNReal ω i) volume 0 t)
    (hAC : ∀ ω (i : Fin d) (t : ℝ≥0), ∫ s in (0 : ℝ)..(t : ℝ), |A s.toNNReal ω i| ≤ C₀)
    (hQint : ∀ ω (i j : Fin d) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => Q s.toNNReal ω i j) volume 0 t)
    (hQC : ∀ ω (i j : Fin d) (t : ℝ≥0), ∫ s in (0 : ℝ)..(t : ℝ), |Q s.toNNReal ω i j| ≤ C₀)
    (hM : ∀ i, IsContLocalMartingale ℱ (Mp X A i) P)
    (hMM : ∀ i j, IsContLocalMartingale ℱ (Np X A Q i j) P)
    {D : Set (Fin d → ℝ)} (hD : IsOpen D) {F : (Fin d → ℝ) → ℝ} (hFm : Measurable F)
    (hF : ContDiffOn ℝ 2 F D) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime ℱ fun ω => (T ω : WithTop ℝ≥0))
    {U : Set (Fin d → ℝ)} (hU : IsOpen U) (hUD : closure U ⊆ D) (hUc : IsCompact (closure U))
    {C : ℝ} (hTU : ∀ ω u, X 0 ω ∈ U → u ≤ T ω → X u ω ∈ closure U)
    (hT0 : ∀ ω, X 0 ω ∉ U → T ω = 0) (hTM : ∀ ω u i, u ≤ T ω → |Mp X A i u ω| ≤ C)
    {x₀ : Fin d → ℝ} (hx₀ : x₀ ∈ D) :
    Martingale (stoppedProcess (itoProc F X A Q) fun ω => (T ω : WithTop ℝ≥0)) ℱ P := by
  -- everywhere continuity of `Mⁱ` and `Nⁱʲ`
  have hMc : ∀ i ω, Continuous fun t => Mp X A i t ω := fun i ω =>
    (((continuous_apply i).comp (hXc ω)).sub continuous_const).sub
      (continuous_pathIntegral (hAint ω i))
  have hNc : ∀ i j ω, Continuous fun t => Np X A Q i j t ω := fun i j ω =>
    ((hMc i ω).mul (hMc j ω)).sub (continuous_pathIntegral (hQint ω i j))
  -- the stopped local martingales are bounded, hence martingales
  have hMT : ∀ i, Martingale
      (stoppedProcess (Mp X A i) fun ω => (T ω : WithTop ℝ≥0)) ℱ P := fun i =>
    martingale_of_isContLocalMartingale_of_bounded
      ((hM i).stoppedProcess_of_continuous (hMc i) hT) (C := C)
      (Eventually.of_forall fun ω t => by
        rw [stoppedProcess_coe]; exact hTM ω _ i (min_le_right _ _))
  have hNT : ∀ i j, Martingale
      (stoppedProcess (Np X A Q i j) fun ω => (T ω : WithTop ℝ≥0)) ℱ P := fun i j =>
    martingale_of_isContLocalMartingale_of_bounded
      ((hMM i j).stoppedProcess_of_continuous (hNc i j) hT) (C := C * C + C₀)
      (Eventually.of_forall fun ω t => by
        rw [stoppedProcess_coe]
        have h1 := hTM ω _ i (min_le_right t (T ω))
        have h2 := hTM ω _ j (min_le_right t (T ω))
        have h3 : |pathIntegral (fun s ω => Q s ω i j) (min t (T ω)) ω| ≤ C₀ :=
          (abs_pathIntegral_le _).trans (hQC ω i j _)
        calc |Np X A Q i j (min t (T ω)) ω|
            = |Mp X A i (min t (T ω)) ω * Mp X A j (min t (T ω)) ω -
                pathIntegral (fun s ω => Q s ω i j) (min t (T ω)) ω| := rfl
          _ ≤ |Mp X A i (min t (T ω)) ω * Mp X A j (min t (T ω)) ω| +
                |pathIntegral (fun s ω => Q s ω i j) (min t (T ω)) ω| := abs_sub _ _
          _ ≤ C * C + C₀ := by
            rw [abs_mul]
            exact add_le_add (mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)) h3)
  -- the frozen data
  set X' := frozenStop U x₀ T X with hX'
  set A' := stopSmul T A with hA'
  set Q' := stopSmul T Q with hQ'
  have hX'p : IsStronglyProgressive ℱ X' :=
    isStronglyProgressive_frozenStop hU.measurableSet x₀ hT hX
  have hX'c : ∀ ω, Continuous fun t => X' t ω := fun ω => by
    simp only [hX', frozenStop]
    split_ifs
    · exact (hXc ω).comp (continuous_id.min continuous_const)
    · exact continuous_const
  have hK : IsCompact (closure U ∪ {x₀}) := hUc.union isCompact_singleton
  have hKD : closure U ∪ {x₀} ⊆ D := union_subset hUD (singleton_subset_iff.2 hx₀)
  have hXK : ∀ ω t, X' t ω ∈ closure U ∪ {x₀} := fun ω t => by
    by_cases hG : X 0 ω ∈ U
    · simp only [hX', frozenStop, hG, ite_true]
      exact Or.inl (hTU ω _ hG (min_le_right _ _))
    · simp only [hX', frozenStop, hG, ite_false]
      exact Or.inr rfl
  have hMb : ∀ ω (i : Fin d) (t : ℝ≥0), |Mp X' A' i t ω| ≤ max C C₀ := fun ω i t => by
    rw [Mp_frozenStop hT0]
    exact (hTM ω _ i (min_le_right t (T ω))).trans (le_max_left _ _)
  have hM' : ∀ i, Martingale (Mp X' A' i) ℱ P := fun i => by
    have e : Mp X' A' i = stoppedProcess (Mp X A i) fun ω => (T ω : WithTop ℝ≥0) := by
      funext t ω
      rw [stoppedProcess_coe, Mp_frozenStop hT0]
    rw [e]; exact hMT i
  have hMM' : ∀ i j, Martingale (Np X' A' Q' i j) ℱ P := fun i j => by
    have e : Np X' A' Q' i j =
        stoppedProcess (Np X A Q i j) fun ω => (T ω : WithTop ℝ≥0) := by
      funext t ω
      rw [stoppedProcess_coe, Np_frozenStop hT0]
    rw [e]; exact hNT i j
  have key : Martingale (itoProc F X' A' Q') ℱ P :=
    martingale_ito_bounded ℱ X' A' Q' hX'p hX'c (isStronglyProgressive_stopSmul hT hA)
      (isStronglyProgressive_stopSmul hT hQ) (max C C₀)
      (Eventually.of_forall fun ω i t => intervalIntegrable_stopSmul_vec (hAint ω i t))
      (Eventually.of_forall fun ω i t =>
        (abs_integral_stopSmul_vec_le (hAC ω) i t).trans (le_max_right _ _))
      (Eventually.of_forall fun ω i j t => intervalIntegrable_stopSmul_matrix (hQint ω i j t))
      (Eventually.of_forall fun ω i j t =>
        (abs_integral_stopSmul_matrix_le (hQC ω) i j t).trans (le_max_right _ _))
      (Eventually.of_forall hMb) hM' hMM'
      (closure U ∪ {x₀}) hK D hD hKD (Eventually.of_forall hXK) F hFm hF
  have e : itoProc F X' A' Q' = stoppedProcess (itoProc F X A Q) fun ω => (T ω : WithTop ℝ≥0) := by
    funext t ω
    rw [stoppedProcess_coe, itoProc_frozenStop hT0]
  rw [← e]; exact key


open ComplexSLE.Infrastructure in
/-- **Itô's formula (martingale form) for data of everywhere bounded variation.** The same
conclusion as `ComplexSLE.External.ito_formula`, for densities `A`, `Q` that are interval integrable
with total variation bounded by `C₀` for *every* `ω` (so `Mⁱ`, `Nⁱʲ` have everywhere continuous
paths) and for paths that stay in `D` almost surely. -/
theorem isContLocalMartingale_itoProc_of_bounded_variation {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ≥0 m0} {d : ℕ} {X A : ℝ≥0 → Ω → (Fin d → ℝ)}
    {Q : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ}
    (hX : IsStronglyProgressive ℱ X) (hXc : ∀ ω, Continuous fun t => X t ω)
    (hA : IsStronglyProgressive ℱ A) (hQ : IsStronglyProgressive ℱ Q) {C₀ : ℝ}
    (hAint : ∀ ω (i : Fin d) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => A s.toNNReal ω i) volume 0 t)
    (hAC : ∀ ω (i : Fin d) (t : ℝ≥0), ∫ s in (0 : ℝ)..(t : ℝ), |A s.toNNReal ω i| ≤ C₀)
    (hQint : ∀ ω (i j : Fin d) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => Q s.toNNReal ω i j) volume 0 t)
    (hQC : ∀ ω (i j : Fin d) (t : ℝ≥0), ∫ s in (0 : ℝ)..(t : ℝ), |Q s.toNNReal ω i j| ≤ C₀)
    (hM : ∀ i, IsContLocalMartingale ℱ (Mp X A i) P)
    (hMM : ∀ i j, IsContLocalMartingale ℱ (Np X A Q i j) P)
    {D : Set (Fin d → ℝ)} (hD : IsOpen D) {F : (Fin d → ℝ) → ℝ} (hFm : Measurable F)
    (hF : ContDiffOn ℝ 2 F D) (hXD : ∀ᵐ ω ∂P, ∀ t, X t ω ∈ D) :
    IsContLocalMartingale ℱ (itoProc F X A Q) P := by
  -- a point of `D`
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ ∈ D := by
    obtain ⟨ω, hω⟩ := hXD.exists
    exact ⟨X 0 ω, hω 0⟩
  have hMc : ∀ i ω, Continuous fun t => Mp X A i t ω := fun i ω =>
    (((continuous_apply i).comp (hXc ω)).sub continuous_const).sub
      (continuous_pathIntegral (hAint ω i))
  -- the total size of the martingale parts, an everywhere continuous adapted process
  set R : ℝ≥0 → Ω → ℝ := fun t ω => ∑ i, |Mp X A i t ω| with hR
  have hRc : ∀ ω, Continuous fun t => R t ω := fun ω =>
    continuous_finsetSum _ fun i _ => continuous_abs.comp (hMc i ω)
  have hRad : StronglyAdapted ℱ R := fun t =>
    Finset.stronglyMeasurable_fun_sum _ fun i _ =>
      continuous_abs.comp_stronglyMeasurable ((hM i).1.stronglyAdapted t)
  have hR0 : ∀ ω, R 0 ω = 0 := fun ω => by
    simp [hR, Mp, pathIntegral_zero]
  set Tn : ℕ → Ω → ℝ≥0 := fun n ω => min (capExitTime R n ω) (exhaustionExitTime X D n ω) with hTn
  have hTst : ∀ n, IsStoppingTime ℱ fun ω => (Tn n ω : WithTop ℝ≥0) := fun n => by
    have := (isStoppingTime_capExitTime hRad hRc n).min
      (isStoppingTime_exhaustionExitTime hX.stronglyAdapted hXc D n)
    simpa only [hTn, WithTop.coe_min] using this
  have hmart : ∀ n, Martingale
      (stoppedProcess (itoProc F X A Q) fun ω => (Tn n ω : WithTop ℝ≥0)) ℱ P := fun n =>
    martingale_stopped_itoProc hX hXc hA hQ hAint hAC hQint hQC hM hMM hD hFm hF (hTst n)
      (isOpen_expU D n) ((closure_expU_subset D n).trans (expK_subset D n))
      ((isCompact_expK D n).of_isClosed_subset isClosed_closure (closure_expU_subset D n))
      (C := n)
      (fun ω u h0 hu => mem_closure_of_le_exhaustionExitTime hXc h0 (hu.trans (min_le_right _ _)))
      (fun ω h0 =>
        le_antisymm ((min_le_right _ _).trans (exhaustionExitTime_eq_zero h0).le) zero_le)
      (fun ω u i hu => by
        have h := abs_apply_le_max_of_le_capExitTime hRc n ω (hu.trans (min_le_left _ _))
        rw [hR0, abs_zero, max_eq_left (Nat.cast_nonneg n)] at h
        calc |Mp X A i u ω| ≤ R u ω :=
              Finset.single_le_sum (f := fun j => |Mp X A j u ω|) (fun j _ => abs_nonneg _)
                (Finset.mem_univ i)
          _ ≤ |R u ω| := le_abs_self _
          _ ≤ n := h)
      hx₀
  have hprog := isStronglyProgressive_itoProc hX hA hQ hFm
  have hcont : ∀ᵐ ω ∂P, Continuous fun t => itoProc F X A Q t ω := by
    filter_upwards [hXD] with ω hω
    exact continuous_itoProc hXc (hAint ω) (hQint ω) hD hF hω
  refine IsContLocalMartingale.of_stopped_seq hprog hcont
    (ρ := fun n ω => (Tn n ω : WithTop ℝ≥0)) hTst ?_ fun n => ?_
  · filter_upwards [hXD] with ω hω t
    obtain ⟨N₁, hN₁⟩ := exists_forall_le_capExitTime hRc ω t
    have hK : IsCompact ((fun s : ℝ≥0 => X s ω) '' Icc 0 t) := isCompact_Icc.image (hXc ω)
    have hKD : (fun s : ℝ≥0 => X s ω) '' Icc 0 t ⊆ D := by
      rintro _ ⟨s, -, rfl⟩
      exact hω s
    obtain ⟨N₂, hN₂⟩ := exists_expU_subset hD hK hKD
    rw [eventually_atTop]
    refine ⟨max (max N₁ N₂) ⌈t⌉₊, fun n hn => ?_⟩
    have hn1 : N₁ ≤ n := (le_max_left _ _ |>.trans (le_max_left _ _)).trans hn
    have hn2 : N₂ ≤ n := (le_max_right _ _ |>.trans (le_max_left _ _)).trans hn
    have hn3 : ⌈t⌉₊ ≤ n := (le_max_right _ _).trans hn
    have htn : t ≤ (n : ℝ≥0) := (Nat.le_ceil t).trans (by exact_mod_cast hn3)
    have h1 : t ≤ capExitTime R n ω := hN₁ n hn1
    have h2 : t ≤ exhaustionExitTime X D n ω := le_exhaustionExitTime htn fun u hu =>
      expU_mono D hn2 (hN₂ ⟨u, ⟨zero_le, hu⟩, rfl⟩)
    exact WithTop.coe_le_coe.2 (le_min h1 h2)
  · refine isContLocalMartingale_of_martingale (hmart n) (hprog.stoppedProcess (hTst n)) ?_
    filter_upwards [hcont] with ω h
    exact h.comp (continuous_untopA_min _)

end ComplexSLE.Infrastructure.Ito

end
