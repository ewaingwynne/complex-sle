/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.RightHull
public import ComplexSLE.Internal.Hull.LocalExistence

/-!
# The duality property (2.4), right hull form

Time reversal of the Loewner equation (paper.tex:L566-570). If `γ` solves `γ' = 2/(γ - U)` on
`[0, t]` and `k(s) = i (γ(t - s) - U_t)`, then `k' = 2/(k - V)` on `[0, t]` with
`V(s) = i (U(t - s) - U_t)`. Consequently `w ∈ range f_t^U ↔ i w ∉ L_t^V`, i.e.
`R_t^U = (-i) L_t^V` (`rightHull_eq_image_leftHull_revDriver`); since `L^{-V} = -L^V`
this is the printed form `R_t^U = i L_t^{i (U(t) - U(t - ·))}` of (2.4), with no sign
discrepancy.
-/

public section

open scoped NNReal ENNReal
open Set Filter Topology

namespace ComplexSLE.Internal

/-- A solution of the Loewner equation with real-time driver `W` on the closed interval `[0, t]`. -/
def ClosedSol (W : ℝ → ℂ) (t : ℝ) (γ : ℝ → ℂ) : Prop :=
  ∀ s ∈ Icc 0 t, γ s ≠ W s ∧ HasDerivWithinAt γ (2 / (γ s - W s)) (Icc 0 t) s

/-- The reversed driver `V(s) = i (U(t - s) - U_t)` (constant for `s ≥ t`). -/
noncomputable def revDriver (U : ℝ≥0 → ℂ) (t : ℝ≥0) : ℝ≥0 → ℂ :=
  fun s => Complex.I * (U (Real.toNNReal ((t : ℝ) - s)) - U t)

theorem continuous_revDriver {U : ℝ≥0 → ℂ} (hU : Continuous U) (t : ℝ≥0) :
    Continuous (revDriver U t) := by
  unfold revDriver
  have h : Continuous fun s : ℝ≥0 => Real.toNNReal ((t : ℝ) - s) :=
    continuous_real_toNNReal.comp (continuous_const.sub NNReal.continuous_coe)
  exact continuous_const.mul ((hU.comp h).sub continuous_const)

/-- Time reversal of a closed-interval solution. -/
theorem closedSol_reverse {W W' : ℝ → ℂ} {t : ℝ} {γ : ℝ → ℂ} {a c : ℂ} (ha : a * a = -1)
    (hγ : ClosedSol W t γ) (hW' : ∀ s ∈ Icc 0 t, W' s = a * (W (t - s) - c)) :
    ClosedSol W' t (fun s => a * (γ (t - s) - c)) := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  intro s hs
  have hs' : t - s ∈ Icc 0 t := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  obtain ⟨hne, hder⟩ := hγ (t - s) hs'
  have hh : HasDerivWithinAt (fun s : ℝ => t - s) (-1) (Icc 0 t) s := by
    simpa using (hasDerivWithinAt_id s (Icc 0 t)).const_sub t
  have hmaps : MapsTo (fun s : ℝ => t - s) (Icc 0 t) (Icc 0 t) :=
    fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hcomp := ((hder.scomp s hh hmaps).sub_const c).const_mul a
  have hsub : γ (t - s) - W (t - s) ≠ 0 := sub_ne_zero.2 hne
  have key : a * (γ (t - s) - c) - W' s = a * (γ (t - s) - W (t - s)) := by
    rw [hW' s hs]; ring
  refine ⟨?_, ?_⟩
  · intro h
    rw [← sub_eq_zero, key] at h
    exact hsub ((mul_eq_zero.1 h).resolve_left ha0)
  · rw [key]
    refine HasDerivWithinAt.congr_deriv hcomp ?_
    rw [neg_one_smul]
    field_simp
    linear_combination -ha

variable {U : ℝ≥0 → ℂ}

theorem closedSol_of_isLoewnerSolution {z : ℂ} {τ : ℝ≥0∞} {γ : ℝ → ℂ}
    (h : IsLoewnerSolution U z τ γ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ) :
    ClosedSol (fun s => U s.toNNReal) t γ := by
  intro s hs
  have hlt : ENNReal.ofReal s < τ :=
    lt_of_le_of_lt (by rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal hs.2) ht
  obtain ⟨h1, h2⟩ := h.2 s hs.1 hlt
  exact ⟨h1, h2.mono Icc_subset_Ici_self⟩

theorem isLoewnerSolution_of_closedSol {t : ℝ≥0} (ht : (0 : ℝ) < t) {z : ℂ} {γ : ℝ → ℂ}
    (h0 : γ 0 = z) (h : ClosedSol (fun s => U s.toNNReal) t γ) :
    IsLoewnerSolution U z (ENNReal.ofReal t) γ := by
  refine ⟨h0, fun s hs hsτ => ?_⟩
  rw [ENNReal.ofReal_lt_ofReal_iff ht] at hsτ
  obtain ⟨h1, h2⟩ := h s ⟨hs, hsτ.le⟩
  refine ⟨h1, h2.mono_of_mem_nhdsWithin ?_⟩
  exact mem_nhdsWithin.2 ⟨Iio t, isOpen_Iio, hsτ, fun x hx => ⟨hx.2, hx.1.le⟩⟩

theorem lt_absorbingTime_of_closedSol (hU : Continuous U) {t : ℝ≥0} {z : ℂ} {γ : ℝ → ℂ}
    (h0 : γ 0 = z) (h : ClosedSol (fun s => U s.toNNReal) t γ) :
    (t : ℝ≥0∞) < absorbingTime U z := by
  rcases eq_or_ne t 0 with rfl | ht
  · refine absorbingTime_pos_of_ne hU ?_
    have := (h 0 ⟨le_rfl, by simp⟩).1
    simpa [h0] using this
  have htpos : (0 : ℝ) < t := by exact_mod_cast pos_iff_ne_zero.2 ht
  have hsol := isLoewnerSolution_of_closedSol htpos h0 h
  have hVc : Continuous fun s : ℝ => U s.toNNReal := hU.comp continuous_real_toNNReal
  have hγc : ContinuousOn γ (Icc 0 (t : ℝ)) := fun s hs => (h s hs).2.continuousWithinAt
  obtain ⟨δ, hδ, hb⟩ := exists_pos_le_norm_Icc htpos.le (hγc.sub hVc.continuousOn)
    (fun s hs => sub_ne_zero.2 (h s hs).1)
  have := lt_absorbingTime_of_norm_sub_ge hU htpos hsol htpos hδ
    (fun s hs => hb s ⟨hs.1, hs.2.le⟩)
  rwa [ENNReal.ofReal_coe_nnreal] at this

/-- Two closed-interval solutions from the same point agree at the endpoint. -/
theorem closedSol_eq_endpoint (hU : Continuous U) {t : ℝ≥0} {z : ℂ} {γ₁ γ₂ : ℝ → ℂ}
    (h₁ : γ₁ 0 = z) (h₂ : γ₂ 0 = z) (hs₁ : ClosedSol (fun s => U s.toNNReal) t γ₁)
    (hs₂ : ClosedSol (fun s => U s.toNNReal) t γ₂) : γ₁ t = γ₂ t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [h₁, h₂]
  have htpos : (0 : ℝ) < t := by exact_mod_cast pos_iff_ne_zero.2 ht
  have heq := (loewner_wellDefined U hU z).2 _ γ₁ γ₂ (isLoewnerSolution_of_closedSol htpos h₁ hs₁)
    (isLoewnerSolution_of_closedSol htpos h₂ hs₂)
  have hc₁ : ContinuousWithinAt γ₁ (Ico 0 (t : ℝ)) t :=
    (hs₁ t ⟨htpos.le, le_rfl⟩).2.continuousWithinAt.mono Ico_subset_Icc_self
  have hc₂ : ContinuousWithinAt γ₂ (Ico 0 (t : ℝ)) t :=
    (hs₂ t ⟨htpos.le, le_rfl⟩).2.continuousWithinAt.mono Ico_subset_Icc_self
  have : (𝓝[Ico 0 (t : ℝ)] (t : ℝ)).NeBot :=
    Filter.NeBot.mono (inferInstance : (𝓝[<] (t : ℝ)).NeBot)
      (nhdsWithin_le_of_mem (Ico_mem_nhdsLT htpos))
  exact tendsto_nhds_unique_of_eventuallyEq hc₁ hc₂ (Filter.eventually_of_mem
    self_mem_nhdsWithin (fun s hs => heq ⟨hs.1, (ENNReal.ofReal_lt_ofReal_iff htpos).2 hs.2⟩))

theorem revDriver_toNNReal (U : ℝ≥0 → ℂ) (t : ℝ≥0) {s : ℝ} (hs : s ∈ Icc 0 (t : ℝ)) :
    revDriver U t s.toNNReal = Complex.I * (U (Real.toNNReal ((t : ℝ) - s)) - U t) := by
  unfold revDriver
  rw [Real.coe_toNNReal s hs.1]

/-- Duality for the centered Loewner map: `w ∈ range f_t^U ↔ t < T^V_{i w}`, where `V` is the
reversed driver. -/
theorem mem_range_centeredLoewnerMap_iff (hU : Continuous U) (t : ℝ≥0) (w : ℂ) :
    w ∈ Set.range (centeredLoewnerMap U hU t) ↔
      (t : ℝ≥0∞) < absorbingTime (revDriver U t) (Complex.I * w) := by
  have hV := continuous_revDriver hU t
  have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨γ, hγ, hmap⟩ := loewnerMap_exists_solution U hU z.1
    have ht : (t : ℝ≥0∞) < absorbingTime U z := notMem_leftHull_iff.1 z.2
    have hsol := closedSol_of_isLoewnerSolution hγ ht
    have hrev := closedSol_reverse (W' := fun s => revDriver U t s.toNNReal) (a := Complex.I)
      (c := U t) hII hsol (fun s hs => by
        rw [revDriver_toNNReal U t hs, Real.toNNReal_of_nonneg (by linarith [hs.2])])
    refine lt_absorbingTime_of_closedSol hV ?_ hrev
    have := hmap t z.2
    simp only [sub_zero, centeredLoewnerMap]
    rw [show loewnerMap U hU t z = γ t from this]
  · intro ht
    obtain ⟨k, hk⟩ := (loewner_wellDefined (revDriver U t) hV (Complex.I * w)).1
    have hsol := closedSol_of_isLoewnerSolution hk ht
    have hrev := closedSol_reverse (W' := fun s => U s.toNNReal) (a := -Complex.I)
      (c := -Complex.I * U t) (by linear_combination hII) hsol (fun s hs => by
        have hs' : (t : ℝ) - s ∈ Icc 0 (t : ℝ) := ⟨by linarith [hs.2], by linarith [hs.1]⟩
        rw [revDriver_toNNReal U t hs', show (t : ℝ) - ((t : ℝ) - s) = s by ring]
        ring_nf
        rw [Complex.I_sq]
        simp [Real.toNNReal_of_nonneg hs.1])
    have hlt := lt_absorbingTime_of_closedSol hU (z := _) rfl hrev
    have hz : _ ∈ (leftHull U t)ᶜ := notMem_leftHull_iff.2 hlt
    refine ⟨⟨_, hz⟩, ?_⟩
    obtain ⟨γ'', hγ'', hmap⟩ := loewnerMap_exists_solution U hU _
    have hs2 := closedSol_of_isLoewnerSolution hγ'' hlt
    have hend := closedSol_eq_endpoint hU rfl hγ''.1 hrev hs2
    simp only [centeredLoewnerMap]
    rw [hmap t hz, ← hend]
    have hk0 : k 0 = Complex.I * w := hk.1
    rw [sub_self, hk0]
    linear_combination (-(w + U t)) * hII

/-- **Duality (2.4), right hull form**: `R_t^U = (-i) L_t^V` for the reversed driver
`V(s) = i (U(t - s) - U_t)`. -/
theorem rightHull_eq_image_leftHull_revDriver (hU : Continuous U) (t : ℝ≥0) :
    rightHull U hU t = (fun u => -Complex.I * u) '' leftHull (revDriver U t) t := by
  ext w
  rw [rightHull, mem_compl_iff, mem_range_centeredLoewnerMap_iff hU t w,
    notMem_leftHull_iff.symm.not, not_not]
  constructor
  · intro h
    exact ⟨Complex.I * w, h, by
      change -Complex.I * (Complex.I * w) = w
      rw [← mul_assoc, show -Complex.I * Complex.I = 1 by simp, one_mul]⟩
  · rintro ⟨u, hu, rfl⟩
    rwa [← mul_assoc, show Complex.I * -Complex.I = 1 by simp, one_mul]

end ComplexSLE.Internal

end
