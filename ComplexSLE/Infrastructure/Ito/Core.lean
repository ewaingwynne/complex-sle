/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Ito.ZPart
public import ComplexSLE.Infrastructure.Ito.WPart
public import ComplexSLE.Infrastructure.Ito.RemPart

/-!
# The bounded core of Itô's formula for `C²` functions with compact support

`BoundedSetting.martingale_core`: under `BoundedSetting ℱ P X A Q C` (see `Setting.lean`), for every
`C²` function `F` with compact support,
`F(X_t) - F(X_0) - ∫₀ᵗ (∑ ∂ᵢF(X) Aⁱ + ½ ∑ ∂ᵢⱼF(X) Qⁱʲ)` is a martingale.

Route: fix `s ≤ t`, `B ∈ ℱ s`. Along the uniform partitions of `[s, t]`,
`F(X_t) - F(X_s) = zSum + wSum + remSum` (`partition_decomposition`). Then `∫_B zSum = 0`
(`ZPart.lean`: bounded predictable factors times martingale increments), `wSum → ∫ₛᵗ itoDrift`
pathwise and boundedly (`WPart.lean`, `Riemann.lean`), and `∫ |remSum| → 0` (`RemPart.lean`:
Taylor remainder `≤ ε_m ∑‖ΔX‖²` with `ε_m → 0` bounded and `∑‖ΔX‖²` bounded in `L²`). Hence
`E[1_B (F(X_t) - F(X_s))] = E[1_B ∫ₛᵗ itoDrift]` (`BoundedSetting.setIntegral_increment_eq`).
-/

@[expose] public section

open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Infrastructure.Ito

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {n : ℕ} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m0}
  {X A : ℝ≥0 → Ω → (Fin n → ℝ)} {Q : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ} {C : ℝ}
  {F : (Fin n → ℝ) → ℝ}

/-- The drift integrand of Itô's formula is progressive when `∂ᵢF`, `∂ᵢⱼF` are measurable. -/
theorem isStronglyProgressive_itoDrift (hX : IsStronglyProgressive ℱ X)
    (hA : IsStronglyProgressive ℱ A) (hQ : IsStronglyProgressive ℱ Q)
    (hg : ∀ i, Measurable (gF F i)) (hH : ∀ i j, Measurable (HF F i j)) :
    IsStronglyProgressive ℱ (itoDrift F X A Q) := by
  unfold itoDrift
  refine (IsStronglyProgressive.finsetSum fun i _ => ?_).add
    ((isStronglyProgressive_const ℱ (1 / 2 : ℝ)).mul
      (IsStronglyProgressive.finsetSum fun i _ => IsStronglyProgressive.finsetSum fun j _ => ?_))
  · exact (isStronglyProgressive_comp_measurable hX (hg i)).mul (isStronglyProgressive_apply hA i)
  · exact (isStronglyProgressive_comp_measurable hX (hH i j)).mul
      (isStronglyProgressive_matrix_apply hQ i j)

theorem intervalIntegrable_itoDrift (hF : ContDiff ℝ 2 F) (hX : ∀ ω, Continuous fun t => X t ω)
    {ω : Ω}
    (hA : ∀ i (t : ℝ≥0), IntervalIntegrable (fun s : ℝ => A s.toNNReal ω i) volume 0 t)
    (hQ : ∀ i j (t : ℝ≥0), IntervalIntegrable (fun s : ℝ => Q s.toNNReal ω i j) volume 0 t)
    (t : ℝ≥0) :
    IntervalIntegrable (fun x : ℝ => itoDrift F X A Q x.toNNReal ω) volume 0 t := by
  have hcX : Continuous fun u : ℝ => X u.toNNReal ω := (hX ω).comp continuous_real_toNNReal
  unfold itoDrift
  have h1 : ∀ i, IntervalIntegrable (fun x : ℝ => gF F i (X x.toNNReal ω) * A x.toNNReal ω i)
      volume 0 t := fun i =>
    (hA i t).continuousOn_mul ((continuous_gF hF i).comp hcX).continuousOn
  have h2 : ∀ i j, IntervalIntegrable
      (fun x : ℝ => HF F i j (X x.toNNReal ω) * Q x.toNNReal ω i j) volume 0 t := fun i j =>
    (hQ i j t).continuousOn_mul ((continuous_HF hF i j).comp hcX).continuousOn
  exact (intervalIntegrable_sum' Finset.univ fun i _ => h1 i).add
    ((intervalIntegrable_sum' Finset.univ fun i _ =>
      intervalIntegrable_sum' Finset.univ fun j _ => h2 i j).const_mul _)

/-- The drift path integrals are a.s. bounded. -/
theorem BoundedSetting.abs_pathIntegral_itoDrift_le (h : BoundedSetting ℱ P X A Q C)
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) :
    ∃ b : ℝ, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, |pathIntegral (itoDrift F X A Q) t ω| ≤ b := by
  obtain ⟨-, L₁, L₂, -, hL₁, hL₂, -⟩ := exists_bounds hF hFc
  refine ⟨∑ _i : Fin n, L₁ * C + (1 / 2) * ∑ _i : Fin n, ∑ _j : Fin n,
    L₂ * (C + (C + C) * C + (C + C) * C + C * C), ?_⟩
  filter_upwards [h.int_A, h.int_Q, h.abs_A, h.abs_Q, h.bd_M] with ω hA hQ hAC hQC hM t
  have hlim := tendsto_wSum_of_paths hF h.cont_X hA hQ (by simp : (0 : ℝ≥0) ≤ t)
  have hb := fun m => abs_wSum_le_of_paths (X := X) (F := F) hL₁ hL₂ hA hQ hAC hQC hM
    (by simp : (0 : ℝ≥0) ≤ t) m
  have := le_of_tendsto' ((continuous_abs.tendsto _).comp hlim) hb
  simpa [pathIntegral] using this

/-- **The mean of the increment of `F ∘ X` on `B ∈ ℱ s` equals that of its drift integral.** -/
theorem BoundedSetting.setIntegral_increment_eq [IsProbabilityMeasure P]
    (h : BoundedSetting ℱ P X A Q C) (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    {s t : ℝ≥0} (hst : s ≤ t) {B : Set Ω} (hB : MeasurableSet[ℱ s] B) :
    ∫ ω in B, (F (X t ω) - F (X s ω)) ∂P =
      ∫ ω in B, (pathIntegral (itoDrift F X A Q) t ω - pathIntegral (itoDrift F X A Q) s ω) ∂P := by
  obtain ⟨L₀, L₁, L₂, hL₀, hL₁, hL₂, hB₂⟩ := exists_bounds hF hFc
  have hXm : ∀ u, Measurable (X u) := h.measurable_X
  have hFm : Measurable F := hF.continuous.measurable
  have hBm : MeasurableSet B := ℱ.le s _ hB
  -- the increment is a.s. bounded
  have hDb : AEBdd P (fun ω => F (X t ω) - F (X s ω)) := by
    refine ⟨((hFm.comp (hXm t)).sub (hFm.comp (hXm s))).aestronglyMeasurable, L₀ + L₀,
      Filter.Eventually.of_forall fun ω => (abs_sub _ _).trans (add_le_add (hL₀ _) (hL₀ _))⟩
  have hZb := fun m => (h.nullOn_zSum hF hFc hst m hB).1
  have hRb := fun m => h.aebdd_remSum hF hFc hst m
  -- the drift sums
  obtain ⟨b, hb⟩ : ∃ b : ℝ, ∀ᵐ ω ∂P, ∀ m, |wSum F X A Q s t m ω| ≤ b := by
    refine ⟨∑ _i : Fin n, L₁ * C + (1 / 2) * ∑ _i : Fin n, ∑ _j : Fin n,
      L₂ * (C + (C + C) * C + (C + C) * C + C * C), ?_⟩
    filter_upwards [h.int_A, h.int_Q, h.abs_A, h.abs_Q, h.bd_M] with ω hA hQ hAC hQC hM m
    exact abs_wSum_le_of_paths (X := X) (F := F) hL₁ hL₂ hA hQ hAC hQC hM hst m
  have hdec : ∀ m, ∀ᵐ ω ∂P, F (X t ω) - F (X s ω) =
      zSum F X A Q s t m ω + wSum F X A Q s t m ω + remSum F X s t m ω := fun m => by
    filter_upwards [h.int_A, h.int_Q] with ω hA hQ
    exact partition_decomposition hA hQ m
  have hWae : ∀ m, wSum F X A Q s t m =ᵐ[P] fun ω => (F (X t ω) - F (X s ω)) -
      zSum F X A Q s t m ω - remSum F X s t m ω := fun m => by
    filter_upwards [hdec m] with ω hω
    rw [hω]; ring
  have hWb : ∀ m, AEBdd P (wSum F X A Q s t m) := fun m => by
    have := (hDb.sub (hZb m)).sub (hRb m)
    refine ⟨?_, ?_⟩
    · exact this.1.congr (hWae m).symm
    · obtain ⟨-, c, hc⟩ := this
      refine ⟨c, ?_⟩
      filter_upwards [hWae m, hc] with ω h1 h2
      rw [h1]; exact h2
  -- integrals over `B`
  have hint : ∀ m, ∫ ω in B, wSum F X A Q s t m ω ∂P =
      ∫ ω in B, (F (X t ω) - F (X s ω)) ∂P - ∫ ω in B, remSum F X s t m ω ∂P := by
    intro m
    rw [setIntegral_congr_ae hBm (by
      filter_upwards [hWae m] with ω hω _ using hω)]
    rw [integral_sub (hDb.sub (hZb m)).integrable.integrableOn (hRb m).integrable.integrableOn,
      integral_sub hDb.integrable.integrableOn (hZb m).integrable.integrableOn,
      h.setIntegral_zSum_eq_zero hF hFc hst m hB]
    ring
  -- limit of the drift sums
  set I' : Ω → ℝ := fun ω => ∫ u in (s : ℝ)..(t : ℝ), itoDrift F X A Q u.toNNReal ω with hI'
  have hlim : Tendsto (fun m => ∫ ω in B, wSum F X A Q s t m ω ∂P) atTop
      (𝓝 (∫ ω in B, I' ω ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (μ := P.restrict B) (fun _ => b)
      (fun m => (hWb m).1.restrict) (integrable_const _)
      (fun m => ae_restrict_of_ae (by
        filter_upwards [hb] with ω hω using by simpa [Real.norm_eq_abs] using hω m))
      (ae_restrict_of_ae ?_)
    filter_upwards [h.int_A, h.int_Q] with ω hA hQ
    exact tendsto_wSum_of_paths hF h.cont_X hA hQ hst
  have hI'eq : ∀ᵐ ω ∂P, I' ω = pathIntegral (itoDrift F X A Q) t ω -
      pathIntegral (itoDrift F X A Q) s ω := by
    filter_upwards [h.int_A, h.int_Q] with ω hA hQ
    exact (pathIntegral_sub_eq (intervalIntegrable_itoDrift hF h.cont_X hA hQ) s t).symm
  -- the remainders
  have hRlim : Tendsto (fun m => ∫ ω in B, remSum F X s t m ω ∂P) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun m => ?_) (h.tendsto_integral_abs_remSum hF hFc hst)
    rw [Real.norm_eq_abs]
    exact (abs_integral_le_integral_abs).trans
      (setIntegral_le_integral (hRb m).abs.integrable
        (Filter.Eventually.of_forall fun ω => abs_nonneg _))
  have h2 : Tendsto (fun m => ∫ ω in B, wSum F X A Q s t m ω ∂P) atTop
      (𝓝 (∫ ω in B, (F (X t ω) - F (X s ω)) ∂P)) := by
    simp only [hint]
    simpa using (tendsto_const_nhds (x := ∫ ω in B, (F (X t ω) - F (X s ω)) ∂P)).sub hRlim
  rw [tendsto_nhds_unique h2 hlim]
  exact setIntegral_congr_ae hBm (by filter_upwards [hI'eq] with ω hω _ using hω)

/-- **The bounded core of Itô's formula, for `F` of class `C²` with compact support.** -/
theorem BoundedSetting.martingale_core [IsProbabilityMeasure P]
    (h : BoundedSetting ℱ P X A Q C) (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) :
    Martingale (fun t ω => F (X t ω) - F (X 0 ω) - pathIntegral (itoDrift F X A Q) t ω) ℱ P := by
  obtain ⟨L₀, -, -, hL₀, -, -, -⟩ := exists_bounds hF hFc
  obtain ⟨b, hb⟩ := h.abs_pathIntegral_itoDrift_le hF hFc
  have hFm : Measurable F := hF.continuous.measurable
  have hGp : IsStronglyProgressive ℱ (itoDrift F X A Q) :=
    isStronglyProgressive_itoDrift h.prog_X h.prog_A h.prog_Q
      (fun i => (continuous_gF hF i).measurable) (fun i j => (continuous_HF hF i j).measurable)
  have hFXp : IsStronglyProgressive ℱ fun t ω => F (X t ω) :=
    isStronglyProgressive_comp_measurable h.prog_X hFm
  have hPIp := isStronglyProgressive_pathIntegral hGp
  have hadapt : StronglyAdapted ℱ
      (fun t ω => F (X t ω) - F (X 0 ω) - pathIntegral (itoDrift F X A Q) t ω) := fun t =>
    ((hFXp.stronglyAdapted t).sub
      ((hFXp.stronglyAdapted 0).mono (ℱ.mono (by simp : (0 : ℝ≥0) ≤ t)))).sub
      (hPIp.stronglyAdapted t)
  have hint : ∀ t, Integrable
      (fun ω => F (X t ω) - F (X 0 ω) - pathIntegral (itoDrift F X A Q) t ω) P := by
    intro t
    refine AEBdd.integrable ⟨((hadapt t).mono (ℱ.le t)).aestronglyMeasurable, (L₀ + L₀) + b, ?_⟩
    filter_upwards [hb] with ω hω
    exact (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add (hL₀ _) (hL₀ _)))
      (hω t))
  refine ⟨hadapt, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) (hint t)
    (fun B _ _ => (hint s).integrableOn) (fun B hB _ => ?_)
    (hadapt s).aestronglyMeasurable).symm
  have hinc := h.setIntegral_increment_eq hF hFc hst hB
  have hBm : MeasurableSet B := ℱ.le s _ hB
  have hDb : AEBdd P (fun ω => F (X t ω) - F (X s ω)) :=
    ⟨((hFm.comp (h.measurable_X t)).sub (hFm.comp (h.measurable_X s))).aestronglyMeasurable,
      L₀ + L₀, Filter.Eventually.of_forall fun ω =>
        (abs_sub _ _).trans (add_le_add (hL₀ _) (hL₀ _))⟩
  have hPI : ∀ u, AEBdd P (pathIntegral (itoDrift F X A Q) u) := fun u =>
    ⟨((hPIp.stronglyAdapted u).mono (ℱ.le u)).aestronglyMeasurable, b, by
      filter_upwards [hb] with ω hω using hω u⟩
  have hFb : ∀ u, AEBdd P (fun ω => F (X u ω)) := fun u =>
    ⟨(hFm.comp (h.measurable_X u)).aestronglyMeasurable, L₀,
      Filter.Eventually.of_forall fun ω => hL₀ _⟩
  have e1 : ∫ ω in B, (F (X t ω) - F (X 0 ω) - pathIntegral (itoDrift F X A Q) t ω) ∂P -
      ∫ ω in B, (F (X s ω) - F (X 0 ω) - pathIntegral (itoDrift F X A Q) s ω) ∂P =
      ∫ ω in B, (F (X t ω) - F (X s ω)) ∂P -
        ∫ ω in B, (pathIntegral (itoDrift F X A Q) t ω -
          pathIntegral (itoDrift F X A Q) s ω) ∂P := by
    rw [← integral_sub (hint t).integrableOn (hint s).integrableOn,
      ← integral_sub hDb.integrable.integrableOn
        ((hPI t).sub (hPI s)).integrable.integrableOn]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    ring
  rw [hinc, sub_self] at e1
  linarith

end ComplexSLE.Infrastructure.Ito

end
