/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.PathStatCanon
public import ComplexSLE.Internal.Phases.AllZMarkov

/-!
# The strong Markov step in integral form (M7/A4c)

For an adapted `SLE_Σ` driver `U`, an a.s. finite `ℱ`-stopping time `τ`, the post-`τ` driver
`V = postDriver U τ` is an `SLE_Σ` driver independent of `ℱ_τ` (EXTERNAL `strongMarkov_sleDriver`).
Let `X = (ρ, β) : Ω → ℝ≥0 × ℝ` be `ℱ_τ`-measurable with `ρ > 0` a.s. (the restart scale and a
real-valued state). Then the rescaled post-`τ` path `CPath.scale ρ⁻¹ (postPath hU τ)` is, jointly
with `β`, distributed as `Λ ⊗ law β`, where `Λ = P.map (CPath.ofDriver U _)` is the law of the
driver `U` itself on `CPath`:

* `lintegral_comp_scale_postPath`: for every measurable `F : CPath × ℝ → ℝ≥0∞`,
  `E F(ρ⁻¹-scaled post-τ path, β) = E ∫ F(w, β) dΛ(w)`.

Proof: independence of `postPath` and `X` gives the product law; scaling by a fixed `r > 0`
preserves `Λ` (`map_scale_eq`, Brownian scaling and uniqueness of the path law); Fubini.

Uses the EXTERNAL `strongMarkov_sleDriver`.
-/

@[expose] public section

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Internal

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- The post-`τ` driver as a random element of `CPath`. -/
noncomputable def postPath (hU : IsSLEDriverAdapted a b c U P ℱ) (τ : Ω → WithTop ℝ≥0) :
    Ω → CPath :=
  CPath.ofDriver (postDriver U τ) (continuous_postDriver hU τ)

theorem measurable_postPath (hU : IsSLEDriverAdapted a b c U P ℱ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime ℱ τ) : Measurable (postPath hU τ) :=
  CPath.measurable_ofDriver (continuous_postDriver hU τ) (measurable_postDriver hU hτ)

/-- **The strong Markov step with a random `ℱ_τ`-measurable rescaling** (integral form). -/
theorem lintegral_comp_scale_postPath (hU : IsSLEDriverAdapted a b c U P ℱ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤)
    {X : Ω → ℝ≥0 × ℝ} (hX : Measurable[hτ.measurableSpace] X) (hρ : ∀ᵐ ω ∂P, 0 < (X ω).1)
    {F : CPath × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (CPath.scale (X ω).1⁻¹ (postPath hU τ ω), (X ω).2) ∂P =
      ∫⁻ ω, ∫⁻ w, F (w, (X ω).2) ∂(P.map (CPath.ofDriver U hU.cont)) ∂P := by
  have : IsProbabilityMeasure P := hU.toIsSLEDriver.isProbabilityMeasure
  obtain ⟨hVd, hind, -⟩ := External.strongMarkov_sleDriver hU τ hτ hfin
  have hUm : ∀ t, Measurable (U t) := fun t => hU.adapted.measurable
  have hVm : ∀ s, Measurable (postDriver U τ s) := measurable_postDriver hU hτ
  have hW : Measurable (postPath hU τ) := measurable_postPath hU hτ
  have hXm : Measurable X := hX.mono hτ.measurableSpace_le le_rfl
  -- the law of the post-`τ` path is the law of the driver
  have hlawW : P.map (postPath hU τ) = P.map (CPath.ofDriver U hU.cont) :=
    map_ofDriver_eq hVd hU.toIsSLEDriver (continuous_postDriver hU τ) hU.cont hVm hUm
  -- independence of the post-`τ` path and `X`
  have hindep : IndepFun (postPath hU τ) X P := by
    have e : MeasurableSpace.comap (postPath hU τ) inferInstance =
        ⨆ s : ℝ≥0, MeasurableSpace.comap
          (fun ω => U ((τ ω).untopA + s) ω - U (τ ω).untopA ω) inferInstance := by
      change MeasurableSpace.comap (postPath hU τ)
        (MeasurableSpace.comap Subtype.val MeasurableSpace.pi) = _
      rw [MeasurableSpace.comap_comp, MeasurableSpace.pi, MeasurableSpace.comap_iSup]
      refine iSup_congr fun s => ?_
      rw [MeasurableSpace.comap_comp]
      rfl
    have hXle : MeasurableSpace.comap X inferInstance ≤ hτ.measurableSpace :=
      hX.comap_le
    exact indep_of_indep_of_le_right (e ▸ hind) hXle
  have hjoint : P.map (fun ω => (postPath hU τ ω, X ω)) =
      (P.map (CPath.ofDriver U hU.cont)).prod (P.map X) := by
    have := (indepFun_iff_map_prod_eq_prod_map_map hW.aemeasurable hXm.aemeasurable).1 hindep
    rwa [hlawW] at this
  have hFm : Measurable fun p : CPath × (ℝ≥0 × ℝ) => F (CPath.scale p.2.1⁻¹ p.1, p.2.2) :=
    hF.comp ((CPath.measurable_scale.comp
      ((measurable_fst.comp measurable_snd).inv.prodMk measurable_fst)).prodMk
      (measurable_snd.comp measurable_snd))
  have hGm : Measurable fun x : ℝ≥0 × ℝ =>
      ∫⁻ w, F (w, x.2) ∂(P.map (CPath.ofDriver U hU.cont)) :=
    Measurable.lintegral_prod_left' (f := fun p : CPath × (ℝ≥0 × ℝ) => F (p.1, p.2.2))
      (hF.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  calc ∫⁻ ω, F (CPath.scale (X ω).1⁻¹ (postPath hU τ ω), (X ω).2) ∂P
      = ∫⁻ p, F (CPath.scale p.2.1⁻¹ p.1, p.2.2)
          ∂(P.map fun ω => (postPath hU τ ω, X ω)) := by
        rw [lintegral_map hFm (hW.prodMk hXm)]
    _ = ∫⁻ p, F (CPath.scale p.2.1⁻¹ p.1, p.2.2)
          ∂((P.map (CPath.ofDriver U hU.cont)).prod (P.map X)) := by rw [hjoint]
    _ = ∫⁻ x, ∫⁻ w, F (CPath.scale x.1⁻¹ w, x.2) ∂(P.map (CPath.ofDriver U hU.cont))
          ∂(P.map X) := lintegral_prod_symm _ hFm.aemeasurable
    _ = ∫⁻ x, ∫⁻ w, F (w, x.2) ∂(P.map (CPath.ofDriver U hU.cont)) ∂(P.map X) := by
        refine lintegral_congr_ae ?_
        have hpos : ∀ᵐ x ∂(P.map X), 0 < x.1 :=
          (ae_map_iff hXm.aemeasurable (measurableSet_lt measurable_const measurable_fst)).2 hρ
        filter_upwards [hpos] with x hx
        have hr : 0 < x.1⁻¹ := inv_pos.2 hx
        have hsc := map_scale_eq hU.toIsSLEDriver hU.cont hUm hr
        calc ∫⁻ w, F (CPath.scale x.1⁻¹ w, x.2) ∂(P.map (CPath.ofDriver U hU.cont))
            = ∫⁻ w', F (w', x.2)
                ∂((P.map (CPath.ofDriver U hU.cont)).map (CPath.scale x.1⁻¹)) :=
              (lintegral_map (hF.comp (measurable_id.prodMk measurable_const))
                (CPath.measurable_scale_const _)).symm
          _ = ∫⁻ w, F (w, x.2) ∂(P.map (CPath.ofDriver U hU.cont)) := by rw [hsc]
    _ = ∫⁻ ω, ∫⁻ w, F (w, (X ω).2) ∂(P.map (CPath.ofDriver U hU.cont)) ∂P := by
        rw [lintegral_map hGm hXm]

end ComplexSLE.Internal

end
