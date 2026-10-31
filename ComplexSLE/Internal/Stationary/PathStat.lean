/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.PathStatRestart
public import ComplexSLE.Internal.Stationary.SLEStat
public import ComplexSLE.Internal.Phases.AllZLebesgue

/-!
# Path-level stationarity of the polar data started at `𝐳` (M7/A4c)

Let `a, b > 0`, `c² ≤ ab`, `hU : IsSLEDriverAdapted a b c U P ℱ`, `p` an admissible density and
`ν = p(u) 1_{[0,2π]}(u) du` (`admissibleMeasure p = admissibleLaw p`). On `(Ω × ℝ, P ⊗ ν)` with the
random point `𝐳 = e^{iu}` let (`pathObs`, in `PathStatRestart.lean`)

  `Ξ_s(ω, u) = (e^{2iθ̂_s(𝐳)}, (θ̂_{s+r}(𝐳) - θ̂_s(𝐳))_{r ≥ 0},
    (log |f̂_{s+r}(𝐳)| - log |f̂_s(𝐳)|)_{r ≥ 0})`

as a measurable map into `ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)` (product σ-algebras). The statement proved is
the equality of **laws of the whole path observable**, for every `s ≥ 0`:

* `map_pathObs_eq_canonical`: `(P ⊗ ν).map Ξ_s = (Λ ⊗ ν).map obsC`, where `Λ = driverLaw hU` is
  the law of the driver on `CPath` and `obsC (w, u)` is the observable of the chain driven by the
  path `w` started at `e^{iu}`; in particular the right side does not depend on `s`;
* `map_pathObs_eq_zero`: `(P ⊗ ν).map Ξ_s = (P ⊗ ν).map Ξ_0` (this is the law of `Ξ_0 =
  (e^{2iu}, (θ̂_r - θ̂_0)_r, (log |f̂_r|)_r)`, as `θ̂_0 = u mod 2π`, `|f̂_0| = 1`).

**mod π versus mod 2π.** The one-time stationarity available (`SLEStat.lean`, A4a) concerns
`θ̂_s mod π`, equivalently `e^{2iθ̂_s}`; the law of `θ̂_s mod 2π` is not available. This is why
the observable records `e^{2iθ̂_s}` and not `e^{iθ̂_s}`. It suffices: conditionally on `ℱ_{σ_z(s)}`
the rescaled post-`σ_z(s)` driver is an `SLE_Σ` driver independent of the state
(strong Markov and Brownian scaling), so `E F(Ξ_s) = E H_F(θ̂_s)` with
`H_F(β) = ∫ F(obsC (w, β)) dΛ(w)`; and `H_F(β + π) = H_F(β)`, because
`obsC (-w, β) = obsC (w, β + π)` (`PathStatMeas.lean`, pathwise reflection `f^{-V}(z) = -f^V(-z)`)
and `-w` has the same law as `w` (`-U =_d U`). So `H_F` is a function of `e^{2iβ}` only, and the
`e^{2iθ̂_s}`-stationarity gives `E H_F(θ̂_s) = ∫ H_F dν`, independent of `s`.

Uses the EXTERNAL `strongMarkov_sleDriver`, and (through the one-time stationarity)
`hormander_oneDim`, `ito_formula`, `timeChange_isContLocalMartingale`, and the pending
`markov_oneDim` as the explicit hypothesis `hMO : MarkovOneDim`.
-/

@[expose] public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter Complex

namespace ComplexSLE.Internal

open Polar

theorem admissibleLaw_eq_admissibleMeasure (p : ℝ → ℝ) :
    admissibleLaw p = admissibleMeasure p := rfl

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-- The law of the driver `U` on `CPath`. -/
noncomputable def driverLaw (hU : IsSLEDriverAdapted a b c U P ℱ) : Measure CPath :=
  P.map (CPath.ofDriver U hU.cont)

theorem isProbabilityMeasure_driverLaw
    (hU : IsSLEDriverAdapted a b c U P ℱ) : IsProbabilityMeasure (driverLaw hU) :=
  (Measure.isProbabilityMeasure_map_iff
    (CPath.measurable_ofDriver hU.cont fun _ => hU.adapted.measurable).aemeasurable).mpr
      (hU.toIsSLEDriver.isProbabilityMeasure)

/-- `H_F(β) = ∫ F(obsC (w, β)) dΛ(w)`: the expectation of the observable of the chain started at
`e^{iβ}`, for the driver law `Λ`. -/
noncomputable def obsKernel (Λ : Measure CPath)
    (F : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞) (β : ℝ) : ℝ≥0∞ :=
  ∫⁻ w, F (obsC (w, β)) ∂Λ

theorem measurable_obsKernel (hU : IsSLEDriverAdapted a b c U P ℱ) (Λ : Measure CPath)
    [SFinite Λ] {F : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    Measurable (obsKernel Λ F) :=
  Measurable.lintegral_prod_left' (f := fun p : CPath × ℝ => F (obsC p))
    (hF.comp (measurable_obsC hU))

/-- **`π`-periodicity of `H_F`** (reflection `obsC (-w, β) = obsC (w, β + π)` and `-U =_d U`). -/
theorem obsKernel_add_pi [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ)
    (ha : 0 < a) (hc : c ^ 2 ≤ a * b) {F : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hF : Measurable F) (β : ℝ) :
    obsKernel (driverLaw hU) F (β + π) = obsKernel (driverLaw hU) F β := by
  have hUm : ∀ t, Measurable (U t) := fun t => hU.adapted.measurable
  have hι := CPath.measurable_ofDriver hU.cont hUm
  obtain ⟨ℱc, hUc⟩ := exists_isSLEDriverAdapted_eval hU.toIsSLEDriver hU.cont hUm
  have : IsProbabilityMeasure (driverLaw hU) := isProbabilityMeasure_driverLaw hU
  have hgood := ae_sigmaDom_eq_Ici hUc (unitPt (β + π)) ha hc (unitPt_ne_zero _)
  have hFβ : Measurable fun w : CPath => F (obsC (w, β)) :=
    hF.comp ((measurable_obsC hU).comp (measurable_id.prodMk measurable_const))
  unfold obsKernel
  calc ∫⁻ w, F (obsC (w, β + π)) ∂(driverLaw hU)
      = ∫⁻ w, F (obsC (CPath.neg w, β)) ∂(driverLaw hU) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hgood] with w hw
        rw [obsC_neg w β hw]
    _ = ∫⁻ w, F (obsC (w, β)) ∂((driverLaw hU).map CPath.neg) :=
        (lintegral_map hFβ CPath.measurable_neg).symm
    _ = ∫⁻ w, F (obsC (w, β)) ∂(driverLaw hU) := by
        rw [driverLaw, map_neg_eq hU.toIsSLEDriver hU.cont hUm]

theorem obsKernel_periodic [IsProbabilityMeasure P] (hU : IsSLEDriverAdapted a b c U P ℱ)
    (ha : 0 < a) (hc : c ^ 2 ≤ a * b) {F : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hF : Measurable F) : Function.Periodic (obsKernel (driverLaw hU) F) π :=
  fun β => obsKernel_add_pi hU ha hc hF β

/-- A `π`-periodic function of `β` is a function of `e^{2iβ}`. -/
theorem periodic_eq_comp_exp {G : ℝ → ℝ≥0∞} (hG : Function.Periodic G π) (β : ℝ) :
    G β = G (Complex.arg (Complex.exp (2 * Complex.I * (β : ℂ))) / 2) := by
  have h : 2 * Complex.I * (β : ℂ) = ((2 * β : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.arg_exp_mul_I, ← self_sub_toIocDiv_zsmul]
  have h2 : (2 * β - toIocDiv Real.two_pi_pos (-π) (2 * β) • (2 * π)) / 2 =
      β - (toIocDiv Real.two_pi_pos (-π) (2 * β) : ℝ) * π := by
    rw [zsmul_eq_mul]; ring
  rw [h2, hG.sub_int_mul_eq]

/-- **Stationarity of the expectation of `H_F(θ̂_s)`**, from the one-time stationarity of
`e^{2iθ̂_s}`. -/
theorem lintegral_obsKernel_thetaHat [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (s : ℝ≥0)
    {F : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ q, obsKernel (driverLaw hU) F (thetaHat hU (unitPt q.2) s q.1)
        ∂(P.prod (admissibleMeasure p)) =
      ∫⁻ u, obsKernel (driverLaw hU) F u ∂(admissibleMeasure p) := by
  have : IsProbabilityMeasure (driverLaw hU) := isProbabilityMeasure_driverLaw hU
  have hper := obsKernel_periodic hU ha hc hF
  have hK := measurable_obsKernel hU (driverLaw hU) hF
  set H : ℂ → ℝ≥0∞ := fun w => obsKernel (driverLaw hU) F (Complex.arg w / 2) with hHdef
  have hHm : Measurable H := hK.comp (Complex.measurable_arg.div_const 2)
  have hexp : ∀ β : ℝ, obsKernel (driverLaw hU) F β =
      H (Complex.exp (2 * Complex.I * (β : ℂ))) := fun β => periodic_eq_comp_exp hper β
  have hlaw := map_exp_thetaHat_prod_eq_of_markovOneDim hMO hU ha hb hc hp s
  have hY : Measurable fun q : Ω × ℝ =>
      Complex.exp (2 * Complex.I * (thetaHat hU (unitPt q.2) s q.1 : ℝ)) := by
    have := measurable_thetaHat_unit hU s
    fun_prop
  have hZ : Measurable fun u : ℝ => Complex.exp (2 * Complex.I * (u : ℂ)) := by fun_prop
  calc ∫⁻ q, obsKernel (driverLaw hU) F (thetaHat hU (unitPt q.2) s q.1)
        ∂(P.prod (admissibleMeasure p))
      = ∫⁻ q, H (Complex.exp (2 * Complex.I * (thetaHat hU (unitPt q.2) s q.1 : ℝ)))
        ∂(P.prod (admissibleMeasure p)) := by simp only [hexp]
    _ = ∫⁻ w, H w ∂((P.prod (admissibleMeasure p)).map fun q : Ω × ℝ =>
          Complex.exp (2 * Complex.I * (thetaHat hU (unitPt q.2) s q.1 : ℝ))) :=
        (lintegral_map hHm hY).symm
    _ = ∫⁻ w, H w ∂((admissibleMeasure p).map fun u : ℝ =>
          Complex.exp (2 * Complex.I * (u : ℂ))) := by rw [hlaw]
    _ = ∫⁻ u, H (Complex.exp (2 * Complex.I * (u : ℂ))) ∂(admissibleMeasure p) :=
        lintegral_map hHm hZ
    _ = ∫⁻ u, obsKernel (driverLaw hU) F u ∂(admissibleMeasure p) := by simp only [hexp]

/-- **Path-level stationarity, integral form.** For every `s ≥ 0` and measurable
`F : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞`,
`E_{P ⊗ ν} F(Ξ_s) = ∫ H_F dν`, a quantity independent of `s`. -/
theorem lintegral_pathObs_eq [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (s : ℝ≥0)
    {F : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ q, F (pathObs hU s q) ∂(P.prod (admissibleMeasure p)) =
      ∫⁻ u, obsKernel (driverLaw hU) F u ∂(admissibleMeasure p) := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  have : IsProbabilityMeasure (driverLaw hU) := isProbabilityMeasure_driverLaw hU
  have hK := measurable_obsKernel hU (driverLaw hU) hF
  have hGm : Measurable fun q : Ω × ℝ =>
      obsKernel (driverLaw hU) F (thetaHat hU (unitPt q.2) s q.1) :=
    hK.comp (measurable_thetaHat_unit hU s)
  have e1 := lintegral_prod_symm (μ := P) (ν := admissibleMeasure p)
    (fun q : Ω × ℝ => F (pathObs hU s q)) (hF.comp (measurable_pathObs hU s)).aemeasurable
  have e2 := lintegral_prod_symm (μ := P) (ν := admissibleMeasure p)
    (fun q : Ω × ℝ => obsKernel (driverLaw hU) F (thetaHat hU (unitPt q.2) s q.1))
    hGm.aemeasurable
  rw [← lintegral_obsKernel_thetaHat hMO hU ha hb hc hp s hF, e1, e2]
  refine lintegral_congr fun u => ?_
  exact lintegral_pathObsAt hU ha hc (unitPt_ne_zero u) s hF

/-- **Path-level stationarity of the polar data started at `𝐳` (A4c).** With the pending external
`markov_oneDim` as the hypothesis `hMO : MarkovOneDim`: for every `s ≥ 0`, the law of
`Ξ_s = (e^{2iθ̂_s(𝐳)}, (θ̂_{s+r}(𝐳) - θ̂_s(𝐳))_r, (log |f̂_{s+r}(𝐳)| - log |f̂_s(𝐳)|)_r)` under
`P ⊗ ν` is `(Λ ⊗ ν).map obsC`, the law of the observable of the chain driven by an independent
copy of `U` started at `e^{iu}`, `u ∼ ν`. -/
theorem map_pathObs_eq_canonical [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (s : ℝ≥0) :
    (P.prod (admissibleMeasure p)).map (pathObs hU s) =
      ((driverLaw hU).prod (admissibleMeasure p)).map obsC := by
  have hν := isProbabilityMeasure_admissibleMeasure hp
  have : IsProbabilityMeasure (driverLaw hU) := isProbabilityMeasure_driverLaw hU
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  have e3 := lintegral_prod_symm (μ := driverLaw hU) (ν := admissibleMeasure p)
    (fun q : CPath × ℝ => F (obsC q)) (hF.comp (measurable_obsC hU)).aemeasurable
  rw [lintegral_map hF (measurable_pathObs hU s), lintegral_map hF (measurable_obsC hU),
    lintegral_pathObs_eq hMO hU ha hb hc hp s hF, e3]
  rfl

/-- **Path-level stationarity of the polar data started at `𝐳` (A4c), headline.** For every
`s ≥ 0`, the law of `Ξ_s` under `P ⊗ ν` equals the law of `Ξ_0`, as measures on
`ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)` (product σ-algebras), `ν = p(u) 1_{[0,2π]}(u) du`. -/
theorem map_pathObs_eq_zero [IsProbabilityMeasure P] (hMO : MarkovOneDim)
    (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (s : ℝ≥0) :
    (P.prod (admissibleMeasure p)).map (pathObs hU s) =
      (P.prod (admissibleMeasure p)).map (pathObs hU 0) :=
  (map_pathObs_eq_canonical hMO hU ha hb hc hp s).trans
    (map_pathObs_eq_canonical hMO hU ha hb hc hp 0).symm

end ComplexSLE.Internal

end
