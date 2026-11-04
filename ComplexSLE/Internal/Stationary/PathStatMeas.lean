/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Stationary.PathStatCanon
public import ComplexSLE.Internal.Stationary.PathStatNeg
public import ComplexSLE.Internal.Polar.PolarContMeas
public import ComplexSLE.Internal.Phases.AllZFHat

/-!
# The polar data as functionals on the canonical path space (M7/A4c)

* `measurable_log_norm_fHat_unit`: `(ω, u) ↦ log |f̂_s(e^{iu})(ω)|` is jointly measurable on
  `Ω × ℝ` (companion of `measurable_thetaHat_unit`; Carathéodory with the open domain
  `{s ∈ sigmaDom}`, `continuousAt_log_norm_fPath_sigmaTime_initial`).
* `thetaC s v z`, `logfC s v z`: `θ̂_s(z)` and `log |f̂_s(z)|` of the chain driven by the continuous
  path `v : CPath`, with the project's junk convention (`0` off `sigmaDom`). For an adapted driver
  `thetaHat hU z s ω = thetaC s (CPath.ofDriver U _ ω) z` (`thetaHat_eq_thetaC`, by `rfl`) and
  `log |fHat hU z s ω| = logfC s (CPath.ofDriver U _ ω) z` (`log_norm_fHat_eq_logfC`).
* `measurable_thetaC_unit`, `measurable_logfC_unit`: joint measurability on `CPath × ℝ` of
  `(v, u) ↦ θ̂_s(e^{iu})(v)`, `log |f̂_s(e^{iu})(v)|`. They are obtained by applying the
  measurability theorems for adapted drivers to the *canonical driver* of `PathStatCanon.lean`
  (the continuous coordinate process on `CPath`).
* `polarInc v ξ = ((θ̂_r - θ̂_0)_r, (log |f̂_r|)_r)` and
  `obsC (v, β) = (e^{2iβ}, polarInc v e^{iβ})`, the observable "started at the angle `β`",
  jointly measurable (`measurable_obsC`).
* `polarInc_neg`, `obsC_neg`: reflection, `polarInc (-v) ξ = polarInc v (-ξ)` when
  `sigmaDom v (-ξ) = [0, ∞)`, hence `obsC (-v, β) = obsC (v, β + π)`.
-/

@[expose] public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal

open Polar

section Adapted

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-- For fixed `z` and `s`, `ω ↦ f̂_s(z)(ω)` is measurable. -/
theorem measurable_fHat_ambient (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) (s : ℝ≥0) :
    Measurable (fHat hU z s) :=
  (measurable_fHat hU (z := z) s).mono ((sigmaFiltration hU z).le s) le_rfl

/-- `u ↦ log |f̂_s(e^{iu})|` is continuous on `{u | s ∈ sigmaDom (e^{iu})}`. -/
theorem continuousOn_log_norm_unit {V : ℝ≥0 → ℂ} (hV : Continuous V) (s : ℝ) :
    ContinuousOn (fun u : ℝ => Real.log ‖fPath V hV (unitPt u) (sigmaTime V hV (unitPt u) s)‖)
      {u | s ∈ sigmaDom V hV (unitPt u)} := fun _ hu =>
  ((continuousAt_log_norm_fPath_sigmaTime_initial hV hu).comp
    (f := unitPt) continuous_unitPt.continuousAt).continuousWithinAt

/-- **Joint measurability of `log |f̂_s(e^{iu})|` on `Ω × ℝ`.** -/
theorem measurable_log_norm_fHat_unit (hU : IsSLEDriverAdapted a b c U P ℱ) (s : ℝ≥0) :
    Measurable fun p : Ω × ℝ => Real.log ‖fHat hU (unitPt p.2) s p.1‖ := by
  refine measurable_of_continuousOn_sections (S := sigmaDomUnit hU (s : ℝ))
    (F := fun p : Ω × ℝ => Real.log ‖fHat hU (unitPt p.2) s p.1‖) (G := fun _ => 0)
    (measurableSet_sigmaDomUnit hU (s : ℝ)) (isOpen_sigmaDomUnit_section hU (s : ℝ))
    measurable_const ?_ ?_ ?_
  · intro p hp
    have hp' : (s : ℝ) ∉ sigmaDom (fun r => U r p.1) (hU.cont p.1) (unitPt p.2) := hp
    simp [fHat_of_notMem hU hp']
  · intro ω
    refine (continuousOn_log_norm_unit (hU.cont ω) (s : ℝ)).congr fun u hu => ?_
    have hu' : (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) (unitPt u) := hu
    simp only [fHat_of_mem hU hu']
  · intro u
    exact Real.measurable_log.comp (measurable_norm.comp (measurable_fHat_ambient hU (unitPt u) s))

end Adapted

/-! ### The polar functionals on `CPath` -/

open Classical in
/-- `θ̂_s(z)` for the chain driven by the continuous path `v` (`0` off `sigmaDom`). -/
noncomputable def thetaC (s : ℝ≥0) (v : CPath) (z : ℂ) : ℝ :=
  if (s : ℝ) ∈ sigmaDom (fun r => v.1 r) v.2 z then
    argPath (fun r => v.1 r) v.2 z (sigmaTime (fun r => v.1 r) v.2 z s) else 0

open Classical in
/-- `log |f̂_s(z)|` for the chain driven by the continuous path `v` (`0` off `sigmaDom`). -/
noncomputable def logfC (s : ℝ≥0) (v : CPath) (z : ℂ) : ℝ :=
  if (s : ℝ) ∈ sigmaDom (fun r => v.1 r) v.2 z then
    Real.log ‖fPath (fun r => v.1 r) v.2 z (sigmaTime (fun r => v.1 r) v.2 z s)‖ else 0

theorem thetaC_of_mem {s : ℝ≥0} {v : CPath} {z : ℂ}
    (h : (s : ℝ) ∈ sigmaDom (fun r => v.1 r) v.2 z) :
    thetaC s v z = argPath (fun r => v.1 r) v.2 z (sigmaTime (fun r => v.1 r) v.2 z s) := by
  unfold thetaC; exact ite_eq_left h

theorem logfC_of_mem {s : ℝ≥0} {v : CPath} {z : ℂ}
    (h : (s : ℝ) ∈ sigmaDom (fun r => v.1 r) v.2 z) :
    logfC s v z =
      Real.log ‖fPath (fun r => v.1 r) v.2 z (sigmaTime (fun r => v.1 r) v.2 z s)‖ := by
  unfold logfC; exact ite_eq_left h

theorem logfC_of_notMem {s : ℝ≥0} {v : CPath} {z : ℂ}
    (h : (s : ℝ) ∉ sigmaDom (fun r => v.1 r) v.2 z) : logfC s v z = 0 := by
  unfold logfC; exact ite_eq_right h

section Relations

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

theorem thetaHat_eq_thetaC (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) (s : ℝ≥0) (ω : Ω) :
    thetaHat hU z s ω = thetaC s (CPath.ofDriver U hU.cont ω) z := rfl

theorem log_norm_fHat_eq_logfC (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) (s : ℝ≥0) (ω : Ω) :
    Real.log ‖fHat hU z s ω‖ = logfC s (CPath.ofDriver U hU.cont ω) z := by
  by_cases h : (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z
  · rw [fHat_of_mem hU h, logfC_of_mem (v := CPath.ofDriver U hU.cont ω) h]
    rfl
  · rw [fHat_of_notMem hU h, logfC_of_notMem (v := CPath.ofDriver U hU.cont ω) h]
    simp

/-- **Joint measurability of `θ̂_s(e^{iu})` on `CPath × ℝ`.** -/
theorem measurable_thetaC_unit (hU : IsSLEDriverAdapted a b c U P ℱ) (s : ℝ≥0) :
    Measurable fun q : CPath × ℝ => thetaC s q.1 (unitPt q.2) := by
  obtain ⟨ℱc, hUc⟩ := exists_isSLEDriverAdapted_eval hU.toIsSLEDriver hU.cont
    (fun t => hU.adapted.measurable)
  exact measurable_thetaHat_unit hUc s

/-- **Joint measurability of `log |f̂_s(e^{iu})|` on `CPath × ℝ`.** -/
theorem measurable_logfC_unit (hU : IsSLEDriverAdapted a b c U P ℱ) (s : ℝ≥0) :
    Measurable fun q : CPath × ℝ => logfC s q.1 (unitPt q.2) := by
  obtain ⟨ℱc, hUc⟩ := exists_isSLEDriverAdapted_eval hU.toIsSLEDriver hU.cont
    (fun t => hU.adapted.measurable)
  have e : (fun q : CPath × ℝ => logfC s q.1 (unitPt q.2)) =
      fun q : CPath × ℝ => Real.log ‖fHat hUc (unitPt q.2) s q.1‖ := by
    funext q
    exact (log_norm_fHat_eq_logfC hUc _ s q.1).symm
  rw [e]
  exact measurable_log_norm_fHat_unit hUc s

end Relations

/-! ### The observable started at the angle `β` -/

/-- The polar increments `((θ̂_r - θ̂_0)_r, (log |f̂_r|)_r)` of the chain `(v, ξ)`. -/
noncomputable def polarInc (v : CPath) (ξ : ℂ) : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) :=
  (fun r => thetaC r v ξ - thetaC 0 v ξ, fun r => logfC r v ξ)

/-- The observable of the chain started at `e^{iβ}`: `(e^{2iβ}, polar increments)`. -/
noncomputable def obsC (q : CPath × ℝ) : ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) :=
  (Complex.exp (2 * Complex.I * (q.2 : ℝ)), polarInc q.1 (unitPt q.2))

section ObsMeas

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

theorem measurable_obsC (hU : IsSLEDriverAdapted a b c U P ℱ) : Measurable obsC := by
  refine Measurable.prodMk (by fun_prop) (Measurable.prodMk ?_ ?_)
  · exact measurable_pi_iff.2 fun r =>
      (measurable_thetaC_unit hU r).sub (measurable_thetaC_unit hU 0)
  · exact measurable_pi_iff.2 fun r => measurable_logfC_unit hU r

end ObsMeas

/-! ### Reflection -/

theorem polarInc_neg (v : CPath) (ξ : ℂ) (h : sigmaDom v.1 v.2 (-ξ) = Ici 0) :
    polarInc (CPath.neg v) ξ = polarInc v (-ξ) := by
  have hV' : Continuous fun s => -v.1 s := v.2.neg
  have hdom : sigmaDom (fun s => -v.1 s) hV' ξ = Ici 0 := by
    rw [sigmaDom_neg v.2 hV' ξ]; exact h
  have hmem : ∀ r : ℝ≥0, (r : ℝ) ∈ sigmaDom v.1 v.2 (-ξ) := fun r => by
    rw [h]; exact r.coe_nonneg
  have hz0 : (0 : ℝ) ∈ lifeSet v.1 (-ξ) := by
    have := sigmaTime_mem_lifeSet v.2 (hmem 0)
    exact mem_lifeSet_of_le this le_rfl this.1
  have hz0' : (0 : ℝ) ∈ lifeSet (fun s => -v.1 s) ξ := by rwa [lifeSet_neg]
  have hθ : ∀ r : ℝ≥0, thetaC r (CPath.neg v) ξ - thetaC 0 (CPath.neg v) ξ =
      thetaC r v (-ξ) - thetaC 0 v (-ξ) := by
    intro r
    have h1 : (r : ℝ) ∈ sigmaDom (fun s => -v.1 s) hV' ξ := by rw [hdom]; exact r.coe_nonneg
    have h0 : ((0 : ℝ≥0) : ℝ) ∈ sigmaDom (fun s => -v.1 s) hV' ξ := by
      rw [hdom]; exact (0 : ℝ≥0).coe_nonneg
    have h0' : ((0 : ℝ≥0) : ℝ) ∈ sigmaDom v.1 v.2 (-ξ) := hmem 0
    have e1 := thetaC_of_mem (v := CPath.neg v) (z := ξ) h1
    have e0 := thetaC_of_mem (v := CPath.neg v) (z := ξ) h0
    have e1' := thetaC_of_mem (v := v) (z := -ξ) (hmem r)
    have e0' := thetaC_of_mem (v := v) (z := -ξ) h0'
    have s0 := sigmaTime_zero hV' hz0'
    have s0' := sigmaTime_zero v.2 hz0
    rw [e1, e0, e1', e0']
    simp only [NNReal.coe_zero] at *
    change argPath (fun s => -v.1 s) hV' ξ (sigmaTime (fun s => -v.1 s) hV' ξ r) -
        argPath (fun s => -v.1 s) hV' ξ (sigmaTime (fun s => -v.1 s) hV' ξ 0) = _
    rw [s0, s0']
    exact argPath_sigmaTime_neg_sub v.2 hV' ξ (hmem r)
  have hl : ∀ r : ℝ≥0, logfC r (CPath.neg v) ξ = logfC r v (-ξ) := by
    intro r
    have h1 : (r : ℝ) ∈ sigmaDom (fun s => -v.1 s) hV' ξ := by rw [hdom]; exact r.coe_nonneg
    rw [logfC_of_mem (v := CPath.neg v) (z := ξ) h1, logfC_of_mem (v := v) (z := -ξ) (hmem r)]
    exact log_norm_fPath_sigmaTime_neg v.2 hV' ξ (hmem r)
  unfold polarInc
  congr 1
  · funext r; exact hθ r
  · funext r; exact hl r

theorem unitPt_add_pi (β : ℝ) : unitPt (β + π) = - unitPt β := by
  unfold unitPt
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

theorem exp_two_mul_I_add_pi (β : ℝ) :
    Complex.exp (2 * Complex.I * ((β + π : ℝ) : ℂ)) = Complex.exp (2 * Complex.I * (β : ℂ)) := by
  push_cast
  have : 2 * Complex.I * ((β : ℂ) + π) = 2 * Complex.I * (β : ℂ) + 2 * π * Complex.I := by ring
  rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- **Reflection of the observable**: `obsC (-v, β) = obsC (v, β + π)` when
`sigmaDom v e^{i(β+π)} = [0, ∞)`. -/
theorem obsC_neg (v : CPath) (β : ℝ) (h : sigmaDom v.1 v.2 (unitPt (β + π)) = Ici 0) :
    obsC (CPath.neg v, β) = obsC (v, β + π) := by
  unfold obsC
  simp only
  rw [exp_two_mul_I_add_pi, unitPt_add_pi, polarInc_neg v (unitPt β)]
  rw [← unitPt_add_pi]
  exact h

end ComplexSLE.Internal

end
