/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.PolarThetaMart

/-!
# Brackets from Itô's formula: the generic layer (M6/S13)

Source-independent tools for the bracket of a process `G(X_t)` obtained from the external Itô
formula E1, used for the θ-half of Lemma 2.11 (`step:polar-real-imag`).

* `isStronglyProgressive_pathIntegral'`: the path integral `t ↦ ∫₀ᵗ ξ_s ds` of a progressively
  measurable process is progressively measurable (Fubini on `[0, i] × Ω × [0, i]`); no
  integrability or continuity is needed.
* The squared deviation `sqDevG G (x, d) = (G x - d)²` on `ℝⁿ⁺¹ = ℝⁿ × ℝ`, with its first and
  second derivatives in coordinate directions (`fderiv_sqDevG_single`, `iteratedFDeriv_sqDevG`).
* `isContLocalMartingale_sq_sub_of_ito`: under the hypotheses of E1 for an `ℝⁿ`-valued state `X`
  and a `C²` function `G`, if `L` is the Itô drift of `G(X)` (so that
  `M^G = G(X_t) - G(X_0) - ∫₀ᵗ L` is a continuous local martingale), then
  `(M^G)² - ∫₀ᵗ ∇G(X_s)ᵀ Q_s ∇G(X_s) ds` is a continuous local martingale. The proof applies E1
  to the augmented state `(X, G(X_0) + ∫₀ᵗ L)` (whose last coordinate has zero martingale part)
  and the function `sqDevG G`.
* `isContLocalMartingale_mul_sub_of_ito`: the polarised version, `M^{G₁} M^{G₂} -
  ∫₀ᵗ ∇G₁ᵀ Q ∇G₂` for a symmetric `Q`, from the squares of `G₁`, `G₂` and `G₁ + G₂`.
* `IsContLocalMartingale.mul_sub_min'`: `V (M_t - M_{t ∧ ρ})` is a continuous local martingale for
  an `ℱ_ρ`-measurable multiplier `V` that need not be bounded (localise at `ρ` on `{|V| > m}`).
-/

public section

open scoped NNReal ENNReal Topology
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal.Polar

/-! ### Path integrals of progressive processes are progressive -/

section Progressive

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}

/-- **The path integral of a progressive process is progressive** (no integrability needed). -/
theorem isStronglyProgressive_pathIntegral' {ξ : ℝ≥0 → Ω → ℝ} (hξ : IsStronglyProgressive ℱ ξ) :
    IsStronglyProgressive ℱ fun t ω => pathIntegral ξ t ω := by
  intro i
  let mI : MeasurableSpace (Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
  let mR : MeasurableSpace ℝ := inferInstance
  -- the integrand on `([0, i] × Ω) × ℝ`
  let F : (Iic i × Ω) × ℝ → ℝ := fun q =>
    {q : (Iic i × Ω) × ℝ | 0 < q.2 ∧ q.2 ≤ ((q.1.1 : ℝ≥0) : ℝ)}.indicator
      (fun q => ξ (min (Real.toNNReal q.2) i) q.1.2) q
  have hφ : Measurable[mI.prod mR, mI] fun q : (Iic i × Ω) × ℝ =>
      ((⟨min (Real.toNNReal q.2) i, min_le_right _ _⟩ : Iic i), q.1.2) := by
    refine Measurable.prodMk ?_ ?_
    · refine Measurable.subtype_mk ?_
      exact (measurable_real_toNNReal.comp (@measurable_snd _ _ mI mR)).min measurable_const
    · exact (@measurable_snd _ _ Subtype.instMeasurableSpace (ℱ i)).comp
        (@measurable_fst _ _ mI mR)
  have hF : StronglyMeasurable[mI.prod mR] F := by
    refine StronglyMeasurable.indicator ((hξ i).comp_measurable hφ) ?_
    have h1 : Measurable[mI.prod mR] fun q : (Iic i × Ω) × ℝ => q.2 :=
      @measurable_snd _ _ mI mR
    have h2 : Measurable[mI.prod mR] fun q : (Iic i × Ω) × ℝ => ((q.1.1 : ℝ≥0) : ℝ) :=
      (measurable_subtype_coe.comp
        (@measurable_fst _ _ Subtype.instMeasurableSpace (ℱ i))).comp
          (@measurable_fst _ _ mI mR) |>.coe_nnreal_real
    exact (measurableSet_lt measurable_const h1).inter (measurableSet_le h1 h2)
  have key := @StronglyMeasurable.integral_prod_right' (Iic i × Ω) ℝ ℝ mI mR volume _ _ _ F hF
  have e : (fun p : Iic i × Ω => pathIntegral ξ (p.1 : ℝ≥0) p.2) = fun p => ∫ y, F (p, y) := by
    funext p
    simp only [pathIntegral]
    rw [intervalIntegral.integral_of_le (p.1 : ℝ≥0).coe_nonneg,
      ← integral_indicator measurableSet_Ioc]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    by_cases h1 : 0 < s ∧ s ≤ ((p.1 : ℝ≥0) : ℝ)
    · have : Real.toNNReal s ≤ i := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ h1.1.le]
        exact h1.2.trans (NNReal.coe_le_coe.2 p.1.2)
      simp only [F, indicator, mem_Ioc, mem_ofPred_eq, h1, and_self, ite_true, min_eq_left this]
    · simp only [F, indicator, mem_Ioc, mem_ofPred_eq, h1, ite_false]
  rw [e]; exact key

end Progressive

/-! ### The squared deviation `(G x - d)²` on `ℝⁿ⁺¹` -/

section SqDev

variable {n : ℕ}

/-- `u ↦ Fin.init u` as a continuous linear map `ℝⁿ⁺¹ → ℝⁿ`. -/
@[expose] noncomputable def initCLM (n : ℕ) : (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) (Fin.castSucc i)

theorem initCLM_apply (u : Fin (n + 1) → ℝ) : initCLM n u = Fin.init u := rfl

/-- The last coordinate as a continuous linear map. -/
@[expose] noncomputable def lastCLM (n : ℕ) : (Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) (Fin.last n)

theorem lastCLM_apply (u : Fin (n + 1) → ℝ) : lastCLM n u = u (Fin.last n) := rfl

/-- `devG G (x, d) = G x - d`. -/
@[expose] noncomputable def devG (G : (Fin n → ℝ) → ℝ) (u : Fin (n + 1) → ℝ) : ℝ :=
  G (Fin.init u) - u (Fin.last n)

/-- `sqDevG G (x, d) = (G x - d)²`. -/
@[expose] noncomputable def sqDevG (G : (Fin n → ℝ) → ℝ) (u : Fin (n + 1) → ℝ) : ℝ :=
  devG G u ^ 2

/-- `{(x, d) | x ∈ D}`. -/
@[expose] def initDom (D : Set (Fin n → ℝ)) : Set (Fin (n + 1) → ℝ) := {u | Fin.init u ∈ D}

/-- The gradient of `sqDevG G` divided by `2 (G x - d)`: `(∇G x, -1)`. -/
@[expose] noncomputable def gradDevG (G : (Fin n → ℝ) → ℝ) (u : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : ℝ :=
  fderiv ℝ G (Fin.init u) (Fin.init (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ)) -
    (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ) (Fin.last n)

/-- The Hessian of `G` padded by zeros. -/
@[expose] noncomputable def hessDevG (G : (Fin n → ℝ) → ℝ) (u : Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) : ℝ :=
  iteratedFDeriv ℝ 2 G (Fin.init u) ![Fin.init (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ),
    Fin.init (Pi.single j (1 : ℝ) : Fin (n + 1) → ℝ)]

theorem init_single_castSucc (i : Fin n) :
    Fin.init (Pi.single (Fin.castSucc i) (1 : ℝ) : Fin (n + 1) → ℝ) = Pi.single i 1 := by
  funext j
  simp only [Fin.init, Pi.single_apply, Fin.castSucc_inj]

theorem init_single_last :
    Fin.init (Pi.single (Fin.last n) (1 : ℝ) : Fin (n + 1) → ℝ) = 0 := by
  funext j
  simp only [Fin.init, Pi.single_apply, Fin.castSucc_ne_last, ite_false, Pi.zero_apply]

theorem gradDevG_castSucc (G : (Fin n → ℝ) → ℝ) (u : Fin (n + 1) → ℝ) (i : Fin n) :
    gradDevG G u (Fin.castSucc i) = fderiv ℝ G (Fin.init u) (Pi.single i 1) := by
  simp [gradDevG, init_single_castSucc, Fin.castSucc_ne_last]

theorem gradDevG_last (G : (Fin n → ℝ) → ℝ) (u : Fin (n + 1) → ℝ) :
    gradDevG G u (Fin.last n) = -1 := by
  simp [gradDevG, init_single_last]

theorem hessDevG_castSucc_castSucc (G : (Fin n → ℝ) → ℝ) (u : Fin (n + 1) → ℝ) (i j : Fin n) :
    hessDevG G u (Fin.castSucc i) (Fin.castSucc j) =
      iteratedFDeriv ℝ 2 G (Fin.init u) ![Pi.single i 1, Pi.single j 1] := by
  simp [hessDevG, init_single_castSucc]

theorem hessDevG_last_left (G : (Fin n → ℝ) → ℝ) (u : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    hessDevG G u (Fin.last n) j = 0 := by
  simp only [hessDevG, init_single_last, iteratedFDeriv_two_apply, Matrix.cons_val_zero,
    map_zero, zero_apply]

theorem hessDevG_last_right (G : (Fin n → ℝ) → ℝ) (u : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    hessDevG G u i (Fin.last n) = 0 := by
  simp only [hessDevG, init_single_last, iteratedFDeriv_two_apply, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, map_zero]

variable {D : Set (Fin n → ℝ)} {G : (Fin n → ℝ) → ℝ}

theorem isOpen_initDom (hD : IsOpen D) : IsOpen (initDom D) :=
  hD.preimage (initCLM n).continuous

theorem measurable_sqDevG (hGm : Measurable G) : Measurable (sqDevG G) :=
  ((hGm.comp (initCLM n).continuous.measurable).sub (measurable_pi_apply _)).pow_const 2

theorem contDiffOn_sqDevG (_hD : IsOpen D) (hG : ContDiffOn ℝ 2 G D) :
    ContDiffOn ℝ 2 (sqDevG G) (initDom D) := by
  have h1 : ContDiffOn ℝ 2 (fun u : Fin (n + 1) → ℝ => G (Fin.init u)) (initDom D) :=
    hG.comp (initCLM n).contDiff.contDiffOn fun u hu => hu
  have h2 : ContDiffOn ℝ 2 (fun u : Fin (n + 1) → ℝ => u (Fin.last n)) (initDom D) :=
    (lastCLM n).contDiff.contDiffOn
  exact (h1.sub h2).pow 2

theorem hasFDerivAt_devG (hD : IsOpen D) (hG : ContDiffOn ℝ 2 G D) {u : Fin (n + 1) → ℝ}
    (hu : u ∈ initDom D) :
    HasFDerivAt (devG G) ((fderiv ℝ G (Fin.init u)).comp (initCLM n) - lastCLM n) u := by
  have h1 : HasFDerivAt G (fderiv ℝ G (Fin.init u)) (Fin.init u) :=
    ((hG.differentiableOn (by norm_num)).differentiableAt (hD.mem_nhds hu)).hasFDerivAt
  have h2 : HasFDerivAt (fun u : Fin (n + 1) → ℝ => G (Fin.init u))
      ((fderiv ℝ G (Fin.init u)).comp (initCLM n)) u :=
    h1.comp u (initCLM n).hasFDerivAt
  exact h2.sub (lastCLM n).hasFDerivAt

theorem fderiv_sqDevG_single (hD : IsOpen D) (hG : ContDiffOn ℝ 2 G D) {u : Fin (n + 1) → ℝ}
    (hu : u ∈ initDom D) (i : Fin (n + 1)) :
    fderiv ℝ (sqDevG G) u (Pi.single i 1) = 2 * devG G u * gradDevG G u i := by
  have h := (hasFDerivAt_devG hD hG hu).pow 2
  have e : sqDevG G = fun u => devG G u ^ 2 := rfl
  rw [e, h.fderiv]
  simp only [smul_apply, sub_apply,
    ContinuousLinearMap.comp_apply, initCLM_apply, lastCLM_apply, smul_eq_mul, gradDevG]
  push_cast
  ring

/-- `w ↦ ∂G(w') e` (with `w' = Fin.init w`) is differentiable, with derivative the Hessian. -/
theorem hasFDerivAt_fderiv_init (hD : IsOpen D) (hG : ContDiffOn ℝ 2 G D) {u : Fin (n + 1) → ℝ}
    (hu : u ∈ initDom D) (e : Fin n → ℝ) :
    HasFDerivAt (fun w : Fin (n + 1) → ℝ => fderiv ℝ G (Fin.init w) e)
      (((fderiv ℝ (fderiv ℝ G) (Fin.init u)).comp (initCLM n)).flip e) u := by
  have h1 : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) (Fin.init u)) (Fin.init u) :=
    (((hG.fderiv_of_isOpen hD (m := 1) (by norm_num)).differentiableOn
      (by norm_num)).differentiableAt (hD.mem_nhds hu)).hasFDerivAt
  have h2 : HasFDerivAt (fun w : Fin (n + 1) → ℝ => fderiv ℝ G (Fin.init w))
      ((fderiv ℝ (fderiv ℝ G) (Fin.init u)).comp (initCLM n)) u :=
    h1.comp u (initCLM n).hasFDerivAt
  have h3 := h2.clm_apply (hasFDerivAt_const e u)
  simpa using h3

theorem iteratedFDeriv_sqDevG (hD : IsOpen D) (hG : ContDiffOn ℝ 2 G D) {u : Fin (n + 1) → ℝ}
    (hu : u ∈ initDom D) (i j : Fin (n + 1)) :
    iteratedFDeriv ℝ 2 (sqDevG G) u ![Pi.single i 1, Pi.single j 1] =
      2 * devG G u * hessDevG G u i j + 2 * gradDevG G u i * gradDevG G u j := by
  have hE := (hasFDerivAt_devG hD hG hu).const_mul 2
  have hGj := (hasFDerivAt_fderiv_init hD hG hu
    (Fin.init (Pi.single j (1 : ℝ) : Fin (n + 1) → ℝ))).sub_const
    ((Pi.single j (1 : ℝ) : Fin (n + 1) → ℝ) (Fin.last n))
  have hg : HasFDerivAt (fun w => 2 * devG G w * gradDevG G w j) _ u := hE.mul hGj
  rw [iteratedFDeriv_two_single (isOpen_initDom hD) (contDiffOn_sqDevG hD hG) hu
    (fun w hw => fderiv_sqDevG_single hD hG hw j) hg]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply, sub_apply,
    initCLM_apply, lastCLM_apply, smul_eq_mul, gradDevG, hessDevG, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

end SqDev

/-! ### Padding a matrix by a zero row and column -/

section Pad

variable {n : ℕ}

/-- `Q` padded by a zero last row and column. -/
@[expose] noncomputable def padQ (Q : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j =>
    Fin.snoc (α := fun _ => ℝ) (fun i' => Fin.snoc (α := fun _ => ℝ) (fun j' => Q i' j') 0 j) 0 i

@[simp] theorem padQ_castSucc_castSucc (Q : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    padQ Q (Fin.castSucc i) (Fin.castSucc j) = Q i j := by
  simp [padQ, Fin.snoc_castSucc]

@[simp] theorem padQ_last_left (Q : Matrix (Fin n) (Fin n) ℝ) (j : Fin (n + 1)) :
    padQ Q (Fin.last n) j = 0 := by
  simp [padQ, Fin.snoc_last]

@[simp] theorem padQ_last_right (Q : Matrix (Fin n) (Fin n) ℝ) (i : Fin (n + 1)) :
    padQ Q i (Fin.last n) = 0 := by
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [padQ, Fin.snoc_last]
  · simp [padQ, Fin.snoc_castSucc, Fin.snoc_last]

theorem continuous_snoc_pair :
    Continuous fun p : (Fin n → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (n + 1) → ℝ) :=
  Continuous.finSnoc (A := fun _ : Fin (n + 1) => ℝ) continuous_fst continuous_snd

theorem continuous_padQ : Continuous (padQ (n := n)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [padQ_last_left]; exact continuous_const
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [padQ_last_right]; exact continuous_const
    · simp only [padQ_castSucc_castSucc]
      exact (continuous_apply j).comp (continuous_apply i)

end Pad

/-! ### Continuity of path integrals of locally integrable integrands -/

section Cont

variable {Ω : Type*}

/-- A path integral with an integrand that is interval integrable on every `[0, t]` is a
continuous function of the upper limit. -/
theorem continuous_pathIntegral' {ξ : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hξ : ∀ t : ℝ≥0, IntervalIntegrable (fun s : ℝ => ξ s.toNNReal ω) volume 0 t) :
    Continuous fun t : ℝ≥0 => pathIntegral ξ t ω := by
  have h0 : ∀ b : ℝ, IntervalIntegrable (fun s : ℝ => ξ s.toNNReal ω) volume 0 b := by
    intro b
    rcases le_or_gt 0 b with hb | hb
    · have := hξ b.toNNReal
      rwa [Real.coe_toNNReal _ hb] at this
    · refine IntervalIntegrable.symm ?_
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le]
      exact (integrableOn_const (C := ξ 0 ω) measure_Ioc_lt_top.ne).congr_fun (fun s hs => by
        have : s.toNNReal = 0 := Real.toNNReal_of_nonpos hs.2
        simp [this]) measurableSet_Ioc
  have hall : ∀ a b : ℝ, IntervalIntegrable (fun s : ℝ => ξ s.toNNReal ω) volume a b :=
    fun a b => (h0 a).symm.trans (h0 b)
  exact (intervalIntegral.continuous_primitive hall 0).comp NNReal.continuous_coe

end Cont

/-! ### The generic bracket lemma -/

section Generic

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}

theorem pathIntegral_add' {ξ η : ℝ≥0 → Ω → ℝ} {ω : Ω} {t : ℝ≥0}
    (hξ : IntervalIntegrable (fun s : ℝ => ξ s.toNNReal ω) volume 0 t)
    (hη : IntervalIntegrable (fun s : ℝ => η s.toNNReal ω) volume 0 t) :
    pathIntegral (fun s ω => ξ s ω + η s ω) t ω = pathIntegral ξ t ω + pathIntegral η t ω :=
  intervalIntegral.integral_add hξ hη

/-- The algebraic identity behind the bracket lemma. -/
theorem sq_bracket_algebra {n : ℕ} (E L : ℝ) (g A : Fin n → ℝ) (H Q : Fin n → Fin n → ℝ)
    (hL : L = ∑ i, g i * A i + (1 / 2) * ∑ i, ∑ j, H i j * Q i j) :
    ∑ i, 2 * E * g i * A i + 2 * E * (-1) * L +
      (1 / 2) * ∑ i, ∑ j, (2 * E * H i j + 2 * g i * g j) * Q i j =
      ∑ i, ∑ j, g i * g j * Q i j := by
  have h1 : ∑ i, 2 * E * g i * A i = 2 * E * ∑ i, g i * A i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i, ∑ j, (2 * E * H i j + 2 * g i * g j) * Q i j =
      2 * E * (∑ i, ∑ j, H i j * Q i j) + 2 * ∑ i, ∑ j, g i * g j * Q i j := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h1, h2, hL]; ring

variable [IsProbabilityMeasure P]

/-- **Bracket of `G(X)` from Itô's formula.** Under the hypotheses of E1 for the `ℝⁿ`-valued
state `X` (drift `A`, diffusion matrix `Q`) and a `C²` function `G` on an open set `D` containing
the path a.s., let `L` be the Itô drift of `G(X)` and `V = ∇G(X)ᵀ Q ∇G(X)` (both given as
progressive processes agreeing with these expressions at positive times whenever the path stays
in `D`). Then `(G(X_t) - G(X_0) - ∫₀ᵗ L)² - ∫₀ᵗ V` is a continuous local martingale. -/
theorem isContLocalMartingale_sq_sub_of_ito {n : ℕ} (X A : ℝ≥0 → Ω → (Fin n → ℝ))
    (Q : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : IsStronglyProgressive ℱ X) (hXc : ∀ ω, Continuous fun t => X t ω)
    (hA : IsStronglyProgressive ℱ A)
    (hAint : ∀ᵐ ω ∂P, ∀ (i : Fin n) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => A (Real.toNNReal s) ω i) volume 0 t)
    (hQ : IsStronglyProgressive ℱ Q)
    (hQint : ∀ᵐ ω ∂P, ∀ (i j : Fin n) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => Q (Real.toNNReal s) ω i j) volume 0 t)
    (hM : ∀ i, IsContLocalMartingale ℱ
      (fun t ω => X t ω i - X 0 ω i - pathIntegral (fun s ω => A s ω i) t ω) P)
    (hMM : ∀ i j, IsContLocalMartingale ℱ (fun t ω =>
      (X t ω i - X 0 ω i - pathIntegral (fun s ω => A s ω i) t ω) *
        (X t ω j - X 0 ω j - pathIntegral (fun s ω => A s ω j) t ω) -
        pathIntegral (fun s ω => Q s ω i j) t ω) P)
    (D : Set (Fin n → ℝ)) (hD : IsOpen D) (G : (Fin n → ℝ) → ℝ) (hGm : Measurable G)
    (hG : ContDiffOn ℝ 2 G D) (hXD : ∀ᵐ ω ∂P, ∀ t, X t ω ∈ D)
    (L V : ℝ≥0 → Ω → ℝ) (hLp : IsStronglyProgressive ℱ L) (hVp : IsStronglyProgressive ℱ V)
    (hLint : ∀ ω (t : ℝ≥0), IntervalIntegrable (fun s : ℝ => L (Real.toNNReal s) ω) volume 0 t)
    (hLIc : ∀ ω, Continuous fun t => pathIntegral L t ω)
    (hLeq : ∀ ω, (∀ t, X t ω ∈ D) → ∀ s : ℝ≥0, 0 < s → L s ω =
      ∑ i, fderiv ℝ G (X s ω) (Pi.single i 1) * A s ω i +
        (1 / 2) * ∑ i, ∑ j,
          iteratedFDeriv ℝ 2 G (X s ω) ![Pi.single i 1, Pi.single j 1] * Q s ω i j)
    (hVeq : ∀ ω, (∀ t, X t ω ∈ D) → ∀ s : ℝ≥0, 0 < s → V s ω =
      ∑ i, ∑ j, fderiv ℝ G (X s ω) (Pi.single i 1) * fderiv ℝ G (X s ω) (Pi.single j 1) *
        Q s ω i j) :
    IsContLocalMartingale ℱ (fun t ω =>
      (G (X t ω) - G (X 0 ω) - pathIntegral L t ω) ^ 2 - pathIntegral V t ω) P := by
  -- the augmented state
  set d : ℝ≥0 → Ω → ℝ := fun t ω => G (X 0 ω) + pathIntegral L t ω with hd
  obtain ⟨X', hX'⟩ : ∃ X' : ℝ≥0 → Ω → (Fin (n + 1) → ℝ),
    X' = fun t ω => Fin.snoc (X t ω) (d t ω) := ⟨_, rfl⟩
  obtain ⟨A', hA'⟩ : ∃ A' : ℝ≥0 → Ω → (Fin (n + 1) → ℝ),
    A' = fun t ω => Fin.snoc (A t ω) (L t ω) := ⟨_, rfl⟩
  obtain ⟨Q', hQ'⟩ : ∃ Q' : ℝ≥0 → Ω → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
    Q' = fun t ω => padQ (Q t ω) := ⟨_, rfl⟩
  have hGX0 : StronglyMeasurable[ℱ 0] fun ω => G (X 0 ω) :=
    (hGm.comp (hX.stronglyAdapted 0).measurable).stronglyMeasurable
  have hGX0p : IsStronglyProgressive ℱ fun (_ : ℝ≥0) ω => G (X 0 ω) :=
    StronglyAdapted.isStronglyProgressive_of_continuous
      (fun t => hGX0.mono (ℱ.mono bot_le)) fun _ => continuous_const
  have hLI := isStronglyProgressive_pathIntegral' hLp (ℱ := ℱ)
  have hVI := isStronglyProgressive_pathIntegral' hVp (ℱ := ℱ)
  have hdp : IsStronglyProgressive ℱ d := fun i => (hGX0p i).add (hLI i)
  have hdc : ∀ ω, Continuous fun t => d t ω := fun ω => continuous_const.add (hLIc ω)
  have hX'p : IsStronglyProgressive ℱ X' := by
    intro i; rw [hX']
    exact continuous_snoc_pair.comp_stronglyMeasurable ((hX i).prodMk (hdp i))
  have hX'c : ∀ ω, Continuous fun t => X' t ω := fun ω => by
    rw [hX']; exact (hXc ω).finSnoc (hdc ω)
  have hA'p : IsStronglyProgressive ℱ A' := by
    intro i; rw [hA']
    exact continuous_snoc_pair.comp_stronglyMeasurable ((hA i).prodMk (hLp i))
  have hA'int : ∀ᵐ ω ∂P, ∀ (i : Fin (n + 1)) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => A' (Real.toNNReal s) ω i) volume 0 t := by
    filter_upwards [hAint] with ω hω i t
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [hA', Fin.snoc_last]; exact hLint ω t
    · simp only [hA', Fin.snoc_castSucc]; exact hω i t
  have hQ'p : IsStronglyProgressive ℱ Q' := by
    intro i; rw [hQ']
    exact continuous_padQ.comp_stronglyMeasurable (hQ i)
  have hQ'int : ∀ᵐ ω ∂P, ∀ (i j : Fin (n + 1)) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => Q' (Real.toNNReal s) ω i j) volume 0 t := by
    filter_upwards [hQint] with ω hω i j t
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [hQ', padQ_last_left]; exact intervalIntegrable_const
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [hQ', padQ_last_right]; exact intervalIntegrable_const
      · simp only [hQ', padQ_castSucc_castSucc]; exact hω i j t
  have hlast : ∀ t ω, X' t ω (Fin.last n) - X' 0 ω (Fin.last n) -
      pathIntegral (fun s ω => A' s ω (Fin.last n)) t ω = 0 := by
    intro t ω
    simp only [hX', hA', Fin.snoc_last, hd, pathIntegral_zero_time]
    ring
  have hM' : ∀ i, IsContLocalMartingale ℱ
      (fun t ω => X' t ω i - X' 0 ω i - pathIntegral (fun s ω => A' s ω i) t ω) P := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [hlast]; exact isContLocalMartingale_zero
    · simp only [hX', hA', Fin.snoc_castSucc]; exact hM i
  have hMM' : ∀ i j, IsContLocalMartingale ℱ (fun t ω =>
      (X' t ω i - X' 0 ω i - pathIntegral (fun s ω => A' s ω i) t ω) *
        (X' t ω j - X' 0 ω j - pathIntegral (fun s ω => A' s ω j) t ω) -
        pathIntegral (fun s ω => Q' s ω i j) t ω) P := by
    intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [hlast, zero_mul, hQ', padQ_last_left, pathIntegral_zero_fun, sub_zero]
      exact isContLocalMartingale_zero
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [hlast, mul_zero, hQ', padQ_last_right, pathIntegral_zero_fun, sub_zero]
        exact isContLocalMartingale_zero
      · simp only [hX', hA', hQ', Fin.snoc_castSucc, padQ_castSucc_castSucc]; exact hMM i j
  have hX'D : ∀ᵐ ω ∂P, ∀ t, X' t ω ∈ initDom D := by
    filter_upwards [hXD] with ω hω t
    change Fin.init (X' t ω) ∈ D
    simp only [hX', Fin.init_snoc]; exact hω t
  have h := External.ito_formula ℱ X' A' Q' hX'p hX'c hA'p hA'int hQ'p hQ'int hM' hMM'
    (initDom D) (isOpen_initDom hD) (sqDevG G) (measurable_sqDevG hGm) (contDiffOn_sqDevG hD hG)
    hX'D
  -- the target is progressive
  have hprog : IsStronglyProgressive ℱ (fun t ω =>
      (G (X t ω) - G (X 0 ω) - pathIntegral L t ω) ^ 2 - pathIntegral V t ω) := by
    intro i
    have h1 : StronglyMeasurable[Subtype.instMeasurableSpace.prod (ℱ i)]
        fun p : Iic i × Ω => G (X p.1 p.2) :=
      (hGm.comp (hX i).measurable).stronglyMeasurable
    have h2 := ((h1.sub (hGX0p i)).sub (hLI i)).pow 2
    exact h2.sub (hVI i)
  refine h.congr_ae hprog ?_
  filter_upwards [hXD] with ω hω t
  have e1 : sqDevG G (X' t ω) = (G (X t ω) - G (X 0 ω) - pathIntegral L t ω) ^ 2 := by
    simp only [sqDevG, devG, hX', Fin.init_snoc, Fin.snoc_last, hd]; ring
  have e0 : sqDevG G (X' 0 ω) = 0 := by
    simp only [sqDevG, devG, hX', Fin.init_snoc, Fin.snoc_last, hd, pathIntegral_zero_time]; ring
  rw [e1, e0, sub_zero]
  congr 1
  refine (pathIntegral_congr_pos (fun s hs => ?_) t).symm
  have hu : X' s ω ∈ initDom D := by
    change Fin.init (X' s ω) ∈ D
    simp only [hX', Fin.init_snoc]; exact hω s
  simp only [fderiv_sqDevG_single hD hG hu, iteratedFDeriv_sqDevG hD hG hu]
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [Fin.sum_univ_castSucc (n := n) (fun j => _), gradDevG_castSucc, gradDevG_last,
    hessDevG_castSucc_castSucc, hessDevG_last_left, hessDevG_last_right, hX', hA', hQ',
    Fin.init_snoc, Fin.snoc_castSucc, Fin.snoc_last, padQ_castSucc_castSucc, padQ_last_left,
    padQ_last_right, mul_zero, Finset.sum_const_zero, add_zero]
  rw [hVeq ω hω s hs]
  exact sq_bracket_algebra _ (L s ω) _ _ _ _ (hLeq ω hω s hs)

/-- The identity `∇(G₁+G₂)ᵀ Q ∇(G₁+G₂) = V₁₁ + 2 V₁₂ + V₂₂` for symmetric `Q`. -/
theorem sum_add_bracket {n : ℕ} (g h : Fin n → ℝ) (Q : Fin n → Fin n → ℝ)
    (hQ : ∀ i j, Q i j = Q j i) :
    ∑ i, ∑ j, (g i + h i) * (g j + h j) * Q i j =
      ∑ i, ∑ j, g i * g j * Q i j + 2 * ∑ i, ∑ j, g i * h j * Q i j +
        ∑ i, ∑ j, h i * h j * Q i j := by
  have hsw : ∑ i, ∑ j, h i * g j * Q i j = ∑ i, ∑ j, g i * h j * Q i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hQ j i]; ring
  have : ∑ i, ∑ j, (g i + h i) * (g j + h j) * Q i j =
      ∑ i, ∑ j, (g i * g j * Q i j + g i * h j * Q i j + h i * g j * Q i j + h i * h j * Q i j) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [this]
  simp only [Finset.sum_add_distrib]
  rw [hsw]; ring

/-- **Cross bracket of `G₁(X)` and `G₂(X)` from Itô's formula** (polarisation of
`isContLocalMartingale_sq_sub_of_ito`), for a symmetric diffusion matrix `Q`. -/
theorem isContLocalMartingale_mul_sub_of_ito {n : ℕ} (X A : ℝ≥0 → Ω → (Fin n → ℝ))
    (Q : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : IsStronglyProgressive ℱ X) (hXc : ∀ ω, Continuous fun t => X t ω)
    (hA : IsStronglyProgressive ℱ A)
    (hAint : ∀ᵐ ω ∂P, ∀ (i : Fin n) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => A (Real.toNNReal s) ω i) volume 0 t)
    (hQ : IsStronglyProgressive ℱ Q)
    (hQint : ∀ᵐ ω ∂P, ∀ (i j : Fin n) (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => Q (Real.toNNReal s) ω i j) volume 0 t)
    (hQsymm : ∀ s ω i j, Q s ω i j = Q s ω j i)
    (hM : ∀ i, IsContLocalMartingale ℱ
      (fun t ω => X t ω i - X 0 ω i - pathIntegral (fun s ω => A s ω i) t ω) P)
    (hMM : ∀ i j, IsContLocalMartingale ℱ (fun t ω =>
      (X t ω i - X 0 ω i - pathIntegral (fun s ω => A s ω i) t ω) *
        (X t ω j - X 0 ω j - pathIntegral (fun s ω => A s ω j) t ω) -
        pathIntegral (fun s ω => Q s ω i j) t ω) P)
    (D : Set (Fin n → ℝ)) (hD : IsOpen D) (G₁ G₂ : (Fin n → ℝ) → ℝ)
    (hG₁m : Measurable G₁) (hG₂m : Measurable G₂)
    (hG₁ : ContDiffOn ℝ 2 G₁ D) (hG₂ : ContDiffOn ℝ 2 G₂ D) (hXD : ∀ᵐ ω ∂P, ∀ t, X t ω ∈ D)
    (hG₁Xc : ∀ ω, Continuous fun t => G₁ (X t ω)) (hG₂Xc : ∀ ω, Continuous fun t => G₂ (X t ω))
    (L₁ L₂ V₁₁ V₁₂ V₂₂ : ℝ≥0 → Ω → ℝ)
    (hL₁p : IsStronglyProgressive ℱ L₁) (hL₂p : IsStronglyProgressive ℱ L₂)
    (hV₁₁p : IsStronglyProgressive ℱ V₁₁) (hV₁₂p : IsStronglyProgressive ℱ V₁₂)
    (hV₂₂p : IsStronglyProgressive ℱ V₂₂)
    (hL₁int : ∀ ω (t : ℝ≥0), IntervalIntegrable (fun s : ℝ => L₁ (Real.toNNReal s) ω) volume 0 t)
    (hL₂int : ∀ ω (t : ℝ≥0), IntervalIntegrable (fun s : ℝ => L₂ (Real.toNNReal s) ω) volume 0 t)
    (hV₁₁int : ∀ ω (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => V₁₁ (Real.toNNReal s) ω) volume 0 t)
    (hV₁₂int : ∀ ω (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => V₁₂ (Real.toNNReal s) ω) volume 0 t)
    (hV₂₂int : ∀ ω (t : ℝ≥0),
      IntervalIntegrable (fun s : ℝ => V₂₂ (Real.toNNReal s) ω) volume 0 t)
    (hL₁Ic : ∀ ω, Continuous fun t => pathIntegral L₁ t ω)
    (hL₂Ic : ∀ ω, Continuous fun t => pathIntegral L₂ t ω)
    (hL₁eq : ∀ ω, (∀ t, X t ω ∈ D) → ∀ s : ℝ≥0, 0 < s → L₁ s ω =
      ∑ i, fderiv ℝ G₁ (X s ω) (Pi.single i 1) * A s ω i +
        (1 / 2) * ∑ i, ∑ j,
          iteratedFDeriv ℝ 2 G₁ (X s ω) ![Pi.single i 1, Pi.single j 1] * Q s ω i j)
    (hL₂eq : ∀ ω, (∀ t, X t ω ∈ D) → ∀ s : ℝ≥0, 0 < s → L₂ s ω =
      ∑ i, fderiv ℝ G₂ (X s ω) (Pi.single i 1) * A s ω i +
        (1 / 2) * ∑ i, ∑ j,
          iteratedFDeriv ℝ 2 G₂ (X s ω) ![Pi.single i 1, Pi.single j 1] * Q s ω i j)
    (hV₁₁eq : ∀ ω, (∀ t, X t ω ∈ D) → ∀ s : ℝ≥0, 0 < s → V₁₁ s ω =
      ∑ i, ∑ j, fderiv ℝ G₁ (X s ω) (Pi.single i 1) * fderiv ℝ G₁ (X s ω) (Pi.single j 1) *
        Q s ω i j)
    (hV₁₂eq : ∀ ω, (∀ t, X t ω ∈ D) → ∀ s : ℝ≥0, 0 < s → V₁₂ s ω =
      ∑ i, ∑ j, fderiv ℝ G₁ (X s ω) (Pi.single i 1) * fderiv ℝ G₂ (X s ω) (Pi.single j 1) *
        Q s ω i j)
    (hV₂₂eq : ∀ ω, (∀ t, X t ω ∈ D) → ∀ s : ℝ≥0, 0 < s → V₂₂ s ω =
      ∑ i, ∑ j, fderiv ℝ G₂ (X s ω) (Pi.single i 1) * fderiv ℝ G₂ (X s ω) (Pi.single j 1) *
        Q s ω i j) :
    IsContLocalMartingale ℱ (fun t ω =>
      (G₁ (X t ω) - G₁ (X 0 ω) - pathIntegral L₁ t ω) *
        (G₂ (X t ω) - G₂ (X 0 ω) - pathIntegral L₂ t ω) - pathIntegral V₁₂ t ω) P := by
  have h₁ := isContLocalMartingale_sq_sub_of_ito X A Q hX hXc hA hAint hQ hQint hM hMM D hD G₁
    hG₁m hG₁ hXD L₁ V₁₁ hL₁p hV₁₁p hL₁int hL₁Ic hL₁eq hV₁₁eq
  have h₂ := isContLocalMartingale_sq_sub_of_ito X A Q hX hXc hA hAint hQ hQint hM hMM D hD G₂
    hG₂m hG₂ hXD L₂ V₂₂ hL₂p hV₂₂p hL₂int hL₂Ic hL₂eq hV₂₂eq
  -- the sum `G₁ + G₂`
  have hdiff : ∀ x ∈ D, DifferentiableAt ℝ G₁ x ∧ DifferentiableAt ℝ G₂ x := fun x hx =>
    ⟨(hG₁.differentiableOn (by norm_num)).differentiableAt (hD.mem_nhds hx),
      (hG₂.differentiableOn (by norm_num)).differentiableAt (hD.mem_nhds hx)⟩
  have hfd : ∀ x ∈ D, ∀ e, fderiv ℝ (fun y => G₁ y + G₂ y) x e =
      fderiv ℝ G₁ x e + fderiv ℝ G₂ x e := by
    intro x hx e
    have := fderiv_add (hdiff x hx).1 (hdiff x hx).2
    rw [show (fun y => G₁ y + G₂ y) = G₁ + G₂ from rfl, this, add_apply]
  have hid : ∀ x ∈ D, ∀ e, iteratedFDeriv ℝ 2 (fun y => G₁ y + G₂ y) x e =
      iteratedFDeriv ℝ 2 G₁ x e + iteratedFDeriv ℝ 2 G₂ x e := by
    intro x hx e
    have := iteratedFDeriv_add_apply (i := 2) (hG₁.contDiffAt (hD.mem_nhds hx))
      (hG₂.contDiffAt (hD.mem_nhds hx))
    rw [show (fun y => G₁ y + G₂ y) = G₁ + G₂ from rfl, this, add_apply]
  have h₁₂ := isContLocalMartingale_sq_sub_of_ito X A Q hX hXc hA hAint hQ hQint hM hMM D hD
    (fun y => G₁ y + G₂ y) (hG₁m.add hG₂m) (hG₁.add hG₂) hXD
    (fun s ω => L₁ s ω + L₂ s ω) (fun s ω => V₁₁ s ω + 2 * V₁₂ s ω + V₂₂ s ω)
    (fun i => (hL₁p i).add (hL₂p i))
    (fun i => ((hV₁₁p i).add ((hV₁₂p i).const_mul 2)).add (hV₂₂p i))
    (fun ω t => (hL₁int ω t).add (hL₂int ω t))
    (fun ω => by
      have : (fun t => pathIntegral (fun s ω => L₁ s ω + L₂ s ω) t ω) =
          fun t => pathIntegral L₁ t ω + pathIntegral L₂ t ω :=
        funext fun t => pathIntegral_add' (hL₁int ω t) (hL₂int ω t)
      rw [this]; exact (hL₁Ic ω).add (hL₂Ic ω))
    (fun ω hω s hs => by
      rw [hL₁eq ω hω s hs, hL₂eq ω hω s hs]
      simp only [hfd _ (hω s), hid _ (hω s), add_mul, Finset.sum_add_distrib, mul_add]
      ring)
    (fun ω hω s hs => by
      rw [hV₁₁eq ω hω s hs, hV₁₂eq ω hω s hs, hV₂₂eq ω hω s hs]
      simp only [hfd _ (hω s)]
      exact (sum_add_bracket _ _ _ (hQsymm s ω)).symm)
  -- continuity of the three processes
  have hc₁ : ∀ ω, Continuous fun t =>
      (G₁ (X t ω) - G₁ (X 0 ω) - pathIntegral L₁ t ω) ^ 2 - pathIntegral V₁₁ t ω := by
    intro ω
    refine Continuous.sub (((hG₁Xc ω).sub continuous_const).sub (hL₁Ic ω) |>.pow 2) ?_
    exact continuous_pathIntegral' (hV₁₁int ω)
  have hc₂ : ∀ ω, Continuous fun t =>
      (G₂ (X t ω) - G₂ (X 0 ω) - pathIntegral L₂ t ω) ^ 2 - pathIntegral V₂₂ t ω := by
    intro ω
    refine Continuous.sub (((hG₂Xc ω).sub continuous_const).sub (hL₂Ic ω) |>.pow 2) ?_
    exact continuous_pathIntegral' (hV₂₂int ω)
  have hc₁₂ : ∀ ω, Continuous fun t =>
      ((fun y => G₁ y + G₂ y) (X t ω) - (fun y => G₁ y + G₂ y) (X 0 ω) -
        pathIntegral (fun s ω => L₁ s ω + L₂ s ω) t ω) ^ 2 -
        pathIntegral (fun s ω => V₁₁ s ω + 2 * V₁₂ s ω + V₂₂ s ω) t ω := by
    intro ω
    have e : (fun t => pathIntegral (fun s ω => L₁ s ω + L₂ s ω) t ω) =
        fun t => pathIntegral L₁ t ω + pathIntegral L₂ t ω :=
      funext fun t => pathIntegral_add' (hL₁int ω t) (hL₂int ω t)
    refine Continuous.sub ?_ ?_
    · refine Continuous.pow ?_ 2
      refine Continuous.sub (((hG₁Xc ω).add (hG₂Xc ω)).sub continuous_const) ?_
      show Continuous fun t => pathIntegral (fun s ω => L₁ s ω + L₂ s ω) t ω
      rw [e]; exact (hL₁Ic ω).add (hL₂Ic ω)
    · exact continuous_pathIntegral' fun t =>
        ((hV₁₁int ω t).add ((hV₁₂int ω t).const_mul 2)).add (hV₂₂int ω t)
  have hsum := ((h₁₂.sub h₁ hc₁₂ hc₁).sub h₂ (fun ω => (hc₁₂ ω).sub (hc₁ ω)) hc₂).const_mul (1 / 2)
  refine hsum.congr_fun' fun t ω => ?_
  simp only [Pi.sub_apply]
  rw [pathIntegral_add' (hL₁int ω t) (hL₂int ω t),
    pathIntegral_add' ((hV₁₁int ω t).add ((hV₁₂int ω t).const_mul 2)) (hV₂₂int ω t),
    pathIntegral_add' (hV₁₁int ω t) ((hV₁₂int ω t).const_mul 2)]
  have e2 : pathIntegral (fun s ω => 2 * V₁₂ s ω) t ω = 2 * pathIntegral V₁₂ t ω := by
    simp only [pathIntegral]; rw [intervalIntegral.integral_const_mul]
  rw [e2]
  ring

end Generic

/-! ### Unbounded `ℱ_ρ`-measurable multipliers -/

section Multiplier

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  [IsProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ}

/-- **`ℱ_ρ`-measurable multiplier of a post-`ρ` increment, without boundedness.** If `M` is an
everywhere-continuous continuous local martingale, `ρ` a finite stopping time and `V` a random
variable with `V 1_{ρ ≤ u}` `ℱ_u`-measurable for every `u`, then `V (M_t - M_{t ∧ ρ})` is a
continuous local martingale (localise at `ρ` on `{|V| > k}`). -/
theorem _root_.ComplexSLE.IsContLocalMartingale.mul_sub_min' (hM : IsContLocalMartingale ℱ M P)
    (hMc : ∀ ω, Continuous fun t => M t ω) {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime ℱ fun ω => (ρ ω : WithTop ℝ≥0)) {V : Ω → ℝ}
    (hV : ∀ u : ℝ≥0, Measurable[ℱ u] fun ω => if ρ ω ≤ u then V ω else 0) :
    IsContLocalMartingale ℱ (fun t ω => V ω * (M t ω - M (min t (ρ ω)) ω)) P := by
  have hprog : IsStronglyProgressive ℱ M := hM.1
  have hZ : (fun t ω => V ω * (M t ω - M (min t (ρ ω)) ω)) =
      fun t ω => (if ρ ω ≤ t then V ω else 0) * (M t ω - M (min t (ρ ω)) ω) := by
    funext t ω
    split_ifs with h
    · rfl
    · replace h : t < ρ ω := lt_of_not_ge h
      rw [min_eq_left h.le, sub_self, mul_zero, mul_zero]
  have hprog' : IsStronglyProgressive ℱ fun t ω => V ω * (M t ω - M (min t (ρ ω)) ω) := by
    rw [hZ]
    intro i
    have h1 := hprog.stoppedProcess hρ
    simp only [funext fun t => funext fun ω => stoppedProcess_coe_min M ρ t ω] at h1
    exact (isStronglyProgressive_ite_le hV i).mul ((hprog i).sub (h1 i))
  have hcont : ∀ ω, Continuous fun t => V ω * (M t ω - M (min t (ρ ω)) ω) := fun ω =>
    continuous_const.mul ((hMc ω).sub ((hMc ω).comp (continuous_id.min continuous_const)))
  -- the localising times: `ρ` on `{|V| > k}`, `∞` on `{|V| ≤ k}`
  let τ : ℕ → Ω → WithTop ℝ≥0 := fun k ω => if |V ω| ≤ k then ⊤ else (ρ ω : WithTop ℝ≥0)
  have hτ : ∀ k, IsStoppingTime ℱ (τ k) := by
    intro k u
    have e : {ω | τ k ω ≤ u} = {ω | ¬ |(if ρ ω ≤ u then V ω else 0)| ≤ k} ∩ {ω | ρ ω ≤ u} := by
      ext ω
      simp only [τ, mem_ofPred_eq, mem_inter_iff]
      by_cases h : |V ω| ≤ k
      · simp only [h, ↓reduceIte]
        refine ⟨fun h' => absurd h' (WithTop.not_top_le_coe u), ?_⟩
        rintro ⟨h1, h2⟩
        simp only [h2, ↓reduceIte, h, not_true_eq_false] at h1
      · simp only [h, ↓reduceIte, WithTop.coe_le_coe]
        constructor
        · intro hρu; exact ⟨by simp [hρu, h], hρu⟩
        · rintro ⟨-, hρu⟩; exact hρu
    rw [e]
    exact ((measurableSet_le (continuous_abs.measurable.comp (hV u)) measurable_const).compl).inter
      (Infrastructure.measurableSet_nnreal_le hρ u)
  have hτev : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ∀ᶠ k in atTop, (t : WithTop ℝ≥0) ≤ τ k ω := by
    refine ae_of_all _ fun ω t => ?_
    filter_upwards [eventually_ge_atTop ⌈|V ω|⌉₊] with k hk
    have : |V ω| ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
    simp only [τ, this, ↓reduceIte, le_top]
  refine IsContLocalMartingale.of_stopped_seq hprog' (ae_of_all _ hcont) hτ hτev fun k => ?_
  -- the stopped process is the bounded-multiplier martingale
  have hVk : ∀ u : ℝ≥0, Measurable[ℱ u] fun ω =>
      if ρ ω ≤ u then (if |V ω| ≤ k then V ω else 0) else 0 := by
    intro u
    have hf : Measurable fun x : ℝ => if |x| ≤ k then x else 0 :=
      Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const) measurable_id
        measurable_const
    have e : (fun ω => if ρ ω ≤ u then (if |V ω| ≤ k then V ω else 0) else 0) =
        (fun x : ℝ => if |x| ≤ k then x else 0) ∘ fun ω => if ρ ω ≤ u then V ω else 0 := by
      funext ω
      simp only [Function.comp]
      split_ifs <;> simp_all
    rw [e]
    exact hf.comp (hV u)
  have h := hM.mul_sub_min hMc hρ (V := fun ω => if |V ω| ≤ k then V ω else 0) (C := k)
    (fun ω => by split_ifs with h <;> simp [h]) hVk
  refine h.congr_fun' fun t ω => ?_
  simp only [stoppedProcess, τ]
  split_ifs with h
  · rw [min_eq_left le_top, untopA_coe']
  · rw [← WithTop.coe_min, untopA_coe', min_assoc, min_self, sub_self, mul_zero, zero_mul]

end Multiplier

end ComplexSLE.Internal.Polar

end
