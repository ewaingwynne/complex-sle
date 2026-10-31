/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Loewner.Transform
public import ComplexSLE.Internal.Polar.Argument
public import ComplexSLE.Internal.Polar.Sigma

/-!
# Reflection `(V, z) ↦ (-V, -z)` of the polar data (M7/A4c)

Deterministic and unconditional. For a continuous driver `V` and a point `z`, the chain driven by
`-V` and started at `z` is minus the chain driven by `V` and started at `-z`
(`f^{-V}_t(z) = - f^V_t(-z)`, the Loewner equation is odd). Hence

* `lifeSet_neg`, `fPath_neg`, `clock_neg`, `sigmaDom_neg`, `sigmaTime_neg`: life set, centered
  path, clock, domain and inverse clock of `(-V, z)` and `(V, -z)` agree;
* `argPath_sub_neg`: the argument *increments* agree,
  `θ^{-V}_t(z) - θ^{-V}_0(z) = θ^V_t(-z) - θ^V_0(-z)` (the arguments themselves differ by an odd
  multiple of `π`, by the initial normalization `θ_0 ∈ [0, 2π)`);
* `argPath_sigmaTime_neg_sub`, `log_norm_fPath_sigmaTime_neg`: the same in σ-time, together with
  `log |f^{-V}_{σ(s)}(z)| = log |f^V_{σ(s)}(-z)|`.

This is the pathwise half of the symmetry `-U =_d U` used for the `π`-reduction in Lemma 2.14
(`paper.tex:L984`) and in the path-level stationarity of `(θ̂, log |f̂|)`.
-/

public section

open scoped NNReal ENNReal Real
open Set Complex

namespace ComplexSLE.Internal.Polar

variable {V : ℝ≥0 → ℂ}

theorem lifeSet_neg (V : ℝ≥0 → ℂ) (z : ℂ) :
    lifeSet (fun s => -V s) z = lifeSet V (-z) := by
  ext t
  simp only [lifeSet, mem_ofPred_eq]
  have := absorbingTime_neg V (-z)
  rw [neg_neg] at this
  rw [this]

theorem solPath_neg (hV : Continuous V) (hV' : Continuous fun s => -V s) (z : ℂ) {t : ℝ}
    (ht : t ∈ lifeSet (fun s => -V s) z) :
    solPath (fun s => -V s) hV' z t = - solPath V hV (-z) t := by
  have h2 := isLoewnerSolution_neg (solPath_isLoewnerSolution hV (-z))
  rw [neg_neg] at h2
  have h1 := solPath_isLoewnerSolution hV' z
  have habs := absorbingTime_neg V (-z)
  rw [neg_neg] at habs
  rw [habs] at h1
  exact (loewner_wellDefined (fun s => -V s) hV' z).2 _ _ _ h1 h2 (by
    simpa [lifeSet, habs] using ht)

theorem fPath_neg (hV : Continuous V) (hV' : Continuous fun s => -V s) (z : ℂ) {t : ℝ}
    (ht : t ∈ lifeSet (fun s => -V s) z) :
    fPath (fun s => -V s) hV' z t = - fPath V hV (-z) t := by
  unfold fPath
  rw [solPath_neg hV hV' z ht]
  ring

theorem norm_fPath_neg (hV : Continuous V) (hV' : Continuous fun s => -V s) (z : ℂ) {t : ℝ}
    (ht : t ∈ lifeSet (fun s => -V s) z) :
    ‖fPath (fun s => -V s) hV' z t‖ = ‖fPath V hV (-z) t‖ := by
  rw [fPath_neg hV hV' z ht, norm_neg]

theorem clock_neg (hV : Continuous V) (hV' : Continuous fun s => -V s) (z : ℂ) {t : ℝ}
    (ht : t ∈ lifeSet (fun s => -V s) z) :
    clock (fun s => -V s) hV' z t = clock V hV (-z) t := by
  unfold clock
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le ht.1] at hr
  have hr' : r ∈ lifeSet (fun s => -V s) z := Icc_subset_lifeSet ht hr
  simp only [clockRate]
  rw [norm_fPath_neg hV hV' z hr']

theorem clockSup_neg (hV : Continuous V) (hV' : Continuous fun s => -V s) (z : ℂ) :
    clockSup (fun s => -V s) hV' z = clockSup V hV (-z) := by
  unfold clockSup
  refine le_antisymm (iSup₂_le fun t ht => ?_) (iSup₂_le fun t ht => ?_)
  · have ht' : t ∈ lifeSet V (-z) := by rwa [lifeSet_neg] at ht
    rw [clock_neg hV hV' z ht]
    exact le_iSup₂_of_le (f := fun t (_ : t ∈ lifeSet V (-z)) =>
      ENNReal.ofReal (clock V hV (-z) t)) t ht' le_rfl
  · have ht' : t ∈ lifeSet (fun s => -V s) z := by rwa [lifeSet_neg]
    rw [← clock_neg hV hV' z ht']
    exact le_iSup₂_of_le (f := fun t (_ : t ∈ lifeSet (fun s => -V s) z) =>
      ENNReal.ofReal (clock (fun s => -V s) hV' z t)) t ht' le_rfl

theorem sigmaDom_neg (hV : Continuous V) (hV' : Continuous fun s => -V s) (z : ℂ) :
    sigmaDom (fun s => -V s) hV' z = sigmaDom V hV (-z) := by
  ext s
  simp only [sigmaDom, mem_ofPred_eq, clockSup_neg hV hV' z]

theorem sigmaTime_neg (hV : Continuous V) (hV' : Continuous fun s => -V s) (z : ℂ) (s : ℝ) :
    sigmaTime (fun s => -V s) hV' z s = sigmaTime V hV (-z) s := by
  unfold sigmaTime
  congr 1
  ext t
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨ht, hs⟩
    refine ⟨by rwa [lifeSet_neg] at ht, ?_⟩
    rwa [clock_neg hV hV' z ht] at hs
  · rintro ⟨ht, hs⟩
    have ht' : t ∈ lifeSet (fun s => -V s) z := by rwa [lifeSet_neg]
    refine ⟨ht', ?_⟩
    rwa [← clock_neg hV hV' z ht'] at hs

/-- **Argument increments under reflection.** For `t` in the life set,
`θ^{-V}_t(z) - θ^{-V}_0(z) = θ^V_t(-z) - θ^V_0(-z)`. -/
theorem argPath_sub_neg (hV : Continuous V) (hV' : Continuous fun s => -V s) (z : ℂ) {t : ℝ}
    (ht : t ∈ lifeSet (fun s => -V s) z) :
    argPath (fun s => -V s) hV' z t - argPath (fun s => -V s) hV' z 0 =
      argPath V hV (-z) t - argPath V hV (-z) 0 := by
  have hz0 : (0 : ℝ) ∈ lifeSet (fun s => -V s) z := mem_lifeSet_of_le ht le_rfl ht.1
  have hz0' : (0 : ℝ) ∈ lifeSet V (-z) := by rwa [lifeSet_neg] at hz0
  set θ : ℝ → ℝ := fun u => argPath V hV (-z) u - argPath V hV (-z) 0 +
    argPath (fun s => -V s) hV' z 0 with hθ
  -- the exponentials of the two initial angles differ by the sign
  have hw : fPath (fun s => -V s) hV' z 0 = - fPath V hV (-z) 0 := fPath_neg hV hV' z hz0
  have hexp0 : exp (argPath (fun s => -V s) hV' z 0 * I) =
      - exp (argPath V hV (-z) 0 * I) := by
    rw [exp_argPath_mul_I hV' hz0, exp_argPath_mul_I hV hz0', hw, norm_neg, neg_div]
  have hc : ContinuousOn θ (lifeSet (fun s => -V s) z) := by
    rw [lifeSet_neg]
    exact ((continuousOn_argPath hV (-z)).sub continuousOn_const).add continuousOn_const
  have he : ∀ u ∈ lifeSet (fun s => -V s) z,
      fPath (fun s => -V s) hV' z u = ‖fPath (fun s => -V s) hV' z u‖ * exp (θ u * I) := by
    intro u hu
    have hu' : u ∈ lifeSet V (-z) := by rwa [lifeSet_neg] at hu
    rw [fPath_neg hV hV' z hu, norm_neg]
    have h1 : θ u * I = argPath V hV (-z) u * I +
        (argPath (fun s => -V s) hV' z 0 * I - argPath V hV (-z) 0 * I) := by
      simp only [hθ]
      push_cast
      ring
    have hne : exp (argPath V hV (-z) 0 * I) ≠ 0 := exp_ne_zero _
    have h2 : exp (θ u * I) = - exp (argPath V hV (-z) u * I) := by
      rw [h1, exp_add, exp_sub, hexp0]
      field_simp
    rw [h2]
    conv_lhs => rw [fPath_eq_norm_mul_exp hV hu']
    ring
  have h0 : θ 0 ∈ Ico 0 (2 * π) := by
    have : θ 0 = argPath (fun s => -V s) hV' z 0 := by simp [hθ]
    rw [this]
    exact argPath_zero_mem_Ico hV' _
  have := argPath_unique hV' hc he h0 ht
  simp only [hθ] at this
  linarith

/-- **σ-time version**: for `s` in the domain of `σ`, the argument increments agree. -/
theorem argPath_sigmaTime_neg_sub (hV : Continuous V) (hV' : Continuous fun s => -V s) (z : ℂ)
    {s : ℝ} (hs : s ∈ sigmaDom V hV (-z)) :
    argPath (fun s => -V s) hV' z (sigmaTime (fun s => -V s) hV' z s) -
        argPath (fun s => -V s) hV' z 0 =
      argPath V hV (-z) (sigmaTime V hV (-z) s) - argPath V hV (-z) 0 := by
  have hs' : s ∈ sigmaDom (fun s => -V s) hV' z := by rwa [sigmaDom_neg hV hV' z]
  rw [sigmaTime_neg hV hV' z]
  refine argPath_sub_neg hV hV' z ?_
  rw [lifeSet_neg]
  exact sigmaTime_mem_lifeSet hV hs

/-- **σ-time version**: the log-moduli agree, `log |f^{-V}_{σ(s)}(z)| = log |f^V_{σ(s)}(-z)|`. -/
theorem log_norm_fPath_sigmaTime_neg (hV : Continuous V) (hV' : Continuous fun s => -V s)
    (z : ℂ) {s : ℝ} (hs : s ∈ sigmaDom V hV (-z)) :
    Real.log ‖fPath (fun s => -V s) hV' z (sigmaTime (fun s => -V s) hV' z s)‖ =
      Real.log ‖fPath V hV (-z) (sigmaTime V hV (-z) s)‖ := by
  rw [sigmaTime_neg hV hV' z]
  have : sigmaTime V hV (-z) s ∈ lifeSet (fun s => -V s) z := by
    rw [lifeSet_neg]
    exact sigmaTime_mem_lifeSet hV hs
  rw [norm_fPath_neg hV hV' z this]

end ComplexSLE.Internal.Polar

end
