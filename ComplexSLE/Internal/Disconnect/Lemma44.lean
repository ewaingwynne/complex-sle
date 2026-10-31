/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Disconnect.Lemma44Bootstrap
public import ComplexSLE.Frozen.Defs.CovMatrix
public import ComplexSLE.Frozen.Defs.CenteredLoewnerMap
import all ComplexSLE.Internal.Loewner.Duality

/-!
# Lemmas 4.4–4.6 in deterministic form: a driver path and ODE estimates

arXiv:2203.07313v4, §4: Lemma 4.4 (`lem-pos-hits-before-neg`, paper.tex:L2036-2039, proof
L2118-2138), Lemma 4.5 (`lem:re-im-bounds`, L2043-2076) and Lemma 4.6 (`lem-c-event`,
L2082-2107).

The probabilistic event of Lemma 4.6 is replaced by a *single deterministic path* `φ` in the range
of `Σ = covMatrix a b c`: `φ(t) = S(t) (√a + i √b)` with `S` real and piecewise linear
(`lemma44Profile`). Then a pathwise ODE estimate holds for every continuous driver `V` that is
uniformly within `1` of `φ` on `[0, 2]` (`exists_lemma44_path`): for every `z` with
`2 C - 1 ≤ Re z` and `|Im z| ≤ 1`, the solution of `γ' = 2 / (γ - V)` from `z` exists on `[0, 2]`
(so `z ∉ L₂^V`) and `f₂ (z) = γ 2 - V 2` satisfies
`Re z - 6 C ≤ Re f₂ (z) ≤ Re z - 3 C` and `|Im f₂ (z)| ≤ M`.

The proof is the bootstrap of Lemma 4.4: while `|γ - V| ≥ 1`, the drift of `γ` has modulus `≤ 2`
(`norm_sub_le_of_closedSol`), which keeps `Re (γ - V) ≥ 2` on `[0, 1]` and `Im (γ - V) ≤ -3` on
`[1, 2]` (`lemma44_step`); `bootstrap_Icc` closes the continuity argument and
`lt_absorbingTime_of_norm_sub_ge` rules out absorption before time `2`
(`lemma44_exists_closedSol`).
-/

public section

open scoped NNReal ENNReal
open Set

namespace ComplexSLE.Internal

/-- The piecewise linear real profile `S(t) = σ t + κ max (t - 1, 0)`. -/
noncomputable def lemma44Profile (σ κ : ℝ) (t : ℝ) : ℝ := σ * t + κ * max (t - 1) 0

/-- The path `φ(t) = S(t) (A + i B)`. -/
noncomputable def lemma44Path (A B σ κ : ℝ) (t : ℝ≥0) : ℂ :=
  ((A * lemma44Profile σ κ t : ℝ) : ℂ) + ((B * lemma44Profile σ κ t : ℝ) : ℂ) * Complex.I

theorem lemma44Path_re (A B σ κ : ℝ) (t : ℝ≥0) :
    (lemma44Path A B σ κ t).re = A * lemma44Profile σ κ t := by
  simp [lemma44Path]

theorem lemma44Path_im (A B σ κ : ℝ) (t : ℝ≥0) :
    (lemma44Path A B σ κ t).im = B * lemma44Profile σ κ t := by
  simp [lemma44Path]

theorem continuous_lemma44Path (A B σ κ : ℝ) : Continuous (lemma44Path A B σ κ) := by
  unfold lemma44Path lemma44Profile
  fun_prop

theorem lemma44Path_zero (A B σ κ : ℝ) : lemma44Path A B σ κ 0 = 0 := by
  simp [lemma44Path, lemma44Profile]

/-- The path `φ` lies in the range of `Σ = covMatrix a b c`: for `0 ≤ c`, `c² ≤ a b`,
`Σ (s B, s A) / (A B + c) = s (A, B)` with `A = √a`, `B = √b`. -/
theorem lemma44Path_mem_range {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc0 : 0 ≤ c)
    (σ κ : ℝ) (t : ℝ≥0) :
    ∃ v : Fin 2 → ℝ, (covMatrix a b c).mulVec v 0 = (lemma44Path (√a) (√b) σ κ t).re ∧
      (covMatrix a b c).mulVec v 1 = (lemma44Path (√a) (√b) σ κ t).im := by
  have hA : 0 < √a := Real.sqrt_pos.2 ha
  have hB : 0 < √b := Real.sqrt_pos.2 hb
  have hAA : √a * √a = a := Real.mul_self_sqrt ha.le
  have hBB : √b * √b = b := Real.mul_self_sqrt hb.le
  have hpos : 0 < √a * √b + c := by positivity
  simp only [lemma44Path_re, lemma44Path_im]
  generalize lemma44Profile σ κ t = s
  refine ⟨![s * √b / (√a * √b + c), s * √a / (√a * √b + c)], ?_, ?_⟩
  · simp [covMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    linear_combination (-(s * √b)) * hAA
  · simp [covMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    linear_combination (-(s * √a)) * hBB

/-- Closeness of `V` to `φ` on `[0, 2]`, componentwise. -/
theorem lemma44_close {A B σ κ : ℝ} {V : ℝ≥0 → ℂ}
    (hV : ∀ t ≤ 2, ‖V t - lemma44Path A B σ κ t‖ < 1) {t : ℝ≥0} (ht : t ≤ 2) :
    |(V t).re - A * lemma44Profile σ κ t| < 1 ∧ |(V t).im - B * lemma44Profile σ κ t| < 1 := by
  have h := hV t ht
  refine ⟨lt_of_le_of_lt ?_ h, lt_of_le_of_lt ?_ h⟩
  · have := Complex.abs_re_le_norm (V t - lemma44Path A B σ κ t)
    rwa [Complex.sub_re, lemma44Path_re] at this
  · have := Complex.abs_im_le_norm (V t - lemma44Path A B σ κ t)
    rwa [Complex.sub_im, lemma44Path_im] at this

/-- Closeness of `V` to `φ` at real times `r ∈ [0, 2]`. -/
theorem lemma44_close_real {A B σ κ : ℝ} {V : ℝ≥0 → ℂ}
    (hV : ∀ t ≤ 2, ‖V t - lemma44Path A B σ κ t‖ < 1) {r : ℝ} (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    |(V r.toNNReal).re - A * lemma44Profile σ κ r| < 1 ∧
      |(V r.toNNReal).im - B * lemma44Profile σ κ r| < 1 := by
  have h := lemma44_close hV (t := r.toNNReal)
    (by rw [Real.toNNReal_le_iff_le_coe]; simpa using hr2)
  simpa [Real.coe_toNNReal r hr0] using h

section Core

variable {A B σ κ C : ℝ}

/-- **The bootstrap step** (Lemma 4.4, paper.tex:L2118-2138): along a Loewner solution `γ` on
`[0, b]`, `b ≤ 2`, from `z` with `2 C - 1 ≤ Re z`, `|Im z| ≤ 1`, one has `‖γ - V‖ ≥ 1`. -/
theorem lemma44_step (hA : 0 < A) (hB : 0 < B) (hσ : B * σ = 10) (hκ : 0 ≤ κ)
    (hC1 : 6 + A * σ ≤ 2 * C) {V : ℝ≥0 → ℂ} (hVc : Continuous V)
    (hV : ∀ t ≤ 2, ‖V t - lemma44Path A B σ κ t‖ < 1) {z : ℂ} (hz1 : 2 * C - 1 ≤ z.re)
    (hz2 : |z.im| ≤ 1) {b : ℝ} (hb2 : b ≤ 2) {γ : ℝ → ℂ} (hγ0 : γ 0 = z)
    (hγ : ClosedSol (fun s => V s.toNNReal) b γ) :
    ∀ r ∈ Icc 0 b, 1 ≤ ‖γ r - V r.toNNReal‖ := by
  have hσpos : 0 < σ := by
    by_contra h
    push Not at h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hB.le h]
  have hAσ : 0 < A * σ := mul_pos hA hσpos
  refine bootstrap_Icc (g := fun r => ‖γ r - V r.toNNReal‖) ?_ ?_ ?_
  · refine ContinuousOn.norm (ContinuousOn.sub ?_ ?_)
    · exact fun r hr => (hγ r hr).2.continuousWithinAt
    · exact (hVc.comp continuous_real_toNNReal).continuousOn
  · have h0 := lemma44_close_real hV (r := 0) le_rfl (by norm_num)
    have hS0 : lemma44Profile σ κ 0 = 0 := by simp [lemma44Profile]
    rw [hS0, mul_zero, sub_zero] at h0
    have hre := (abs_lt.1 h0.1).2
    have := Complex.re_le_norm (γ 0 - V (0 : ℝ).toNNReal)
    simp only [hγ0, Complex.sub_re] at this ⊢
    linarith
  · intro x hx hf
    have hx0 : 0 ≤ x := hx.1
    have hxb : x < b := hx.2
    have hdrift := norm_sub_le_of_closedSol hγ hx0 hxb.le hf
    rw [hγ0] at hdrift
    have hre := Complex.abs_re_le_norm (γ x - z)
    have him := Complex.abs_im_le_norm (γ x - z)
    rw [Complex.sub_re] at hre
    rw [Complex.sub_im] at him
    have hre' := (abs_le.1 (hre.trans hdrift)).1
    have him' := (abs_le.1 (him.trans hdrift)).2
    have hcl := lemma44_close_real hV hx0 (hxb.le.trans hb2)
    have hVre := (abs_lt.1 hcl.1).2
    have hVim := (abs_lt.1 hcl.2).1
    have hz2' := (abs_le.1 hz2).2
    change 1 < ‖γ x - V x.toNNReal‖
    rcases le_or_gt x 1 with hx1 | hx1
    · have hS : lemma44Profile σ κ x = σ * x := by
        simp [lemma44Profile, max_eq_right (by linarith : x - 1 ≤ 0)]
      rw [hS] at hVre
      have h1 : A * (σ * x) ≤ A * σ := by
        rw [← mul_assoc]; exact mul_le_of_le_one_right hAσ.le hx1
      have := Complex.re_le_norm (γ x - V x.toNNReal)
      rw [Complex.sub_re] at this
      linarith
    · have hS : lemma44Profile σ κ x = σ * x + κ * (x - 1) := by
        simp [lemma44Profile, max_eq_left (by linarith : 0 ≤ x - 1)]
      rw [hS] at hVim
      have h1 : B * σ ≤ B * (σ * x + κ * (x - 1)) := by
        have : σ ≤ σ * x := by nlinarith
        have : 0 ≤ κ * (x - 1) := mul_nonneg hκ (by linarith)
        nlinarith
      have := Complex.abs_im_le_norm (γ x - V x.toNNReal)
      rw [Complex.sub_im] at this
      have h2 := neg_abs_le ((γ x).im - (V x.toNNReal).im)
      have hx2 : x ≤ 2 := hxb.le.trans hb2
      linarith

/-- **Existence on `[0, 2]`.** Under the hypotheses of `lemma44_step`, the Loewner equation
driven by `V` has a solution on `[0, 2]` from `z`. -/
theorem lemma44_exists_closedSol (hA : 0 < A) (hB : 0 < B) (hσ : B * σ = 10) (hκ : 0 ≤ κ)
    (hC1 : 6 + A * σ ≤ 2 * C) {V : ℝ≥0 → ℂ} (hVc : Continuous V)
    (hV : ∀ t ≤ 2, ‖V t - lemma44Path A B σ κ t‖ < 1) {z : ℂ} (hz1 : 2 * C - 1 ≤ z.re)
    (hz2 : |z.im| ≤ 1) :
    ∃ γ : ℝ → ℂ, γ 0 = z ∧ ClosedSol (fun s => V s.toNNReal) ((2 : ℝ≥0) : ℝ) γ := by
  obtain ⟨γ, hγ, -⟩ := loewnerMap_exists_solution V hVc z
  have hz0 : z ≠ V 0 := by
    intro h
    have h0 := lemma44_close_real hV (r := 0) le_rfl (by norm_num)
    have hS0 : lemma44Profile σ κ 0 = 0 := by simp [lemma44Profile]
    rw [hS0, mul_zero, sub_zero] at h0
    have hre := (abs_lt.1 h0.1).2
    have hσpos : 0 < σ := by
      by_contra h'
      push Not at h'
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hB.le h']
    have : 0 < A * σ := mul_pos hA hσpos
    simp only [Real.toNNReal_zero] at hre
    rw [← h] at hre
    linarith
  have hpos : 0 < absorbingTime V z := absorbingTime_pos_of_ne hVc hz0
  have hlt : (2 : ℝ≥0∞) < absorbingTime V z := by
    by_contra hle
    push Not at hle
    have hne : absorbingTime V z ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofNat_ne_top hle
    have hτ : ENNReal.ofReal (absorbingTime V z).toReal = absorbingTime V z :=
      ENNReal.ofReal_toReal hne
    have hτpos : 0 < (absorbingTime V z).toReal := ENNReal.toReal_pos hpos.ne' hne
    have hτ2 : (absorbingTime V z).toReal ≤ 2 := by
      have := ENNReal.toReal_mono ENNReal.ofNat_ne_top hle
      simpa using this
    have hγ' := hγ
    rw [← hτ] at hγ'
    have hbig := lt_absorbingTime_of_norm_sub_ge hVc hτpos hγ' (a := 0) hτpos one_pos
      (fun s hs => by
        have hcs := closedSol_of_isLoewnerSolution hγ' (t := s.toNNReal) (by
          change ENNReal.ofReal s < _
          exact (ENNReal.ofReal_lt_ofReal_iff hτpos).2 hs.2)
        rw [Real.coe_toNNReal s hs.1] at hcs
        exact lemma44_step hA hB hσ hκ hC1 hVc hV hz1 hz2 (hs.2.le.trans hτ2) hγ.1 hcs s
          ⟨hs.1, le_rfl⟩)
    rw [hτ] at hbig
    exact lt_irrefl _ hbig
  exact ⟨γ, hγ.1, closedSol_of_isLoewnerSolution hγ (t := 2) hlt⟩

/-- **Lemma 4.4–4.6, deterministic form, with explicit parameters.** The conclusion of
`exists_lemma44_path` for the path `lemma44Path A B σ κ`, assuming the arithmetic relations
between `A B σ κ C`. -/
theorem lemma44_estimate (hA : 0 < A) (hB : 0 < B) (hσ : B * σ = 10) (hκ : 0 ≤ κ)
    (hC1 : 6 + A * σ ≤ 2 * C) (hC4 : 4 ≤ C) (hCA : A * (2 * σ + κ) = 9 * C / 2)
    {V : ℝ≥0 → ℂ} (hVc : Continuous V)
    (hV : ∀ t ≤ 2, ‖V t - lemma44Path A B σ κ t‖ < 1) {z : ℂ} (hz1 : 2 * C - 1 ≤ z.re)
    (hz2 : |z.im| ≤ 1) :
    ∃ h : z ∈ (leftHull V 2)ᶜ,
      z.re - 6 * C ≤ (centeredLoewnerMap V hVc 2 ⟨z, h⟩).re ∧
      (centeredLoewnerMap V hVc 2 ⟨z, h⟩).re ≤ z.re - 3 * C ∧
      |(centeredLoewnerMap V hVc 2 ⟨z, h⟩).im| ≤ 6 + B * (2 * σ + κ) := by
  obtain ⟨γ, hγ0, hγ⟩ := lemma44_exists_closedSol hA hB hσ hκ hC1 hVc hV hz1 hz2
  have hmem : z ∈ (leftHull V 2)ᶜ :=
    (notMem_leftHull_iff_exists_closedSol hVc 2 z).2 ⟨γ, hγ0, hγ⟩
  refine ⟨hmem, ?_⟩
  rw [centeredLoewnerMap_eq_of_closedSol hVc hγ0 hγ hmem]
  have hb2 : ((2 : ℝ≥0) : ℝ) ≤ 2 := by simp
  have hfloor := lemma44_step hA hB hσ hκ hC1 hVc hV hz1 hz2 hb2 hγ0 hγ
  have hdrift := norm_sub_le_of_closedSol hγ (x := ((2 : ℝ≥0) : ℝ)) (by simp) le_rfl hfloor
  rw [hγ0] at hdrift
  have hcl := lemma44_close (A := A) (B := B) (σ := σ) (κ := κ) hV (t := 2) le_rfl
  have hS2 : lemma44Profile σ κ ((2 : ℝ≥0) : ℝ) = 2 * σ + κ := by
    simp [lemma44Profile]
    norm_num
    ring
  rw [hS2] at hcl
  have hre := Complex.abs_re_le_norm (γ ((2 : ℝ≥0) : ℝ) - z)
  have him := Complex.abs_im_le_norm (γ ((2 : ℝ≥0) : ℝ) - z)
  rw [Complex.sub_re] at hre
  rw [Complex.sub_im] at him
  have hd4 : ‖γ ((2 : ℝ≥0) : ℝ) - z‖ ≤ 4 := by
    have := hdrift
    norm_num at this ⊢
    linarith
  have hre' := abs_le.1 (hre.trans hd4)
  have him' := abs_le.1 (him.trans hd4)
  have hVre := abs_lt.1 hcl.1
  have hVim := abs_lt.1 hcl.2
  have hz2' := abs_le.1 hz2
  have hBS : 0 ≤ B * (2 * σ + κ) := by
    have : 0 < 2 * σ + κ := by
      by_contra h'
      push Not at h'
      nlinarith
    positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [Complex.sub_re]; linarith
  · rw [Complex.sub_re]; linarith
  · rw [Complex.sub_im, abs_le]
    constructor <;> linarith

end Core

/-- **Lemmas 4.4–4.6 in deterministic form** (paper.tex:L2036-2138). For `0 < a, b`, `0 ≤ c`,
`c² ≤ a b` there is a continuous path `φ` with `φ 0 = 0` in the range of `Σ = covMatrix a b c`
(the hypothesis `hφS` of the support theorem `External.support_sleDriver`) and constants
`C ≥ 2`, `M`, `η > 0` such that for every continuous driver `V` with `‖V t - φ t‖ < η` on
`[0, 2]` and every `z` with `2 C - 1 ≤ Re z ≤ 7 C + 1`, `|Im z| ≤ 1`: `z ∉ L₂^V`,
`Re z - 6 C ≤ Re f₂^V (z) ≤ Re z - 3 C` and `|Im f₂^V (z)| ≤ M`. -/
theorem exists_lemma44_path (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc0 : 0 ≤ c)
    (_hc : c ^ 2 ≤ a * b) :
    ∃ (φ : ℝ≥0 → ℂ) (C M η : ℝ), Continuous φ ∧ φ 0 = 0 ∧
      (∀ t, ∃ v : Fin 2 → ℝ, (covMatrix a b c).mulVec v 0 = (φ t).re ∧
        (covMatrix a b c).mulVec v 1 = (φ t).im) ∧
      2 ≤ C ∧ 0 < η ∧
      ∀ (V : ℝ≥0 → ℂ) (hV : Continuous V), (∀ t ≤ 2, ‖V t - φ t‖ < η) →
        ∀ z : ℂ, 2 * C - 1 ≤ z.re → z.re ≤ 7 * C + 1 → |z.im| ≤ 1 →
          ∃ h : z ∈ (leftHull V 2)ᶜ,
            z.re - 6 * C ≤ (centeredLoewnerMap V hV 2 ⟨z, h⟩).re ∧
            (centeredLoewnerMap V hV 2 ⟨z, h⟩).re ≤ z.re - 3 * C ∧
            |(centeredLoewnerMap V hV 2 ⟨z, h⟩).im| ≤ M := by
  have hA : 0 < √a := Real.sqrt_pos.2 ha
  have hB : 0 < √b := Real.sqrt_pos.2 hb
  set A := √a with hAdef
  set B := √b with hBdef
  set σ : ℝ := 10 / B with hσdef
  set C : ℝ := 4 + 5 * A / B with hCdef
  set κ : ℝ := 9 * C / (2 * A) - 2 * σ with hκdef
  have hσ : B * σ = 10 := by rw [hσdef]; field_simp
  have hAσ : A * σ = 10 * A / B := by rw [hσdef]; field_simp
  have hC4 : 4 ≤ C := by
    have : 0 ≤ 5 * A / B := by positivity
    rw [hCdef]
    linarith
  have hC1 : 6 + A * σ ≤ 2 * C := by
    rw [hAσ, hCdef]
    have : 2 * (5 * A / B) = 10 * A / B := by ring
    linarith
  have hκ : 0 ≤ κ := by
    have : κ = 18 / A + 5 / (2 * B) := by
      rw [hκdef, hCdef, hσdef]; field_simp; ring
    rw [this]; positivity
  have hCA : A * (2 * σ + κ) = 9 * C / 2 := by
    rw [hκdef]; field_simp; ring
  refine ⟨lemma44Path A B σ κ, C, 6 + B * (2 * σ + κ), 1, continuous_lemma44Path A B σ κ,
    lemma44Path_zero A B σ κ, lemma44Path_mem_range ha hb hc0 σ κ, by linarith, one_pos, ?_⟩
  intro V hV hVclose z hz1 _ hz2
  exact lemma44_estimate hA hB hσ hκ hC1 hC4 hCA hV hVclose hz1 hz2

end ComplexSLE.Internal

end
