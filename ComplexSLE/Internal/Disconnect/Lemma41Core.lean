/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Disconnect.Lemma41Hull
public import ComplexSLE.Internal.Disconnect.Lemma44
public import ComplexSLE.Internal.Disconnect.LineApprox
public import ComplexSLE.Frozen.Defs.CovMatrix
import ComplexSLE.Infrastructure.Planar.Separation
import ComplexSLE.Infrastructure.Planar.Pullback
import ComplexSLE.Frozen.Concatenation_LeftHull
import ComplexSLE.Frozen.Lemma_2_4_RightHull
import ComplexSLE.Internal.Phases.KoebeHit

/-!
# Lemma 4.1, deterministic core

arXiv:2203.07313v4, Lemma 4.1 (`lem-disconnect-2`, paper.tex:L1960-1963), proof L2159-2195, with
the two-scale choice of `U^±` of ERRATA.md R20 (small balls around preimages of `2 C ± i / 2`
under the zero-driver map).

`lemma41_core`: for `0 < a, b`, `0 ≤ c`, `c² ≤ a b` there are a path `φ` (Lemma 4.4), times
`T, K` and constants `η₁, η₂, η₃, r > 0`, points `p₁, p₂` such that every continuous driver `u`
which is uniformly small on `[0, T]` (`E1`), uniformly close to `φ` after time `T` on `[0, 2]`
(`E23`) and uniformly small after time `2 + T` on `[0, K]` (`E4`) has `L_{K+2+T}(u)` disjoint from
one of `B_r(p_±)` and disconnecting it from infinity.

The proof is deterministic; the three events are the three events of the paper.
-/

public section

open scoped NNReal
open Set Metric ComplexSLE

namespace ComplexSLE.Internal

theorem isClosed_slitI (T : ℝ≥0) : IsClosed (slitI T) := by
  have : slitI T = {z | z.re = 0 ∧ z.im ^ 2 ≤ 4 * (T : ℝ)} := by
    ext z
    exact mem_slitI_iff
  rw [this]
  exact (isClosed_eq Complex.continuous_re continuous_const).inter
    (isClosed_le ((Complex.continuous_im).pow 2) continuous_const)

theorem abs_re_lt_of_infDist_slitI {T : ℝ≥0} {z : ℂ} {δ : ℝ} (h : infDist z (slitI T) < δ) :
    |z.re| < δ := by
  refine lt_of_le_of_lt ?_ h
  rw [Metric.le_infDist ⟨0, zero_mem_slitI T⟩]
  intro y hy
  have h1 := Complex.abs_re_le_norm (z - y)
  rw [Complex.sub_re, (mem_slitI_iff.1 hy).1, sub_zero] at h1
  rwa [dist_eq_norm]

theorem abs_im_lt_of_infDist_slitR {T : ℝ≥0} {z : ℂ} {δ : ℝ} (h : infDist z (slitR T) < δ) :
    |z.im| < δ := by
  refine lt_of_le_of_lt ?_ h
  rw [Metric.le_infDist ⟨0, zero_mem_slitR T⟩]
  intro y hy
  have h1 := Complex.abs_im_le_norm (z - y)
  rw [Complex.sub_im, (mem_slitR_iff.1 hy).1, sub_zero] at h1
  rwa [dist_eq_norm]

/-- **Lemma 4.1, deterministic core.** -/
theorem lemma41_core (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc0 : 0 ≤ c) (hc : c ^ 2 ≤ a * b) :
    ∃ (φ : ℝ≥0 → ℂ) (T K : ℝ≥0) (η₁ η₂ η₃ r : ℝ) (p₁ p₂ : ℂ),
      Continuous φ ∧ φ 0 = 0 ∧
      (∀ t, ∃ v : Fin 2 → ℝ, (covMatrix a b c).mulVec v 0 = (φ t).re ∧
        (covMatrix a b c).mulVec v 1 = (φ t).im) ∧
      0 < η₁ ∧ 0 < η₂ ∧ 0 < η₃ ∧ 0 < r ∧
      ∀ u : ℝ≥0 → ℂ, Continuous u →
        (∀ t ≤ T, ‖u t‖ < η₁) → (∀ t ≤ 2, ‖u (t + T) - u T - φ t‖ < η₂) →
        (∀ t ≤ K, ‖u (t + (2 + T)) - u (2 + T)‖ < η₃) →
        (Disjoint (ball p₁ r) (leftHull u (K + 2 + T)) ∧
          DisconnectsFromInfinity (leftHull u (K + 2 + T)) (ball p₁ r)) ∨
        (Disjoint (ball p₂ r) (leftHull u (K + 2 + T)) ∧
          DisconnectsFromInfinity (leftHull u (K + 2 + T)) (ball p₂ r)) := by
  obtain ⟨φ, C, M₀, η₂, hφc, hφ0, hφS, hC, hη₂, h44⟩ := exists_lemma44_path a b c ha hb hc0 hc
  set M : ℝ := max M₀ 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  -- the time `T`
  set T : ℝ≥0 := ⟨((7 * C + 4) / 2) ^ 2, sq_nonneg _⟩ with hTdef
  have hsqrtT : Real.sqrt (T : ℝ) = (7 * C + 4) / 2 := by
    have : (T : ℝ) = ((7 * C + 4) / 2) ^ 2 := rfl
    rw [this, Real.sqrt_sq (by linarith)]
  have hTpos : 0 < T := by
    rw [← NNReal.coe_pos]
    change 0 < ((7 * C + 4) / 2) ^ 2
    have : 0 < (7 * C + 4) / 2 := by linarith
    positivity
  -- the target points
  set wp : ℂ := ((2 * C : ℝ) : ℂ) + 2 * ((1 / 4 : ℝ) : ℂ) * Complex.I with hwp
  set wm : ℂ := ((2 * C : ℝ) : ℂ) - 2 * ((1 / 4 : ℝ) : ℂ) * Complex.I with hwm
  have hwp_notin : wp ∉ slitR T := fun h => by
    have := (mem_slitR_iff.1 h).1
    simp [hwp] at this
  have hwm_notin : wm ∉ slitR T := fun h => by
    have := (mem_slitR_iff.1 h).1
    simp [hwm] at this
  obtain ⟨pp, hpp_slit, hpp⟩ := exists_zeroMap_eq hwp_notin
  obtain ⟨pm, hpm_slit, hpm⟩ := exists_zeroMap_eq hwm_notin
  have hSc : IsClosed (slitI T) := isClosed_slitI T
  have hSne : (slitI T).Nonempty := ⟨0, zero_mem_slitI T⟩
  have hdp : 0 < infDist pp (slitI T) := (hSc.notMem_iff_infDist_pos hSne).1 hpp_slit
  have hdm : 0 < infDist pm (slitI T) := (hSc.notMem_iff_infDist_pos hSne).1 hpm_slit
  set d : ℝ := min (infDist pp (slitI T)) (infDist pm (slitI T)) with hd
  have hdpos : 0 < d := lt_min hdp hdm
  obtain ⟨rp, hrp, hrp'⟩ := Metric.continuousAt_iff.1
    (differentiableAt_zeroMap hpp_slit).continuousAt (1 / 8) (by norm_num)
  obtain ⟨rm, hrm, hrm'⟩ := Metric.continuousAt_iff.1
    (differentiableAt_zeroMap hpm_slit).continuousAt (1 / 8) (by norm_num)
  set r : ℝ := min (min rp rm) (d / 4) with hr
  have hrpos : 0 < r := lt_min (lt_min hrp hrm) (by linarith)
  set δ : ℝ := min (d / 2) (1 / 8) with hδ
  have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδd : δ ≤ d / 2 := min_le_left _ _
  have hδ8 : δ ≤ 1 / 8 := min_le_right _ _
  obtain ⟨η₁, hη₁, hlineT⟩ := lineApprox T hTpos δ hδpos
  -- the time `K`
  set K : ℝ≥0 := ⟨((M + 4) / 2) ^ 2, sq_nonneg _⟩ with hKdef
  have hsqrtK : Real.sqrt (K : ℝ) = (M + 4) / 2 := by
    have : (K : ℝ) = ((M + 4) / 2) ^ 2 := rfl
    rw [this, Real.sqrt_sq (by linarith)]
  have hKpos : 0 < K := by
    rw [← NNReal.coe_pos]
    change 0 < ((M + 4) / 2) ^ 2
    have : 0 < (M + 4) / 2 := by linarith
    positivity
  obtain ⟨η₃, hη₃, hlineK⟩ := lineApprox K hKpos (1 / 2) (by norm_num)
  refine ⟨φ, T, K, η₁, η₂, η₃, r, pp, pm, hφc, hφ0, hφS, hη₁, hη₂, hη₃, hrpos, ?_⟩
  intro u hu E1 E23 E4
  -- the shifted drivers
  set W : ℝ≥0 → ℂ := fun t => u (t + T) - u T with hWdef
  have hW : Continuous W := (hu.comp (continuous_id.add continuous_const)).sub continuous_const
  have hW0 : W 0 = 0 := by simp [hWdef]
  set W' : ℝ≥0 → ℂ := fun t => W (t + 2) - W 2 with hW'def
  have hW' : Continuous W' := (hW.comp (continuous_id.add continuous_const)).sub continuous_const
  have hW'small : ∀ t ≤ K, ‖W' t‖ < η₃ := by
    intro t ht
    have e : W' t = u (t + (2 + T)) - u (2 + T) := by
      simp only [hW'def, hWdef]
      rw [add_assoc]
      ring
    rw [e]
    exact E4 t ht
  -- Lemma 4.4 for `W`
  have h44W : ∀ z : ℂ, 2 * C - 1 ≤ z.re → z.re ≤ 7 * C + 1 → |z.im| ≤ 1 →
      ∃ h : z ∈ (leftHull W 2)ᶜ, z.re - 6 * C ≤ (centeredLoewnerMap W hW 2 ⟨z, h⟩).re ∧
        (centeredLoewnerMap W hW 2 ⟨z, h⟩).re ≤ z.re - 3 * C ∧
        |(centeredLoewnerMap W hW 2 ⟨z, h⟩).im| ≤ M := by
    intro z h1 h2 h3
    obtain ⟨h, a1, a2, a3⟩ := h44 W hW E23 z h1 h2 h3
    exact ⟨h, a1, a2, a3.trans (le_max_left _ _)⟩
  -- Lemma 4.2/4.3 for `u` at `T` and for `W'` at `K`
  obtain ⟨hL1, hR1, -, -, hRtip, -, hfT⟩ := hlineT u hu E1
  obtain ⟨hL1', -, htop, hbot, -, -, -⟩ := hlineK W' hW' hW'small
  have hB : ∀ w ∈ leftHull W' K, |w.re| < 1 / 2 := fun w hw =>
    abs_re_lt_of_infDist_slitI (hL1' w hw)
  have hb₁ : ∃ b ∈ leftHull W' K, M + 2 < b.im := by
    obtain ⟨z, hz, hzim⟩ := htop
    rw [hsqrtK] at hzim
    exact ⟨z, hz, by linarith⟩
  have hb₂ : ∃ b ∈ leftHull W' K, b.im < -(M + 2) := by
    obtain ⟨z, hz, hzim⟩ := hbot
    rw [hsqrtK] at hzim
    exact ⟨z, hz, by linarith⟩
  -- the right hull `R = R_T(u)`
  have hRcpt : IsCompact (rightHull u hu T) := isCompact_rightHull hu T
  have hRc : IsPreconnected (rightHull u hu T) := (lemma_2_4_rightHull u hu T).isPreconnected
  have hR0 : (0 : ℂ) ∈ rightHull u hu T := zero_mem_rightHull hu T
  have hRimδ : ∀ w ∈ rightHull u hu T, |w.im| < δ := fun w hw =>
    abs_im_lt_of_infDist_slitR (hR1 w hw)
  obtain ⟨q, hqR, hq⟩ := hRtip
  rw [hsqrtT] at hq
  obtain ⟨hL'c, hL'conn, hL'0, hL'ball, β, hβR, hβL', hβre⟩ := lemma41_hull_side hW hW0 hC
    (K := K) h44W hB hb₁ hb₂ hRcpt hRc hR0 hqR (by linarith)
    (fun w hw => (hRimδ w hw).trans_le (hδ8.trans (by norm_num)))
  -- the images of the small balls under `f_T`
  have key : ∀ (p w : ℂ), d ≤ infDist p (slitI T) → zeroMap T p = w →
      (∀ x, dist x p < r → dist (zeroMap T x) (zeroMap T p) < 1 / 8) →
      ∀ z ∈ ball p r, ∃ h : z ∈ (leftHull u T)ᶜ,
        centeredLoewnerMap u hu T ⟨z, h⟩ ∈ ball w (1 / 4) := by
    intro p w hdp hpw hcont z hz
    have hz' := mem_ball.1 hz
    have hrd : r ≤ d / 4 := min_le_right _ _
    have hfar : δ ≤ infDist z (slitI T) := by
      have := infDist_le_infDist_add_dist (x := p) (y := z) (s := slitI T)
      rw [dist_comm] at this
      linarith
    have hnot : z ∈ (leftHull u T)ᶜ := fun hzL => by
      have := hL1 z hzL
      linarith
    refine ⟨hnot, ?_⟩
    have h1 := hfT z hnot hfar
    have h2 := hcont z hz'
    rw [hpw] at h2
    rw [mem_ball, dist_eq_norm]
    rw [dist_eq_norm] at h2
    calc ‖centeredLoewnerMap u hu T ⟨z, hnot⟩ - w‖
        = ‖(centeredLoewnerMap u hu T ⟨z, hnot⟩ - zeroMap T z) + (zeroMap T z - w)‖ := by
          congr 1; ring
      _ ≤ ‖centeredLoewnerMap u hu T ⟨z, hnot⟩ - zeroMap T z‖ + ‖zeroMap T z - w‖ :=
          norm_add_le _ _
      _ < 1 / 4 := by linarith
  have hdp₁ : d ≤ infDist pp (slitI T) := min_le_left _ _
  have hdp₂ : d ≤ infDist pm (slitI T) := min_le_right _ _
  have key₁ := key pp wp hdp₁ hpp (fun x hx => hrp' (hx.trans_le ((min_le_left _ _).trans
    (min_le_left _ _))))
  have key₂ := key pm wm hdp₂ hpm (fun x hx => hrm' (hx.trans_le ((min_le_left _ _).trans
    (min_le_right _ _))))
  -- separation
  have hAim : ∀ w ∈ rightHull u hu T, |w.im| < 1 / 4 := fun w hw =>
    (hRimδ w hw).trans_le (hδ8.trans (by norm_num))
  have hsep : ∀ z₁ ∈ centeredLoewnerMap u hu T '' (Subtype.val ⁻¹' ball pp r),
      ∀ z₂ ∈ centeredLoewnerMap u hu T '' (Subtype.val ⁻¹' ball pm r),
      DisconnectsFromInfinity (rightHull u hu T ∪ leftHull W (K + 2)) {z₁} ∨
        DisconnectsFromInfinity (rightHull u hu T ∪ leftHull W (K + 2)) {z₂} := by
    rintro _ ⟨⟨z₁, hz₁⟩, hz₁b, rfl⟩ _ ⟨⟨z₂, hz₂⟩, hz₂b, rfl⟩
    obtain ⟨h₁, hh₁⟩ := key₁ z₁ hz₁b
    obtain ⟨h₂, hh₂⟩ := key₂ z₂ hz₂b
    exact Planar.disconnectsFromInfinity_of_two_connected hRcpt hRc hL'c hL'conn
      (x0 := 2 * C) (ε := 1 / 4) (by norm_num) hAim hL'ball hR0 hL'0 hβR hβL'
      (by simp only [Complex.zero_re]; linarith) hβre hh₁ hh₂
  -- pullback to `L_{K+2+T}(u)`
  have hconc : leftHull u (K + 2 + T) = leftHull u T ∪
      {z | ∃ h : z ∈ (leftHull u T)ᶜ, centeredLoewnerMap u hu T ⟨z, h⟩ ∈
        leftHull W (K + 2) \ rightHull u hu T} := concatenation_leftHull u hu (K + 2) T
  have hgrowth : ∀ M : ℝ, ∃ M' : ℝ, ∀ z : ↥(leftHull u T)ᶜ, M' ≤ ‖(z : ℂ)‖ →
      M ≤ ‖centeredLoewnerMap u hu T z‖ := fun M => by
    obtain ⟨M', hM'⟩ := centeredLoewnerMap_norm_ge hu T M
    exact ⟨M', fun z hz => hM' z.1 z.2 hz⟩
  have hFR : ∀ z : ↥(leftHull u T)ᶜ, centeredLoewnerMap u hu T z ∉ rightHull u hu T :=
    fun z hmem => hmem ⟨z, rfl⟩
  have hpull : ∀ V : Set ℂ,
      DisconnectsFromInfinity (rightHull u hu T ∪ leftHull W (K + 2))
        (centeredLoewnerMap u hu T '' (Subtype.val ⁻¹' V)) →
      DisconnectsFromInfinity (leftHull u (K + 2 + T)) V := fun V hV => by
    rw [hconc]
    exact Planar.disconnectsFromInfinity_pullback (continuous_centeredLoewnerMap hu T) hFR hgrowth
      hV
  -- finish
  have fin : ∀ (p w : ℂ), (∀ z ∈ ball p r, ∃ h : z ∈ (leftHull u T)ᶜ,
        centeredLoewnerMap u hu T ⟨z, h⟩ ∈ ball w (1 / 4)) → ‖w - ((2 * C : ℝ) : ℂ)‖ ≤ 1 / 2 →
      DisconnectsFromInfinity (rightHull u hu T ∪ leftHull W (K + 2))
        (centeredLoewnerMap u hu T '' (Subtype.val ⁻¹' ball p r)) →
      Disjoint (ball p r) (leftHull u (K + 2 + T)) ∧
        DisconnectsFromInfinity (leftHull u (K + 2 + T)) (ball p r) := by
    intro p w hkey hw hdis
    refine ⟨?_, hpull _ hdis⟩
    refine Set.disjoint_left.2 fun z hzb hzL => ?_
    obtain ⟨h, hh⟩ := hkey z hzb
    rw [hconc] at hzL
    rcases hzL with hzL | ⟨h', hmem⟩
    · exact h hzL
    · have h3 : centeredLoewnerMap u hu T ⟨z, h⟩ ∈ ball ((2 * C : ℝ) : ℂ) (3 * (1 / 4)) := by
        rw [mem_ball, dist_eq_norm] at hh ⊢
        calc ‖centeredLoewnerMap u hu T ⟨z, h⟩ - ((2 * C : ℝ) : ℂ)‖
            = ‖(centeredLoewnerMap u hu T ⟨z, h⟩ - w) + (w - ((2 * C : ℝ) : ℂ))‖ := by
              congr 1; ring
          _ ≤ ‖centeredLoewnerMap u hu T ⟨z, h⟩ - w‖ + ‖w - ((2 * C : ℝ) : ℂ)‖ := norm_add_le _ _
          _ < 3 * (1 / 4) := by linarith
      exact Set.disjoint_left.1 hL'ball hmem.1 h3
  have hwp_close : ‖wp - ((2 * C : ℝ) : ℂ)‖ ≤ 1 / 2 := by
    have : wp - ((2 * C : ℝ) : ℂ) = 2 * ((1 / 4 : ℝ) : ℂ) * Complex.I := by simp [hwp]
    rw [this]
    simp
    norm_num
  have hwm_close : ‖wm - ((2 * C : ℝ) : ℂ)‖ ≤ 1 / 2 := by
    have : wm - ((2 * C : ℝ) : ℂ) = -(2 * ((1 / 4 : ℝ) : ℂ) * Complex.I) := by simp [hwm]
    rw [this]
    simp
    norm_num
  rcases disconnectsFromInfinity_or hsep with h | h
  · exact Or.inl (fin pp wp key₁ hwp_close h)
  · exact Or.inr (fin pm wm key₂ hwm_close h)

end ComplexSLE.Internal

end
