/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.AllZEvents
public import ComplexSLE.Internal.Phases.EventMeasEvents
public import ComplexSLE.Internal.Loewner.Transform
public import ComplexSLE.Internal.Loewner.Injective
public import ComplexSLE.Internal.Hull.ConnectedNoExt
public import ComplexSLE.Internal.Polar.PolarDerivShift
public import Mathlib.Analysis.Complex.OpenMapping

/-!
# The event of Proposition 3.2(a) is scale invariant and future dependent (M7/D2)

Source: paper.tex:L1276-1281 and L1456-1466. The event family of Proposition 3.2(a) in the
R14 `ε`-form is

  `𝓔(z) = {∀ ε > 0, ∃ t < T_z, dist(z, L_t) < ε}`.

Both algebraic hypotheses of Lemma 3.3 hold pathwise for every continuous driver:

* `scaleInvariantEvents_hull_approach`: `T_{rz}(r u(·/r²)) = r² T_z(u)`
  (`absorbingTime_scale`) and `L_t(r u(·/r²)) = r L_{t/r²}(u)` (`leftHull_scale`), and the
  distance scales by `r`.
* `futureDependentEvents_hull_approach`: for `z ∉ L_s`, the event holds for `(u, z)` iff it holds
  for `(V, f_s z)`, `V = u(· + s) - u s`. The proof uses the concatenation (2.3):
  `T_z = s + T^V_{f_s z}` (`absorbingTime_eq_add_shift`) and
  `L_{t + s} ∖ L_s = f_s^{-1}(L^V_t)` (`mem_leftHull_add_iff`),
  together with the facts that `f_s` is holomorphic on the open set `ℂ ∖ L_s`
  (`exists_differentiableOn_extension_loewnerMap`), hence continuous at `z`, and open near `z`
  (open mapping theorem, injectivity of `f_s`, `centeredLoewnerMap_injective`): hence a point of
  `L^V_t` close to `f_s z` is the `f_s`-image of a point of `L_{t+s}` close to `z`, and
  conversely.

No external input is used.
-/

public section

open scoped NNReal ENNReal Topology
open Set Metric Filter

namespace ComplexSLE.Internal

/-! ### Scaling -/

theorem infDist_scale_lt_iff {S : Set ℂ} (hS : S.Nonempty) {r : ℝ≥0} (hr : 0 < r) (z : ℂ)
    (ε : ℝ) :
    infDist ((r : ℂ) * z) ((fun w => (r : ℂ) * w) '' S) < r * ε ↔ infDist z S < ε := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  rw [infDist_lt_iff (hS.image _), infDist_lt_iff hS]
  have hd : ∀ y : ℂ, dist ((r : ℂ) * z) ((r : ℂ) * y) = r * dist z y := fun y => by
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul]
    simp
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, h⟩
    refine ⟨y, hy, ?_⟩
    rw [hd] at h
    exact lt_of_mul_lt_mul_left h hr'.le
  · rintro ⟨y, hy, h⟩
    refine ⟨(r : ℂ) * y, ⟨y, hy, rfl⟩, ?_⟩
    rw [hd]
    exact mul_lt_mul_of_pos_left h hr'

theorem scaleInvariantEvents_hull_approach :
    ScaleInvariantEvents fun u z => ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < absorbingTime u z ∧
      infDist z (leftHull u t) < ε := by
  intro u hu r hr z
  beta_reduce
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hr2 : (r ^ 2 : ℝ≥0) ≠ 0 := by simpa using hr.ne'
  have hr2' : ((r ^ 2 : ℝ≥0) : ℝ≥0∞) ≠ 0 := by simpa using hr.ne'
  rw [absorbingTime_scale u z r hr]
  constructor
  · intro h ε hε
    obtain ⟨t, ht, hd⟩ := h (ε / r) (div_pos hε hr')
    refine ⟨r ^ 2 * t, ?_, ?_⟩
    · rw [ENNReal.coe_mul]
      exact ENNReal.mul_lt_mul_right hr2' ENNReal.coe_ne_top ht
    · rw [leftHull_scale u r hr, mul_div_cancel_left₀ _ hr2]
      have := (infDist_scale_lt_iff (leftHull_nonempty u t) hr z (ε / r)).2 hd
      rwa [mul_div_cancel₀ _ hr'.ne'] at this
  · intro h ε hε
    obtain ⟨t, ht, hd⟩ := h (r * ε) (mul_pos hr' hε)
    refine ⟨t / r ^ 2, ?_, ?_⟩
    · rw [ENNReal.coe_div hr2, ENNReal.div_lt_iff (Or.inl hr2') (Or.inl ENNReal.coe_ne_top),
        mul_comm]
      exact ht
    · rw [leftHull_scale u r hr] at hd
      exact (infDist_scale_lt_iff (leftHull_nonempty u _) hr z ε).1 hd

/-! ### Future dependence -/

section Future

variable {u : ℝ≥0 → ℂ}

/-- `f_s` is continuous at every point of `ℂ ∖ L_s`, and open near it: the image of every
neighbourhood of `z ∈ ℂ ∖ L_s` under the (extended) `g_s` is a neighbourhood of `g_s z`. -/
theorem exists_extension_loewnerMap_nhds (hu : Continuous u) (s : ℝ≥0) (z : ℂ)
    (hz : z ∈ (leftHull u s)ᶜ) :
    ∃ G : ℂ → ℂ, (∀ y : ↥(leftHull u s)ᶜ, G y = loewnerMap u hu s y) ∧
      ContinuousAt G z ∧ ∀ N ∈ 𝓝 z, G '' N ∈ 𝓝 (G z) := by
  obtain ⟨G, hG, hGd⟩ := exists_differentiableOn_extension_loewnerMap hu s
  have hopen : IsOpen (leftHull u s)ᶜ := Polar.isOpen_compl_leftHull u hu s
  have hGa : AnalyticAt ℂ G z := hGd.analyticAt (hopen.mem_nhds hz)
  refine ⟨G, hG, hGa.continuousAt, ?_⟩
  have hinj : Function.Injective (centeredLoewnerMap u hu s) := centeredLoewnerMap_injective hu s
  have hGinj : Set.InjOn G (leftHull u s)ᶜ := by
    intro x hx y hy hxy
    have := @hinj ⟨x, hx⟩ ⟨y, hy⟩ (by
      simp only [centeredLoewnerMap, ← hG, hxy])
    exact congrArg Subtype.val this
  rcases hGa.eventually_constant_or_nhds_le_map_nhds with hconst | hopenmap
  · exfalso
    -- `G` is constant near `z`, contradicting injectivity
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
      (hconst.and (hopen.mem_nhds hz))
    have h1 : z + (ε / 2 : ℝ) ∈ ball z ε := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hε)]
      exact half_lt_self hε
    have h2 : z ∈ ball z ε := mem_ball_self hε
    have := hGinj (hball h1).2 (hball h2).2 (by rw [(hball h1).1, (hball h2).1])
    have h3 : ((ε / 2 : ℝ) : ℂ) = 0 := by simpa using this
    have : (ε / 2 : ℝ) = 0 := by exact_mod_cast h3
    linarith
  · intro N hN
    exact hopenmap (Filter.image_mem_map hN)

/-- **Future dependence of the event of Proposition 3.2(a)**: for `z ∉ L_s`,
`∀ ε > 0, ∃ t < T_z, dist(z, L_t) < ε` holds for `(u, z)` iff it holds for `(V, f_s z)`,
`V = u(· + s) - u s`. -/
theorem futureDependentEvents_hull_approach :
    FutureDependentEvents fun u z => ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < absorbingTime u z ∧
      infDist z (leftHull u t) < ε := by
  intro u hu s z hz
  beta_reduce
  set V : ℝ≥0 → ℂ := fun r => u (r + s) - u s with hV
  set w := centeredLoewnerMap u hu s ⟨z, hz⟩ with hw
  have hT : absorbingTime u z = s + absorbingTime V w := absorbingTime_eq_add_shift hu s z hz
  have hopen := Polar.isOpen_compl_leftHull u hu s
  obtain ⟨G, hG, hGc, hGo⟩ := exists_extension_loewnerMap_nhds hu s z hz
  have hf : ∀ y (hy : y ∈ (leftHull u s)ᶜ),
      centeredLoewnerMap u hu s ⟨y, hy⟩ = G y - u s := fun y hy => by
    simp only [centeredLoewnerMap]
    rw [← hG ⟨y, hy⟩]
  have hGz : G z = w + u s := by rw [hw, hf z hz]; ring
  constructor
  · -- forward
    intro h ε hε
    obtain ⟨δ, hδ, hδb⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem (hopen.mem_nhds hz)
      (hGc.preimage_mem_nhds (Metric.ball_mem_nhds (G z) hε)))
    obtain ⟨t, ht, hd⟩ := h δ hδ
    obtain ⟨y, hyL, hyd⟩ := (infDist_lt_iff (leftHull_nonempty u t)).1 hd
    have hyb : y ∈ ball z δ := by rw [mem_ball, dist_comm]; exact hyd
    obtain ⟨hyc, hyG⟩ := hδb hyb
    have hst : (s : ℝ≥0∞) < absorbingTime u y := notMem_leftHull_iff.1 hyc
    have hyt : absorbingTime u y ≤ t := hyL
    have hs_lt : s < t := by exact_mod_cast hst.trans_le hyt
    have htt : (t - s) + s = t := tsub_add_cancel_of_le hs_lt.le
    refine ⟨t - s, ?_, ?_⟩
    · have : (((t - s) + s : ℝ≥0) : ℝ≥0∞) < s + absorbingTime V w := by
        rw [htt, ← hT]; exact ht
      rw [ENNReal.coe_add, add_comm] at this
      exact (ENNReal.add_lt_add_iff_left ENNReal.coe_ne_top).1 this
    · have hyV : centeredLoewnerMap u hu s ⟨y, hyc⟩ ∈ leftHull V (t - s) :=
        (mem_leftHull_add_iff hu (t - s) s y hyc).1 (by rw [htt]; exact hyL)
      refine lt_of_le_of_lt (infDist_le_dist_of_mem hyV) ?_
      have h1 : dist w (centeredLoewnerMap u hu s ⟨y, hyc⟩) = dist (G z) (G y) := by
        rw [hf y hyc, dist_eq_norm, dist_eq_norm, hGz]
        congr 1; ring
      rw [h1, dist_comm]
      exact mem_ball.1 hyG
  · -- backward
    intro h ε hε
    obtain ⟨δ, hδ, hδb⟩ := Metric.mem_nhds_iff.1 (hopen.mem_nhds hz)
    have hε₁ : 0 < min ε δ := lt_min hε hδ
    obtain ⟨ε', hε', hε'b⟩ := Metric.mem_nhds_iff.1 (hGo _ (ball_mem_nhds z hε₁))
    obtain ⟨t', ht', hd⟩ := h ε' hε'
    obtain ⟨y', hy'L, hy'd⟩ := (infDist_lt_iff (leftHull_nonempty V t')).1 hd
    have hmem : y' + u s ∈ ball (G z) ε' := by
      rw [mem_ball, dist_eq_norm, hGz]
      have : y' + u s - (w + u s) = y' - w := by ring
      rw [this, ← dist_eq_norm, dist_comm]
      exact hy'd
    obtain ⟨y, hyb, hGy⟩ := hε'b hmem
    have hyc : y ∈ (leftHull u s)ᶜ := hδb (ball_subset_ball (min_le_right _ _) hyb)
    have hfy : centeredLoewnerMap u hu s ⟨y, hyc⟩ = y' := by
      rw [hf y hyc, hGy]; ring
    refine ⟨t' + s, ?_, ?_⟩
    · rw [hT, ENNReal.coe_add, add_comm]
      exact (ENNReal.add_lt_add_iff_left ENNReal.coe_ne_top).2 ht'
    · have hyL : y ∈ leftHull u (t' + s) :=
        (mem_leftHull_add_iff hu t' s y hyc).2 (by rw [hfy]; exact hy'L)
      refine lt_of_le_of_lt (infDist_le_dist_of_mem hyL) ?_
      rw [dist_comm]
      exact lt_of_lt_of_le (mem_ball.1 hyb) (min_le_left _ _)

end Future

end ComplexSLE.Internal

end
