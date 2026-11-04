/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Duality.Locality
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import all ComplexSLE.Internal.Loewner.Duality

/-!
# The zero driver: hulls and maps for `U ≡ 0`

arXiv:2203.07313v4, proof of Lemma 4.3 (paper.tex:L2008-2019), deterministic. For the driver
`U ≡ 0` the Loewner equation `γ' = 2 / γ` has the solution `γ s = zeroMap s z`, where
`zeroMap T z = z (1 + 4 T / z²)^(1/2)` (principal branch), because `γ² = z² + 4 s`
(`closedSol_zero_sq`). The solution hits `0` at the time `-z²/4` exactly when `z` lies on the slit
`slitI T = [-2 √T i, 2 √T i]`. We prove:

* `leftHull_zero`: `L^0_T = slitI T`;
* `centeredLoewnerMap_zero`: `f^0_T z = zeroMap T z` for `z ∉ slitI T`;
* `exists_zeroMap_eq`: every `w ∉ slitR T` is `zeroMap T z` for some `z ∉ slitI T`
  (explicit preimage `z = w (1 - 4 T / w²)^(1/2)`);
* `zeroMap_sq`, `differentiableAt_zeroMap`, `zeroMap_mul_deriv`: `zeroMap T z ^ 2 = z ^ 2 + 4 T`
  and `zeroMap T z * (zeroMap T)'(z) = z`.
-/

public section

open scoped NNReal ENNReal
open Set Complex

namespace ComplexSLE.Internal

/-- The vertical slit `[-2 √T i, 2 √T i]` (the hull of the zero driver). -/
@[expose] noncomputable def slitI (T : ℝ≥0) : Set ℂ :=
  segment ℝ (-((2 * Real.sqrt T : ℝ) : ℂ) * I) (((2 * Real.sqrt T : ℝ) : ℂ) * I)

/-- The horizontal slit `[-2 √T, 2 √T]` (the right hull of the zero driver). -/
@[expose] noncomputable def slitR (T : ℝ≥0) : Set ℂ :=
  segment ℝ (-((2 * Real.sqrt T : ℝ) : ℂ)) ((2 * Real.sqrt T : ℝ) : ℂ)

/-- The map `f^0_T`: `zeroMap T z = z (1 + 4 T / z²)^(1/2)` with the principal branch. -/
@[expose] noncomputable def zeroMap (T : ℝ) (z : ℂ) : ℂ :=
  z * (1 + 4 * (T : ℂ) / z ^ 2) ^ (1 / 2 : ℂ)

/-- A symmetric segment through the origin in direction `u`. -/
theorem mem_segment_pm_iff (c : ℝ) (hc : 0 ≤ c) (u z : ℂ) (hu : u ≠ 0) :
    z ∈ segment ℝ (-(c : ℂ) * u) ((c : ℂ) * u) ↔ ∃ x : ℝ, |x| ≤ c ∧ z = (x : ℂ) * u := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨θ, ⟨h0, h1⟩, rfl⟩
    refine ⟨(2 * θ - 1) * c, ?_, ?_⟩
    · rw [abs_mul]
      have : |2 * θ - 1| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
      calc |2 * θ - 1| * |c| ≤ 1 * |c| := by gcongr
        _ = c := by rw [one_mul, abs_of_nonneg hc]
    · simp only [Complex.real_smul]
      push_cast
      ring
  · rintro ⟨x, hx, rfl⟩
    rcases hc.eq_or_lt with rfl | hcpos
    · have : x = 0 := by simpa using hx
      subst this
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩
    · refine ⟨(1 + x / c) / 2, ⟨?_, ?_⟩, ?_⟩
      · have := (abs_le.1 hx).1
        have : -1 ≤ x / c := by rw [le_div_iff₀ hcpos]; linarith
        linarith
      · have := (abs_le.1 hx).2
        have : x / c ≤ 1 := by rw [div_le_iff₀ hcpos]; linarith
        linarith
      · have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
        simp only [Complex.real_smul]
        push_cast
        field_simp
        ring

theorem mem_slitI_iff {T : ℝ≥0} {z : ℂ} : z ∈ slitI T ↔ z.re = 0 ∧ z.im ^ 2 ≤ 4 * T := by
  unfold slitI
  rw [mem_segment_pm_iff _ (by positivity) I z I_ne_zero]
  have hT := Real.sq_sqrt T.coe_nonneg
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨by simp, ?_⟩
    simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    have : x ^ 2 ≤ (2 * √(T:ℝ)) ^ 2 := sq_le_sq' (abs_le.1 hx).1 (abs_le.1 hx).2
    nlinarith
  · rintro ⟨h0, h⟩
    refine ⟨z.im, abs_le_of_sq_le_sq (by nlinarith) (by positivity), ?_⟩
    apply Complex.ext <;> simp [h0]

theorem mem_slitR_iff {T : ℝ≥0} {z : ℂ} : z ∈ slitR T ↔ z.im = 0 ∧ z.re ^ 2 ≤ 4 * T := by
  have := mem_segment_pm_iff (2 * Real.sqrt T) (by positivity) 1 z one_ne_zero
  simp only [mul_one] at this
  unfold slitR
  rw [this]
  have hT := Real.sq_sqrt T.coe_nonneg
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨by simp, ?_⟩
    simp only [ofReal_re]
    have : x ^ 2 ≤ (2 * √(T:ℝ)) ^ 2 := sq_le_sq' (abs_le.1 hx).1 (abs_le.1 hx).2
    nlinarith
  · rintro ⟨h0, h⟩
    refine ⟨z.re, abs_le_of_sq_le_sq (by nlinarith) (by positivity), ?_⟩
    apply Complex.ext <;> simp [h0]

theorem zero_mem_slitI (T : ℝ≥0) : (0 : ℂ) ∈ slitI T := by
  rw [mem_slitI_iff]; simp

theorem zero_mem_slitR (T : ℝ≥0) : (0 : ℂ) ∈ slitR T := by
  rw [mem_slitR_iff]; simp

theorem mem_slitI_iff_sq {T : ℝ≥0} {z : ℂ} :
    z ∈ slitI T ↔ (z ^ 2).im = 0 ∧ -(4 * (T : ℝ)) ≤ (z ^ 2).re ∧ (z ^ 2).re ≤ 0 := by
  rw [mem_slitI_iff]
  simp only [pow_two, mul_re, mul_im]
  constructor
  · rintro ⟨h0, h⟩
    rw [h0]
    refine ⟨by ring, by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2, h3⟩
    have : z.re = 0 := by
      rcases mul_eq_zero.1 (show z.re * z.im = 0 by linarith) with h | h
      · exact h
      · rw [h] at h3; nlinarith
    exact ⟨this, by rw [this] at h2; nlinarith⟩

theorem mem_slitR_iff_sq {T : ℝ≥0} {z : ℂ} :
    z ∈ slitR T ↔ (z ^ 2).im = 0 ∧ 0 ≤ (z ^ 2).re ∧ (z ^ 2).re ≤ 4 * (T : ℝ) := by
  rw [mem_slitR_iff]
  simp only [pow_two, mul_re, mul_im]
  constructor
  · rintro ⟨h0, h⟩
    rw [h0]
    refine ⟨by ring, by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2, h3⟩
    have : z.im = 0 := by
      rcases mul_eq_zero.1 (show z.re * z.im = 0 by linarith) with h | h
      · rw [h] at h2; nlinarith
      · exact h
    exact ⟨this, by rw [this] at h3; nlinarith⟩

theorem mem_slitI_iff_mem_slitR {T : ℝ≥0} {z w : ℂ} (h : w ^ 2 = z ^ 2 + 4 * (T : ℂ)) :
    z ∈ slitI T ↔ w ∈ slitR T := by
  rw [mem_slitI_iff_sq, mem_slitR_iff_sq]
  have hre : (w ^ 2).re = (z ^ 2).re + 4 * (T : ℝ) := by
    rw [h]; simp
  have him : (w ^ 2).im = (z ^ 2).im := by
    rw [h]; simp
  rw [hre, him]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨h1, ?_, ?_⟩ <;> linarith

theorem cpow_half_sq (q : ℂ) : (q ^ (1 / 2 : ℂ)) ^ 2 = q := by
  simp

theorem zeroMap_sq {T : ℝ} {z : ℂ} (hz : z ≠ 0) : zeroMap T z ^ 2 = z ^ 2 + 4 * (T : ℂ) := by
  unfold zeroMap
  rw [mul_pow, cpow_half_sq]
  field_simp

theorem zeroMap_zero_time (z : ℂ) : zeroMap 0 z = z := by
  simp [zeroMap]

theorem ne_zero_of_notMem_slitI {T : ℝ≥0} {z : ℂ} (hz : z ∉ slitI T) : z ≠ 0 :=
  fun h => hz (h ▸ zero_mem_slitI T)

theorem one_add_div_mem_slitPlane {T : ℝ≥0} {s : ℝ} {z : ℂ} (hz : z ∉ slitI T) (hs : 0 ≤ s)
    (hsT : s ≤ T) : 1 + 4 * (s : ℂ) / z ^ 2 ∈ slitPlane := by
  have hz0 : z ≠ 0 := ne_zero_of_notMem_slitI hz
  by_contra hq
  rw [mem_slitPlane_iff] at hq
  push Not at hq
  obtain ⟨hre, him⟩ := hq
  set q := 1 + 4 * (s : ℂ) / z ^ 2 with hqdef
  have hqa : q = ((q.re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using him)
  have key : ((q.re - 1 : ℝ) : ℂ) * z ^ 2 = 4 * s := by
    have : (q.re : ℂ) = 1 + 4 * (s : ℂ) / z ^ 2 := by rw [← hqa]
    push_cast
    rw [this]
    field_simp
    ring
  have hne : q.re - 1 ≠ 0 := by linarith
  have hneg : q.re - 1 < 0 := by linarith
  have hz2 : z ^ 2 = ((4 * s / (q.re - 1) : ℝ) : ℂ) := by
    have h' : (q.re : ℂ) - 1 ≠ 0 := by exact_mod_cast hne
    push_cast at key ⊢
    rw [eq_div_iff h']
    linear_combination key
  apply hz
  rw [mem_slitI_iff_sq, hz2]
  simp only [ofReal_im, ofReal_re]
  refine ⟨trivial, ?_, ?_⟩
  · rw [le_div_iff_of_neg hneg]
    nlinarith
  · exact div_nonpos_of_nonneg_of_nonpos (by positivity) hneg.le

theorem hasDerivAt_zeroMap_real {T : ℝ≥0} {z : ℂ} (hz : z ∉ slitI T) {s : ℝ} (hs : 0 ≤ s)
    (hsT : s ≤ T) : HasDerivAt (fun y : ℝ => zeroMap y z) (2 / zeroMap s z) s := by
  have hz0 : z ≠ 0 := ne_zero_of_notMem_slitI hz
  have hq := one_add_div_mem_slitPlane hz hs hsT
  have hq0 : (1 + 4 * (s : ℂ) / z ^ 2) ≠ 0 := slitPlane_ne_zero hq
  have h1 : HasDerivAt (fun u : ℂ => 1 + 4 * u / z ^ 2) (4 / z ^ 2) (s : ℂ) := by
    simpa using (((hasDerivAt_id (s : ℂ)).const_mul 4).div_const (z ^ 2)).const_add 1
  have h2 := (h1.cpow_const (c := (1 / 2 : ℂ)) hq).const_mul z
  have h3 := h2.comp_ofReal
  have hp : (1 + 4 * (s : ℂ) / z ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    simp [hq0]
  refine HasDerivAt.congr_deriv (f := fun y : ℝ => zeroMap y z) h3 ?_
  have e : (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) := by norm_num
  rw [e, Complex.cpow_neg]
  unfold zeroMap
  field_simp
  ring

theorem closedSol_zeroMap {T : ℝ≥0} {z : ℂ} (hz : z ∉ slitI T) :
    ClosedSol (fun _ => 0) T (fun s => zeroMap s z) := by
  intro s hs
  have hz0 : z ≠ 0 := ne_zero_of_notMem_slitI hz
  refine ⟨?_, ?_⟩
  · have hq := one_add_div_mem_slitPlane hz hs.1 hs.2
    have hq0 : (1 + 4 * (s : ℂ) / z ^ 2) ≠ 0 := slitPlane_ne_zero hq
    unfold zeroMap
    refine mul_ne_zero hz0 ?_
    rw [Ne, Complex.cpow_eq_zero_iff]
    simp [hq0]
  · simpa using (hasDerivAt_zeroMap_real hz hs.1 hs.2).hasDerivWithinAt

theorem closedSol_zero_sq {t : ℝ} {z : ℂ} {γ : ℝ → ℂ} (h0 : γ 0 = z)
    (h : ClosedSol (fun _ => 0) t γ) : ∀ s ∈ Icc 0 t, γ s ^ 2 = z ^ 2 + 4 * (s : ℂ) := by
  have hder : ∀ s ∈ Icc 0 t,
      HasDerivWithinAt (fun s : ℝ => γ s ^ 2 - 4 * (s : ℂ)) 0 (Icc 0 t) s := by
    intro s hs
    obtain ⟨hne, hd⟩ := h s hs
    have hne' : γ s ≠ 0 := by simpa using hne
    have h4 : HasDerivWithinAt (fun s : ℝ => 4 * (s : ℂ)) 4 (Icc 0 t) s := by
      simpa using ((hasDerivWithinAt_id s (Icc 0 t)).ofReal_comp).const_mul (4 : ℂ)
    have := (hd.pow 2).sub h4
    convert this using 1
    simp only [sub_zero] at *
    field_simp
    ring
  intro s hs
  by_cases ht : 0 < t
  · have hc := constant_of_derivWithin_zero (f := fun s : ℝ => γ s ^ 2 - 4 * (s : ℂ))
      (fun x hx => (hder x hx).differentiableWithinAt) (fun x hx => by
        exact (hder x (Ico_subset_Icc_self hx)).derivWithin
          ((uniqueDiffOn_Icc ht) x (Ico_subset_Icc_self hx))) s hs
    simp only [h0, Complex.ofReal_zero, mul_zero, sub_zero] at hc
    linear_combination hc
  · have : s = 0 := le_antisymm (hs.2.trans (not_lt.1 ht)) hs.1
    subst this
    simp [h0]

/-- The hull of the zero driver is the vertical slit. -/
theorem leftHull_zero (T : ℝ≥0) : leftHull (fun _ : ℝ≥0 => (0 : ℂ)) T = slitI T := by
  ext z
  constructor
  · intro hzL
    by_contra hz
    exact ((notMem_leftHull_iff_exists_closedSol (U := fun _ : ℝ≥0 => (0 : ℂ)) continuous_const
      T z).2 ⟨fun s => zeroMap s z, by simpa using zeroMap_zero_time z, closedSol_zeroMap hz⟩) hzL
  · intro hz
    by_contra hzL
    obtain ⟨γ, h0, h⟩ := (notMem_leftHull_iff_exists_closedSol
      (U := fun _ : ℝ≥0 => (0 : ℂ)) continuous_const T z).1 hzL
    have hsq := closedSol_zero_sq h0 h
    rw [mem_slitI_iff_sq] at hz
    obtain ⟨him, hlo, hhi⟩ := hz
    set s0 : ℝ := -(z ^ 2).re / 4 with hs0
    have hs0m : s0 ∈ Icc (0 : ℝ) T := ⟨by rw [hs0]; linarith, by rw [hs0]; linarith⟩
    have hz2 : z ^ 2 = (((z ^ 2).re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using him)
    have h1 : γ s0 ^ 2 = 0 := by
      rw [hsq s0 hs0m, hz2, hs0]
      push_cast
      ring
    exact (h s0 hs0m).1 (by simpa using pow_eq_zero_iff (two_ne_zero) |>.1 h1)

theorem centeredLoewnerMap_zero {T : ℝ≥0} {z : ℂ} (hz : z ∉ slitI T)
    (h : z ∈ (leftHull (fun _ : ℝ≥0 => (0 : ℂ)) T)ᶜ) :
    centeredLoewnerMap (fun _ : ℝ≥0 => (0 : ℂ)) continuous_const T ⟨z, h⟩ = zeroMap T z := by
  have := centeredLoewnerMap_eq_of_closedSol (U := fun _ : ℝ≥0 => (0 : ℂ)) continuous_const
    (t := T) (z := z) (γ := fun s => zeroMap s z) (by simpa using zeroMap_zero_time z)
    (closedSol_zeroMap hz) h
  simpa using this

theorem exists_zeroMap_eq {T : ℝ≥0} {w : ℂ} (hw : w ∉ slitR T) :
    ∃ z : ℂ, z ∉ slitI T ∧ zeroMap T z = w := by
  have hw0 : w ≠ 0 := fun h => hw (h ▸ zero_mem_slitR T)
  set u : ℂ := 1 - 4 * (T : ℂ) / w ^ 2 with hu
  have hu_slit : u ∈ slitPlane := by
    by_contra hq
    rw [mem_slitPlane_iff] at hq
    push Not at hq
    obtain ⟨hre, him⟩ := hq
    have hqa : u = ((u.re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using him)
    have hne : 1 - u.re ≠ 0 := by linarith
    have hpos : 0 < 1 - u.re := by linarith
    have key : ((1 - u.re : ℝ) : ℂ) * w ^ 2 = 4 * (T : ℝ) := by
      have : (u.re : ℂ) = 1 - 4 * (T : ℂ) / w ^ 2 := by rw [← hqa]
      push_cast
      rw [this]
      field_simp
      ring
    have hw2 : w ^ 2 = ((4 * (T : ℝ) / (1 - u.re) : ℝ) : ℂ) := by
      have h' : (1 : ℂ) - (u.re : ℂ) ≠ 0 := by exact_mod_cast hne
      push_cast at key ⊢
      rw [eq_div_iff h']
      linear_combination key
    apply hw
    rw [mem_slitR_iff_sq, hw2]
    simp only [ofReal_im, ofReal_re]
    refine ⟨trivial, by positivity, ?_⟩
    rw [div_le_iff₀ hpos]
    nlinarith [T.coe_nonneg]
  have hu0 : u ≠ 0 := slitPlane_ne_zero hu_slit
  have hsq0 : u ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; simp [hu0]
  set z : ℂ := w * u ^ (1 / 2 : ℂ) with hz
  have hz2 : z ^ 2 = w ^ 2 - 4 * (T : ℂ) := by
    rw [hz, mul_pow, cpow_half_sq, hu]
    field_simp
  have hz0 : z ≠ 0 := mul_ne_zero hw0 hsq0
  refine ⟨z, ?_, ?_⟩
  · rw [mem_slitI_iff_mem_slitR (w := w) (by rw [hz2]; ring)]
    exact hw
  · have hq : 1 + 4 * (T : ℂ) / z ^ 2 = u⁻¹ := by
      have hw2 : w ^ 2 * u = z ^ 2 := by
        rw [hz, mul_pow, cpow_half_sq, mul_comm]
      rw [← hw2, hu]
      have : w ^ 2 - 4 * (T : ℂ) ≠ 0 := by rw [← hz2]; exact pow_ne_zero 2 hz0
      have hh : w ^ 2 * (1 - 4 * (T : ℂ) / w ^ 2) ≠ 0 := by
        rw [← hu, hw2]; exact pow_ne_zero 2 hz0
      field_simp
      ring
    unfold zeroMap
    rw [hq, Complex.inv_cpow u _ (Complex.mem_slitPlane_iff_arg.1 hu_slit).1, hz]
    field_simp

theorem differentiableAt_zeroMap {T : ℝ≥0} {z : ℂ} (hz : z ∉ slitI T) :
    DifferentiableAt ℂ (zeroMap T) z := by
  have hz0 : z ≠ 0 := ne_zero_of_notMem_slitI hz
  have hq := one_add_div_mem_slitPlane hz T.coe_nonneg le_rfl
  have hd : DifferentiableAt ℂ (fun w : ℂ => 1 + 4 * ((T : ℝ) : ℂ) / w ^ 2) z := by
    fun_prop (disch := exact pow_ne_zero 2 hz0)
  have hc := (HasDerivAt.cpow_const hd.hasDerivAt (c := (1 / 2 : ℂ)) hq).differentiableAt
  exact (differentiableAt_id.mul hc : DifferentiableAt ℂ _ z)

theorem zeroMap_mul_deriv {T : ℝ≥0} {z : ℂ} (hz : z ∉ slitI T) :
    zeroMap T z * deriv (zeroMap T) z = z := by
  have hz0 : z ≠ 0 := ne_zero_of_notMem_slitI hz
  have hd := (differentiableAt_zeroMap hz).hasDerivAt
  have h1 : HasDerivAt (zeroMap T ^ 2) (2 * zeroMap T z * deriv (zeroMap T) z) z := by
    simpa using hd.pow 2
  have h2 : HasDerivAt (fun w : ℂ => w ^ 2 + 4 * ((T : ℝ) : ℂ)) (2 * z) z := by
    simpa using (hasDerivAt_pow 2 z).add_const (4 * ((T : ℝ) : ℂ))
  have h3 : HasDerivAt (zeroMap T ^ 2) (2 * z) z := by
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
    exact zeroMap_sq hw
  have := h1.unique h3
  linear_combination this / 2

end ComplexSLE.Internal

end
