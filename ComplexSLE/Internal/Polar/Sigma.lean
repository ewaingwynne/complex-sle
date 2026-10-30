/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.Path

/-!
# The σ-time parametrisation (Definition 2.9, `defn-sigma`, `eqn-defn-sigma`)

For a continuous driver `U` and a point `z`, the clock `A(t) = ∫₀ᵗ |f_s(z)|⁻² ds` is continuous and
strictly increasing on the life set `[0, T_z)` with `A(0) = 0` (`Path.lean`). Its supremum
`clockSup = sup_{t < T_z} A(t) ∈ [0, ∞]` bounds the honest domain `sigmaDom = [0, clockSup)` of the
inverse `σ_z` (`sigmaTime`), which is characterised by

  `s = ∫₀^{σ_z(s)} |f_u(z)|⁻² du` for `s ∈ [0, clockSup)` (paper.tex:L842, `eqn-defn-sigma`),

and is a continuous strictly increasing bijection `[0, clockSup) → [0, T_z)` with `σ_z(0) = 0`.
Remark 2.12 (`remark-sigma`, a.s. `clockSup = ∞` for an SLE_Σ driver) is probabilistic and is not
part of this file; here we record the deterministic input `clockSup = ∞` when `T_z = ∞` and `|f|`
is bounded, used in that argument. Off the domain `sigmaTime` is junk.
-/

public section

open scoped NNReal ENNReal
open Set

namespace ComplexSLE.Internal.Polar

variable {U : ℝ≥0 → ℂ}

/-! ### The supremum of the clock and the domain of `σ_z` -/

/-- `sup_{t < T_z} A(t) ∈ [0, ∞]`. -/
@[expose] noncomputable def clockSup (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) : ℝ≥0∞ :=
  ⨆ t ∈ lifeSet U z, ENNReal.ofReal (clock U hU z t)

/-- The honest domain `[0, clockSup)` of `σ_z`. -/
@[expose] def sigmaDom (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) : Set ℝ :=
  {s | 0 ≤ s ∧ ENNReal.ofReal s < clockSup U hU z}

theorem mem_sigmaDom {hU : Continuous U} {z : ℂ} {s : ℝ} :
    s ∈ sigmaDom U hU z ↔ 0 ≤ s ∧ ENNReal.ofReal s < clockSup U hU z := Iff.rfl

theorem sigmaDom_subset_Ici (hU : Continuous U) (z : ℂ) : sigmaDom U hU z ⊆ Ici 0 :=
  fun _ hs => hs.1

theorem mem_sigmaDom_of_le {hU : Continuous U} {z : ℂ} {s s' : ℝ} (hs : s ∈ sigmaDom U hU z)
    (h0 : 0 ≤ s') (hle : s' ≤ s) : s' ∈ sigmaDom U hU z :=
  ⟨h0, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hle) hs.2⟩

theorem ofReal_clock_le_clockSup (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    ENNReal.ofReal (clock U hU z t) ≤ clockSup U hU z :=
  le_iSup₂_of_le (f := fun t (_ : t ∈ lifeSet U z) => ENNReal.ofReal (clock U hU z t)) t ht le_rfl

/-- Clock values lie in the domain of `σ_z` (strictly below the supremum, since the life set has
no largest element). -/
theorem clock_mem_sigmaDom (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    clock U hU z t ∈ sigmaDom U hU z := by
  refine ⟨clock_nonneg hU ht, ?_⟩
  obtain ⟨t', ht', hlt⟩ := exists_gt_mem_lifeSet ht
  refine lt_of_lt_of_le ?_ (ofReal_clock_le_clockSup hU ht')
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (clock_nonneg hU ht)).2
    (clock_lt_clock hU ht.1 hlt ht')

theorem zero_mem_sigmaDom (hU : Continuous U) {z : ℂ} (hz : (0 : ℝ) ∈ lifeSet U z) :
    (0 : ℝ) ∈ sigmaDom U hU z := by
  have := clock_mem_sigmaDom hU hz
  rwa [clock_zero] at this

theorem exists_gt_mem_sigmaDom {hU : Continuous U} {z : ℂ} {s : ℝ} (hs : s ∈ sigmaDom U hU z) :
    ∃ s' ∈ sigmaDom U hU z, s < s' := by
  obtain ⟨x, hx1, hx2⟩ := exists_between hs.2
  have hxtop : x ≠ ⊤ := ne_top_of_lt hx2
  refine ⟨x.toReal, ⟨ENNReal.toReal_nonneg, by rwa [ENNReal.ofReal_toReal hxtop]⟩, ?_⟩
  exact (ENNReal.ofReal_lt_iff_lt_toReal hs.1 hxtop).1 hx1

theorem sigmaDom_mem_nhdsWithin {hU : Continuous U} {z : ℂ} {s : ℝ} (hs : s ∈ sigmaDom U hU z) :
    sigmaDom U hU z ∈ nhdsWithin s (Ici 0) := by
  obtain ⟨s', hs', hlt⟩ := exists_gt_mem_sigmaDom hs
  have : Ico 0 s' ∈ nhdsWithin s (Ici 0) := by
    refine mem_nhdsWithin.2 ⟨Iio s', isOpen_Iio, hlt, ?_⟩
    rintro u ⟨hu1, hu2⟩
    exact ⟨hu2, hu1⟩
  exact Filter.mem_of_superset this fun u hu => mem_sigmaDom_of_le hs' hu.1 hu.2.le

theorem sigmaDom_mem_nhds {hU : Continuous U} {z : ℂ} {s : ℝ} (hs : s ∈ sigmaDom U hU z)
    (h0 : 0 < s) : sigmaDom U hU z ∈ nhds s := by
  obtain ⟨s', hs', hlt⟩ := exists_gt_mem_sigmaDom hs
  exact Filter.mem_of_superset (Ioo_mem_nhds h0 hlt) fun u hu =>
    mem_sigmaDom_of_le hs' hu.1.le hu.2.le

theorem sigmaDom_eq_Ici {hU : Continuous U} {z : ℂ} (h : clockSup U hU z = ⊤) :
    sigmaDom U hU z = Ici 0 := by
  ext s; simp [mem_sigmaDom, h]

/-- **Intermediate values of the clock.** Every `s ∈ [0, clockSup)` is a clock value. -/
theorem exists_clock_eq (hU : Continuous U) {z : ℂ} {s : ℝ} (hs : s ∈ sigmaDom U hU z) :
    ∃ t ∈ lifeSet U z, clock U hU z t = s := by
  obtain ⟨t₁, ht₁, hlt⟩ := lt_biSup_iff.1 hs.2
  have hslt : s < clock U hU z t₁ := by
    by_contra h
    push Not at h
    exact absurd hlt (not_lt.2 (ENNReal.ofReal_le_ofReal h))
  have hz : (0 : ℝ) ∈ lifeSet U z := mem_lifeSet_of_le ht₁ le_rfl ht₁.1
  have hcont : ContinuousOn (clock U hU z) (Icc 0 t₁) :=
    (continuousOn_clock hU z).mono (Icc_subset_lifeSet ht₁)
  have hmem : s ∈ Icc (clock U hU z 0) (clock U hU z t₁) := by
    rw [clock_zero]; exact ⟨hs.1, hslt.le⟩
  obtain ⟨t, ht, hts⟩ := intermediate_value_Icc ht₁.1 hcont hmem
  exact ⟨t, Icc_subset_lifeSet ht₁ ht, hts⟩

/-! ### The inverse clock `σ_z` -/

/-- **The σ-time parametrisation `σ_z`** (Definition 2.9): for `s ∈ [0, clockSup)`, the unique
time `t ∈ [0, T_z)` with `∫₀ᵗ |f_u(z)|⁻² du = s`. Junk off the domain. -/
@[expose] noncomputable def sigmaTime (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) (s : ℝ) : ℝ :=
  sInf {t | t ∈ lifeSet U z ∧ s ≤ clock U hU z t}

/-- `σ_z` inverts the clock: `σ_z (A t) = t` on the life set. -/
theorem sigmaTime_eq_of_clock_eq (hU : Continuous U) {z : ℂ} {t s : ℝ} (ht : t ∈ lifeSet U z)
    (h : clock U hU z t = s) : sigmaTime U hU z s = t := by
  unfold sigmaTime
  have hmem : t ∈ {t | t ∈ lifeSet U z ∧ s ≤ clock U hU z t} := ⟨ht, h.ge⟩
  refine le_antisymm (csInf_le ⟨0, fun _ hu => hu.1.1⟩ hmem) (le_csInf ⟨t, hmem⟩ ?_)
  rintro u ⟨hu, hsu⟩
  by_contra hlt
  push Not at hlt
  have := clock_lt_clock hU hu.1 hlt ht
  linarith

theorem sigmaTime_clock (hU : Continuous U) {z : ℂ} {t : ℝ} (ht : t ∈ lifeSet U z) :
    sigmaTime U hU z (clock U hU z t) = t :=
  sigmaTime_eq_of_clock_eq hU ht rfl

theorem sigmaTime_mem_lifeSet (hU : Continuous U) {z : ℂ} {s : ℝ} (hs : s ∈ sigmaDom U hU z) :
    sigmaTime U hU z s ∈ lifeSet U z := by
  obtain ⟨t, ht, hts⟩ := exists_clock_eq hU hs
  rw [sigmaTime_eq_of_clock_eq hU ht hts]; exact ht

/-- `eqn-defn-sigma`: `s = ∫₀^{σ_z(s)} |f_u(z)|⁻² du` on the domain. -/
theorem clock_sigmaTime (hU : Continuous U) {z : ℂ} {s : ℝ} (hs : s ∈ sigmaDom U hU z) :
    clock U hU z (sigmaTime U hU z s) = s := by
  obtain ⟨t, ht, hts⟩ := exists_clock_eq hU hs
  rw [sigmaTime_eq_of_clock_eq hU ht hts]; exact hts

theorem sigmaTime_zero (hU : Continuous U) {z : ℂ} (hz : (0 : ℝ) ∈ lifeSet U z) :
    sigmaTime U hU z 0 = 0 :=
  sigmaTime_eq_of_clock_eq hU hz (clock_zero hU z)

theorem sigmaTime_nonneg (hU : Continuous U) {z : ℂ} {s : ℝ} (hs : s ∈ sigmaDom U hU z) :
    0 ≤ sigmaTime U hU z s :=
  (sigmaTime_mem_lifeSet hU hs).1

theorem sigmaTime_strictMonoOn (hU : Continuous U) (z : ℂ) :
    StrictMonoOn (sigmaTime U hU z) (sigmaDom U hU z) := by
  intro s hs s' hs' hlt
  have h1 := clock_sigmaTime hU hs
  have h2 := clock_sigmaTime hU hs'
  by_contra hle
  push Not at hle
  have := (clock_monotoneOn hU z) (sigmaTime_mem_lifeSet hU hs') (sigmaTime_mem_lifeSet hU hs) hle
  linarith

theorem sigmaTime_monotoneOn (hU : Continuous U) (z : ℂ) :
    MonotoneOn (sigmaTime U hU z) (sigmaDom U hU z) :=
  (sigmaTime_strictMonoOn hU z).monotoneOn

theorem sigmaTime_lt_sigmaTime_iff (hU : Continuous U) {z : ℂ} {s s' : ℝ}
    (hs : s ∈ sigmaDom U hU z) (hs' : s' ∈ sigmaDom U hU z) :
    sigmaTime U hU z s < sigmaTime U hU z s' ↔ s < s' :=
  (sigmaTime_strictMonoOn hU z).lt_iff_lt hs hs'

theorem sigmaTime_le_sigmaTime_iff (hU : Continuous U) {z : ℂ} {s s' : ℝ}
    (hs : s ∈ sigmaDom U hU z) (hs' : s' ∈ sigmaDom U hU z) :
    sigmaTime U hU z s ≤ sigmaTime U hU z s' ↔ s ≤ s' :=
  (sigmaTime_strictMonoOn hU z).le_iff_le hs hs'

/-- `σ_z` maps `[0, clockSup)` onto `[0, T_z)` (Remark 2.12 modulo `clockSup = ∞`). -/
theorem image_sigmaTime (hU : Continuous U) (z : ℂ) :
    sigmaTime U hU z '' sigmaDom U hU z = lifeSet U z := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact sigmaTime_mem_lifeSet hU hs
  · intro ht
    exact ⟨clock U hU z t, clock_mem_sigmaDom hU ht, sigmaTime_clock hU ht⟩

theorem sigmaTime_pos (hU : Continuous U) {z : ℂ} {s : ℝ} (hs : s ∈ sigmaDom U hU z)
    (h0 : 0 < s) : 0 < sigmaTime U hU z s := by
  have hz : (0 : ℝ) ∈ sigmaDom U hU z := mem_sigmaDom_of_le hs le_rfl hs.1
  have hz' : (0 : ℝ) ∈ lifeSet U z := by
    have := sigmaTime_mem_lifeSet hU hz
    exact mem_lifeSet_of_le this le_rfl this.1
  have := (sigmaTime_lt_sigmaTime_iff hU hz hs).2 h0
  rwa [sigmaTime_zero hU hz'] at this

/-- `σ_z` is continuous on its domain. -/
theorem continuousOn_sigmaTime (hU : Continuous U) (z : ℂ) :
    ContinuousOn (sigmaTime U hU z) (sigmaDom U hU z) := by
  intro s hs
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · subst h0
    have hz : (0 : ℝ) ∈ lifeSet U z := by
      have := sigmaTime_mem_lifeSet hU hs
      exact mem_lifeSet_of_le this le_rfl this.1
    have hright : ContinuousWithinAt (sigmaTime U hU z) (Ici 0) 0 := by
      refine continuousWithinAt_right_of_monotoneOn_of_image_mem_nhdsWithin
        (sigmaTime_monotoneOn hU z) (sigmaDom_mem_nhdsWithin hs) ?_
      rw [image_sigmaTime, sigmaTime_zero hU hz]
      exact lifeSet_mem_nhdsWithin hz
    exact hright.mono (sigmaDom_subset_Ici hU z)
  · have hpos := sigmaTime_pos hU hs h0
    refine (continuousAt_of_monotoneOn_of_image_mem_nhds (sigmaTime_monotoneOn hU z)
      (sigmaDom_mem_nhds hs h0) ?_).continuousWithinAt
    rw [image_sigmaTime]
    exact lifeSet_mem_nhds (sigmaTime_mem_lifeSet hU hs) hpos

/-! ### Deterministic input to Remark 2.12 -/

/-- If `T_z = ∞` and `|f_t(z)| ≤ M` for all `t ≥ 0`, then `A(t) ≥ t / M²`, so `clockSup = ∞`. -/
theorem clockSup_eq_top_of_norm_le (hU : Continuous U) {z : ℂ} (hT : absorbingTime U z = ⊤)
    {M : ℝ} (hM : ∀ t, 0 ≤ t → ‖fPath U hU z t‖ ≤ M) : clockSup U hU z = ⊤ := by
  have hlife : lifeSet U z = Ici 0 := lifeSet_eq_Ici hT
  have hMpos : 0 < M := lt_of_lt_of_le (norm_fPath_pos hU (by rw [hlife]; exact le_rfl)) (hM 0 le_rfl)
  -- `A(t) ≥ t / M²`
  have hlow : ∀ t, 0 ≤ t → t / M ^ 2 ≤ clock U hU z t := by
    intro t ht
    have htl : t ∈ lifeSet U z := by rw [hlife]; exact ht
    have hint := intervalIntegrable_clockRate hU htl
    have : ∫ s in (0 : ℝ)..t, (M ^ 2)⁻¹ ≤ ∫ s in (0 : ℝ)..t, clockRate U hU z s := by
      refine intervalIntegral.integral_mono_on ht (by simp) hint fun s hs => ?_
      unfold clockRate
      have hs' : s ∈ lifeSet U z := by rw [hlife]; exact hs.1
      have h1 : 0 < ‖fPath U hU z s‖ := norm_fPath_pos hU hs'
      have h2 : ‖fPath U hU z s‖ ≤ M := hM s hs.1
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ h1.le h2 2)
    change t / M ^ 2 ≤ ∫ s in (0 : ℝ)..t, clockRate U hU z s
    simpa [div_eq_mul_inv] using this
  rw [eq_top_iff]
  refine le_of_forall_lt fun x hx => ?_
  have hxtop : x ≠ ⊤ := ne_top_of_lt hx
  set t := (x.toReal + 1) * M ^ 2 with ht
  have ht0 : 0 ≤ t := by positivity
  have htl : t ∈ lifeSet U z := by rw [hlife]; exact ht0
  refine lt_of_lt_of_le ?_ (ofReal_clock_le_clockSup hU htl)
  have h1 : x.toReal < clock U hU z t := by
    have := hlow t ht0
    have h2 : t / M ^ 2 = x.toReal + 1 := by
      rw [ht]; field_simp
    linarith
  rw [← ENNReal.ofReal_toReal hxtop]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).2 h1

end ComplexSLE.Internal.Polar

end
