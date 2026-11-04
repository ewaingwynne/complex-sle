/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Polar.PolarContArg
public import ComplexSLE.Internal.Polar.PolarThetaHat
public import ComplexSLE.Internal.Polar.DriverMeasurability
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Joint measurability of `θ̂_s(e^{iu})` and `θ̂_s - θ̂_0` on `Ω × ℝ` (M7/A3)

For `hU : IsSLEDriverAdapted a b c U P ℱ`, `s : ℝ≥0` and the random point `z_u = e^{iu}`:

* `measurableSet_sigmaDom_unit`: the set `{(ω, u) | s ∈ sigmaDom (U(ω)) z_u}` is measurable;
* `measurable_thetaHat_sub_unit`: `(ω, u) ↦ θ̂_s(z_u)(ω) - θ̂_0(z_u)(ω)` is measurable;
* `measurable_thetaHat_unit`: `(ω, u) ↦ θ̂_s(z_u)(ω)` is measurable (the previous item plus the
  explicit `θ̂_0 = θ_0`, `measurable_thetaHat_zero_unit`),

with `thetaHat` the project's convention (`0` off `sigmaDom`, a.s. never).

**Route (Carathéodory with an open domain).** For fixed `u` the map `θ̂_s - θ̂_0` is measurable in
`ω` (`isStronglyProgressive_thetaHat`); for fixed `ω` it is continuous in `u` on the open set
`{u | s ∈ sigmaDom (U ω) z_u}` (`PolarContArg.lean`) and equal to a jointly measurable function
off it. The domain `{(ω, u) | s ∈ sigmaDom}` is measurable: `s ∈ sigmaDom` iff some rational time
`t` has `t < T_z` and `s < A_t(z)` (`mem_sigmaDom_iff_exists_grid`), and `{t < T_z}`, `A_t` are
jointly measurable in `(ω, u)` because the pair `(U(ω), z_u)` is the single shifted driver
`U(ω) - z_u` started at `0` (`lifeSet_shift`, `fPath_shift`, `clock_shift`), to which the existing
fixed-`z` results (`measurableSet_mem_lifeSet`, `measurable_clock`) apply on the product space
`Ω × ℝ` with the constant filtration. A general lemma (`measurable_of_continuousOn_sections`)
turns the three ingredients into measurability.
-/

public section

open scoped NNReal ENNReal Topology Real
open Set Filter MeasureTheory Complex

namespace ComplexSLE.Internal.Polar

/-! ### A Carathéodory lemma for sections continuous on an open domain -/

/-- **Carathéodory with an open domain.** Let `S ⊆ Ω × ℝ` be measurable with open `ω`-sections,
`F` measurable in `ω` for every `u` and continuous in `u` on the section `S_ω`, and equal to a
jointly measurable `G` off `S`. Then `F` is jointly measurable. -/
theorem measurable_of_continuousOn_sections {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E] [MeasurableSpace E]
    [BorelSpace E] {S : Set (Ω × ℝ)} (hS : MeasurableSet S)
    (hopen : ∀ ω, IsOpen {u | (ω, u) ∈ S}) {F G : Ω × ℝ → E} (hG : Measurable G)
    (hoff : ∀ p, p ∉ S → F p = G p)
    (hcont : ∀ ω, ContinuousOn (fun u => F (ω, u)) {u | (ω, u) ∈ S})
    (hmeas : ∀ u, Measurable fun ω => F (ω, u)) : Measurable F := by
  classical
  let q : ℕ → ℝ → ℝ := fun n u => (⌊((n : ℝ) + 1) * u⌋ : ℝ) / ((n : ℝ) + 1)
  let Fn : ℕ → Ω × ℝ → E := fun n p => if p ∈ S then F (p.1, q n p.2) else G p
  have hFn : ∀ n, Measurable (Fn n) := by
    intro n
    have h1 : Measurable fun x : Ω × ℤ => F (x.1, (x.2 : ℝ) / ((n : ℝ) + 1)) :=
      measurable_from_prod_countable_left fun k => hmeas ((k : ℝ) / ((n : ℝ) + 1))
    have h2 : Measurable fun p : Ω × ℝ => (p.1, ⌊((n : ℝ) + 1) * p.2⌋) :=
      measurable_fst.prodMk (Int.measurable_floor.comp (measurable_const.mul measurable_snd))
    exact Measurable.ite hS (h1.comp h2) hG
  refine measurable_of_tendsto_metrizable hFn (tendsto_pi_nhds.2 fun p => ?_)
  by_cases hp : p ∈ S
  · have hFn_eq : ∀ n, Fn n p = F (p.1, q n p.2) := fun n => by simp [Fn, hp]
    simp only [hFn_eq]
    -- `q n u → u`
    have hq : Tendsto (fun n => q n p.2) atTop (𝓝 p.2) := by
      have hlow : ∀ n : ℕ, p.2 - 1 / ((n : ℝ) + 1) ≤ q n p.2 := fun n => by
        have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have := Int.lt_floor_add_one (((n : ℝ) + 1) * p.2)
        simp only [q]
        rw [le_div_iff₀ hn]
        have h2 : (p.2 - 1 / ((n : ℝ) + 1)) * ((n : ℝ) + 1) = ((n : ℝ) + 1) * p.2 - 1 := by
          field_simp
        rw [h2]
        linarith
      have hup : ∀ n : ℕ, q n p.2 ≤ p.2 := fun n => by
        have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        simp only [q]
        rw [div_le_iff₀ hn, mul_comm]
        exact Int.floor_le _
      have h0 : Tendsto (fun n : ℕ => p.2 - 1 / ((n : ℝ) + 1)) atTop (𝓝 p.2) := by
        have := (tendsto_const_nhds (x := p.2)).sub tendsto_one_div_add_atTop_nhds_zero_nat
        rwa [sub_zero] at this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le h0 tendsto_const_nhds hlow hup
    have hcontAt : ContinuousAt (fun u => F (p.1, u)) p.2 :=
      (hcont p.1).continuousAt ((hopen p.1).mem_nhds hp)
    exact hcontAt.tendsto.comp hq
  · have : ∀ n, Fn n p = G p := fun n => by simp [Fn, hp]
    simp only [this, hoff p hp]
    exact tendsto_const_nhds

/-! ### The shifted driver: `(U, z)` as the single driver `U - z` started at `0` -/

section Shift

variable {U : ℝ≥0 → ℂ} {z : ℂ}

theorem lifeSet_shift (U : ℝ≥0 → ℂ) (z : ℂ) : lifeSet (fun r => U r - z) 0 = lifeSet U z := by
  have := lifeSet_sub_const (U := U) z z
  rwa [sub_self] at this

theorem fPath_shift (hU : Continuous U) (hU' : Continuous fun r => U r - z) {t : ℝ}
    (ht : t ∈ lifeSet U z) : fPath (fun r => U r - z) hU' 0 t = fPath U hU z t := by
  have := fPath_sub_const hU hU' (c := z) ht
  rw [sub_self] at this
  exact this.symm

theorem clock_shift (hU : Continuous U) (hU' : Continuous fun r => U r - z) {t : ℝ}
    (ht : t ∈ lifeSet U z) : clock (fun r => U r - z) hU' 0 t = clock U hU z t := by
  unfold clock
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le ht.1] at hr
  have hr' : r ∈ lifeSet U z := Icc_subset_lifeSet ht hr
  simp only [clockRate]
  rw [fPath_shift hU hU' hr']

end Shift

/-! ### `s ∈ sigmaDom` is tested on a countable set of times -/

/-- The grid time `k / (N + 1)`. -/
@[expose] noncomputable def gridTime (N k : ℕ) : ℝ≥0 := (k : ℝ≥0) / ((N : ℝ≥0) + 1)

theorem coe_gridTime (N k : ℕ) : ((gridTime N k : ℝ≥0) : ℝ) = (k : ℝ) / ((N : ℝ) + 1) := by
  simp [gridTime]

section Grid

variable {U : ℝ≥0 → ℂ}

/-- `s ∈ sigmaDom` iff `s ≥ 0` and for some rational grid time `t`, `t < T_z` and `s < A_t(z)`. -/
theorem mem_sigmaDom_iff_exists_grid (hU : Continuous U) {z : ℂ} {s : ℝ} :
    s ∈ sigmaDom U hU z ↔ 0 ≤ s ∧ ∃ N k : ℕ, ((gridTime N k : ℝ≥0) : ℝ) ∈ lifeSet U z ∧
      s < clock U hU z (gridTime N k) := by
  constructor
  · intro hs
    refine ⟨hs.1, ?_⟩
    obtain ⟨t₁, ht₁, hlt⟩ := lt_biSup_iff.1 hs.2
    have hslt : s < clock U hU z t₁ := by
      by_contra h
      push Not at h
      exact absurd hlt (not_lt.2 (ENNReal.ofReal_le_ofReal h))
    have ht₁pos : 0 < t₁ := by
      rcases eq_or_lt_of_le ht₁.1 with h | h
      · rw [← h, clock_zero] at hslt
        exact absurd hs.1 (not_le.2 hslt)
      · exact h
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.1
      ((continuousOn_clock hU z) t₁ ht₁) (clock U hU z t₁ - s) (by linarith)
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    set k : ℕ := ⌊((N : ℝ) + 1) * t₁⌋₊ with hk
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hkle : (k : ℝ) ≤ ((N : ℝ) + 1) * t₁ := Nat.floor_le (by positivity)
    have hklt : ((N : ℝ) + 1) * t₁ < k + 1 := Nat.lt_floor_add_one _
    have hgle : (k : ℝ) / ((N : ℝ) + 1) ≤ t₁ := by
      rw [div_le_iff₀ hN1]; linarith
    have hglt : t₁ - 1 / ((N : ℝ) + 1) < (k : ℝ) / ((N : ℝ) + 1) := by
      rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hN1]; linarith
    have hmem : ((gridTime N k : ℝ≥0) : ℝ) ∈ lifeSet U z := by
      rw [coe_gridTime]
      exact mem_lifeSet_of_le ht₁ (by positivity) hgle
    refine ⟨N, k, hmem, ?_⟩
    have hdist : dist ((gridTime N k : ℝ≥0) : ℝ) t₁ < δ := by
      rw [coe_gridTime, Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
      have : (N : ℝ) + 1 ≠ 0 := hN1.ne'
      have h1 : 1 / ((N : ℝ) + 1) < δ := by simpa [one_div] using hN
      linarith
    have := hδ' hmem hdist
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.1]
  · rintro ⟨hs0, N, k, hmem, hlt⟩
    refine ⟨hs0, lt_of_lt_of_le ?_ (ofReal_clock_le_clockSup hU hmem)⟩
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hs0 hlt)).2 hlt

end Grid

/-! ### Measurability of the domain in `(ω, u)` -/

section Product

variable {Ω : Type} {m : MeasurableSpace Ω} {U : ℝ≥0 → Ω → ℂ}

/-- The shifted driver `V_r(ω, u) = U_r(ω) - e^{iu}` on `Ω × ℝ`. -/
@[expose] noncomputable def shiftedDriver (U : ℝ≥0 → Ω → ℂ) (r : ℝ≥0) (p : Ω × ℝ) : ℂ :=
  U r p.1 - Complex.exp ((p.2 : ℂ) * Complex.I)

theorem continuous_shiftedDriver (hc : ∀ ω, Continuous fun t => U t ω) (p : Ω × ℝ) :
    Continuous fun r => shiftedDriver U r p :=
  (hc p.1).sub continuous_const

theorem measurable_shiftedDriver {ℱ : Filtration ℝ≥0 m} (had : Adapted ℱ U) (r : ℝ≥0) :
    Measurable (shiftedDriver U r) := by
  have h1 : Measurable fun p : Ω × ℝ => U r p.1 :=
    ((had r).mono (ℱ.le r) le_rfl).comp measurable_fst
  have h2 : Measurable fun p : Ω × ℝ => Complex.exp ((p.2 : ℂ) * Complex.I) :=
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp measurable_snd).mul_const _)
  exact h1.sub h2

variable {ℱ : Filtration ℝ≥0 m}

/-- The constant filtration on `Ω × ℝ` (the product σ-algebra), to which the fixed-time results
of `Measurability.lean` and `ClockArg.lean` apply. -/
@[expose] def prodConstFiltration (m : MeasurableSpace Ω) :
    Filtration ℝ≥0 (m.prod Real.measurableSpace) :=
  Filtration.const ℝ≥0 (m.prod Real.measurableSpace) le_rfl

theorem adapted_shiftedDriver (had : Adapted ℱ U) :
    Adapted (prodConstFiltration m) (shiftedDriver U) := fun r => measurable_shiftedDriver had r

/-- `{(ω, u) | t < T_{e^{iu}}(ω)}` is measurable. -/
theorem measurableSet_mem_lifeSet_unit (hc : ∀ ω, Continuous fun t => U t ω) (had : Adapted ℱ U)
    (t : ℝ≥0) :
    MeasurableSet {p : Ω × ℝ |
      (t : ℝ) ∈ lifeSet (fun r => U r p.1) (Complex.exp ((p.2 : ℂ) * Complex.I))} := by
  have h := measurableSet_mem_lifeSet (continuous_shiftedDriver hc) (adapted_shiftedDriver had) t 0
  have heq : {p : Ω × ℝ |
      (t : ℝ) ∈ lifeSet (fun r => U r p.1) (Complex.exp ((p.2 : ℂ) * Complex.I))} =
      {p : Ω × ℝ | (t : ℝ) ∈ lifeSet (fun r => shiftedDriver U r p) 0} := by
    ext p
    simp only [mem_ofPred_eq, shiftedDriver]
    rw [lifeSet_shift (fun r => U r p.1)]
  rw [heq]
  exact h

open Classical in
/-- `(ω, u) ↦ A_t(e^{iu})(ω)` on `{t < T}` (and `0` elsewhere) is measurable. -/
theorem measurable_clock_unit (hc : ∀ ω, Continuous fun t => U t ω) (had : Adapted ℱ U)
    (t : ℝ≥0) :
    Measurable fun p : Ω × ℝ =>
      if (t : ℝ) ∈ lifeSet (fun r => U r p.1) (Complex.exp ((p.2 : ℂ) * Complex.I)) then
        clock (fun r => U r p.1) (hc p.1) (Complex.exp ((p.2 : ℂ) * Complex.I)) t else 0 := by
  have h := measurable_clock (continuous_shiftedDriver hc) (adapted_shiftedDriver had) t 0
  have heq : (fun p : Ω × ℝ =>
      if (t : ℝ) ∈ lifeSet (fun r => U r p.1) (Complex.exp ((p.2 : ℂ) * Complex.I)) then
        clock (fun r => U r p.1) (hc p.1) (Complex.exp ((p.2 : ℂ) * Complex.I)) t else 0) =
      fun p : Ω × ℝ =>
        if (t : ℝ) ∈ lifeSet (fun r => shiftedDriver U r p) 0 then
          clock (fun r => shiftedDriver U r p) (continuous_shiftedDriver hc p) 0 t else 0 := by
    funext p
    have hlife : lifeSet (fun r => shiftedDriver U r p) 0 =
        lifeSet (fun r => U r p.1) (Complex.exp ((p.2 : ℂ) * Complex.I)) := by
      simp only [shiftedDriver]
      exact lifeSet_shift (fun r => U r p.1) _
    by_cases hp : (t : ℝ) ∈ lifeSet (fun r => U r p.1) (Complex.exp ((p.2 : ℂ) * Complex.I))
    · have hp' : (t : ℝ) ∈ lifeSet (fun r => shiftedDriver U r p) 0 := by rw [hlife]; exact hp
      simp only [hp, hp', ↓reduceIte]
      exact (clock_shift (hc p.1) (continuous_shiftedDriver hc p) hp).symm
    · have hp' : (t : ℝ) ∉ lifeSet (fun r => shiftedDriver U r p) 0 := by rw [hlife]; exact hp
      simp only [hp, hp', ↓reduceIte]
  rw [heq]
  exact h

/-- **The domain `{(ω, u) | s ∈ sigmaDom (U ω) e^{iu}}` is measurable.** -/
theorem measurableSet_sigmaDom_unit (hc : ∀ ω, Continuous fun t => U t ω) (had : Adapted ℱ U)
    (s : ℝ) :
    MeasurableSet {p : Ω × ℝ |
      s ∈ sigmaDom (fun r => U r p.1) (hc p.1) (Complex.exp ((p.2 : ℂ) * Complex.I))} := by
  classical
  have hset : {p : Ω × ℝ |
      s ∈ sigmaDom (fun r => U r p.1) (hc p.1) (Complex.exp ((p.2 : ℂ) * Complex.I))} =
      {_p : Ω × ℝ | 0 ≤ s} ∩ ⋃ N : ℕ, ⋃ k : ℕ,
        ({p : Ω × ℝ | ((gridTime N k : ℝ≥0) : ℝ) ∈
            lifeSet (fun r => U r p.1) (Complex.exp ((p.2 : ℂ) * Complex.I))} ∩
          {p : Ω × ℝ | s < (if ((gridTime N k : ℝ≥0) : ℝ) ∈
              lifeSet (fun r => U r p.1) (Complex.exp ((p.2 : ℂ) * Complex.I)) then
            clock (fun r => U r p.1) (hc p.1) (Complex.exp ((p.2 : ℂ) * Complex.I))
              (gridTime N k) else 0)}) := by
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iUnion]
    rw [mem_sigmaDom_iff_exists_grid]
    constructor
    · rintro ⟨h0, N, k, hmem, hlt⟩
      exact ⟨h0, N, k, hmem, by simpa only [hmem, ↓reduceIte] using hlt⟩
    · rintro ⟨h0, N, k, hmem, hlt⟩
      exact ⟨h0, N, k, hmem, by simpa only [hmem, ↓reduceIte] using hlt⟩
  rw [hset]
  refine (MeasurableSet.const _).inter
    (MeasurableSet.iUnion fun N => MeasurableSet.iUnion fun k => ?_)
  exact (measurableSet_mem_lifeSet_unit hc had _).inter
    (measurableSet_lt measurable_const (measurable_clock_unit hc had _))

end Product

/-! ### Continuity along the unit circle `u ↦ e^{iu}` -/

section Unit

variable {V : ℝ≥0 → ℂ}

/-- The unit-circle point `e^{iu}`. -/
@[expose] noncomputable def unitPt (u : ℝ) : ℂ := Complex.exp ((u : ℂ) * Complex.I)

theorem continuous_unitPt : Continuous unitPt := by
  unfold unitPt; fun_prop

/-- `u ↦ θ̂_s(e^{iu}) - θ̂_0(e^{iu})` is continuous on `{u | s ∈ sigmaDom (e^{iu})}`. -/
theorem continuousOn_argPath_sub_unit (hV : Continuous V) (s : ℝ) :
    ContinuousOn (fun u : ℝ => argPath V hV (unitPt u) (sigmaTime V hV (unitPt u) s) -
        argPath V hV (unitPt u) 0) {u | s ∈ sigmaDom V hV (unitPt u)} := fun _ hu =>
  ((continuousAt_argPath_sub_initial hV hu).comp
    (f := unitPt) continuous_unitPt.continuousAt).continuousWithinAt

theorem isOpen_sigmaDom_unit (hV : Continuous V) (s : ℝ) :
    IsOpen {u : ℝ | s ∈ sigmaDom V hV (unitPt u)} :=
  (isOpen_sigmaDomSet V hV s).preimage continuous_unitPt

end Unit

/-! ### The joint measurability corollary for `IsSLEDriverAdapted` drivers -/

section Final

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

/-- For fixed `z` and `s`, `ω ↦ θ̂_s(z)(ω)` is measurable (`θ̂` is `𝒢`-progressive and
`𝒢_s ≤ m`). -/
theorem measurable_thetaHat (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ) (s : ℝ≥0) :
    Measurable fun ω => thetaHat hU z s ω :=
  ((isStronglyProgressive_thetaHat hU (z := z)).stronglyAdapted s).measurable.mono
    ((sigmaFiltration hU z).le s) le_rfl

/-- The domain `{(ω, u) | s ∈ sigmaDom (U ω) e^{iu}}` for an `IsSLEDriverAdapted` driver. -/
@[expose] def sigmaDomUnit (hU : IsSLEDriverAdapted a b c U P ℱ) (s : ℝ) : Set (Ω × ℝ) :=
  {p | s ∈ sigmaDom (fun r => U r p.1) (hU.cont p.1) (unitPt p.2)}

theorem measurableSet_sigmaDomUnit (hU : IsSLEDriverAdapted a b c U P ℱ) (s : ℝ) :
    MeasurableSet (sigmaDomUnit hU s) :=
  measurableSet_sigmaDom_unit hU.cont hU.adapted s

theorem isOpen_sigmaDomUnit_section (hU : IsSLEDriverAdapted a b c U P ℱ) (s : ℝ) (ω : Ω) :
    IsOpen {u | (ω, u) ∈ sigmaDomUnit hU s} :=
  isOpen_sigmaDom_unit (hU.cont ω) s

theorem thetaHat_eq_zero_of_notMem_sigmaDomUnit (hU : IsSLEDriverAdapted a b c U P ℱ) (s : ℝ≥0)
    {p : Ω × ℝ} (hp : p ∉ sigmaDomUnit hU s) : thetaHat hU (unitPt p.2) s p.1 = 0 :=
  thetaHat_of_notMem hU hp

/-- `(ω, u) ↦ θ̂_0(e^{iu})(ω)` is measurable (`θ̂_0 = θ_0` is explicit). -/
theorem measurable_thetaHat_zero_unit (hU : IsSLEDriverAdapted a b c U P ℱ) :
    Measurable fun p : Ω × ℝ => thetaHat hU (unitPt p.2) 0 p.1 := by
  classical
  have h1 : Measurable fun p : Ω × ℝ => U 0 p.1 :=
    ((hU.adapted 0).mono (ℱ.le 0) le_rfl).comp measurable_fst
  have h2 : Measurable fun p : Ω × ℝ => unitPt p.2 :=
    continuous_unitPt.measurable.comp measurable_snd
  have harg : Measurable fun p : Ω × ℝ => Complex.arg (unitPt p.2 - U 0 p.1) :=
    Complex.measurable_arg.comp (h2.sub h1)
  have hS := measurableSet_sigmaDomUnit hU 0
  have heq : (fun p : Ω × ℝ => thetaHat hU (unitPt p.2) 0 p.1) =
      fun p : Ω × ℝ => if p ∈ sigmaDomUnit hU 0 then
        (if 0 ≤ Complex.arg (unitPt p.2 - U 0 p.1) then Complex.arg (unitPt p.2 - U 0 p.1)
        else Complex.arg (unitPt p.2 - U 0 p.1) + 2 * π) else 0 := by
    funext p
    by_cases hp : p ∈ sigmaDomUnit hU 0
    · have hp' : ((0 : ℝ≥0) : ℝ) ∈ sigmaDom (fun r => U r p.1) (hU.cont p.1) (unitPt p.2) := by
        rw [NNReal.coe_zero]; exact hp
      rw [thetaHat_of_mem hU hp']
      have hz0 : (0 : ℝ) ∈ lifeSet (fun r => U r p.1) (unitPt p.2) :=
        ne_driver_zero_of_mem_sigmaDomSet hp
      rw [NNReal.coe_zero, sigmaTime_zero (hU.cont p.1) hz0, argPath_zero, argInit_eq]
      simp only [hp, ↓reduceIte]
    · rw [thetaHat_eq_zero_of_notMem_sigmaDomUnit hU 0 hp]
      simp only [hp, ↓reduceIte]
  rw [heq]
  exact Measurable.ite hS (Measurable.ite (measurableSet_le measurable_const harg) harg
    (harg.add_const _)) measurable_const

/-- **Joint measurability of `θ̂_s(e^{iu}) - θ̂_0(e^{iu})` on `Ω × ℝ`.** -/
theorem measurable_thetaHat_sub_unit (hU : IsSLEDriverAdapted a b c U P ℱ) (s : ℝ≥0) :
    Measurable fun p : Ω × ℝ =>
      thetaHat hU (unitPt p.2) s p.1 - thetaHat hU (unitPt p.2) 0 p.1 := by
  refine measurable_of_continuousOn_sections (S := sigmaDomUnit hU (s : ℝ))
    (F := fun p : Ω × ℝ => thetaHat hU (unitPt p.2) s p.1 - thetaHat hU (unitPt p.2) 0 p.1)
    (G := fun p : Ω × ℝ => -thetaHat hU (unitPt p.2) 0 p.1)
    (measurableSet_sigmaDomUnit hU (s : ℝ)) (isOpen_sigmaDomUnit_section hU (s : ℝ))
    (measurable_thetaHat_zero_unit hU).neg ?_ ?_ ?_
  · intro p hp
    simp [thetaHat_eq_zero_of_notMem_sigmaDomUnit hU s hp]
  · intro ω
    refine (continuousOn_argPath_sub_unit (hU.cont ω) (s : ℝ)).congr fun u hu => ?_
    have hu' : (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) (unitPt u) := hu
    have h0 : ((0 : ℝ≥0) : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) (unitPt u) := by
      rw [NNReal.coe_zero]
      exact mem_sigmaDom_of_le hu' le_rfl s.coe_nonneg
    have hz0 : (0 : ℝ) ∈ lifeSet (fun r => U r ω) (unitPt u) :=
      ne_driver_zero_of_mem_sigmaDomSet hu'
    change thetaHat hU (unitPt u) s ω - thetaHat hU (unitPt u) 0 ω = _
    rw [thetaHat_of_mem hU hu', thetaHat_of_mem hU h0, NNReal.coe_zero,
      sigmaTime_zero (hU.cont ω) hz0]
  · intro u
    change Measurable fun ω : Ω => thetaHat hU (unitPt u) s ω - thetaHat hU (unitPt u) 0 ω
    exact (measurable_thetaHat hU (unitPt u) s).sub (measurable_thetaHat hU (unitPt u) 0)

/-- **Joint measurability of `θ̂_s(e^{iu})` itself on `Ω × ℝ`.** -/
theorem measurable_thetaHat_unit (hU : IsSLEDriverAdapted a b c U P ℱ) (s : ℝ≥0) :
    Measurable fun p : Ω × ℝ => thetaHat hU (unitPt p.2) s p.1 := by
  have e : (fun p : Ω × ℝ => thetaHat hU (unitPt p.2) s p.1) =
      fun p : Ω × ℝ => (thetaHat hU (unitPt p.2) s p.1 - thetaHat hU (unitPt p.2) 0 p.1) +
        thetaHat hU (unitPt p.2) 0 p.1 := by
    funext p; ring
  rw [e]
  exact (measurable_thetaHat_sub_unit hU s).add (measurable_thetaHat_zero_unit hU)

end Final

end ComplexSLE.Internal.Polar

end
