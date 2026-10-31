/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.ErgodicConstRegen
public import ComplexSLE.Internal.Phases.ErgodicConstHit
public import ComplexSLE.Internal.Phases.AllZFHat
public import ComplexSLE.Internal.Polar.PolarSigmaTop
public import ComplexSLE.Internal.Recurrence.Renewal

/-!
# The regeneration times of Lemma 3.3 (M7/A5b)

For an adapted driver `hU`, `z ≠ 0` and `k : ℕ`, `hitTime hU z k` is the first `ℱ`-time
`t ≥ σ_z(k)` with `t < T_z` and `e^{2iθ_t(z)} = 1` (`θ_t` the continuous argument `argPath`). It is
the stopping time `S` at which the proof of Lemma 3.3 (paper.tex:L1361-1372) regenerates:

* `isStoppingTime_hitTime`: `S` is an `ℱ`-stopping time. With `ρ = σ_z(k)` and `τ_n` the exit times
  of the annuli, `{S ≤ u} = ⋃_n {R_n < τ_n} ∩ {R_n ≤ u}` where `R_n` is the first time after `ρ`
  at which the stopped argument `θ_{t ∧ τ_n}` (an everywhere continuous `ℱ`-progressive process)
  visits `πℤ` (`hitAfterRand`, `ErgodicConstHit.lean`).
* `nonempty_regenDatum`: if (for `ν`-a.e. `u`, by the recurrence of `θ̂`) `e^{2iθ̂}` returns to `1`
  at arbitrarily large σ-times a.s., and the null sets lie in `ℱ 0`, then there is a
  `RegenDatum hU z k` (`ErgodicConstRegen.lean`) with `S = hitTime` and `τ = A(S)` the σ-time of
  `S` (`A` the clock of Definition 2.9): `σ_z(τ) = S`, `τ ≥ k`, `e^{2iθ̂_τ} = 1`; the state
  `(|f̂_τ|, θ̂_τ)` is `ℱ_S`-measurable (stopped values of the `ℱ`-progressive processes
  `f_t(z)`, `θ_t(z)` at `S`, `isStronglyProgressive_centeredOrZero`,
  `isStronglyProgressive_argOrZero`), and the observable identity is
  `pathObsAt_eq_obsC` at `s = τ(ω)`.

No external input is used.
-/

@[expose] public section

open scoped NNReal ENNReal Topology Real
open Set MeasureTheory ProbabilityTheory Filter

namespace ComplexSLE.Internal

open Polar

section Hit

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

variable (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ)

/-- The times `t ≥ σ_z(k)` with `t < T_z` and `θ_t(z) ∈ πℤ`. -/
def hitSet (k : ℕ) (ω : Ω) : Set ℝ≥0 :=
  {t | sigmaTop hU z k ω ≤ (t : WithTop ℝ≥0) ∧ (t : ℝ) ∈ lifeSet (fun s => U s ω) z ∧
    argPath (fun s => U s ω) (hU.cont ω) z (t : ℝ) ∈ ComplexSLE.Recurrence.latticeSet 0}

/-- **The regeneration time**: the first `ℱ`-time `t ≥ σ_z(k)` with `t < T_z` and
`θ_t(z) ∈ πℤ` (`⊤` if there is none). -/
noncomputable def hitTime (k : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ t ∈ hitSet hU z k ω, (t : WithTop ℝ≥0)

variable {z}

theorem le_hitTime (k : ℕ) (ω : Ω) : sigmaTop hU z k ω ≤ hitTime hU z k ω :=
  le_iInf₂ fun _ ht => ht.1

theorem hitTime_le_of_mem {k : ℕ} {ω : Ω} {t : ℝ≥0} (ht : t ∈ hitSet hU z k ω) :
    hitTime hU z k ω ≤ t :=
  iInf₂_le t ht

theorem hitTime_eq_top_of_empty {k : ℕ} {ω : Ω} (h : hitSet hU z k ω = ∅) :
    hitTime hU z k ω = ⊤ := by
  refine top_unique (le_iInf₂ fun t ht => ?_)
  rw [h] at ht
  exact absurd ht (notMem_empty t)

/-- The hit set has a smallest element (continuity of `θ` on the life set, closedness of `πℤ`). -/
theorem exists_min_hitSet {k : ℕ} {ω : Ω} (h : (hitSet hU z k ω).Nonempty) :
    ∃ t ∈ hitSet hU z k ω, ∀ t' ∈ hitSet hU z k ω, t ≤ t' := by
  obtain ⟨t₁, ht₁⟩ := h
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top ht₁.1)
  have hlife := ht₁.2.1
  have hrle : ∀ t : ℝ≥0, (sigmaTop hU z k ω ≤ (t : WithTop ℝ≥0)) ↔ r ≤ t := fun t => by
    rw [← hr]; exact_mod_cast Iff.rfl
  have hrt₁ : r ≤ t₁ := (hrle t₁).1 ht₁.1
  set f : ℝ≥0 → ℝ := fun t => argPath (fun s => U s ω) (hU.cont ω) z (t : ℝ) with hf
  have hcont : ContinuousOn f (Icc r t₁) :=
    (continuousOn_argPath (hU.cont ω) z).comp NNReal.continuous_coe.continuousOn
      (fun t ht => mem_lifeSet_of_le hlife t.coe_nonneg (by exact_mod_cast ht.2))
  have hB : IsClosed (Icc r t₁ ∩ f ⁻¹' ComplexSLE.Recurrence.latticeSet 0) :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc (ComplexSLE.Recurrence.isClosed_latticeSet 0)
  have hne : (Icc r t₁ ∩ f ⁻¹' ComplexSLE.Recurrence.latticeSet 0).Nonempty :=
    ⟨t₁, ⟨hrt₁, le_rfl⟩, ht₁.2.2⟩
  have hmem := hB.csInf_mem hne (OrderBot.bddBelow _)
  refine ⟨sInf (Icc r t₁ ∩ f ⁻¹' ComplexSLE.Recurrence.latticeSet 0), ⟨?_, ?_, hmem.2⟩, ?_⟩
  · exact (hrle _).2 hmem.1.1
  · exact mem_lifeSet_of_le hlife (NNReal.coe_nonneg _) (by exact_mod_cast hmem.1.2)
  · intro t' ht'
    have hmem₁ : t₁ ∈ Icc r t₁ ∩ f ⁻¹' ComplexSLE.Recurrence.latticeSet 0 :=
      ⟨⟨hrt₁, le_rfl⟩, ht₁.2.2⟩
    by_cases hle : t' ≤ t₁
    · have hmem' : t' ∈ Icc r t₁ ∩ f ⁻¹' ComplexSLE.Recurrence.latticeSet 0 :=
        ⟨⟨(hrle t').1 ht'.1, hle⟩, ht'.2.2⟩
      exact csInf_le (OrderBot.bddBelow _) hmem'
    · push Not at hle
      exact (csInf_le (OrderBot.bddBelow _) hmem₁).trans hle.le

theorem hitTime_eq_coe_of_min {k : ℕ} {ω : Ω} {t : ℝ≥0} (ht : t ∈ hitSet hU z k ω)
    (hmin : ∀ t' ∈ hitSet hU z k ω, t ≤ t') : hitTime hU z k ω = t :=
  le_antisymm (hitTime_le_of_mem hU ht) (le_iInf₂ fun t' ht' => by exact_mod_cast hmin t' ht')

/-- If the hit set is nonempty the hit time is a (minimal) element of it. -/
theorem exists_hitTime_eq_coe {k : ℕ} {ω : Ω} (h : (hitSet hU z k ω).Nonempty) :
    ∃ t ∈ hitSet hU z k ω, hitTime hU z k ω = t := by
  obtain ⟨t, ht, hmin⟩ := exists_min_hitSet hU h
  exact ⟨t, ht, hitTime_eq_coe_of_min hU ht hmin⟩

end Hit

section Stopping

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

variable (hU : IsSLEDriverAdapted a b c U P ℱ) (z : ℂ)

/-- `R_n`: the first time after `σ_z(k)` at which the stopped argument `θ_{t ∧ τ_n}` visits
`πℤ`. -/
noncomputable def hitStopped (k n : ℕ) : Ω → WithTop ℝ≥0 :=
  ComplexSLE.Recurrence.hitAfterRand (argStopped hU z n) (ComplexSLE.Recurrence.latticeSet 0)
    (sigmaTop hU z k)

variable {z}

theorem isStoppingTime_hitStopped (k n : ℕ) : IsStoppingTime ℱ (hitStopped hU z k n) :=
  ComplexSLE.Recurrence.isStoppingTime_hitAfterRand
    ((isStronglyProgressive_argStopped hU z n).stronglyAdapted) (continuous_argStopped hU z n)
    (ComplexSLE.Recurrence.isClosed_latticeSet 0) (isStoppingTime_sigmaTop hU z k)

theorem le_coe_of_untopA_le {x : WithTop ℝ≥0} (hx : x ≠ ⊤) {j : ℝ≥0} (h : x.untopA ≤ j) :
    x ≤ (j : WithTop ℝ≥0) := by
  obtain ⟨a, rfl⟩ := WithTop.ne_top_iff_exists.1 hx
  have : a ≤ j := h
  exact_mod_cast this

theorem untopA_le_of_le_coe {x : WithTop ℝ≥0} {j : ℝ≥0} (h : x ≤ (j : WithTop ℝ≥0)) :
    x.untopA ≤ j := by
  obtain ⟨a, rfl⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top h)
  have : a ≤ j := by exact_mod_cast h
  exact this

/-- Pathwise description of `{S ≤ u}` through the localised hitting times `R_n`. -/
theorem hitTime_le_iff (k : ℕ) (ω : Ω) (u : ℝ≥0) :
    hitTime hU z k ω ≤ (u : WithTop ℝ≥0) ↔ ∃ n : ℕ,
      hitStopped hU z k n ω < (exitNN hU z n ω : WithTop ℝ≥0) ∧
      hitStopped hU z k n ω ≤ (u : WithTop ℝ≥0) := by
  have hF := ComplexSLE.Recurrence.isClosed_latticeSet 0
  constructor
  · intro h
    have hne : (hitSet hU z k ω).Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hitTime_eq_top_of_empty hU hne] at h
      exact WithTop.not_top_le_coe u h
    obtain ⟨t, ht, hteq⟩ := exists_hitTime_eq_coe hU hne
    rw [hteq] at h
    have htu : t ≤ u := by exact_mod_cast h
    have hlife := ht.2.1
    have hz : 0 < absorbingTime (fun s => U s ω) z := lt_of_le_of_lt bot_le hlife.2
    obtain ⟨n, hn⟩ := exists_lt_exitTime (hU.cont ω) hlife
    have hn' : (t : ℝ) < exitR hU z n ω := hn
    have hRn : hitStopped hU z k n ω ≤ (t : WithTop ℝ≥0) := by
      unfold hitStopped
      rw [ComplexSLE.Recurrence.hitAfterRand_le_iff hF (continuous_argStopped hU z n)]
      refine ⟨ht.1, t, untopA_le_of_le_coe ht.1, le_rfl, ?_⟩
      rw [argStopped_eq hU z n hz, min_eq_left hn'.le]
      exact ht.2.2
    refine ⟨n, lt_of_le_of_lt hRn ?_, hRn.trans (by exact_mod_cast htu)⟩
    have : t < exitNN hU z n ω := by
      rw [← NNReal.coe_lt_coe, coe_exitNN]; exact hn'
    exact_mod_cast this
  · rintro ⟨n, hlt, hle⟩
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hle)
    have hRr : hitStopped hU z k n ω ≤ (r : WithTop ℝ≥0) := hr.ge
    unfold hitStopped at hRr
    rw [ComplexSLE.Recurrence.hitAfterRand_le_iff hF (continuous_argStopped hU z n)] at hRr
    obtain ⟨hρr, j, hj1, hjr, hj3⟩ := hRr
    have hrt : r < exitNN hU z n ω := by
      have : (r : WithTop ℝ≥0) < (exitNN hU z n ω : WithTop ℝ≥0) := by rw [hr]; exact hlt
      exact_mod_cast this
    have hz : 0 < absorbingTime (fun s => U s ω) z := by
      by_contra hz
      rw [exitNN, exitR_eq_zero hU z n hz, Real.toNNReal_zero] at hrt
      exact not_lt_zero hrt
    have hjlt : (j : ℝ) < exitR hU z n ω := by
      have : j < exitNN hU z n ω := lt_of_le_of_lt hjr hrt
      rwa [← NNReal.coe_lt_coe, coe_exitNN] at this
    have hjlife : (j : ℝ) ∈ lifeSet (fun s => U s ω) z :=
      mem_lifeSet_of_le (exitR_mem_lifeSet hU z n hz) j.coe_nonneg hjlt.le
    have hjmem : j ∈ hitSet hU z k ω := by
      refine ⟨le_coe_of_untopA_le (ne_top_of_le_ne_top WithTop.coe_ne_top hρr) hj1, hjlife, ?_⟩
      rw [argStopped_eq hU z n hz, min_eq_left hjlt.le] at hj3
      exact hj3
    have hru : r ≤ u := by
      have : (r : WithTop ℝ≥0) ≤ u := hr.le.trans hle
      exact_mod_cast this
    exact (hitTime_le_of_mem hU hjmem).trans (by exact_mod_cast hjr.trans hru)

/-- **The regeneration time is an `ℱ`-stopping time.** -/
theorem isStoppingTime_hitTime (k : ℕ) : IsStoppingTime ℱ (hitTime hU z k) := by
  intro u
  have key : {ω | hitTime hU z k ω ≤ (u : WithTop ℝ≥0)} = ⋃ n : ℕ,
      ({ω | hitStopped hU z k n ω < (exitNN hU z n ω : WithTop ℝ≥0)} ∩
        {ω | hitStopped hU z k n ω ≤ (u : WithTop ℝ≥0)}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    exact hitTime_le_iff hU k ω u
  rw [key]
  refine MeasurableSet.iUnion fun n => ?_
  have hR := isStoppingTime_hitStopped hU (z := z) k n
  have hτ := isStoppingTime_exitNN hU z n
  have h1 : MeasurableSet[hR.measurableSpace]
      {ω | hitStopped hU z k n ω < (exitNN hU z n ω : WithTop ℝ≥0)} := by
    have : {ω | hitStopped hU z k n ω < (exitNN hU z n ω : WithTop ℝ≥0)} =
        {ω | (exitNN hU z n ω : WithTop ℝ≥0) ≤ hitStopped hU z k n ω}ᶜ := by
      ext ω; simp only [mem_ofPred_eq, mem_compl_iff, not_le]
    rw [this]
    exact (IsStoppingTime.measurableSet_stopping_time_le hτ hR).compl
  exact ((hR.measurableSet _).1 h1).2 u

end Stopping

section Datum

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m} {a b c : ℝ}
  {U : ℝ≥0 → Ω → ℂ}

variable (hU : IsSLEDriverAdapted a b c U P ℱ) {z : ℂ}

/-- If `σ_z` is defined on `[0, ∞)` and `e^{2iθ̂}` returns to `1` at arbitrarily large σ-times,
the hit set is nonempty. -/
theorem hitSet_nonempty_of_recurrent {ω : Ω}
    (hall : sigmaDom (fun r => U r ω) (hU.cont ω) z = Ici 0)
    (hrecω : ∀ s : ℝ≥0, ∃ t : ℝ≥0, s ≤ t ∧
      Complex.exp (2 * Complex.I * (thetaHat hU z t ω : ℂ)) = 1) (k : ℕ) :
    (hitSet hU z k ω).Nonempty := by
  have hmemr : ∀ s : ℝ≥0, (s : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z := fun s => by
    rw [hall]; exact s.coe_nonneg
  obtain ⟨t, hkt, hexp⟩ := hrecω k
  have hmem := hmemr t
  have hσ := sigmaTime_mem_lifeSet (hU.cont ω) hmem
  have hσ0 := sigmaTime_nonneg (hU.cont ω) hmem
  refine ⟨(sigmaTime (fun r => U r ω) (hU.cont ω) z t).toNNReal, ?_, ?_, ?_⟩
  · rw [sigmaTop_of_mem hU (hmemr k), WithTop.coe_le_coe]
    exact Real.toNNReal_le_toNNReal
      ((sigmaTime_monotoneOn (hU.cont ω) z) (hmemr k) hmem (by exact_mod_cast hkt))
  · rw [Real.coe_toNNReal _ hσ0]; exact hσ
  · rw [Real.coe_toNNReal _ hσ0]
    rw [thetaHat_of_mem hU hmem] at hexp
    rw [ComplexSLE.Recurrence.mem_latticeSet_iff_exp]
    simpa using hexp

/-- The σ-time `τ = A(t)` of an `ℱ`-time `t` of the hit set, and the pathwise identities. -/
theorem hitSet_sigma_facts {ω : Ω} {k : ℕ}
    (hall : sigmaDom (fun r => U r ω) (hU.cont ω) z = Ici 0) {t : ℝ≥0}
    (ht : t ∈ hitSet hU z k ω) {τ : ℝ≥0}
    (hτ : (τ : ℝ) = clock (fun r => U r ω) (hU.cont ω) z (t : ℝ)) :
    sigmaTop hU z τ ω = (t : WithTop ℝ≥0) ∧
      thetaHat hU z τ ω = argPath (fun r => U r ω) (hU.cont ω) z (t : ℝ) ∧
      fHat hU z τ ω = fPath (fun r => U r ω) (hU.cont ω) z (t : ℝ) ∧ (k : ℝ≥0) ≤ τ := by
  have hlife := ht.2.1
  have hdom : (τ : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z := by
    rw [hτ]; exact clock_mem_sigmaDom (hU.cont ω) hlife
  have hσ : sigmaTime (fun r => U r ω) (hU.cont ω) z (τ : ℝ) = (t : ℝ) := by
    rw [hτ]; exact sigmaTime_clock (hU.cont ω) hlife
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sigmaTop_of_mem hU hdom, hσ, Real.toNNReal_coe]
  · rw [thetaHat_of_mem hU hdom, hσ]
  · rw [fHat_of_mem hU hdom, hσ]
  · have hmemk : (k : ℝ) ∈ sigmaDom (fun r => U r ω) (hU.cont ω) z := by
      rw [hall]; exact_mod_cast Nat.cast_nonneg k
    have hk1 := ht.1
    rw [sigmaTop_of_mem hU hmemk, WithTop.coe_le_coe, Real.toNNReal_le_iff_le_coe] at hk1
    have hσk := sigmaTime_mem_lifeSet (hU.cont ω) hmemk
    have h2 := (clock_monotoneOn (hU.cont ω) z) hσk hlife hk1
    rw [clock_sigmaTime (hU.cont ω) hmemk, ← hτ] at h2
    exact_mod_cast h2

theorem sigmaFiltration_le_hitTime {s : ℝ≥0} {k : ℕ} (hs : s ≤ (k : ℝ≥0)) :
    sigmaFiltration hU z s ≤ (isStoppingTime_hitTime hU (z := z) k).measurableSpace := by
  have h1 : sigmaFiltration hU z s ≤ sigmaFiltration hU z (k : ℝ≥0) :=
    (sigmaFiltration hU z).mono hs
  refine h1.trans ?_
  exact IsStoppingTime.measurableSpace_mono (isStoppingTime_sigmaTop hU z k)
    (isStoppingTime_hitTime hU k) (fun ω => le_hitTime hU k ω)

/-- **The regeneration datum** (`ErgodicConstRegen.lean`) at level `k`, for `z ≠ 0` such that
`e^{2iθ̂(z)}` is a.s. recurrent to `1` (and null sets in `ℱ 0`). -/
theorem nonempty_regenDatum [IsProbabilityMeasure P]
    (hnull : ∀ N : Set Ω, MeasurableSet N → P N = 0 → MeasurableSet[ℱ 0] N)
    (ha : 0 < a) (hc : c ^ 2 ≤ a * b) (hz : z ≠ 0)
    (hrec : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, ∃ t : ℝ≥0, s ≤ t ∧
      Complex.exp (2 * Complex.I * (thetaHat hU z t ω : ℂ)) = 1) (k : ℕ) :
    Nonempty (RegenDatum hU z k) := by
  classical
  have hgood : ∀ᵐ ω ∂P, sigmaDom (fun r => U r ω) (hU.cont ω) z = Ici 0 ∧
      (hitSet hU z k ω).Nonempty := by
    filter_upwards [ae_sigmaDom_eq_Ici hU z ha hc hz, hrec] with ω h1 h2
    exact ⟨h1, hitSet_nonempty_of_recurrent hU h1 h2 k⟩
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hNgood : ∀ ω, ω ∉ N → sigmaDom (fun r => U r ω) (hU.cont ω) z = Ici 0 ∧
      (hitSet hU z k ω).Nonempty := fun ω hω => by
    by_contra h; exact hω (hNsub h)
  have hae : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  set S : Ω → WithTop ℝ≥0 := hitTime hU z k with hSdef
  have hS : IsStoppingTime ℱ S := isStoppingTime_hitTime hU k
  set τ : Ω → ℝ≥0 := fun ω => if ω ∈ N then 0 else
    (clock (fun r => U r ω) (hU.cont ω) z (((S ω).untopA : ℝ≥0) : ℝ)).toNNReal with hτdef
  -- pathwise facts off `N`
  have hpath : ∀ ω, ω ∉ N → ∃ t : ℝ≥0, S ω = (t : WithTop ℝ≥0) ∧ t ∈ hitSet hU z k ω ∧
      (τ ω : ℝ) = clock (fun r => U r ω) (hU.cont ω) z (t : ℝ) := by
    intro ω hω
    obtain ⟨t, ht, hteq⟩ := exists_hitTime_eq_coe hU (hNgood ω hω).2
    refine ⟨t, hteq, ht, ?_⟩
    have hSω : S ω = (t : WithTop ℝ≥0) := hteq
    have hteq' : ((S ω).untopA : ℝ≥0) = t := by rw [hSω]; rfl
    simp only [hτdef, hω, ite_false, hteq']
    exact Real.coe_toNNReal _ (clock_nonneg (hU.cont ω) ht.2.1)
  have hτ0 : ∀ ω, ω ∈ N → τ ω = 0 := fun ω hω => by simp [hτdef, hω]
  refine ⟨⟨S, hS, ?_, τ, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- hfin
    filter_upwards [hae] with ω hω
    obtain ⟨t, ht, -⟩ := hpath ω hω
    rw [ht]; exact WithTop.coe_ne_top
  · -- hX
    have hNS : MeasurableSet[hS.measurableSpace] N := by
      rw [hS.measurableSet]
      have h0 := hnull N hNm hN0
      refine ⟨(le_iSup (fun t => ℱ t) 0) _ h0, fun i => ?_⟩
      exact (ℱ.mono (zero_le : (0 : ℝ≥0) ≤ i) _ h0).inter (hS i)
    have hX₀ : Measurable[hS.measurableSpace]
        (fun ω => (‖fHat hU z (0 : ℝ≥0) ω‖₊, thetaHat hU z (0 : ℝ≥0) ω)) := by
      have hle : sigmaFiltration hU z (0 : ℝ≥0) ≤ hS.measurableSpace :=
        sigmaFiltration_le_hitTime hU (by simp)
      have h1 := (measurable_fHat hU (z := z) (0 : ℝ≥0)).mono hle le_rfl
      have h2 := (((isStronglyProgressive_thetaHat hU (z := z)).stronglyAdapted
        (0 : ℝ≥0)).measurable).mono hle le_rfl
      exact (measurable_nnnorm.comp h1).prodMk h2
    have hX' : Measurable[hS.measurableSpace] (fun ω =>
        (‖stoppedValue (centeredOrZero U hU.cont z) S ω‖₊, stoppedValue (argOrZero hU z) S ω)) := by
      have h1 := measurable_stoppedValue
        (isStronglyProgressive_centeredOrZero hU.cont hU.adapted z) hS
      have h2 := measurable_stoppedValue (isStronglyProgressive_argOrZero hU z) hS
      exact (measurable_nnnorm.comp h1).prodMk h2
    have heq : (fun ω => (‖fHat hU z (τ ω) ω‖₊, thetaHat hU z (τ ω) ω)) = fun ω =>
        if ω ∈ N then (‖fHat hU z (0 : ℝ≥0) ω‖₊, thetaHat hU z (0 : ℝ≥0) ω) else
          (‖stoppedValue (centeredOrZero U hU.cont z) S ω‖₊,
            stoppedValue (argOrZero hU z) S ω) := by
      funext ω
      by_cases hω : ω ∈ N
      · simp only [hω, ite_true, hτ0 ω hω]
      · simp only [hω, ite_false]
        obtain ⟨t, hSt, ht, hτt⟩ := hpath ω hω
        obtain ⟨-, h2, h3, -⟩ := hitSet_sigma_facts hU (hNgood ω hω).1 ht hτt
        have hSt' : S ω = (t : WithTop ℝ≥0) := hSt
        have hl := ht.2.1
        have e1 : stoppedValue (centeredOrZero U hU.cont z) S ω =
            fPath (fun r => U r ω) (hU.cont ω) z (t : ℝ) := by
          simp only [stoppedValue, hSt']; exact centeredOrZero_eq hU.cont z hl
        have e2 : stoppedValue (argOrZero hU z) S ω =
            argPath (fun r => U r ω) (hU.cont ω) z (t : ℝ) := by
          simp only [stoppedValue, hSt']; exact argOrZero_eq hU z hl
        rw [e1, e2, h2, h3]
    rw [heq]
    let _ : MeasurableSpace Ω := hS.measurableSpace
    exact Measurable.ite hNS hX₀ hX'
  · -- hpos
    filter_upwards [hae] with ω hω
    obtain ⟨t, -, ht, hτt⟩ := hpath ω hω
    obtain ⟨-, -, hf, -⟩ := hitSet_sigma_facts hU (hNgood ω hω).1 ht hτt
    rw [hf]
    exact nnnorm_pos.2 (fPath_ne_zero (hU.cont ω) ht.2.1)
  · -- hobs
    filter_upwards [hae] with ω hω
    obtain ⟨t, hSt, ht, hτt⟩ := hpath ω hω
    have hall := (hNgood ω hω).1
    obtain ⟨h1, -, -, -⟩ := hitSet_sigma_facts hU hall ht hτt
    have e := pathObsAt_eq_obsC hU (z := z) (s := τ ω) (ω := ω) hall
    have hpp : postPath hU (sigmaTop hU z (τ ω)) ω = postPath hU S ω := by
      apply Subtype.ext
      funext s'
      have hSt' : S ω = (t : WithTop ℝ≥0) := hSt
      simp only [postPath, CPath.ofDriver, postDriver, h1, hSt']
    rw [e, hpp]
  · -- hstate
    filter_upwards [hae] with ω hω
    obtain ⟨t, -, ht, hτt⟩ := hpath ω hω
    obtain ⟨-, h2, -, -⟩ := hitSet_sigma_facts hU (hNgood ω hω).1 ht hτt
    rw [h2]
    have := (ComplexSLE.Recurrence.mem_latticeSet_iff_exp).1 ht.2.2
    simpa using this
  · -- hk
    filter_upwards [hae] with ω hω
    obtain ⟨t, -, ht, hτt⟩ := hpath ω hω
    exact (hitSet_sigma_facts hU (hNgood ω hω).1 ht hτt).2.2.2
  · -- hpast
    intro n hn
    have hle : sigmaFiltration hU z (n : ℝ≥0) ≤ hS.measurableSpace :=
      sigmaFiltration_le_hitTime hU (by exact_mod_cast hn)
    have h := (measurable_fHat hU (z := z) (n : ℝ≥0)).mono hle le_rfl
    exact Real.measurable_log.comp (measurable_norm.comp h)

end Datum

end ComplexSLE.Internal

end
