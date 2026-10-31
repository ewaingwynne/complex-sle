/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Disconnect.DiscEventMeas
public import ComplexSLE.Internal.Phases.Prop32BUpMarkov
public import ComplexSLE.Internal.Polar.PolarContMeas

/-!
# Theorem 1.10(a), upgrade step: lower semicontinuity of `q(z) = P(Disc(U, z))` and `Λ ≠ ∅` (M8/T5b)

Source: paper.tex:L2199-2217 (proof of Theorem 1.10(a), "very similar to the proof of
Proposition 3.2(b)"), with the correction R27 (ERRATA.md).

For an adapted `SLE_Σ` driver `U` put `q(ξ) = evProb Disc P U ξ = P(Disc(U, ξ))`.

* `lowerSemicontinuous_evProb_disc`: `q` is lower semicontinuous on `ℂ`. The sections
  `{w | Disc u w}` of the event are open for a continuous path (`isOpen_setOf_disc`), so a point
  of the event at `z` is a point of the event at `w` for all `w` near `z`; for a sequence
  `w_n → z` this gives `{Disc z} ⊆ ⋃_N ⋂_{n ≥ N} {Disc w_n}` (a Fatou argument at the level of
  sets) and hence `q(z) ≤ liminf q(w_n)`.
* `isOpen_evProb_disc_unit_pos`: `Λ = {u | q(e^{iu}) > 0}` is open.
* `exists_evProb_disc_pos_of_lemma41`: if Lemma 4.1 holds for `U` then `q(z) > 0` for some `z ≠ 0`
  (hence `Λ ≠ ∅`): the open set `V` of Lemma 4.1 misses `L_t` and hence `0`, and any `z₀ ∈ V`
  satisfies `Disc(U, z₀)` on the event of Lemma 4.1.
-/

public section

open scoped NNReal ENNReal Topology
open MeasureTheory Filter Set

namespace ComplexSLE.Internal

open Polar

section Lsc

variable {Ω : Type} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {a b c : ℝ} {U : ℝ≥0 → Ω → ℂ}

/-- **`q(z) = P(Disc(U, z))` is lower semicontinuous** (Fatou, openness of the sections of
`Disc`). -/
theorem lowerSemicontinuous_evProb_disc (hU : IsSLEDriverAdapted a b c U P ℱ) :
    LowerSemicontinuous (evProb Disc P U) := by
  intro z y hy
  by_contra hcon
  have hfreq : ∃ᶠ w in 𝓝 z, evProb Disc P U w ≤ y := by
    refine Filter.not_eventually.1 ?_ |>.mono fun w hw => not_lt.1 hw
    exact hcon
  obtain ⟨w, hw, hwle⟩ := exists_seq_forall_of_frequently hfreq
  set A : ℕ → Set Ω := fun n => {ω | Disc (fun s => U s ω) (w n)} with hA
  set C : ℕ → Set Ω := fun N => ⋂ n, ⋂ (_ : N ≤ n), A n with hC
  have hCmono : Monotone C := fun N N' hNN' => by
    refine Set.iInter₂_mono' fun n hn => ⟨n, hNN'.trans hn, subset_rfl⟩
  have hsub : {ω | Disc (fun s => U s ω) z} ⊆ ⋃ N, C N := by
    intro ω hω
    have hopen := isOpen_setOf_disc (hU.cont ω)
    have hev : ∀ᶠ n in atTop, w n ∈ {x | Disc (fun s => U s ω) x} :=
      hw.eventually (hopen.mem_nhds hω)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    exact mem_iUnion.2 ⟨N, mem_iInter₂.2 fun n hn => hN n hn⟩
  have hle : evProb Disc P U z ≤ y := by
    calc evProb Disc P U z ≤ P (⋃ N, C N) := measure_mono hsub
      _ = ⨆ N, P (C N) := hCmono.measure_iUnion
      _ ≤ y := by
        refine iSup_le fun N => ?_
        refine le_trans (measure_mono ?_) (hwle N)
        intro ω hω
        have := mem_iInter.1 (mem_iInter.1 hω N) le_rfl
        exact this
  exact absurd hy (not_lt.2 hle)

/-- `Λ = {u | q(e^{iu}) > 0}` is open. -/
theorem isOpen_evProb_disc_unit_pos (hU : IsSLEDriverAdapted a b c U P ℱ) :
    IsOpen {u : ℝ | 0 < evProb Disc P U (unitPt u)} :=
  ((lowerSemicontinuous_evProb_disc hU).isOpen_preimage 0).preimage continuous_unitPt

/-- **`Λ ≠ ∅` from Lemma 4.1** (paper.tex:L2205): if Lemma 4.1 holds for the driver `U`
(with `U 0 = 0` everywhere), then `P(Disc(U, z₀)) > 0` for some `z₀ ≠ 0`. -/
theorem exists_evProb_disc_pos_of_lemma41 (h0 : ∀ ω, U 0 ω = 0)
    (hL : ∃ (V : Set ℂ) (t : ℝ≥0), IsOpen V ∧ Bornology.IsBounded V ∧ V.Nonempty ∧ 0 < t ∧
      0 < P {ω | Disjoint V (leftHull (fun s => U s ω) t) ∧
        DisconnectsFromInfinity (leftHull (fun s => U s ω) t) V}) :
    ∃ z : ℂ, z ≠ 0 ∧ 0 < evProb Disc P U z := by
  obtain ⟨V, t, -, -, ⟨z₀, hz₀⟩, ht, hS⟩ := hL
  set S : Set Ω := {ω | Disjoint V (leftHull (fun s => U s ω) t) ∧
    DisconnectsFromInfinity (leftHull (fun s => U s ω) t) V} with hSdef
  have hne : S.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [hcon, measure_empty] at hS
    exact lt_irrefl _ hS
  obtain ⟨ω₀, hω₀⟩ := hne
  have hz0 : z₀ ≠ 0 := by
    rintro rfl
    have := driver_zero_mem_leftHull (fun s => U s ω₀) t
    rw [h0 ω₀] at this
    exact Set.disjoint_left.1 hω₀.1 hz₀ this
  refine ⟨z₀, hz0, lt_of_lt_of_le hS (measure_mono fun ω hω => ?_)⟩
  refine ⟨t, ht, fun hmem => Set.disjoint_left.1 hω.1 hz₀ hmem, ?_⟩
  exact disconnectsFromInfinity_mono_right hω.2 (singleton_subset_iff.2 hz₀)

end Lsc

end ComplexSLE.Internal

end
