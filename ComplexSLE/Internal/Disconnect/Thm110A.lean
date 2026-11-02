/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsSLEDriver
public import ComplexSLE.Frozen.Defs.IsSLEDriverAdapted
public import ComplexSLE.Frozen.Defs.LeftHull
public import ComplexSLE.Frozen.Defs.DisconnectsFromInfinity
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import ComplexSLE.Internal.Disconnect.Thm110ALsc
import ComplexSLE.Internal.Disconnect.Thm110AMarkov
import ComplexSLE.Internal.Disconnect.Thm110AZeroOne

/-!
# Theorem 1.10(a) from Lemma 4.1: the upgrade to every `z` (M8/T5b)

`theorem_1_10_a_of_lemma41` has exactly the binders and the conclusion of the frozen anchor
`ComplexSLE.theorem_1_10_a` (paper.tex:L502-507: for each `z ≠ 0`, a.s. some `L_t`, `t > 0`,
disconnects `z` from `∞` without containing it), plus one extra explicit hypothesis `hL41`
(placed after `hc`): Lemma 4.1 (paper.tex:L1938-2224), in the internal form of
`review/plans/M8.md`: for every `SLE_Σ` driver `U'` on every probability space there are a bounded
open nonempty `V` and a time `t > 0` such that, with positive probability, `L_t` misses `V` and
disconnects it from `∞`.

Proof (paper.tex:L2199-2217, "very similar to the proof of Proposition 3.2(b)", with the correction
R27: the hitting lemma replaces Girsanov):

1. Pass to the adapted everywhere-continuous version `U'` of `U` (`IsSLEDriver.exists_adapted`).
   `q(ξ) = P(Disc(U', ξ))` satisfies `q(rξ) = q(ξ)` (`evProb_mul`, `evProb_eq_unit`).
2. `Λ = {u | q(e^{iu}) > 0} ≠ ∅` (`exists_evProb_disc_pos_of_lemma41`): any `z₀ ∈ V` is not `0`, as
   `0 ∈ L_t`, and satisfies `Disc(U', z₀)` on the event of Lemma 4.1.
3. `q` is lower semicontinuous (`lowerSemicontinuous_evProb_disc`, Fatou), so `Λ` is open.
4. `Λ = ℝ` (`evProb_disc_unit_pos`): R27 hitting lemma and the Markov inequality at `σ_z(s)`
   (`lintegral_evProb_fHat_le`, from the restart implication `disc_of_disc_restart`).
5. `q ≥ q_* > 0` on `ℂ ∖ {0}` (`exists_lowerBound_disc`), lower semicontinuity and compactness of
   the unit circle.
6. Lévy's upward theorem (`ae_disc_of_lowerBound`): `P(Disc(U', z)) = 1`; transfer back to `U`.

Uses the classical inputs `strongMarkov_sleDriver` and, through the polar and recurrence layers,
`ito_formula` and `timeChange_isContLocalMartingale` (and what they use), all proved in-project
(`Internal/ExternalProofs/`).
-/

public section

open scoped NNReal ENNReal
open MeasureTheory

namespace ComplexSLE.Internal

/-- **Theorem 1.10(a) from Lemma 4.1** (paper.tex:L2199-2217, with the correction R27). Same
binders and conclusion as the frozen `ComplexSLE.theorem_1_10_a`, plus the explicit hypothesis
`hL41` (Lemma 4.1): for every `SLE_Σ` driver on every probability space, some bounded open
nonempty `V` is, for some `t > 0` and with positive probability, disjoint from `L_t` and
disconnected from `∞` by `L_t`. -/
theorem theorem_1_10_a_of_lemma41 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (hL41 : ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (U' : ℝ≥0 → Ω' → ℂ), IsSLEDriver a b c U' P' →
      ∃ (V : Set ℂ) (t : ℝ≥0), IsOpen V ∧ Bornology.IsBounded V ∧ V.Nonempty ∧ 0 < t ∧
        0 < P' {ω | Disjoint V (leftHull (U' · ω) t) ∧
          DisconnectsFromInfinity (leftHull (U' · ω) t) V})
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ℝ≥0 → Ω → ℂ) (hU : IsSLEDriver a b c U P) (z : ℂ) (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, ∃ t : ℝ≥0, 0 < t ∧ z ∉ leftHull (U · ω) t ∧
      DisconnectsFromInfinity (leftHull (U · ω) t) {z} := by
  obtain ⟨ℱ, U', hUU', h0, hnull, hU'⟩ := hU.exists_adapted
  obtain ⟨z₀, hz₀, hq₀⟩ :=
    exists_evProb_disc_pos_of_lemma41 h0 (hL41 Ω P U' hU'.toIsSLEDriver)
  have hΛ := exists_evProb_disc_unit_pos hU' hz₀ hq₀
  have hpos : ∀ ξ : ℂ, ξ ≠ 0 → 0 < evProb Disc P U' ξ := fun ξ hξ =>
    evProb_disc_pos hnull hU' ha hb hc hΛ hξ
  obtain ⟨qs, hqs, hlow⟩ := exists_lowerBound_disc hU' hpos
  have hz' := ae_disc_of_lowerBound hU' ha hc hqs hlow hz
  filter_upwards [hz', hUU'] with ω h1 h2
  have e : (fun t => U' t ω) = fun t => U t ω := funext h2
  rw [e] at h1
  exact h1

end ComplexSLE.Internal

end
