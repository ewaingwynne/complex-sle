/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Frozen.Defs.IsAdmissibleDensity
public import ComplexSLE.Frozen.Defs.IntegralII
public import ComplexSLE.Frozen.Defs.IsSLEDriver
public import ComplexSLE.Frozen.Defs.LeftHull
public import ComplexSLE.Internal.Stationary.SLEStatLaw
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import ComplexSLE.Internal.Phases.Prop32BUpEvents
import ComplexSLE.Internal.Phases.Prop32BUpMarkov
import ComplexSLE.Internal.Phases.Prop32BUpHit
import ComplexSLE.Internal.Phases.Prop32BUpZeroOne

/-!
# Proposition 3.2(b): the upgrade from the random point to every `z` (M7/E5)

`proposition_3_2_b_of_conv` has exactly the conclusion (and the hypotheses `a b c p hp hII Ω P U hU
z hz`) of the frozen anchor `ComplexSLE.proposition_3_2_b` (paper.tex:L1276-1283, R14 `ε`-form),
with one extra explicit hypothesis `hconv`:

  for every adapted `SLE_Σ` driver `U'` on any `Ω' : Type`, with `μ = P' ⊗ ν`,
  `ν = admissibleMeasure p`, `μ(∃ ε > 0, ∀ t < T_z, ε ≤ dist(z, L_t)) > 0` at the random point
  `z = e^{iu}` (`lem-converse-w-o-upgrade`, `E 𝔮(𝐳) > 0`, proved separately).

Proof (paper.tex:L1786-1816 with the approved correction R27: the hitting lemma replaces Girsanov):

1. `q(ξ) = P(StaysAway(U, ξ))` satisfies `q(ξ) = q(ξ/|ξ|)` (`evProb_eq_unit`, Prop32BUpMarkov).
2. `Λ = {u | q(e^{iu}) > 0}` is nonempty (`exists_evProb_unit_pos`, Fubini from `hconv`) and open
   (`isOpen_evProb_unit_pos`: the Koebe ball, `staysAway_of_staysAwayBy`, Prop32BUpEvents).
3. `Λ = ℝ` (`evProb_unit_pos`, Prop32BUpHit): `θ̂(e^{iu})` hits a level `θ* ∈ Λ` with positive
   probability (R27, `sle_hits_lower`/`sle_hits_upper`), so `θ̂_s ∈ Λ` for some rational `s` with
   positive probability, and `q(e^{iu}) = ∫ q(f̂_s) dP > 0` (Markov step at the σ-time `σ_z(s)`).
   Hence `q(z) > 0` for all `z ≠ 0` (`evProb_pos`).
4. Koebe ball and compactness of the unit circle: `q ≥ q_* > 0` (`exists_lowerBound`).
5. Martingale 0-1 step (`ae_staysAway_of_lowerBound`, Prop32BUpZeroOne): Lévy's upward theorem.

Consumes the EXTERNALs `strongMarkov_sleDriver`, and through the polar layer
`ito_formula`, `timeChange_isContLocalMartingale`, `hormander_oneDim`; no Girsanov.
-/

public section

open scoped NNReal ENNReal
open MeasureTheory Metric Set

namespace ComplexSLE.Internal

open Polar

/-- **Proposition 3.2(b), upgrade from the random point to every `z`, on a fixed probability
space** (paper.tex:L1786-1816, with the correction R27). Same hypotheses and conclusion as the
frozen `ComplexSLE.proposition_3_2_b` (R14 `ε`-form of "a.s. `lim_{t → T_z⁻} dist(z, L_t) > 0`"),
plus the explicit input `hconv` for the space `(Ω, P)` of the statement only: for every adapted
`SLE_Σ` driver `U'` on `(Ω, P)` (with any filtration), the event `∃ ε > 0, ∀ t < T_z,
ε ≤ dist(z, L_t)` has positive probability for the random point `z = e^{iu}`,
`(ω, u) ∼ P ⊗ admissibleMeasure p` (`lem-converse-w-o-upgrade`). -/
theorem proposition_3_2_b_of_conv_on (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (p : ℝ → ℝ) (hp : IsAdmissibleDensity a b c p) (hII : 0 < integralII a b c p)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hconv : ∀ (ℱ' : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (U' : ℝ≥0 → Ω → ℂ),
      IsSLEDriverAdapted a b c U' P ℱ' →
      0 < (P.prod (admissibleMeasure p))
        {x : Ω × ℝ | ∃ ε > 0, ∀ t : ℝ≥0,
          (t : ℝ≥0∞) < absorbingTime (fun s => U' s x.1) (unitPt x.2) →
            ε ≤ infDist (unitPt x.2) (leftHull (fun s => U' s x.1) t)})
    (U : ℝ≥0 → Ω → ℂ) (hU : IsSLEDriver a b c U P) (z : ℂ) (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, ∃ ε > 0, ∀ t : ℝ≥0, (t : ℝ≥0∞) < absorbingTime (U · ω) z →
      ε ≤ infDist z (leftHull (U · ω) t) := by
  have _ := hII
  have hν : IsProbabilityMeasure (admissibleMeasure p) := isProbabilityMeasure_admissibleMeasure hp
  obtain ⟨ℱ, U', hUU', -, hnull, hU'⟩ := hU.exists_adapted
  have hΛ := exists_evProb_unit_pos hU' (hconv ℱ U' hU')
  have hpos : ∀ ξ : ℂ, ξ ≠ 0 → 0 < evProb StaysAway P U' ξ := fun ξ hξ =>
    evProb_pos hnull hU' ha hb hc hΛ hξ
  obtain ⟨qs, hqs, hlow⟩ := exists_lowerBound hU' ha hc hpos
  have hz' := ae_staysAway_of_lowerBound hU' ha hc hqs hlow hz
  filter_upwards [hz', hUU'] with ω h1 h2
  have e : (fun t => U' t ω) = fun t => U t ω := funext h2
  rw [e] at h1
  exact h1

/-- **Proposition 3.2(b), upgrade from the random point to every `z`** (paper.tex:L1786-1816, with
the correction R27). Same hypotheses and conclusion as the frozen `ComplexSLE.proposition_3_2_b`
(R14 `ε`-form of "a.s. `lim_{t → T_z⁻} dist(z, L_t) > 0`"), plus the explicit input `hconv`:
for every adapted `SLE_Σ` driver on any `Ω' : Type`, the event `∃ ε > 0, ∀ t < T_z,
ε ≤ dist(z, L_t)` has positive probability for the random point `z = e^{iu}`,
`(ω, u) ∼ P' ⊗ admissibleMeasure p` (`lem-converse-w-o-upgrade`). -/
theorem proposition_3_2_b_of_conv (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (p : ℝ → ℝ) (hp : IsAdmissibleDensity a b c p) (hII : 0 < integralII a b c p)
    (hconv : ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (ℱ' : Filtration ℝ≥0 ‹MeasurableSpace Ω'›) (U' : ℝ≥0 → Ω' → ℂ),
      IsSLEDriverAdapted a b c U' P' ℱ' →
      0 < (P'.prod (admissibleMeasure p))
        {x : Ω' × ℝ | ∃ ε > 0, ∀ t : ℝ≥0,
          (t : ℝ≥0∞) < absorbingTime (fun s => U' s x.1) (unitPt x.2) →
            ε ≤ infDist (unitPt x.2) (leftHull (fun s => U' s x.1) t)})
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ℝ≥0 → Ω → ℂ) (hU : IsSLEDriver a b c U P) (z : ℂ) (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, ∃ ε > 0, ∀ t : ℝ≥0, (t : ℝ≥0∞) < absorbingTime (U · ω) z →
      ε ≤ infDist z (leftHull (U · ω) t) :=
  proposition_3_2_b_of_conv_on a b c ha hb hc p hp hII Ω P (hconv Ω P) U hU z hz

end ComplexSLE.Internal

end
