# M8 / T5b — Theorem 1.10(a) from Lemma 4.1: the upgrade to every z (prover brief, Sonnet)

Source: arXiv:2203.07313v4 proof of Theorem 1.10(a), L2199-2217 ("very similar to the proof of Prop 3.2(b)"), with the
approved correction ERRATA.md R27 (hitting lemma instead of Girsanov; P13 covers this step too). Orchestrator plan:
review/plans/M8.md §4. This is the M7-E5 argument (files ComplexSLE/Internal/Phases/Prop32BUp*.lean — read them first; reuse
their generic lemmas, adapt their StaysAway-specific ones) applied to the disconnection event, with two simplifications:
Λ ≠ ∅ comes directly from Lemma 4.1 (no Fubini), and the uniform lower bound comes from lower semicontinuity (no Koebe ball).

Goal (new files `ComplexSLE/Internal/Disconnect/Thm110A*.lean`, namespace `ComplexSLE.Internal`): a theorem
`theorem_1_10_a_of_lemma41` with EXACTLY the binders and conclusion of the frozen `ComplexSLE.theorem_1_10_a`
(ComplexSLE/Frozen/Theorem_1_10_A.lean — read-only; DRAFT: do NOT import it or Internal/Theorem_1_10_A.lean) plus one extra
explicit hypothesis, placed after `hc`:
```lean
(hL41 : ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (U' : ℝ≥0 → Ω' → ℂ),
  IsSLEDriver a b c U' P' → ∃ (V : Set ℂ) (t : ℝ≥0), IsOpen V ∧ Bornology.IsBounded V ∧ V.Nonempty ∧ 0 < t ∧
    0 < P' {ω | Disjoint V (leftHull (U' · ω) t) ∧ DisconnectsFromInfinity (leftHull (U' · ω) t) V})
```
(this is the statement of Lemma 4.1 being proved concurrently in Internal/Disconnect/Lemma41*.lean by another Sonnet; do not
touch those files). You may use hL41 only for drivers on the given space (Ω, P) if that is all you need.

Available (committed): `ComplexSLE/Internal/Disconnect/DiscEvent*.lean`: `DiscAt`, `Disc` (literally the frozen event),
`isOpen_setOf_disc`, `measurableEvents_disc`, `scaleInvariantEvents_disc`, `disc_of_disc_restart` (restart, one direction),
`measurableSet_setOf_discAt` (ℱ_t-measurable for adapted drivers), `measurableSet_setOf_disc`, `disc_iff_exists_rat`;
`ComplexSLE/Infrastructure/Planar/Disconnect.lean` (`disconnectsFromInfinity_of_preconnected`, `_mono`, `_singleton_iff`).
M7 machinery: `evProb`, `measure_inter_postDriver`, `evProb_mul`, `evProb_eq_unit`, `measurable_evProb`
(Prop32BUpMarkov/Hit.lean); `ae_mem_of_forall_measureReal_le` (Lévy upward, Prop32BUpZeroOne.lean); the R27 hitting route
in `evProb_unit_pos` (Prop32BUpHit.lean) using `sle_hits_lower` / `sle_hits_upper` (Internal/Recurrence/SLE.lean), θ̂ and
σ-times (Internal/Polar/*, `sigmaFiltration`, `isStoppingTime_sigmaTop`, `ae_sigmaDom_eq_Ici`), `IsSLEDriver.exists_adapted`.

Blueprint:
1. Pass to the adapted everywhere-continuous version U' (`exists_adapted`, as Prop32BUp.lean does); q(ξ) := evProb Disc P U' ξ.
   Scaling: q(rξ) = q(ξ), q(ξ) = q(ξ/|ξ|).
2. Λ := {u : ℝ | 0 < q(e^{iu})} ≠ ∅: hL41 for U' gives V, t, a set S of positive outer measure. Since U' 0 ω = 0, 0 ∈ L_t(ω)
   and V misses L_t(ω) for ω ∈ S (S ≠ ∅), so 0 ∉ V; pick z₀ ∈ V: z₀ ≠ 0, S ⊆ {Disc(U' ω, z₀)} (DiscAt at t, as {z₀} ⊆ V),
   hence q(z₀) ≥ P S > 0 (monotonicity of outer measure; the Disc event is measurable).
3. q is lower semicontinuous on ℂ: the sections {w | Disc u w} are open (isOpen_setOf_disc), so by Fatou
   liminf_{w→z} q(w) ≥ q(z). Hence Λ is open.
4. Λ = ℝ (R27, as in `evProb_unit_pos`): for every u, θ̂(e^{iu}) hits a level θ* ∈ Λ (below for c ≥ 0, above for c ≤ 0, using
   2π-periodicity) with positive probability; Λ open ⇒ θ̂_s ∈ Λ with positive probability for some rational s. Markov at the
   σ-time σ_z(s) (`measure_inter_postDriver`) plus the pathwise implication `disc_of_disc_restart` and scaling give
   q(z) ≥ ∫ q(f̂_s(z)) dP > 0. Only the inequality "≥" is available (Disc is not future-dependent in the iff sense).
5. Uniform bound: q > 0 and lower semicontinuous on the compact unit circle ⇒ q ≥ q* > 0 there; by scaling on ℂ \ {0}.
6. 0-1 (as in `ae_staysAway_of_lowerBound`): with 𝒢_n := ℱ_{σ_z(n)} and E := {Disc(U', z)}: for A ∈ 𝒢_n,
   q* P(A) ≤ P(A ∩ E) (Markov at σ_z(n) + restart implication); E is a.s. equal to ⋃_{n, rational q} ({DiscAt at q} ∩
   {q ≤ σ_z(n)}) ∈ ⨆ 𝒢_n ({DiscAt at q} ∈ ℱ_q by `measurableSet_setOf_discAt`; B ∈ ℱ_q ⇒ B ∩ {q ≤ σ} ∈ ℱ_σ; DiscAt at q
   needs q < T_z and σ_z(n) ↑ T_z). Lévy upward ⇒ P(E) = 1. Transfer back from U' to U.

Allowed EXTERNALs (through the reused M7 machinery only): strongMarkov_sleDriver, ito_formula, timeChange_isContLocalMartingale,
hormander_oneDim (whatever `sle_hits_*` and the polar layer consume). Ownership: new files
`ComplexSLE/Internal/Disconnect/Thm110A*.lean` only; scratch in `.lake/probes/m8-t5b/`.
Checks: `lake build ComplexSLE.Internal.Disconnect.Thm110A`; `tools/check.sh --quick`;
`python3 -I tools/leanprobe.py externals ComplexSLE.Internal.Disconnect.Thm110A ComplexSLE.Internal.theorem_1_10_a_of_lemma41`.
Budget ~5 hours; land what is proved, report the rest precisely.

## Hard rules (repeat verbatim in every worker brief)


1. Never edit a file under `ComplexSLE/Frozen/`, `frozen-anchor-manifest.json`,
   `DEPGRAPH*.md`, `STATUS.md`, `ERRATA.md`, `lakefile.toml`, `lean-toolchain`
   or `lake-manifest.json`. If a frozen declaration looks wrong, stop and report.
2. No `sorry`, `admit`, `axiom`, `opaque` placeholders, `native_decide`,
   `implemented_by`, `@[extern]`, `unsafe`, or `set_option maxHeartbeats`
   (or any other heartbeat / recursion / debug override) anywhere in tracked files.
   Unfinished work stays out of `ComplexSLE/` or is reported as unfinished.
3. Never add a hypothesis to a source-facing statement to make a proof go through.
   A needed intermediate result is proved, not assumed.
4. Never import a frozen anchor that is in state `DRAFT_SORRY`, nor its provider
   module (see the manifest). Consume only sealed anchors, your own files, and
   `EXTERNAL` inputs through `ComplexSLE/External/` when your brief lists them.
5. Every Lean file is a `module`: copyright comment, `module`, imports
   (`public import` for anything statements need), module docstring,
   `public section` (`@[expose] public section` for source-facing definitions).
6. At most 1500 lines per file. Split larger files.
7. Do not run `lake clean`, delete anything under `.lake/`, or modify Mathlib.
8. Do not commit; the orchestrator commits. Do not touch files you were not given.
9. Scratch and probe files go outside `ComplexSLE/` (e.g. `.lake/probes/`) and are
   deleted after use.
10. Report exactly: files changed, approach, the exact commands run and their output,
    `#print axioms` for every new public theorem, and anything unproved or uncertain.
11. Do not spawn subagents, forks or parallel workers of your own (the orchestrator enforces a two-agent cap).

Handoff: files changed; exact statements; approach; commands and outputs; externals; anything unproved.
