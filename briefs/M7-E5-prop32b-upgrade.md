# M7 / E5 — Prop 3.2(b): upgrade from the random point to every z (prover brief, Sonnet)

Source: proof of Prop 3.2(b) L1786-1816, with the approved correction ERRATA.md R27 (hitting lemma replaces Girsanov).
Goal (INTERNAL, new files ComplexSLE/Internal/Phases/Prop32BUp*.lean): a theorem with EXACTLY the conclusion of the frozen
ComplexSLE.proposition_3_2_b (ComplexSLE/Frozen/Proposition_3_2_B.lean, read-only; R14 ε-form "∃ ε > 0, ∀ t < T_z, ε ≤ infDist z L_t")
from the frozen hypotheses PLUS one explicit input hypothesis
  hconv : for the random point (μ = P'.prod (admissibleMeasure p) for every adapted SLE driver on any Ω' : Type),
          μ(lim_{t→T_z} dist(z, L_t) > 0) > 0      [state it in the ε-form; this is lem-converse-w-o-upgrade, being proved separately]
(name it proposition_3_2_b_of_conv). Steps (paper + R27):
1. q(z) := P(the ε-form event at z); scale invariance gives q(z) = q(z/|z|) (Phases/Prop32AEvents.lean has the scaling of the
   distance; adapt to the "stays away" event — Phases/EventMeasEvents.lean measurableEvents_hull_stays_away).
2. Λ := {u : q(e^{iu}) > 0} has positive ν-measure (from hconv by Fubini), hence is nonempty.
3. R27 hitting lemma (Internal/Recurrence/SLE.lean sle_hits_lower / sle_hits_upper — for c ≥ 0 resp. c ≤ 0): θ̂(z) hits a level θ* with
   e^{iθ*} ∈ Λ with positive probability (choose θ* below arg z for c ≥ 0, above for c ≤ 0); together with future dependence
   (the "stays away" analogue of futureDependentEvents_hull_approach) + scaling + strong Markov at the hitting σ-time
   (Phases/AllZMarkov.lean; Stationary/PathStatMarkov.lean) this gives q(z) > 0 for all z ≠ 0.
4. Koebe ball + compactness (L1806-1810, step:prop-ii-b-koebe-ball: EXTERNAL koebe_distortion): if the event holds at z with
   radius r then it holds for all w ∈ B(z, r/16) (with 15r/16); hence q is bounded below by some q_* > 0 on the unit circle (finite
   cover), so everywhere by scaling.
5. Martingale 0-1 (L1811-1816): P(event | ℱ_{σ_z(t̃)}) ≥ q_* for all t̃ (strong Markov + future dependence + scaling), and Lévy's
   upward theorem (Mathlib: MeasureTheory.Integrable.tendsto_ae_condExp or Martingale convergence for condExp of an indicator)
   gives the indicator ≥ q_* a.s., so the event has probability 1.
Allowed inputs: Mathlib; sealed defs/anchors; Internal/Infrastructure lemmas; approved EXTERNALs (koebe_distortion, koebe_quarter,
strongMarkov, markov_oneDim, hormander, ito, timeChange). Ownership: new files ComplexSLE/Internal/Phases/Prop32BUp*.lean only;
scratch in your own .lake/probes subdirectory. Another Sonnet works on Phases/KoebeChain*.lean. Checks: lake build; leanprobe
externals; tools/check.sh --quick. Budget ~4 hours; land what is proved, report the rest precisely.

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
