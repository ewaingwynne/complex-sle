# M10-B2: recurrence of stationary sums (from scratch)

Goal: a sorry-free proof of the EXACT statement of `ComplexSLE.External.recurrence_stationary`
(`ComplexSLE/External/RecurrenceStationary.lean`, read only) as
`ComplexSLE.Internal.ExternalProofs.recurrence_stationary` in
`ComplexSLE/Internal/ExternalProofs/RecurrenceStationary.lean` (helpers in further new files under
`ComplexSLE/Internal/ExternalProofs/` or `ComplexSLE/Infrastructure/Ergodic/`). Copy the theorem type verbatim.
Import no `ComplexSLE.External.*` module. Nothing in either Mathlib or the third-party repo proves this; the
argument below is elementary and needs no ergodic decomposition (and not even `hint`).

Notation: `S n ω = ∑ k ∈ range n, ξ k ω` (so `S 0 = 0`); stationarity `hstat` is equality of laws of the shifted
sequences on `ℕ → ℝ`, so for a measurable `B̃ ⊆ ℕ → ℝ`,
`P {ω | (fun n => ξ (n + k) ω) ∈ B̃} = P {ω | (fun n => ξ n ω) ∈ B̃}`.

Step 1 (no ε-return has probability 0). For `ε > 0` let `B̃ε = {x | ∀ n ≥ 1, ε ≤ |∑ k ∈ range n, x k|}` and
`Bε k = {ω | (fun n => ξ (n + k) ω) ∈ B̃ε}`. Claim `P (Bε 0) = 0`.
- Separation: if `j < k`, `ω ∈ Bε j` and `ω ∈ Bε k`... more precisely if `ω ∈ Bε j` and `j < k` then
  `|S k ω - S j ω| = |∑ i ∈ range (k - j), ξ (i + j) ω| ≥ ε`. So the reals `S k ω`, `k < N`, `ω ∈ Bε k`, are
  pairwise `ε`-separated and lie in `[-M_N ω, M_N ω]`, `M_N ω = max_{k ≤ N} |S k ω|`; hence
  `#{k < N | ω ∈ Bε k} ≤ 2 M_N ω / ε + 1`.
- Stationarity: `∫ #{k < N | ω ∈ Bε k} = N · P (Bε 0)`.
- From `hlim` (Cesàro averages → 0 a.s.) get `M_N / N → 0` a.s. (elementary).
- So `P (Bε 0) ≤ ∫ min 1 (2 M_N/(ε N) + 1/N) → 0` by dominated convergence.
Step 2 (infinitely often). By Step 1 and stationarity, `P (Bδ k) = 0` for all `k` and all rational `δ > 0`, so a.s.
for every `k` and every `δ > 0` there is `n ≥ 1` with `|S (k + n) - S k| < δ`. If for some `ε` the set
`{n | |S n ω| < ε}` were finite (it contains `0`), let `L` be its maximum; with `δ < ε - |S L ω|` the return after `L`
gives `|S (L + n) ω| < ε`, contradicting maximality. Conclude `∃ᶠ n in atTop, |S n ω| < ε` for every `ε > 0`.
Measurability: the events are countable intersections/unions of measurable sets (`hmeas`); `Bε k` is the preimage
of a measurable set under the measurable map `ω ↦ (fun n => ξ (n + k) ω)`.

Checks: `lake build ComplexSLE.Internal.ExternalProofs.RecurrenceStationary`;
`python3 -I tools/leanprobe.py axioms ComplexSLE.Internal.ExternalProofs.RecurrenceStationary ComplexSLE.Internal.ExternalProofs.recurrence_stationary`
(only propext, Classical.choice, Quot.sound). Every new file a module, at most 1500 lines.
Stop condition: a precise obstruction, with the failing goal.
Handoff: files created, approach, exact commands and output, axioms, anything unproved.

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
