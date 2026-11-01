# M10-A6: time change of a continuous local martingale

Goal: a sorry-free proof of the EXACT statement of `ComplexSLE.External.timeChange_isContLocalMartingale`
(`ComplexSLE/External/TimeChangeIsContLocalMartingale.lean`, read only) as
`ComplexSLE.Internal.ExternalProofs.timeChange_isContLocalMartingale` in
`ComplexSLE/Internal/ExternalProofs/TimeChangeIsContLocalMartingale.lean` (helpers in new files under
`ComplexSLE/Infrastructure/Stochastic/TimeChange*.lean` or ported files). Copy the theorem type verbatim.
The provider must not import any `ComplexSLE.External.*` module, directly or transitively. NOTE:
`ComplexSLE/Infrastructure/Stochastic/StoppedLocalMartingale.lean` itself imports this external (it derives stopped
local martingales from it), so you must NOT import `StoppedLocalMartingale` or anything that imports it; check every
import closure with `grep -rl "import ComplexSLE.External" ComplexSLE` and following imports.

Available, external-free: `ComplexSLE/Infrastructure/Stochastic/ContinuousOptionalStopping.lean` (a continuous
martingale stopped at any stopping time is a martingale; `setIntegral_apply_stoppingTime_eq_min` for bounded finite
stopping times), `TimeChangeTransfer.lean` (`IsContLocalMartingale.of_consistent_seq`,
`isStronglyProgressive_indicator_lt`), `LocalMartingaleAlgebra.lean`, `CondShift.lean` (check each is external-free
before importing). Third-party material you may port (read only, run nothing inside
`~/ext-src/lean-formalizations`, commit 31e7483):
- `ReflectedGMS/Forms/StoppedFormAssociationOptionalSampling.lean` and its local imports:
  `martingale_stoppedValue_clock_of_bound_of_ae` (time change of a BOUNDED right-continuous martingale by a monotone
  finite family of stopping times), `setIntegral_stoppedValue_eq_of_le_of_le_const`;
- `QuantumZipper/Proofs/ItoLite/OptionalStopping.lean` (`isStoppingTime_hittingBtwn_of_isClosed`,
  `martingale_stoppedProcess_of_continuous`).
Ported files go to the mirrored path `ComplexSLE/Infrastructure/Zipper/<upstream path>`, keep upstream namespaces,
start with our standard comment block followed by the three lines
`Ported from leobon12/lean-formalizations @31e7483,` / `<upstream path>;` / `trimmed and adapted to Lean v4.36 and the module system.`,
and are converted to the module system; check first whether a file is already ported there.

Route: localize `M` by its localizing times `τ n` and the exit times `ρ n` of `[-n, n]` (closed-set hitting times of
an everywhere-continuous adapted process are stopping times), handling an unbounded `M 0` (e.g. `|M 0| > n` gives the
constant process); each `N = M^{τ n ∧ ρ n}` is a bounded continuous martingale on the relevant event; optional
sampling for bounded stopping times plus bounded convergence gives that `s ↦ N (σ s)` is a `𝒢`-martingale; the
localizing sequence for `M ∘ σ` is `ρ' n = inf {s | τ n ∧ ρ n ≤ σ s}` (a `𝒢`-stopping time since `𝒢 s = ℱ_{σ s}`), with
`(M ∘ σ)^{ρ' n} = N ∘ σ`; progressive measurability of `M ∘ σ` for `𝒢` from adaptedness and path continuity.

Checks: `lake build ComplexSLE.Internal.ExternalProofs.TimeChangeIsContLocalMartingale`;
`python3 -I tools/leanprobe.py axioms <module> ComplexSLE.Internal.ExternalProofs.timeChange_isContLocalMartingale`
(only propext, Classical.choice, Quot.sound). Every new file a module, at most 1500 lines.
Stop condition: a precise obstruction (e.g. the statement is false as written), with the failing goal.
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
