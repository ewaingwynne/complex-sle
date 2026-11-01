# M10-A5: strong Markov property of the SLE_Σ driver

Goal: a sorry-free proof of the EXACT statement of `ComplexSLE.External.strongMarkov_sleDriver`
(`ComplexSLE/External/StrongMarkovSLEDriver.lean`, read only) as
`ComplexSLE.Internal.ExternalProofs.strongMarkov_sleDriver` in
`ComplexSLE/Internal/ExternalProofs/StrongMarkovSLEDriver.lean` (helpers in new files under
`ComplexSLE/Infrastructure/Stochastic/StrongMarkov*.lean` or ported files). Copy the theorem type verbatim.
The provider must not import any `ComplexSLE.External.*` module, directly or transitively (check import closures:
e.g. `Infrastructure/Stochastic/StoppedLocalMartingale.lean` imports an external).

Definitions: `ComplexSLE/Frozen/Defs/{IsSLEDriver,IsSLEDriverAdapted,ComplexGaussian,CovMatrix}.lean`.
`IsSLEDriverAdapted` gives every-path continuity, `Adapted ℱ U` (so each `U t` is measurable) and independence of each
single increment `U t - U s` from `ℱ s`. Look in `ComplexSLE/Internal/Driver/` and `ComplexSLE/Infrastructure/` for
existing driver lemmas (e.g. `indep_shift_past`, shifts at deterministic times, `IsSLEDriver` of shifted drivers) and
reuse them.

Third-party templates (read only, run nothing inside `~/ext-src/lean-formalizations`, commit 31e7483):
- `QuantumZipper/Proofs/Probability/StrongMarkov.lean` (real BM, finite `ℝ≥0`-valued stopping times, arbitrary
  filtration with a whole-future-path independence hypothesis `hind`): dyadic approximation of `T` from above,
  `setIntegral_dyadicTime`, `setIntegral_bcf`, `map_restrict_finite_eq`, `map_restrict_smPath_eq`,
  `indep_smPath`;
- `BouRabeeGwynne/BrownianStrongMarkov.lean` (`standardBrownianLaw_aeFiniteStopping_map_restrict`): handling of
  a.s.-finite stopping times by truncation `τ ∧ n` on `{τ ≤ n}`.
Port what you use to the mirrored path `ComplexSLE/Infrastructure/Zipper/<upstream path>` (upstream namespaces;
our standard comment block, then the three lines `Ported from leobon12/lean-formalizations @31e7483,` /
`<upstream path>;` / `trimmed and adapted to Lean v4.36 and the module system.`; module system), or rewrite.
Check whether a file is already ported there first.

Route: (i) from single-increment independence derive independence of the whole future increment process
`(U (t + s) - U t)_s` from `ℱ t` (induction over finitely many times, then a π-system argument);
(ii) simple Markov at deterministic and then countably-valued stopping times; (iii) dyadic approximation
`τ_k ↓ τ` on `{τ ≤ n}` and path continuity give, for `A ∈ ℱ_τ`, that the law of the shifted path on `A` is
`P A •` the law of `U`'s path (finite-dimensional laws via bounded continuous test functions); this gives
both the `IsSLEDriver` clause (law of increments, independent increments, `W 0 = 0`, continuity) and the
independence clause; (iv) the `𝒢` clause from (iii) applied at the stopping time `τ + s` (`𝒢 s` is `ℱ_{τ+s}`),
minding that `untopA` sends `⊤` to `0` (only on a null set, since `τ < ⊤` a.s.).

Checks: `lake build ComplexSLE.Internal.ExternalProofs.StrongMarkovSLEDriver`;
`python3 -I tools/leanprobe.py axioms <module> ComplexSLE.Internal.ExternalProofs.strongMarkov_sleDriver`
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
