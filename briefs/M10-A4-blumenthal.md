# M10-A4: Blumenthal 0-1 law for the SLE_Σ driver

Goal: a sorry-free proof of the EXACT statement of `ComplexSLE.External.blumenthal_sleDriver`
(`ComplexSLE/External/BlumenthalSLEDriver.lean`, read only) as
`ComplexSLE.Internal.ExternalProofs.blumenthal_sleDriver` in
`ComplexSLE/Internal/ExternalProofs/BlumenthalSLEDriver.lean` (helpers in new files). Copy the theorem type verbatim.
The provider must not import any `ComplexSLE.External.*` module, directly or transitively.

Care points: `IsSLEDriver` (`ComplexSLE/Frozen/Defs/IsSLEDriver.lean`) gives only a.s. continuity, `U 0 = 0` a.s.,
`HasIndepIncrements` and Gaussian laws of increments: each `U s` is only a.e.-measurable, so the comap σ-algebras in
the statement need not be sub-σ-algebras of the ambient one, and `A` is an arbitrary set (`P` is applied as an outer
measure). Reduce to a countable family of measurable versions: on the a.s. continuity event `U s` is a limit of
`U q`, `q` rational; every set of `σ(U s : s ≤ ε)` lies in the σ-algebra of countably many coordinates; replace
`U q` by measurable versions (countably many null sets). Then the germ σ-algebra is independent of itself: the
past `σ(U q : q ≤ ε)` is independent of the increments after `ε`, and the germ σ-algebra is generated, up to null
sets, by increments `U q - U q'` with `0 < q' < q`, because `U q' → U 0 = 0`.

Third-party template (read only, run nothing inside `~/ext-src/lean-formalizations`, commit 31e7483):
`QuantumZipper/Proofs/Probability/GermZeroOne.lean` (`isTrivialSigma_iInf_bmPast` for real BM;
`IsTrivialSigma`, `isTrivialSigma_of_indep_self`, `isTrivialSigma_iInf_sup`) and
`QuantumZipper/Proofs/Probability/TailTrivial.lean` (`isTrivialSigma_iInf_bmPast_of`). Port what you use to the
mirrored path `ComplexSLE/Infrastructure/Zipper/<upstream path>` (upstream namespaces; our standard comment block,
then the three lines `Ported from leobon12/lean-formalizations @31e7483,` / `<upstream path>;` /
`trimmed and adapted to Lean v4.36 and the module system.`; module system), or rewrite; check whether it is
already ported. Mathlib: `ProbabilityTheory.indep_iSup_of_directed_le`, `measure_eq_zero_or_one_of_indep_self`,
`HasIndepIncrements`.

Checks: `lake build ComplexSLE.Internal.ExternalProofs.BlumenthalSLEDriver`;
`python3 -I tools/leanprobe.py axioms <module> ComplexSLE.Internal.ExternalProofs.blumenthal_sleDriver`
(only propext, Classical.choice, Quot.sound). Every new file a module, at most 1500 lines.
Stop condition: a precise obstruction (in particular if the statement is false for non-measurable `U s`: then
give a counterexample sketch and stop), with the failing goal.
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
