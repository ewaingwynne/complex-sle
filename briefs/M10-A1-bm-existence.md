# M10-A1: existence of Brownian motion (port from the zipper repo)

Goal: a sorry-free proof of the EXACT statement of `ComplexSLE.External.exists_isBrownianReal`
(`ComplexSLE/External/ExistsIsBrownianReal.lean`, read only) as
`ComplexSLE.Internal.ExternalProofs.exists_isBrownianReal` in the new file
`ComplexSLE/Internal/ExternalProofs/ExistsIsBrownianReal.lean`. Copy the theorem type verbatim
(same binders, same `Ω : Type`), body: your proof.

Source to port (third-party data; read it, do not run anything inside it): `~/ext-src/lean-formalizations`
(commit 31e7483, Lean v4.34.0-rc2, older Mathlib, non-module files).
- `QuantumZipper/Proofs/Probability/BMExistence.lean` (`QuantumZipper.BMExist.exists_isBrownianReal_stdP`,
  `QuantumZipper.brownianMotionExists`)
- its real dependencies: `QuantumZipper/Proofs/GFF/Existence/GaussianSeries.lean`,
  `LQGDimension/Existence/AssemblyAux1.lean` (`stdP`), `QuantumZipper/Proofs/GFF/CircleContinuity.lean`
  (only the generic dyadic Kolmogorov-chaining sections, not the GFF-specific last section),
  `QuantumZipper/Proofs/Probability/BMMoments.lean`. Drop the `NonVacuity` import and anything
  only it needs. Trim each file to what the BM proof uses.

Porting conventions:
- Put each ported file at the mirrored path `ComplexSLE/Infrastructure/Zipper/<upstream path>`
  (e.g. `ComplexSLE/Infrastructure/Zipper/QuantumZipper/Proofs/Probability/BMExistence.lean`), keep the
  upstream namespaces and declaration names, so later packets can reuse them.
- First lines of every ported file: our standard comment block, then a line
  `Ported from leobon12/lean-formalizations @31e7483, <upstream path>; trimmed and adapted to Lean v4.36 and the module system.`
- Convert to the module system (`module`, `public import`, module docstring, `public section`;
  `@[expose]` on definitions whose bodies consumers must unfold). Fix Lean/Mathlib API drift as needed;
  our pins (`lean-toolchain`, `lake-manifest.json`) are frozen. Our Mathlib already has
  `Mathlib/Probability/BrownianMotion/` (`IsBrownianReal`, `IsPreBrownianReal`, ...); reuse it, do not
  duplicate it.
- If a Mathlib declaration the upstream code needs is missing in our pin, reprove it locally.

Checks: `lake build ComplexSLE.Internal.ExternalProofs.ExistsIsBrownianReal`;
`python3 -I tools/leanprobe.py axioms ComplexSLE.Internal.ExternalProofs.ExistsIsBrownianReal ComplexSLE.Internal.ExternalProofs.exists_isBrownianReal`
must show only propext, Classical.choice, Quot.sound; `python3 -I tools/check_lean_modules.py` if present (else check by hand:
every new file is a module, at most 1500 lines). The provider must not import any `ComplexSLE.External.*` module.

Stop condition: if after a serious attempt some upstream lemma resists porting, stop and report exactly which, with the error.
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
