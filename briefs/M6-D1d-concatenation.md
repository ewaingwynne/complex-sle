# M6 / D1d — concatenation property (2.3) (prover brief)

Goal: prove four provider theorems, each with EXACTLY the type of its frozen anchor (read-only; copy statements
verbatim including the `(by fun_prop)` terms and `open scoped NNReal`):
- `ComplexSLE.Internal.concatenation_centeredLoewnerMap` ← ComplexSLE/Frozen/Concatenation_CenteredLoewnerMap.lean
- `ComplexSLE.Internal.concatenation_leftHull`           ← ComplexSLE/Frozen/Concatenation_LeftHull.lean
- `ComplexSLE.Internal.concatenation_image_leftHull`     ← ComplexSLE/Frozen/Concatenation_ImageLeftHull.lean
- `ComplexSLE.Internal.concatenation_rightHull`          ← ComplexSLE/Frozen/Concatenation_RightHull.lean
Source: paper.tex:L559-565 with ERRATA R18; auto-approved as AUTO-1 (two reviews; their proof sketch: η(r) = γ(r+t) − U t
solves the V-problem from f_t z, gluing gives the converse, so T_z = t + T^V_{f_t z}; injectivity of f^V_s by backward
uniqueness is needed only for the right-hull formula).

Allowed inputs: Mathlib; sealed defs ComplexSLE/Frozen/Defs/*; PROVED sealed anchors (loewner_wellDefined, loewnerMap_eq,
loewnerMap_exists_solution, scaling_*, reflection_*); public lemmas in ComplexSLE/Internal/Loewner/ (Transform, MapTransform,
Duality — Duality.lean has closed-interval solutions, time reversal and endpoint uniqueness, useful for injectivity) and
ComplexSLE/Internal/Hull/ (LocalExistence: local solutions and gluing). Prefer NOT to use any External (an injectivity
proof by backward uniqueness keeps the results PROVED). No DRAFT anchor or provider. Use the characterization theorems;
never unfold Classical.choose.

Ownership: the four provider files (keep header/docstring; add imports/section/namespace ComplexSLE.Internal), new files
under ComplexSLE/Internal/Loewner/ (e.g. Concatenation.lean, Injective.lean). No other edits.
Checks: `lake build` of the four providers; exact-type probes in .lake/probes/ (deleted after);
`python3 -I tools/leanprobe.py externals <module> <decl>` for all four (report PROVED / PROVED_REL);
`tools/check.sh --quick`. Don't run full tools/check.sh.
Stop condition: if a frozen statement looks false, STOP and report precisely. Budget ~4 hours.

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

Handoff: files changed; approach; exact commands and outputs; externals status for every new public theorem;
anything unproved or uncertain.
