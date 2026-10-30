# Loewner evolution driven by complex Brownian motion — Lean formalization

Formalization of arXiv:2203.07313v4 (Gwynne–Pfeffer, "Loewner evolution driven by
complex Brownian motion"). Workflow: LeanAutoformalizationSkills (`lean-orchestrator`,
`build-proof-dependency-graph`, `lean-statement-audit`), installed in `~/.claude/skills/`.
Plan: `PLAN.md`. Status ledger: `STATUS.md`. Author rulings and errata: `ERRATA.md`.

## Source of truth

- Source: `source/arxiv-2203.07313v4/complex-sle-final.tex`
  (sha256 `6f182d3af83b14781ad6c96c634a6d211230b0a54490453aca70cb52f77db252`).
  Cite it as `paper.tex:Lx-Ly`. The PDF in `source/` is for reading only.
- Toolchain and Mathlib pins (`lean-toolchain`, `lake-manifest.json`) are frozen.
  Do not update them.

## External inputs

Classical results missing from Mathlib (Itô calculus, strong Markov property, Koebe, …) are
author-approved exact Lean statements in manifest state `EXTERNAL`, in `ComplexSLE/External/`.
A result that consumes one is `PROVED_REL{E…}`, never `PROVED`. A brief may list only the
externals that the dependency graph assigns to its node.

## Environment

```bash
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"
```

`lake`/`lean` print harmless `getpwuid_r` and `could not canonicalize path` warnings.
`.lake/packages` is a hard-linked copy of `~/formalization/.lake/packages` (same pins).

- Compile one file: `lake env lean ComplexSLE/Path/To/File.lean`
- Build one module: `lake build ComplexSLE.Path.To.File`
- Full gate (orchestrator): `tools/check.sh`
- Probes: `python3 -I tools/leanprobe.py axioms MODULE DECL` / `abi MODULE DECL`

## Layout

- `ComplexSLE/Frozen/` — author-approved anchors, **one public declaration per file**,
  bound by `frozen-anchor-manifest.json`. **Read-only for everyone except the
  orchestrator, and only after an author ruling.**
- `ComplexSLE/External/` — frozen `EXTERNAL` inputs (permanent, manifest-registered).
- `ComplexSLE/Internal/` — providers (implementation modules) below the anchors.
- `ComplexSLE/Infrastructure/` — reusable, source-independent mathematics.
- There is no root aggregator module (it would import draft anchors); `lake build`
  builds every module under `ComplexSLE/` via a glob.

## Approvals (ruling R26)

The author asked (2026-10-30) for about a third as many approval pauses. Rules:

1. **No "start the next milestone?" questions.** Milestones roll over automatically. Each milestone
   close is committed, pushed and reported without a question unless an author decision is pending.
2. **Auto-approval (`AUTO-n` in ERRATA.md, listed in the next packet for retroactive veto).** The
   orchestrator approves on the author's behalf:
   - mechanical companions of an author-approved declaration: the remaining parts of an approved split,
     analogues in the same pattern (right hulls, maps f_t, reflected or shifted drivers), characterization
     theorems of an approved definition, and versioned successors that change only docstrings, binder
     names or an unambiguous typo;
   - literal transcriptions of a source definition or statement with no modeling choice (no new carrier,
     normalization, quantifier, a.s. or hypothesis decision beyond existing rulings), after a transient
     compile and two independent fresh Sonnet reviews that ACCEPT (cosmetic changes only);
   - unambiguous typo errata (T-items).
   Proof-route substitutions, graph amendments and internal/infrastructure lemmas never needed approval;
   they are reported only.
3. **Author approval, batched into one packet per milestone** (`review/approvals/M<k>.md`, one question):
   new EXTERNAL inputs; any declaration with a modeling choice or a departure from the literal source
   (added or changed hypotheses, carriers, normalizations, encodings, splits and witness policy);
   corrections of mathematical errors in the paper (P-items) and other rulings; scope changes.
   While a packet is pending, work continues on everything that does not depend on it (drafts and proofs
   against pending statements stay in scratch, unfrozen). Pause only when the whole remaining frontier
   depends on the packet.
4. **Safety.** AUTO never applies to EXTERNAL inputs, nor to anything weaker than the literal source. If the
   author vetoes an AUTO item, it gets a versioned successor and every dependent seal and audit is redone.

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
