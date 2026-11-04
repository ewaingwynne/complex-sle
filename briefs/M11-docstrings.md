# M11 cleanup packet: comments that name deleted declarations

Goal: the orchestrator deleted every Lean declaration that no frozen result's proof uses (259 declarations and
4 files). Some docstrings and comments in the remaining files still mention deleted declarations. Rewrite those
comments so that every backticked Lean name they mention still exists, while keeping them accurate and readable.

Inputs:
- `.lake/probes/dead/doc_hits.txt`: `file:line: name` for each backticked mention found mechanically (82 hits,
  38 files). Some hits are false positives: the name also exists under another namespace, or the text is maths
  rather than a Lean name. Check before you edit.
- `.lake/probes/dead/deleted_names.txt`: fully qualified names of every deleted declaration.
- To see what a deleted declaration said, use `git show HEAD:<file>`. HEAD is the pre-deletion state.

What to do:
- Edit only comments: module docstrings `/-! … -/`, declaration docstrings `/-- … -/` and `--` comments. Do not
  change any Lean code, and do not add or remove declarations.
- Where a comment lists a deleted lemma among a file's main results, drop it from the list. If the deleted lemma
  was one form of something that still exists, point at the surviving form instead.
- Where a sentence describes deleted material, such as a section header over removed lemmas, remove or shorten it.
- Do not invent claims. If you cannot make a comment accurate, delete the comment rather than guessing.
- Files under `ComplexSLE/Frozen/` and `ComplexSLE/External/` are frozen: do not edit them, even when they have a
  hit. Report any such hit.
- Do not touch `RESULTS.md`, `README.md`, `briefs/` or `review/`; the orchestrator updates those.

Check: run `lake build` once at the end. Note that `lake build MODULE` for each touched module is not enough on
its own, so run the full build. It must finish with `Build completed successfully`. Then re-run the mechanical
search for leftover mentions:
`grep -nwFf <(sed 's/.*\.//' .lake/probes/dead/deleted_names.txt | awk 'length>=5') -r --include=*.lean ComplexSLE`.
Every remaining hit should be a false positive you can name.

Handoff: list each file changed with one line on what changed. Give the build result line, and the leftover-grep
hits with the reason each is a false positive.
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
