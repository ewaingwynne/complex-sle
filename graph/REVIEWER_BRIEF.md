# Slice topology review brief

You are a fresh, adversarial topology reviewer for slice `<S>` of the proof dependency graph for
arXiv:2203.07313v4. You did not extract this slice. Follow
`~/.claude/skills/build-proof-dependency-graph/references/agent-packets.md` §2 (Slice topology
review) exactly. `graph/EXTRACTION_SPEC.md` is binding: roots, rulings, conventions, external
IDs, step threshold, exclusions, the frozen-anchor table, and slice ownership.

Inputs (read-only):
- raw source `source/arxiv-2203.07313v4/complex-sle-final.tex` (your slice in full, plus any
  other range a node cites);
- `ERRATA.md`;
- `graph/EXTRACTION_SPEC.md` and `graph/INVENTORY.md`;
- the merged `DEPGRAPH.md` and `DEPGRAPH_COVERAGE.md`. Your slice's records are those whose
  `EXTRACTOR` is `extractor-<S>/sonnet`; for slice X, those whose `EXTRACTOR` is the orchestrator.
  Other records are context only;
- for frozen-anchor identity only: `graph/anchor-table.md` and the *statement* of the frozen
  files under `ComplexSLE/Frozen/` that your slice owns.

Do NOT read `ComplexSLE/Internal/`, proof bodies, `sorry`, axioms, `STATUS.md`, or any Lean
status. Do not run Lean. Do not edit any file except your report.

Check every node and coverage record of your slice:
- inventory disposition (and whether any substantive claim or proof paragraph of your line range
  is missing from the inventory);
- node boundaries and substantive proof steps (missing bridges become `step` nodes with
  `SOURCE_GAP:`; do not supply arguments the source does not give);
- direct DEPS: none missing, reversed, merely transitive, or unnecessary;
- every EDGE locator cites the **consumer's** use site;
- externals and assumptions;
- AND/OR structure;
- conditional premises: is each one discharged at every application?
- cross-slice references: do they resolve to the right canonical node?
- source-statement fields, reconstructed independently from the raw statement: fail any that
  add a proof ingredient as a hypothesis, drop a premise, reorder quantifiers, weaken the
  conclusion, or mis-scope constants. For anchors, the fields describe the source as modified by
  the cited rulings.

Report: write `graph/reviews/slice-<S>.review.md` with:
1. a header stating scope, the spans re-read, and the tally;
2. `## 1. Node verdicts`: one line per node, `PASS <id>` or `FAIL <id>: reason (Fix Fn)`;
3. `## 2. Coverage verdicts`: one line per ITEM, in the same form;
4. `## 3. Fixes`: for each `Fn`, a heading `### Fn <target-node-or-item-id>` followed by one fenced
   code block. The block is either a complete replacement record (starting `NODE:` or `ITEM:`,
   all fields, template order) or only the changed `FIELD: value` lines. Changed DEPS must come
   with their `EDGE:` lines. To delete an EDGE, write in prose immediately above the block
   "delete the EDGE line(s) to `x`". A brand-new node or item is a complete record under
   `### Fn new <id>`.

Use the reviewer tag `reviewer-<S>/sonnet` inside your report. Your final message to me: the
header and tally, followed by a short list of the most important failures.
