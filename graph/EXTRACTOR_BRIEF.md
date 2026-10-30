# Extraction brief (slice workers)

You are a source-topology extraction worker for slice `<S>` of a proof dependency graph for
arXiv:2203.07313v4. Follow `~/.claude/skills/build-proof-dependency-graph/references/agent-packets.md`
§1 (Extraction packet) exactly, together with `graph/EXTRACTION_SPEC.md` (binding: roots, conventions,
rulings, external IDs, step threshold, exclusions, frozen-anchor table, slice ownership, canonical
cross-slice IDs, and field rules). Node schema: `~/.claude/skills/build-proof-dependency-graph/assets/DEPGRAPH.template.md`.

Read: the source `source/arxiv-2203.07313v4/complex-sle-final.tex` (your slice in full, and other
ranges read-only as needed for statements you reference); `ERRATA.md`; `graph/EXTRACTION_SPEC.md`;
`graph/INVENTORY.md` (your slice's items); and, only to copy identity fields, `graph/anchor-table.md`
and the frozen declaration files of anchors you own (`ComplexSLE/Frozen/**`, read the
statement only). Do **not** read `ComplexSLE/Internal/`, proof bodies, Lean status, axioms, or
`STATUS.md`. Do not seek Lean evidence.

Output: write exactly one file, `graph/packets/slice-<S>.md`, with three sections:
- `## Nodes`: node blocks in the template schema (every field, in template order, for every
  node you own, including external nodes first cited in your slice);
- `## Coverage`: one `ITEM:` record (coverage schema: ITEM, KIND, SOURCE, DISPOSITION, REASON,
  COVERAGE_STATUS: PROPOSED, EXTRACTOR, REVIEWER: -) for **every** inventory item of your slice
  in `graph/INVENTORY.md`, plus any items you add for unlabeled substantive claims/proof
  paragraphs (ID form `inv:Lnnn:slug`);
- `## Report`: source ranges read; node/edge counts; coverage mapped/excluded counts;
  cross-slice edges (to canonical IDs you do not own); alternate routes; SOURCE_GAP nodes;
  new `ext:` IDs; uncertainty list; confirmation that no Lean evidence was sought, no anchor ABI
  was edited or inferred, and no other file was changed.

Use `EXTRACTOR: extractor-<S>/sonnet`. Every DEPS/ROUTES entry has exactly one `EDGE:` line
citing the consumer's use site. Do not edit any other file, do not commit, do not run Lean.
Your final message: the `## Report` section verbatim.
