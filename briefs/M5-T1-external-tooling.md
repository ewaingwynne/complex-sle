# M5 / T1 — EXTERNAL state in the frozen-anchor tooling (tooling brief)

Goal: extend the project tooling so author-approved external inputs can be frozen and consumed, and so that
the set of externals each result depends on is computed mechanically (PLAN.md §7 option (a), §11; ERRATA R1).

Semantics of an EXTERNAL anchor:
- kind "theorem", manifest state "EXTERNAL", path under `ComplexSLE/External/` (one public theorem per file,
  module file with the usual FROZEN_ANCHOR_* markers), body exactly `by sorry` forever; prefix/suffix hashes and
  abi_sha256 as for other theorem anchors; author_approval required; NO "implementation" provider.
- Unlike DRAFT_SORRY anchors, an EXTERNAL module MAY be imported by any project module (that is its purpose).
- No other file may live under `ComplexSLE/External/` (every file there must be an EXTERNAL manifest anchor).
- An EXTERNAL file may import only Mathlib, sealed definition anchors (ComplexSLE/Frozen/Defs/*) and other
  EXTERNAL modules — never Internal/Infrastructure modules or theorem anchors.
- The existing rules for DRAFT_SORRY / SEALED must keep working unchanged (run the current gate before/after).

Work items (Ownership: tools/check_frozen_anchors.py, tools/leanprobe.py, tools/manifest_add.py, tools/check.sh,
plus a new test fixture directory under .lake/probes/ext-test/ that you delete at the end. No other files.):
1. check_frozen_anchors.py: accept state "EXTERNAL" with the rules above (allowlist exactly the one `sorry` in the
   body, like DRAFT_SORRY; forbid `implementation`; enforce the path, the import restrictions, and the
   "every file under ComplexSLE/External/ is a manifest EXTERNAL anchor" rule). Importing an EXTERNAL module must not
   count as a DRAFT import violation. Also: a SEALED theorem must still not depend (by import) on a DRAFT_SORRY anchor.
2. leanprobe.py: add a subcommand `externals MODULE DECL` that elaborates a probe importing MODULE and computes the
   transitive closure of constants used by DECL (type and value), reporting JSON
   {"decl", "axioms", "externals": [sorted EXTERNAL exports from the manifest that occur in the closure],
    "status": "PROVED" | "PROVED_REL" | "UNSOUND"}.
   status = PROVED if axioms ⊆ {propext, Classical.choice, Quot.sound}; PROVED_REL if the only extra axiom is sorryAx
   AND every constant in the closure whose own value directly mentions sorryAx is an EXTERNAL export; UNSOUND
   otherwise (list the offending constants). Implement the closure walk in Lean (a small `run_cmd`/`#eval` using
   `Lean.Environment`, `ConstantInfo.getUsedConstantsAsSet` or `Expr.getUsedConstants`) — do it efficiently (use a
   visited set; stop descending into Mathlib/Init constants by prefix only if that is provably safe — better: walk
   everything but cache).
   Add `externals-all MANIFEST` that runs it for every SEALED theorem anchor and prints one line each.
3. manifest_add.py: support kind "theorem" with "state": "EXTERNAL" in the spec (no implementation; state EXTERNAL).
4. check.sh: after the ABI step (full mode only), run `leanprobe.py externals-all` and fail on any UNSOUND.
5. Test: build a throwaway fixture in .lake/probes/ext-test/ (copy of the manifest + a dummy EXTERNAL file and a dummy
   consumer, checked with --root pointing at a temp copy, or by temporarily adding files and then removing them — but
   the real repository must end exactly as it started apart from your four tool files). Demonstrate: an EXTERNAL
   anchor passes; a file under External/ not in the manifest fails; an EXTERNAL importing an Internal module fails;
   `externals` reports PROVED for ComplexSLE.loewner_wellDefined and PROVED_REL{dummy} for the consumer, and UNSOUND
   for a consumer with a stray sorry.

Checks: `tools/check.sh` (full) passes on the real repository at the end; paste outputs of all fixture tests.
Environment: export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH".
Rules: do not edit anything under ComplexSLE/, the manifest, DEPGRAPH*, STATUS, ERRATA, lakefile/toolchain/manifest.
Do not commit. No `lake clean`, nothing deleted under .lake/ except your own fixture. Report: files changed, approach,
commands + outputs, anything uncertain.
