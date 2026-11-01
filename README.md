# complex-sle

Lean 4 / Mathlib formalization of

> E. Gwynne and J. Pfeffer, *Loewner evolution driven by complex Brownian motion*,
> arXiv:2203.07313v4 (2023).

## Status

Complete for the planned scope: every author-frozen root is proved, either outright or relative to approved externals.
- **Frozen theorems.** There are 14 frozen roots and 26 sealed theorems in total. 17 sealed theorems are proved outright
  and 9 are proved relative to externals. None is left as a draft.
- **Main results.** All of these are `PROVED_REL`, meaning proved relative to approved external inputs:
  - Theorem 1.8, the four phases and the explicit c = 0 description.
  - Theorem 1.10(a) and (b).
  - Propositions 3.1(a,b) and 3.2(a,b).
- **Deterministic results.** These are proved with no external input:
  - well-definedness of the Loewner chain;
  - the existence part of Lemma 2.13;
  - Lemma 2.4 (connected hulls);
  - (2.1)–(2.3);
  - Proposition 1.5, in the coupling form of ruling R28.

Results that use classical theorems absent from Mathlib (Itô's formula, the strong Markov property, Hörmander's
theorem, the Koebe quarter theorem, …) are reported as **proved relative to** explicitly listed, author-approved external
statements (`ComplexSLE/External/`, manifest state `EXTERNAL`). They are never counted as unconditionally proved. 13 of the
18 approved externals are actually consumed; RESULTS.md §5 lists which root uses which.

## Where to look

| File | Contents |
|---|---|
| `RESULTS.md` | Paper → Lean map for every in-scope numbered item, with computed statuses, the external boundary and an honest gap list (§7). |
| `STATUS.md` | Ledger by milestone (M0–M9). |
| `ERRATA.md` | Author rulings R1–R29: corrections of the paper (P-items), typos (T-items) and modeling choices. |
| `PLAN.md` | Campaign plan and scope. |
| `ComplexSLE/Frozen/` | The author-approved statements, one declaration per file, bound by `frozen-anchor-manifest.json`. |
| `ComplexSLE/Internal/`, `ComplexSLE/Infrastructure/` | The proofs. |
| `DEPGRAPH.md` | The reviewed source-level dependency graph. It is source-only by design; Lean status lives in STATUS.md and RESULTS.md. |
| `review/` | Statement audits (`review/audits/`), approval packets (`review/approvals/`) and milestone plans (`review/plans/`). |

## Building and checking

```bash
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"
lake build
tools/check.sh
python3 -I tools/leanprobe.py externals-all frozen-anchor-manifest.json
```

- `lake build` builds everything.
- `tools/check.sh` runs the full gate: build, module headers, the frozen-anchor guard, ABI hashes, externals, and
  forbidden constructs.
- The last command computes PROVED or PROVED_REL for each sealed theorem.

Toolchain: Lean `v4.36.0-rc2`, Mathlib `v4.36.0-rc2` (see `lake-manifest.json`).
