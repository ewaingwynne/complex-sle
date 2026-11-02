# complex-sle

Lean 4 / Mathlib formalization of

> E. Gwynne and J. Pfeffer, *Loewner evolution driven by complex Brownian motion*,
> arXiv:2203.07313v4 (2023).

## Status

Every author-frozen root is proved, with no `sorry` and no external input.
- **Frozen theorems:** 14 frozen roots and 36 sealed theorems. All are proved outright: `#print axioms` shows only
  `propext`, `Classical.choice` and `Quot.sound`. None is left as a draft.
- **Main results:**
  - Theorem 1.8, including c = 0, and Propositions 3.1(a,b) and 3.2(a,b);
  - Theorem 1.10(a) and (b);
  - well-definedness of the Loewner chain, the existence part of Lemma 2.13, Lemma 2.4 and (2.1)–(2.3);
  - Proposition 1.5, in the coupling form of ruling R28;
  - existence of the SLE_Σ driver.
- **Classical inputs, proved in-project** (M10):
  - existence of Brownian motion;
  - Itô's formula (martingale form) and time change of local martingales;
  - the strong Markov and Blumenthal properties and the support theorem for the driver;
  - the Birkhoff ergodic theorem and the recurrence of stationary sums;
  - the conformality and driver-continuity of the Loewner maps.
- **Departures from the paper's route.** The paper's appeal to Hörmander's theorem (Lemma A.2) and to the Markov property
  of the transition kernel is replaced:
  - by the semigroup of θ̂ with Feller continuity, the periodic Poisson equation and Cesàro averaging;
  - by an occupation estimate in Lemma 3.3.

  See ruling R31 in `ERRATA.md`.

Some code is ported from leobon12/lean-formalizations @31e7483 and marked so in `ComplexSLE/Infrastructure/Zipper/`.
That repository has no license file.

## Where to look

| File | Contents |
|---|---|
| `RESULTS.md` | Paper → Lean map for every in-scope numbered item, with computed statuses, the external boundary and an honest gap list (§7). |
| `STATUS.md` | Ledger by milestone (M0–M10). |
| `ERRATA.md` | Author rulings R1–R31: corrections of the paper (P-items), typos (T-items) and modeling choices. |
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
- The last command computes the status of each sealed theorem (PROVED, or PROVED_REL if it used an external; none
  does now).

Toolchain: Lean `v4.36.0-rc2`, Mathlib `v4.36.0-rc2` (see `lake-manifest.json`).
