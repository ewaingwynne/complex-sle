# M10: refresh RESULTS.md after ruling R31 (no externals left)

Ownership: `RESULTS.md` only. Edit no other file.

State (git HEAD 5058dde):
- `hormander_oneDim` and `markov_oneDim` are deleted (R31 in `ERRATA.md`; plan `review/plans/M10-reroute.md`).
- Every one of the 36 sealed theorems is `PROVED`: `python3 -I tools/leanprobe.py externals-all`.
- The `hMO` binders are gone, the kernel route (`Stationary/Kernel*`, `Kolmogorov`, `SLEStat*`) and `AllZDensity` are
  deleted, and several declarations were renamed:

  | Old | New |
  |---|---|
  | `lemma_3_9_of_markov` | `lemma_3_9` |
  | `lintegral_comp_lemma_3_9_of_markov` | `lintegral_comp_lemma_3_9` |
  | `integral_comp_lemma_3_9_of_markov` | `integral_comp_lemma_3_9` |
  | `converse_of_markov` | `converse_w_o_upgrade` |
  | `proposition_3_2_a_of_markov` | `proposition_3_2_a_main` |
  | `proposition_3_1_{a,b}_of_markov` | `proposition_3_1_{a,b}_core` |
  | `*_thetaHat_prod_*_of_markovOneDim` | `integral_comp_thetaHat_prod_admissible`, `map_addCircle_thetaHat_prod_eq_admissible`, `map_exp_thetaHat_prod_eq_admissible` (`Stationary/InvarianceStationary.lean`) |

- The new route has these pieces:
  - semigroup: `Stationary/ThetaSemigroup*`;
  - periodic Poisson equation: `Infrastructure/PeriodicODE/Poisson*` and `DoubleZero*`, plus
    `Stationary/InvariancePoisson`;
  - Cesàro and invariance: `Stationary/InvarianceCesaro`, `InvarianceStationary`;
  - occupation estimate: `Stationary/Occupation*`, used by Lemma 3.3 in `Phases/AllZ.lean`.

Task: update `RESULTS.md` so that every statement in it is true at HEAD, in its present structure and style.
1. Header snapshot: date 2026-11-02, the HEAD hash, the module and line counts (count `ComplexSLE/**/*.lean`), and
   "No `sorry` anywhere in `ComplexSLE/`".
2. Status conventions:
   - drop the `hMO` paragraph and the "only hormander and markov remain" sentences;
   - `PROVED_REL` no longer occurs, so say so;
   - recompute the status of every cited declaration with `leanprobe` (the batched `externals_many` as before, or the
     CLI `python3 -I tools/leanprobe.py externals MODULE DECL`);
   - fix every renamed or deleted name and file path. Check each cited name exists, for example with
     `grep -rn "theorem NAME" ComplexSLE`.
3. Summary table: 36 PROVED, 0 PROVED_REL; 14 roots, all PROVED; externals: 10 proved and sealed under `External/`,
   8 deleted (list them).
4. The rows for Lemma 2.14, Lemma A.1, Lemma A.2, Lemma 3.3 and any other affected row: describe the actual Lean route
   in one or two sentences, and say where it departs from the paper. The paper uses Hörmander smoothing and a
   transition density; here they are replaced by Feller continuity plus the Poisson equation plus Cesàro averaging,
   and by the occupation estimate.
5. The gap list: remove the items that are now closed and keep the rest accurate.

Checks:
- each cited declaration exists: grep each backticked `ComplexSLE.…` name;
- `grep -n "PROVED_REL\|hMO\|markov_oneDim\|hormander_oneDim\|_of_markov" RESULTS.md` should hit only the historical
  remarks that you mark as historical.

Handoff: a summary of the changes, and the commands with their output.

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
