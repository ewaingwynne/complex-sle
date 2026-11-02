# M10-R6: remove every dependence on `hormander_oneDim` and `markov_oneDim`

Context: M10 re-route of the last two externals (`review/plans/M10-reroute.md`, steps 5–6). The replacements have
landed:
- `Stationary/Invariance*.lean`: the hMO-free one-time stationarity theorems
  `integral_comp_thetaHat_prod_admissible`, `map_addCircle_thetaHat_prod_eq_admissible` and
  `map_exp_thetaHat_prod_eq_admissible`;
- `Stationary/Occupation*.lean`: `exists_pos_measure_thetaHat_preimage_eq_zero`, i.e. for null `N` some `t > 0` has
  `P(θ̂_t(z) ∈ N) = 0`.

Goal: afterwards no module other than `ComplexSLE/External/HormanderOneDim.lean` and
`ComplexSLE/External/MarkovOneDim.lean` imports either of them, directly or transitively. The orchestrator then
deletes those two files and their manifest entries. You must not touch them.

Ownership: every file under `ComplexSLE/Internal/` and `ComplexSLE/Infrastructure/`. You may create files and delete
modules there.

Not yours, read-only: `ComplexSLE/Frozen/`, `ComplexSLE/External/`, the manifest, `DEPGRAPH*`, `STATUS.md`,
`ERRATA.md`, and `ComplexSLE/Internal/ExternalProofs/` (do not edit it, unless an import there must change; report if
so).

Steps:
1. **Lemma 3.3** is already done (commit 0bfe1e6): `Phases/AllZ.lean` uses the occupation estimate, and
   `AllZDensity.lean` is deleted. Nothing to do here.
2. **One-time stationarity.**
   - Replace every use of `integral_comp_thetaHat_prod_of_markovOneDim` (`Phases/ErgodicMean.lean`),
     `map_addCircle_thetaHat_prod_eq_of_markovOneDim` and `map_exp_thetaHat_prod_eq_of_markovOneDim`
     (`Stationary/SLEStat.lean`) by the `_admissible` versions, and delete the old theorems.
   - Delete the transition-kernel route that only served them:
     - in `SLEStat.lean`: `integral_comp_thetaHat_eq_kernelOp`, `integral_comp_thetaHat_prod`, `*_of_kernel`, and
       the `β`/`hMO` versions `map_addCircle_thetaHat_prod_eq` and `map_exp_thetaHat_prod_eq`;
     - `integral_kernelOp_admissibleMeasure` (`SLEStatLaw.lean`);
     - `MarkovOneDimConclusion`, `MarkovOneDimFor`, `MarkovOneDim` and `exists_isDiffusionKernel`
       (`SLEStatKernel.lean`).
   - Keep what is still used, for instance `exists_beta`.
3. **Binders.** Remove every `(hMO : MarkovOneDim)` binder and every `hMO` argument in all files. At the call sites
   of `External.markov_oneDim` (`Proposition_3_1_A.lean`, `Proposition_3_1_B.lean`, `Phases/Prop32A.lean`,
   `Phases/ConverseMain.lean`, `Phases/Lemma37.lean`) drop the argument and the import of `External.MarkovOneDim`.
   - Rename every declaration whose name ends in `_of_markov` or `_of_markovOneDim` and whose hypothesis is now gone:
     drop the suffix if the shorter name is free in its namespace, otherwise use `_core`.
   - Update all references.
   - Do not rename anything that a frozen anchor's provider exports. Check `frozen-anchor-manifest.json` (read
     only), fields `implementation.module` and `implementation.export`. If such an export changes signature or
     name, stop and report.
4. **Docstrings.** Fix every module and declaration docstring that names `hMO`, `MarkovOneDim`, `markov_oneDim`,
   `hormander_oneDim`, "EXTERNAL (R29)" or the kernel route as an input. Describe the actual route instead: the
   semigroup of θ̂ with Feller continuity, the periodic Poisson equation, Cesàro invariance and the occupation
   estimate. Also fix stale claims that a module "consumes" `ito_formula`, `strongMarkov_sleDriver`,
   `timeChange_isContLocalMartingale` or other externals that are now proved. Keep the edits minimal and factual.
5. **Dead kernel route.**
   - After 2–3, the modules `Stationary/{KernelBasic,KernelInvariance,KernelLaw,Kolmogorov,SLEStatKernel,SLEStatLaw,SLEStat}.lean`
     may be unused or nearly empty. Move any declaration that is still used elsewhere to a suitable live module;
     for instance `ThetaHatSolution.lean` imports `KernelBasic` and probably needs only a few imports from it.
   - Delete modules that are then unused, or that only state results conditional on `IsDiffusionKernel`.
   - Report the deleted modules.
6. **Verification.**
   - `lake build`, the full build, must succeed with no new warnings except long lines.
   - `grep -rn "HormanderOneDim\|MarkovOneDim\|hormander_oneDim\|markov_oneDim\|hMO" ComplexSLE --include=*.lean | grep -v "^ComplexSLE/External/"`
     must print nothing.
   - For every module, `python3 .lake/probes/closure.py <Module>` must print `clean`. Loop over all modules with
     `find ComplexSLE -name '*.lean' | sed 's|/|.|g; s|\.lean$||' | grep -v '^ComplexSLE\.External\.\(Hormander\|MarkovOneDim\)' | xargs python3 .lake/probes/closure.py | grep -v clean`,
     which must print nothing.
   - `python3 -I tools/leanprobe.py axioms ComplexSLE.Internal.Theorem_1_8 ComplexSLE.Internal.theorem_1_8` and the
     same for the providers of `theorem_1_8_c_zero`, `proposition_3_1_a/b` and `proposition_3_2_a/b`, which must
     report only propext, Classical.choice and Quot.sound. Find the exact provider modules and exports in the
     manifest.
   - `python3 -I tools/check_lean_modules.py --root . --max-lines 1500`.

If something does not close within budget, leave the tree compiling, with every intermediate theorem still proved,
and report exactly what is left. Never leave a `sorry`.

Handoff: files changed, created and deleted; renames (old → new); commands and output; axioms; what is left.

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
