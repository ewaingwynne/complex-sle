# AU-M10-reroute: audit of the removal of `hormander_oneDim` and `markov_oneDim` (independent, refute-first)

You are a fresh auditor; you did not write any of this code. Your posture is refute-first: try to show that something
is wrong. Edit no project file. The only file you write is the report `review/audits/AU-M10-reroute.md`. Scratch goes
in `.lake/probes/au-reroute/`; delete it at the end. Model the report's format on `review/audits/AU-M10-externals.md`.

Scope: the commits `git log 116be1c..HEAD`, plus the working tree as it stands (the orchestrator may not have committed
yet). The plan is `review/plans/M10-reroute.md`, the ruling is R31 in `ERRATA.md`, and the briefs are
`briefs/M10-R{1,2,3,4,5a,6}-*.md`.

Items, each PASS or FAIL with evidence:
1. **Freeze.**
   - `git diff 116be1c -- ComplexSLE/Frozen` is empty.
   - Under `ComplexSLE/External/`, only `HormanderOneDim.lean` and `MarkovOneDim.lean` were deleted.
   - `python3 -I tools/leanprobe.py verify-abi` reports every anchor's ABI unchanged.
   - The manifest lost exactly the two `ext.*` entries.
   - The `FROZEN_MANIFEST` sha256 in `DEPGRAPH.md` and `graph/DEPGRAPH.header.md` equals the manifest's.
2. **No sorry, no axioms.**
   - `grep -rnw sorry ComplexSLE` finds nothing.
   - `python3 -I tools/leanprobe.py externals-all` gives every theorem anchor `PROVED`; list any `PROVED_REL`.
   - `#print axioms` for the six §3 roots (`theorem_1_8`, `theorem_1_8_c_zero`, `proposition_3_1_a/b`,
     `proposition_3_2_a/b`) and for their providers is exactly `propext`, `Classical.choice`, `Quot.sound`.
3. **Hypothesis smuggling.** For each new theorem the providers rely on, check that no binder is conclusion-shaped or
   assumes a hard step. The theorems are:
   - `exists_periodic_solution_of_doubleZero`, `exists_periodic_poisson_of_pos`,
     `exists_periodic_poisson_of_solutions`, `eq_zero_of_periodic_generator_eq_const`;
   - `thetaSemigroup_add`, `continuous_thetaSemigroup`, `thetaSemigroup_sub_self`;
   - `exists_poisson_generator`, `poisson_const_eq`, `tendsto_cesaro_of_continuous`,
     `integral_thetaSemigroup_admissible`;
   - the three `*_admissible` theorems, `ae_volume_occupation_null`, `exists_pos_measure_thetaHat_preimage_eq_zero`,
     and `exists_zero_lattice_diffusionD`.

   Check also that every application discharges its premises. Classify every binder of the three `*_admissible`
   theorems and of `ae_volume_occupation_null`.
4. **Mathematical soundness, spot checks.** Read and assess, with concrete reasoning:
   - **(a)** the critical-case ODE route (`Infrastructure/PeriodicODE/DoubleZero*.lean`): residual, ends via
     L'Hôpital, and gluing. Are the hypotheses of `exists_periodic_solution_of_doubleZero` actually met by `(µ, D)`
     when `c² = ab` (`InvariancePoisson.lean`, `CriticalCoefficients.lean`)?
   - **(b)** the Chapman–Kolmogorov proof (`ThetaSemigroup.lean`): is the restart identity used at the right time,
     and is the `π`/`2π` bookkeeping correct?
   - **(c)** the invariance argument (`InvarianceStationary.lean`, `InvarianceCesaro.lean`): does it use Feller
     continuity of `Q_s f` legitimately?
   - **(d)** the new Lemma 3.3 proof (`Phases/AllZ.lean`): is the stopping time `σ_z(t₀)` valid for a deterministic
     `t₀`?
   - **(e)** the critical-case zero-occupation argument (`OccupationCritical.lean`, `OccupationBump.lean`).
5. **Consumers.**
   - The binder removals and renames in R6 changed no provider export. Compare the manifest's
     `implementation.export` names with the files.
   - No module imports a deleted module.
   - `lake build --no-build`, or the build state, is consistent.
   - Run `python3 -I tools/check_lean_modules.py --root . --max-lines 1500`.
6. **Graph gate.** Run
   `python3 tools/proof_depgraph.py --db DEPGRAPH.md --manifest DEPGRAPH_COVERAGE.md --source-root . --require-reviewed --require-complete-coverage --require-initial-lean-status --require-all-reachable --check`.
7. **Docstrings.**
   - Grep `ComplexSLE/` for stale mentions of `hMO`, `MarkovOneDim`, `markov_oneDim`, `hormander_oneDim`,
     `IsDiffusionKernel`, `kernelOp`, `SLEStatKernel`, `AllZDensity`, or of "EXTERNAL" inputs that are now proved.
   - List the hits. Hits in docstrings are non-blocking unless they misstate what a theorem depends on.

Verdict: PASS only if items 1–6 pass. List non-blocking notes separately.

Commands: `export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"` first. Do not run `lake clean`; do not edit any file
except the report.

Handoff: the report path and a summary of the verdict, with blocking defects (if any) first.

