# M6 / S6 — measurability of the Loewner path in ω (prover brief)

Goal: source-independent-in-spirit INTERNAL lemmas (new files under ComplexSLE/Internal/Polar/, e.g. Measurability.lean)
proving that the Loewner objects are measurable / adapted functionals of a continuous driver. Setting: `hU :
ComplexSLE.IsSLEDriverAdapted a b c U P ℱ` (ComplexSLE/Frozen/Defs/IsSLEDriverAdapted.lean; paths continuous for every ω,
U adapted to ℱ), z : ℂ. Use the existing polar objects (read ComplexSLE/Internal/Polar/{Path,Sigma,Argument}.lean:
lifeSet, solPath, fPath, exitTime, clock, sigmaTime, argPath).
Target statements (shape; adjust names/forms honestly, no extra hypotheses):
1. `IsStoppingTime ℱ (fun ω => absorbingTime (U · ω) z)`   — {T_z ≤ t} = {z ∈ L_t(ω)} ∈ ℱ t.
2. For each t : ℝ≥0, the map ω ↦ (if (t:ℝ) ∈ lifeSet (U · ω) z then fPath (U · ω) (hU.cont ω) z t else 0) is ℱ t-measurable;
   same for solPath, and for the indicator of {t ∈ lifeSet}.
3. The exit times exitTime n (Path.lean) are ℱ-stopping times; clock and argPath values at fixed t (on lifeSet) are
   ℱ t-measurable.
Suggested route (from the polar prover): Grönwall stability of the Loewner solution under sup-norm perturbations of the
driver on [0, t] (Mathlib: dist_le_of_approx_trajectories_ODE_of_mem / ODE_solution_unique-type estimates; project:
Internal/Hull/LocalExistence.lean lt_absorbingTime_of_norm_sub_ge for persistence of existence), so that for fixed z and t
the map (U restricted to [0,t]) ↦ f_t(z) is continuous on the open set where t < T_z (w.r.t. sup norm); then approximate
U(ω)|[0,t] by piecewise-linear dyadic interpolations, which are measurable functions of finitely many ℱ t-measurable values
U(k t/2^m)(ω), and conclude by measurable_of_tendsto_metrizable. For 1., {T_z > t} is then a union over rationals of events
determined by the approximations (or use lower semicontinuity of T_z in the driver).
Allowed inputs: Mathlib; sealed defs and PROVED anchors; Internal/Infrastructure lemmas. No Externals (target PROVED).
Ownership: new files under ComplexSLE/Internal/Polar/ (do not edit the existing Polar files) and source-independent
ODE-stability helpers under ComplexSLE/Infrastructure/ODE/ (new files).
Checks: lake build of your modules; `python3 -I tools/leanprobe.py externals <module> <decl>` (target PROVED);
`tools/check.sh --quick`. Don't run full tools/check.sh. Budget ~4 hours; land what is proved.

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

Handoff: files changed; exact statements; approach; commands and outputs; externals status; anything unproved.
