# M7 / E1 — Lemma 3.7 (lem-computation) in the form Prop 3.2(b) consumes (prover brief, Sonnet)

Source: source/arxiv-2203.07313v4/complex-sle-final.tex L1506-1548. Goal (INTERNAL, new files
ComplexSLE/Internal/Phases/Lemma37*.lean): on μ = P.prod (admissibleMeasure p) with the random point z = e^{iu}, for fixed
t̃, s̃ ≥ 0, with t = σ_z(t̃) and t + s = σ_z(s̃ + t̃) (so s = σ_z(s̃ + t̃) − σ_z(t̃)), and the future hull
L_{t,s+t} = leftHull (u ↦ U(· + t) − U t) s (concatenation (2.3)), prove the equality in law
   dist(f_t(z), L_{t,s+t}) / |f_t(z)|  =_d  dist(z, L_{σ_z(s̃)})
(as real random variables under μ). This is the only consequence of Lemma 3.7 used later (Step 2 of the proof of
lem-converse-w-o-upgrade, L1690). Note the source states the stronger joint law of (f_t/|f_t|, L_{t,s+t}/|f_t|); only e^{2iθ̂} is
stationary (not e^{iθ̂}), but the distance is invariant under the simultaneous negation (direction, hull) ↦ (−direction, −hull)
(Stationary/PathStatNeg.lean; Loewner/Transform.lean leftHull_neg; IsSLEDriver.neg), so the stated consequence is fine —
explain this in a docstring.
Route: exactly the restart machinery of Stationary/PathStat*.lean: at T = σ_z(t̃), with the scaled-shifted driver V and
z' = f_T(z)/|f_T(z)| (Polar/PolarRestartSigma.lean), the rescaled future hull L_{T,T+s}/|f_T| equals the hull of V at time
(s/|f_T|²), and by the restart clock identity this time is σ^V_{z'}(s̃) (clock scale invariance, restart_sigmaTime); so the
left side equals dist(z', L^V_{σ^V_{z'}(s̃)}) pathwise. Then strong Markov at T (Stationary/PathStatMarkov.lean
lintegral_comp_scale_postPath) + one-time stationarity of e^{2iθ̂_t̃} (Stationary/SLEStat.lean) + the negation symmetry give the
law equality. Measurability: Phases/EventMeas*.lean (infDist to hulls is measurable in (path, point)).
Allowed inputs: Mathlib; sealed defs/anchors; Internal/Infrastructure lemmas; approved EXTERNALs (markov_oneDim, strongMarkov,
hormander, ito, timeChange). Ownership: new files ComplexSLE/Internal/Phases/Lemma37*.lean only. Use only your own subdirectory of
.lake/probes for scratch. Checks: lake build; leanprobe externals; tools/check.sh --quick. Budget ~3 hours.

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

Handoff: files changed; exact statements; approach; commands and outputs; externals; anything unproved.
