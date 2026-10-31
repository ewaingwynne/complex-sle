# M7 / D1 — the Koebe hitting bound (3.13) and 0 ∈ R_t (prover brief, Sonnet)

Goal (INTERNAL lemmas, new files ComplexSLE/Internal/Phases/KoebeHit*.lean), source L1460-1466 (eqn-hit-koebe), graph SOURCE_GAP
step:zero-in-right-hull:
1. 0 ∈ R_t for every continuous U and t (R_t = rightHull, complement of the range of f_t): f_t(w) = g_t(w) − U_t ≠ 0 for
   w ∉ L_t (Internal/Hull/Basic.lean loewnerMap_ne_driver).
2. For z ∉ L_t with d := infDist z (leftHull U t) > 0: ‖f_t'(z)‖ · d ≤ 4 ‖f_t(z)‖, where f_t' is the complex derivative of
   w ↦ f_t(w) = solPath U hU w t − U t at z (Internal/Polar/PolarDeriv.lean: hasDerivAt_solPath_initial, derivPath; the
   extension agrees with centeredLoewnerMap on ℂ ∖ L_t, Polar/Path.lean). Proof: f_t is holomorphic and injective on the open
   ball B(z, d) ⊆ ℂ ∖ L_t (holomorphy: Polar/PolarDeriv.lean differentiableOn_solPath_initial; injectivity:
   Internal/Loewner/Injective.lean centeredLoewnerMap_injective), and its image avoids 0 (part 1). Apply EXTERNAL
   ComplexSLE.External.koebe_quarter (ComplexSLE/External/KoebeQuarter.lean — read its exact normalisation: unit disc, f 0,
   ‖f'(0)‖/4) to F(ζ) := f_t(z + d ζ): F(B(0,1)) ⊇ B(F(0), |F'(0)|/4) = B(f_t(z), d|f_t'(z)|/4), and 0 ∉ F(B(0,1)), so
   d|f_t'(z)|/4 ≤ |f_t(z)|.
3. Consequence in polar/σ-time form: for z ≠ 0 and s ∈ sigmaDom, infDist z (leftHull U (σ_z s)) ≤ 4 ‖f̂_s(z)‖/‖f̂'_s(z)‖ =
   4 exp(−(log‖f̂'_s‖ − log‖f̂_s‖)), using derivPath and sigmaLogRatio (Polar/PolarDerivSigma.lean); and the corollary:
   if limsup_{s→∞} (log|f̂'_s(z)| − log|f̂_s(z)|) = +∞ then z ∈ closure (⋃_{t < T_z} L_t) (the hitting-phase closure clause of
   ComplexSLE/Frozen/Defs/IsHittingPhase.lean), and if the limit is +∞ then the R14 ε-form "∀ ε > 0, ∃ t < T_z, infDist z L_t < ε"
   of Prop 3.2(a) (ComplexSLE/Frozen/Proposition_3_2_A.lean, read-only) holds.
Allowed inputs: Mathlib; sealed defs; Internal lemmas; EXTERNAL koebe_quarter. Ownership: new files
ComplexSLE/Internal/Phases/KoebeHit*.lean only. Another Sonnet works on Stationary/PathStat*.lean.
Checks: lake build; leanprobe externals (expect PROVED_REL{koebe_quarter} for 2-3); tools/check.sh --quick. Budget ~3 hours.

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

Handoff: files changed; exact statements; approach; commands and outputs; externals; anything unproved.
