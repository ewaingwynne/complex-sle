# M7 / A4b — deterministic restart identity for the polar data at σ_z(t̃) (prover brief, Sonnet)

Goal (INTERNAL, deterministic; new files ComplexSLE/Internal/Polar/PolarRestart*.lean): for a continuous driver U, z with
T_z > 0, and t̃ ∈ sigmaDom U hU z, let T = sigmaTime U hU z t̃ (= σ_z(t̃) < T_z), w = fPath U hU z T (≠ 0), r = ‖w‖ and the
scaled-shifted driver V s := r⁻¹ (U (T + r² s) − U T) (continuous; use ℝ≥0 arithmetic carefully). Let z' := w / r (|z'| = 1).
Prove, for all s ≥ 0:
 (i) lifeSet/absorbing time: T_{z'}(V) = (T_z(U) − T)/r² (as ℝ≥0∞), and fPath V z' s = r⁻¹ · fPath U z (T + r² s) on the life set
     (concatenation (2.3) map formula: Frozen/Concatenation_CenteredLoewnerMap.lean or Internal/Loewner/Concatenation.lean
     centeredLoewnerMap_add_eq; scaling: Internal/Loewner/MapTransform.lean centeredLoewnerMap_scale — or redo via
     isLoewnerSolution_shift / isLoewnerSolution_scale on Polar/Path.lean solPath);
 (ii) clock: clock V z' s = clock U z (T + r² s) − clock U z T (the clock is scale invariant), hence
     sigmaDom V z' = {s | t̃ + s ∈ sigmaDom U z} − t̃ and sigmaTime V z' s = (sigmaTime U z (t̃ + s) − T)/r²;
 (iii) polar data: argPath V z' (sigmaTime V z' s) − argPath V z' 0 = argPath U z (sigmaTime U z (t̃+s)) − argPath U z T, and
     log‖fPath V z' (sigmaTime V z' s)‖ = log‖fPath U z (sigmaTime U z (t̃+s))‖ − log‖fPath U z T‖; with e^{i argPath V z' 0} = z'
     = e^{iθ̂_t̃(z)} (Polar/Argument.lean argPath_unique / exp form).
These are the "future dependence" + "scale invariance" identities behind Lemma 3.2 and the regeneration step of Lemma 3.3.
Allowed inputs: Mathlib; sealed defs/anchors; Internal lemmas. No externals (target PROVED).
Ownership: new files ComplexSLE/Internal/Polar/PolarRestart*.lean only. Another Sonnet works on Phases/AllZ*.lean.
Checks: lake build of your modules; leanprobe externals; tools/check.sh --quick. Budget ~3 hours.

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
