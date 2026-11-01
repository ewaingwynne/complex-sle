# M10-A2: the two Loewner externals, in-project

Goal: sorry-free proofs of the EXACT statements of
- `ComplexSLE.External.loewnerMap_conformal` (`ComplexSLE/External/LoewnerMapConformal.lean`) and
- `ComplexSLE.External.loewnerMap_tendstoUniformly` (`ComplexSLE/External/LoewnerMapTendstoUniformly.lean`)
(both read only) as `ComplexSLE.Internal.ExternalProofs.loewnerMap_conformal` in
`ComplexSLE/Internal/ExternalProofs/LoewnerMapConformal.lean` and
`ComplexSLE.Internal.ExternalProofs.loewnerMap_tendstoUniformly` in
`ComplexSLE/Internal/ExternalProofs/LoewnerMapTendstoUniformly.lean` (helpers in further new files under
`ComplexSLE/Internal/ExternalProofs/` if needed). Copy each theorem type verbatim. Neither provider may
import any `ComplexSLE.External.*` module (directly or transitively), so the results are PROVED outright.

Existing in-project material (already proved, no externals):
- open complement: `Polar.isOpen_compl_leftHull` (`Internal/Polar/PolarDerivShift.lean`);
- boundedness: `isBounded_leftHull'`, holomorphic extension: `exists_differentiableOn_extension_loewnerMap`,
  `one_le_norm_sub_driver_of_far` (`Internal/Hull/ConnectedNoExt.lean`);
- injectivity: `centeredLoewnerMap_injective` (`Internal/Loewner/Injective.lean`), with `g_t = f_t + U_t`;
- growth: `centeredLoewnerMap_norm_ge`, `continuous_centeredLoewnerMap` (`Internal/Disconnect/Growth.lean`);
- stability in the driver: `exists_stability` (`Internal/Polar/Stability.lean`, pointwise in `z`; its proof
  uses an explicit lower bound `η` for `|f_s(z)|` on `[0,t]`, with `ρ = η/4·e^{-Kt}`, `C = e^{Kt}`, `K = 4/η²`).
Check these before writing new lemmas (grep `ComplexSLE/Internal`, `ComplexSLE/Infrastructure`).
Before importing an Internal module, check in `frozen-anchor-manifest.json` that it is not a provider of a
DRAFT anchor (there are none left, but check) and that its import closure has no `ComplexSLE.External` module
(`grep -rl "import ComplexSLE.External" ComplexSLE/Internal ComplexSLE/Infrastructure` and follow imports).

Suggested route:
1. Conformal: take `G` = the holomorphic extension; injectivity from `centeredLoewnerMap_injective`; the only
   new estimate is `z (G z - z) → 2t` along `cobounded ℂ`: `g_t(z) - z = ∫₀ᵗ 2/(g_s(z) - U_s) ds`, and
   `|g_s(z) - U_s| ≥ |z| - M - 2s` for large `|z|` gives `|z/(g_s - U_s) - 1| → 0` uniformly in `s ≤ t`.
2. Uniform convergence: a version of `exists_stability` with the lower bound `η` explicit, then a uniform `η` over
   `{(t,z) : t ≤ T, infDist z (L_T) ≥ ε}` (compactness for bounded `z`, growth bound for large `|z|`); locally
   uniform convergence gives sup-norm convergence on `[0,T]`; shift `g` versus `f` by `U_t`, `V_n t`;
   monotonicity of hulls for `t ≤ T`.

Checks: `lake build` of both provider modules; `python3 -I tools/leanprobe.py axioms <module> <decl>` for both
(only propext, Classical.choice, Quot.sound). Every new file a module, at most 1500 lines.
Stop condition: a precise obstruction (e.g. a needed lemma is false as stated), reported with the failing goal.
Handoff: files created, approach, exact commands and output, axioms, anything unproved.

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
