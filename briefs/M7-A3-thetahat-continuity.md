# M7 / A3 — continuity of θ̂_s(z) and f̂_s(z) in the starting point z (prover brief, Sonnet)

Goal (INTERNAL lemmas, new files ComplexSLE/Internal/Polar/PolarCont*.lean): for a continuous driver U (fixed path) and
s ≥ 0, the maps z ↦ θ̂_s(z) = argPath U hU z (sigmaTime U hU z s) and z ↦ log|f̂_s(z)| are continuous on the open set of
z ≠ 0 with (s:ℝ) ∈ sigmaDom U hU z (and that set is open), up to the 2π-ambiguity of the argument handled honestly (θ̂ is
the continuous lift with θ̂_0 ∈ [0, 2π) — continuity in z may fail where arg z crosses 0; prove continuity of
e^{iθ̂_s(z)} and of θ̂_s(z) − θ̂_0(z), which is what consumers need). Then the joint measurability corollary: for
hU : IsSLEDriverAdapted a b c U P ℱ, (ω, u) ↦ e^{iθ̂_s(e^{iu})}(ω) and (ω, u) ↦ θ̂_s − θ̂_0 are measurable on Ω × ℝ
(Carathéodory: measurable in ω for fixed u — Polar/DriverMeasurability.lean — and continuous in u).
Tools: Polar/{Path,Sigma,Argument,Stability,PolarDerivShift}.lean (exists_stability, exists_lipschitz_initial: Lipschitz
dependence of f_s on the starting point on [0,t]), clock continuity in z via the Lipschitz bound and dominated convergence,
sigmaTime continuity from strict monotonicity of the clock.
Allowed inputs: Mathlib; sealed defs; Internal/Infrastructure lemmas. No externals (target PROVED).
Ownership: new files ComplexSLE/Internal/Polar/PolarCont*.lean only. Another Sonnet works on Stationary/Kernel*.lean.
Checks: lake build; leanprobe externals; tools/check.sh --quick. Budget ~3 hours.

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
