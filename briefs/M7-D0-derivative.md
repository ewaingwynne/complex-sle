# M7 / D0 — the derivative of the Loewner map and (eqn-abs-zt') (prover brief, Fable, HARD)

Goal (INTERNAL lemmas; source/arxiv-2203.07313v4/complex-sle-final.tex L880-890, L928; graph step:polar-derivative-sde,
SOURCE_GAP "z-differentiability of f_t(z) asserted, not justified"):
1. Deterministic: for continuous U and z with t < T_z, z ↦ g_t(z) is complex-differentiable at z with derivative g_t'(z) ≠ 0,
   and t ↦ g_t'(z) satisfies ∂_t g_t'(z) = −2 g_t'(z) / f_t(z)² on [0, T_z) (as a HasDerivWithinAt (Ici 0) statement), so
   log|g_t'(z)| = −2 ∫₀ᵗ Re(f_s(z)⁻²) ds, i.e. log|f_t'(z)| = −2∫₀ᵗ cos(2θ_s)/|f_s|² ds (f' = g').
   Prefer a proof WITHOUT the conformality external: the flow is differentiable in the initial point (variational equation)
   because the field 2/(w − U_s) is holomorphic in w uniformly on the tube around the solution — e.g. show the difference
   quotient (g_t(w) − g_t(z))/(w − z) satisfies a linear ODE and converges by Grönwall (ComplexSLE/Infrastructure/ODE/,
   ComplexSLE/Internal/Polar/Stability.lean has the stability estimate). If you use `ComplexSLE.External.loewnerMap_conformal`
   (holomorphy) instead, say so (the results become PROVED_REL{loewnerMap_conformal}).
2. Time change: with the polar objects (ComplexSLE/Internal/Polar/*: argPath θ, clock, sigmaTime, sigmaDom; Remark 2.12
   ae_sigmaDom_eq_Ici in PolarSigmaTop.lean), log|f̂'_s(z)| = log|f'_{σ_z(s)}(z)| = −2∫₀ˢ cos(2θ̂_u) du for s ∈ sigmaDom
   (change of variables as in PolarTimeSigma.pathIntegral_sigmaStop_eq), hence log(|f̂'|/|f̂|) decomposes as
   −(log|f̂| − log|f̂_0|) − 2∫cos 2θ̂, which with isContLocalMartingale_sigmaLogMart gives the drift −2cos2θ̂ − ν(θ̂) =
   −(ν(θ̂) + 2cos 2θ̂) and the same martingale part (up to sign) — state this decomposition in the form lem-integral-ii
   (Prop 3.2(a), L1430-1460) and the c = 0 boundary lemma (lem-c0-bdy, L1910-1930) will consume: integralII has density
   ν + 2cos 2u (ComplexSLE/Frozen/Defs/IntegralII.lean).
Allowed inputs: Mathlib; sealed defs and anchors; Internal/Infrastructure lemmas; EXTERNALs only if unavoidable (report).
Ownership: new files under ComplexSLE/Internal/Polar/ prefixed PolarDeriv*, and ComplexSLE/Infrastructure/ODE/ (new files).
Another prover concurrently adds PolarTheta* files — don't touch those. Do not edit existing files.
Checks: lake build; `python3 -I tools/leanprobe.py externals <module> <decl>`; `tools/check.sh --quick`. Don't run full
tools/check.sh. Budget ~5 hours; land what is proved, report the rest precisely.

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
