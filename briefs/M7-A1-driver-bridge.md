# M7 / A1 — from IsSLEDriver to an adapted driver with an independent random angle (prover brief, Sonnet)

Context: the frozen §3 roots (ComplexSLE/Frozen/{Theorem_1_8,Proposition_3_1_A,…}.lean, read-only) take
`hU : IsSLEDriver a b c U P` on an arbitrary (Ω, P) (a.s. continuous paths, no filtration). The internal polar layer
(ComplexSLE/Internal/Polar/*, e.g. isDiffusionSolution_thetaHat in PolarThetaHat.lean) needs
`ComplexSLE.IsSLEDriverAdapted a b c U P ℱ` (ComplexSLE/Frozen/Defs/IsSLEDriverAdapted.lean: everywhere-continuous paths,
adapted, increments independent of ℱ s). Section 3 of the paper also samples a random point 𝐳 on the unit circle,
independent of the driver, with arg 𝐳 ~ p(u) 1_{[0,2π]}(u) du (graph SOURCE_GAP step:section3-product-extension).
Goal (INTERNAL lemmas, new files under ComplexSLE/Internal/Driver/ prefixed Bridge*):
1. Adapted version: for hU : IsSLEDriver a b c U P (a, b > 0, c² ≤ ab) there are a filtration ℱ (the natural filtration of U
   enlarged by the measurable P-null sets) and U' with ∀ᵐ ω, ∀ t, U' t ω = U t ω and IsSLEDriverAdapted a b c U' P ℱ.
   Independence of U_t − U_s from the past: reuse IsSLEDriver.indep_shift_past (ComplexSLE/Internal/Driver/Shift.lean);
   null sets: ComplexSLE/Infrastructure/Stochastic/ContinuousModification.lean (completedFiltration, modification lemmas).
2. Product extension: for a probability measure ν on ℝ (Borel), on Ω × ℝ with P.prod ν, the lifted driver
   U'' t (ω, u) = U' t ω is IsSLEDriverAdapted for a filtration ℱ'' with ℱ'' 0 ∋ σ(snd) (the angle is ℱ''_0-measurable),
   e.g. ℱ'' t = (ℱ t).comap fst ⊔ (Borel).comap snd (plus null sets if needed); and snd has law ν and is independent of U''.
3. Transfer: for any event family E(ω) depending only on the path of U, ∀ᵐ ω ∂P, E(U · ω) iff ∀ᵐ x ∂(P.prod ν), E(U'' · x)
   (state it in the form the roots need: a.s. statements about absorbingTime / leftHull of U transfer from U'' to U, using
   that U' = U a.s. and the hull objects are functions of the path).
Allowed inputs: Mathlib; sealed defs; Internal/Infrastructure lemmas. No externals (target PROVED).
Ownership: new files under ComplexSLE/Internal/Driver/ prefixed Bridge*. Do not edit existing files.
Checks: lake build of your modules; `python3 -I tools/leanprobe.py externals <module> <decl>` (target PROVED);
`tools/check.sh --quick`. Budget ~3 hours; land what is proved, report the rest precisely.

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
