# M7 / A2 — Lemma A.1 in kernel form (prover brief, Sonnet)

Goal (INTERNAL lemmas, new files ComplexSLE/Internal/Stationary/Kernel*.lean): with α, β as in Lemma A.1 (smooth, α and β²
π-periodic, Hörmander condition; see Stationary/Coefficients.lean for the SLE instances), a kernel p : ℝ≥0 → ℝ → ℝ → ℝ
(p ≥ 0, p t u · continuous, and for every u some/any IsDiffusionSolution started at u has time-t law p t u v dv — the
representation clause of ComplexSLE.External.hormander_oneDim), the semigroup T_t f u := ∫ f v * p t u v, and an
IsKolmogorovDensity p₀ (Stationary/KolmogorovDensity.lean), prove
   ∀ t, ∀ f bounded measurable (or C² π-periodic first, then extend as Stationary/Law.lean does), ∫₀^π T_t f u * p₀ u du = ∫₀^π f u * p₀ u du,
and the law form (the pushforward of p₀ du on [0,π] mod π is invariant under the kernel).
Route: φ(t) := ∫ T_t f · p₀. For each u take a solution X^u from u (hypothesis: existence of a solution from every u on some
probability space — state it as a hypothesis; for SLE it is supplied by isDiffusionSolution_thetaHat with z = e^{iu}, see
ComplexSLE/Internal/Polar/PolarThetaHat.lean); Itô in expectation (Stationary/ItoReal.lean: integral_sub_integral_eq,
hasDerivWithinAt_integral_comp) gives the derivative of T_t f(u) at t = 0 as Lf(u); the semigroup identity T_{t+s} = T_t ∘ T_s
is the Markov hypothesis (state it exactly as the consumer-side form of the pending external markov_oneDim,
review/approvals/drafts/MarkovOneDim.lean.txt, i.e. as an explicit hypothesis — do NOT import or assume the external);
T_s f is C² and π-periodic (hormander smoothness + equivariance — hypotheses); then φ'(t) = ∫ L(T_t f) p₀ = 0 by
IsKolmogorovDensity.integral_generator_eq_zero, so φ is constant (constant_of_has_deriv_right_zero). Reuse Kolmogorov.lean /
Law.lean wherever possible (they prove the same for a single process with initial law p₀).
Allowed inputs: Mathlib; sealed defs; Internal/Infrastructure lemmas; EXTERNALs ito_formula, hormander_oneDim (only as
hypothesis shapes / existing upstream use). Ownership: new files ComplexSLE/Internal/Stationary/Kernel*.lean only.
Another Sonnet works under ComplexSLE/Internal/Polar/ (prefix PolarCont*). Checks: lake build; leanprobe externals;
tools/check.sh --quick. Budget ~3 hours.

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
