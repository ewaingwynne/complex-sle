# M7 / C2 — assemble Proposition 3.1 (a)/(b) (prover brief, Sonnet)

Goal: prove INTERNAL theorems with EXACTLY the types of the frozen anchors ComplexSLE.proposition_3_1_a and
proposition_3_1_b (ComplexSLE/Frozen/Proposition_3_1_{A,B}.lean, read-only) EXCEPT for one extra first argument
(hMO : ComplexSLE.Internal.MarkovOneDim) (Internal/Stationary/SLEStatKernel.lean): names
ComplexSLE.Internal.proposition_3_1_a_of_markov / proposition_3_1_b_of_markov, in new files ComplexSLE/Internal/Phases/Prop31*.lean.
(When the author approves the pending external markov_oneDim, the providers become `… (External.markov_oneDim) …`.)
Ingredients (all proved):
- Driver bridge: Internal/Driver/Bridge*.lean (IsSLEDriver → adapted version on a completed filtration; transfer of a.s. hull
  statements back to U).
- Lemma 3.3 consequences for the random point: Internal/Phases/ErgodicConst.lean not_tendsto_atBot_logFHat (I ≥ 0),
  tendsto_logFHat_div_of_integralI_neg (I < 0), on μ = P.prod (admissibleMeasure p).
- Lemma 3.5 / ODE comparison: Internal/Phases/SwallowDistanceAE.lean (ae_tendsto_sigmaLogNorm_atBot: T_z < ∞ ⇒ log|f̂| → −∞;
  ae_absorbingTime_lt_top_of_tendsto_sigmaLogNorm_div: log|f̂|/s → −α < 0 ⇒ T_z < ∞). Note these are per fixed z; apply them
  fibrewise at z = e^{iu} (Fubini on the product, or restate on the product) — logFHat hU s (ω,u) = log‖fHat hU (unitPt u) s ω‖.
- Lemma 3.2: Internal/Phases/AllZ.lean lemma_3_2 with E = {T_z = ∞} (resp. {T_z < ∞}); MeasurableEvents from
  Internal/Phases/EventMeasEvents.lean; ScaleInvariantEvents / FutureDependentEvents from Internal/Phases/AllZExamples.lean
  (proved for {T_z < ∞}; derive the {= ∞} version by negation — MeasurableEvents.not).
Allowed inputs: Mathlib; sealed defs/anchors; Internal/Infrastructure lemmas; existing EXTERNAL uses upstream.
Ownership: new files ComplexSLE/Internal/Phases/Prop31*.lean only.
Checks: lake build of your modules; an exact-type probe showing the theorem with hMO applied has the frozen type (example :
∀ hMO, <frozen statement> := fun hMO => proposition_3_1_a_of_markov hMO); leanprobe externals; tools/check.sh --quick. Budget ~3 hours.

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
