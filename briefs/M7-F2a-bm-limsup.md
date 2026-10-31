# M7 / F2a — Brownian motion oscillates: limsup B_t = +∞ and liminf B_t = −∞ a.s. (prover brief, Sonnet)

Goal (source-independent; new file ComplexSLE/Infrastructure/Stochastic/BrownianOscillation.lean): for a standard real
Brownian motion (Mathlib's IsBrownianReal, Mathlib/Probability/BrownianMotion/Basic.lean), a.s. limsup_{t→∞} B_t = +∞ and
liminf_{t→∞} B_t = −∞ (state as: ∀ᵐ ω, ∀ M, ∀ T, ∃ t ≥ T, B t ω ≥ M, and the same with ≤ −M).
Route (no externals): P(sup_{t ≥ T} B_t ≥ M) ≥ P(B_{T+n} − B_T ≥ M + |B_T| …) — simplest: the event A = {limsup B_n/√n = +∞}
or directly: P(B_n ≥ M√n... ) use scaling (IsBrownianReal.smul) to get P(B_{n} ≥ √n) = P(B_1 ≥ 1) =: q > 0 for all n, so
P(B_n ≥ √n infinitely often) ≥ q by reverse Fatou (measure_limsup_ge or Mathlib's limsup lemmas), and {B_n ≥ √n i.o.} is a
tail event of the independent increments (B_{k+1} − B_k): Kolmogorov 0-1 in Mathlib (measure_zero_or_one_of_measurableSet_limsup_atTop
or ProbabilityTheory.measure_eq_zero_or_one_of_indep_self / Kolmogorov's 0-1 law for iIndep σ-algebras) gives probability 1;
B_n ≥ √n i.o. ⇒ limsup = +∞. Symmetric for liminf (IsBrownianReal.neg).
Also the time-changed corollary consumed later (graph step:c0-bdy-martingale-bm, using EXTERNAL dambis_dubins_schwarz): if
N_t = β_{A_t} a.s. with A_t → ∞ and β Brownian, then limsup N_t = +∞ a.s. (pure composition; state and prove it).
Allowed inputs: Mathlib only (and the external only as a hypothesis shape for the corollary — no import needed).
Ownership: the new file only. Another Sonnet works on Stationary/PathStat*.lean. Checks: lake build; leanprobe externals
(target PROVED); tools/check.sh --quick. Budget ~2 hours.

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
