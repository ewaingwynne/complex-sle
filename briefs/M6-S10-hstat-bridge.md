# M6 / S10 — bridge: stationary law ⇒ the recurrence input hstat (prover brief)

Goal (INTERNAL lemmas, new file ComplexSLE/Internal/Recurrence/StatBridge.lean): derive the hypothesis `hstat` of
`ComplexSLE.Recurrence.sle_recurrence'` and its reflected form in `sle_recurrence_nonpos`
(ComplexSLE/Internal/Recurrence/Recurrence2.lean; goodSet / latticeSet in Renewal.lean) from the stationarity output of the
Stationary layer (ComplexSLE/Internal/Stationary/Law.lean: map_addCircle_eq_of_markov / map_exp_eq_of_markov give that the
law of X_t mod π (as an AddCircle π-valued variable) equals that of X_0 for all t; the initial law has density p₀ on
[0, π] — see integral_comp_zero_of_map_eq and IsKolmogorovDensity in KolmogorovDensity.lean).
Target (shape): if for all t the law of ((X t : ℝ) : AddCircle π) equals a fixed measure μ, and μ has no atoms — or more
concretely μ is the pushforward of p₀ · Lebesgue on [0, π] with p₀ integrable — then ∀ η > 0, ∃ ε > 0, ∀ t,
P.real {ω | X t ω ∉ goodSet x ε} ≤ η (and the reflected version for −X, −x). Note X t ∉ goodSet x ε iff X t mod π lies in an
arc of length ε just below x mod π, so this is uniform absolute continuity of μ on small arcs. State it so that it composes
directly with map_addCircle_eq_of_markov's conclusion; state the hypotheses on μ in the weakest natural form (μ continuous,
i.e. NoAtoms, suffices: μ of the arc (x−ε, x) mod π tends to 0 as ε → 0 by continuity from above).
Allowed inputs: Mathlib; Internal lemmas. No externals. Target PROVED.
Ownership: the new file only. Checks: lake build; `python3 -I tools/leanprobe.py externals <module> <decl>`;
`tools/check.sh --quick`. Don't run full tools/check.sh. Budget ~2 hours.

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
