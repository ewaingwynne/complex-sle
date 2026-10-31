# M7 / E3 — Step 3 of the proof of lem-converse-w-o-upgrade: the Koebe chain (3.17)–(3.28) (prover brief, Sonnet)

Source: source/arxiv-2203.07313v4/complex-sle-final.tex, proof of Lemma 3.9 (lem-converse-w-o-upgrade), Step 1 setup L1655-1670 and
Step 3 L1700-1785 (eqn-dist-event, eqn-two-formulas, eqn-two-formulas-b, eqn-two-dist-ratio, eqn-koebe-t, eqn-dist-1, eqn-dist-cases,
eqn-koebe-union, eqn-dist-es, eqn-dist-2, eqn-dist-esc; graph steps step:hulls-compact, step:future-point-outside-hulls,
step:zero-in-future-left-hull, step:converse-event-converges — several are SOURCE_GAP in DEPGRAPH.md; read those records).
Goal (INTERNAL, deterministic; new files ComplexSLE/Internal/Phases/KoebeChain*.lean): for a continuous driver U, z with
0 < t < t + s < T_z, writing f_t, L_{t,s+t}, R_{t,s+t} for the concatenation objects (Frozen/Concatenation_*.lean,
Internal/Loewner/Concatenation.lean), the event E_s of (eqn-dist-event) and a UNIVERSAL constant C (state it explicitly, e.g.
C = log 16 or whatever falls out), prove (eqn-dist-3):
   log(dist(f_t z, L_{t,s+t}) / |f_t z|) − log dist(z, L_{s+t}) ≤ 1_{E_s} · log(|f_t'(z)| / |f_t z|) + 1_{E_s^c} · log(1/dist(z, L_t)) + C.
Tools: EXTERNALs koebe_quarter and koebe_distortion (ComplexSLE/External/Koebe*.lean — read their normalisations; rescale to balls
B(w, r)); the Koebe hitting bound and 0 ∈ R_t (Phases/KoebeHit*.lean); holomorphy/injectivity of f_t and of f_{t,s+t}
(Polar/PolarDeriv.lean, Loewner/Injective.lean), the derivative chain rule f_{s+t}' = f_{t,s+t}'(f_t z) f_t'(z) from the maps formula
of (2.3) and PolarDeriv (prove it); compactness/closedness of hulls (Hull/ConnectedNoExt.lean isBounded_leftHull', isClosed_leftHull').
The paper's ≍ statements have universal constants (1/4 and 4 from Koebe quarter; distortion constants) — make every constant explicit.
If a step is genuinely false as stated (e.g. a missing case or a wrong direction of an inequality), STOP that step and report
precisely with a counterexample sketch; prove the rest.
Allowed inputs: Mathlib; sealed defs/anchors; Internal lemmas; approved EXTERNALs koebe_quarter, koebe_distortion. No others
(target PROVED_REL{koebe_*}). Ownership: new files ComplexSLE/Internal/Phases/KoebeChain*.lean only; scratch in your own
.lake/probes subdirectory. Another Sonnet works on Phases/Lemma38*.lean. Checks: lake build; leanprobe externals;
tools/check.sh --quick. Budget ~4 hours.

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

Handoff: files changed; exact statements (incl. the explicit C and the definition of E_s); approach; commands and outputs;
externals; anything unproved.
