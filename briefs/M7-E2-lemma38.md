# M7 / E2 — Lemma 3.8 (lem-log-finite-exp): E log(1/dist(𝐳, L_{σ(t̃)})) < ∞ (prover brief, Sonnet)

Source: source/arxiv-2203.07313v4/complex-sle-final.tex L1550-1630 (multi-scale argument). Goal (INTERNAL, new files
ComplexSLE/Internal/Phases/Lemma38*.lean): on μ = P.prod (admissibleMeasure p) with z = e^{iu}, for each t̃ > 0,
∫ log(1/dist(z, L_{σ_z(t̃)})) dμ < ∞ (the integrand is ≥ 0 since |z| = 1 and 0... CHECK: the paper says 0 ∈ L_{σ(t̃)} — it is
U 0 = 0 ∈ L_t (Internal/Hull/Basic.lean driver_zero_mem_leftHull, with U 0 = 0 a.s.) — so dist ≤ 1). Equivalently the tail
bound P(dist(z, L_{σ_z(t̃)}) ≤ 16^{−k}) ≤ C 2^{−k}.
Route (paper): τ_k = first time L_t hits B(z, 16^{−k}) (a stopping time — hulls are adapted; Phases/EventMeas*.lean,
Polar/Measurability.lean); EXTERNAL koebe_distortion (ComplexSLE/External/KoebeDistortion.lean — read its normalisation) on
B(z, dist(z, L_{τ_k})) with 0 ∈ R_{τ_k} (Phases/KoebeHit.lean zero_mem_rightHull) gives (3.19): f_{τ_k}(B_{16^{−k−1}}(z))/|f_{τ_k}(z)| ⊆
B_{1/2}(f_{τ_k}(z)/|f_{τ_k}(z)|); T_k = first exit of the rescaled future hull L_{τ_k,t}/|f_{τ_k}| from B_{1/2}(0) satisfies T_k ≤ τ_{k+1}; the
clock increment ∫_{τ_k}^{T_k} |f_v|^{−2} dv equals the exit-time clock of the restarted chain (restart identity at a stopping time:
Polar/PolarRestart*.lean + concatenation), which by strong Markov + scaling (Stationary/PathStatMarkov.lean lintegral_comp_scale_postPath)
is independent of ℱ_{τ_k} with a law not depending on k — careful: the restart point is f_{τ_k}(z)/|f_{τ_k}(z)| (a random unit vector),
and the exit-clock law may depend on it; the paper glosses this. Either show the exit-clock functional is bounded below in law
uniformly over the starting direction (e.g. P(clock ≥ q) ≥ 1/2 for all unit starting points, by continuity/compactness or by a
direct estimate: before the hull reaches distance 1/2 from 0 the point stays at distance ≥ 1/2 from the driver path…) or find the
honest replacement, and REPORT how you handled it. Then independence across k and the binomial bound give
P(∫_0^{τ_k} |f|^{−2} ≤ qN) ≤ C_N 2^{−k}, i.e. P(τ_k ≤ σ_z(qN)) ≤ C_N 2^{−k}, hence the tail bound and integrability.
Allowed inputs: Mathlib; sealed defs/anchors; Internal/Infrastructure lemmas; approved EXTERNALs (koebe_distortion, koebe_quarter,
strongMarkov, markov_oneDim, hormander, ito, timeChange). Ownership: new files ComplexSLE/Internal/Phases/Lemma38*.lean only;
scratch only in your own .lake/probes subdirectory. Another Sonnet works on Phases/Lemma37*.lean. Checks: lake build; leanprobe
externals; tools/check.sh --quick. Budget ~4 hours; if the uniformity over the starting direction needs more than the available
tools, STOP and report precisely; land what is proved.

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

Handoff: files changed; exact statements; approach (including the uniformity issue); commands and outputs; externals; anything unproved.
