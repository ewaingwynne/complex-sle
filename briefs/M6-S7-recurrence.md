# M6 / S7 — recurrence of the argument process (Lemma 2.16) and the P13 hitting lemma (prover brief, Fable, HARD)

Goal: INTERNAL lemmas (no frozen anchors), stated for an abstract 1-D diffusion so they can run before the polar layer
is finished, then specialised to the coefficients µ, 2D of SLE_Σ:
(A) the hitting lemma of ruling R27 (ERRATA.md, "Fix for P13, approved as R27"): for c ≥ 0 (c < 0 by symmetry), a diffusion
    with generator µ∂ + D∂² started at y hits every level θ* < y with positive probability; for c² < ab also every θ* > y.
(B) claim (2.45) in the proof of Lemma 2.16 (source/arxiv-2203.07313v4/complex-sle-final.tex L1164-1249): uniform
    positive probability δ of hitting x within time T from every y ∈ [x, x+π−ε];
(C) Lemma 2.16 itself (L1155-1163, with the R19 sign: in the critical case the recurrence point is e^{2ix} with
    tan x = sgn(c)√(b/a)), in the form downstream needs (read DEPGRAPH.md nodes lem-recurrence, step:rec-*; consumers
    lem-stationary-sde / Lemma 3.4). The renewal argument (step:rec-renewal) needs the strong Markov property of the
    argument process at the stopping times τ_k — state it as an explicit hypothesis of the abstract lemma (exactly like
    hMarkov in ComplexSLE/Internal/Stationary/Kolmogorov.lean); a Markov external (markov_oneDim, pending author approval,
    draft review/approvals/drafts/MarkovOneDim.lean.txt) will discharge it later — do NOT import or assume it otherwise.
Graph nodes (orientation):
- lem-recurrence [SOURCE_GAP]: if |c|<sqrt(ab): for each w on the unit circle, a.s. there exist arbitrarily large t~ with e^{2i hat-theta_t~(zz)} = w; if |c|=sqrt(ab): a.s. arbitrarily large t~ with e^{2i hat-theta_t~(zz)} = e^{2ix (deps: lem-stationary, step:wlog-c-nonneg-arg, step:rec-reduction-to-x, step:rec-renewal, step:rec-tau-finite, step:rec-angle-h)
- step:rec-angle-hit-unif: P^y[exists t~ in [0,T], hat-theta_t~ = x] >= delta (deps: step:rec-monotone-in-y)
- step:rec-hit-fixed-y [SOURCE_GAP]: P^y[exists t~ in [0,T] with hat-theta_t~ = x] > 0 (eqn-angle-hit-fixed) (deps: step:rec-scale-function-hit, step:rec-time-change-omega)
- step:rec-monotone-in-y: y -> P^y[exists t~ in [0,T], hat-theta = x] is non-increasing on (x,x+pi), so for each eps there exist T,delta with (2.45) on [x,x+pi-eps] (deps: step:rec-hit-fixed-y, ext:strong-markov-bm)
- step:rec-reduction-to-x: both bullets follow from: a.s. arbitrarily large t~ with e^{2i hat-theta_t~} = e^{2ix} (deps: step:D-structure, step:wlog-c-nonneg-arg)
- step:rec-renewal [SOURCE_GAP]: on the event that all tau_k^eps<infty, [hat-theta_t~(zz)] hits x infinitely often a.s. (deps: step:rec-angle-hit-unif, ext:strong-markov-bm, ext:martingale-convergence, step:stat-theta-bm-sde)
- step:rec-scale-function-hit: liminf_{v->x} psi(v) > -infinity, hence by [Law05, Lemma 1.24] with positive probability R<infinity and X_R = x (deps: ext:scale-function, step:rec-time-change-omega, step:D-structure, step:p-case2-welldefined)
- step:rec-tau-finite: a.s. there is eps>0 with tau_k^eps<infty for every k; else lim e^{2i hat-theta_t~} = e^{2ix} which has probability 0 (deps: lem-stationary, lem-stationary.admissible, step:rec-renewal)
- step:rec-time-change-omega: for r in [0,R], dX_r = mu(X_r)/(2D(X_r)) dr + dZ_r with Z_r = int_0^omega(r) sqrt(2D(hat theta)) dW' a standard linear BM (deps: step:stat-theta-bm-sde, ext:levy-characterization, step:D-structure)
- step:wlog-c-nonneg-arg [SOURCE_GAP]: the conclusion of lem-recurrence for (a,b,c,p) follows from that for (a,b,-c, p~) with p~(u) = p(-u): conjugating U gives an SLE_{Sigma~} driver, Sigma~ = [[a,-c],[-c,b]], conj(zz) has angle density p (deps: defn-sle, eqn-cov-matrix, step:reflect-map-identity, step:p-wlog-c-nonneg, def-arg, defn-sigma)

Tools: EXTERNAL `ComplexSLE.External.scale_function_hit` (ScaleFunctionHit.lean; truncated exit times; "drift bounded
above near l"), `ComplexSLE.External.timeChange_isContLocalMartingale` (for the unit-diffusion time change ω of L1192),
`ito_formula` (scale function S(θ) is a local martingale: µS' + DS'' = 0). The R27 text suggests working directly in t̃-time
with the scale function and optional stopping (now available, PROVED: ComplexSLE/Infrastructure/Stochastic/
ContinuousOptionalStopping.lean, LocalMartingaleAlgebra.lean, ContinuousModification.lean) instead of the time change —
choose the cleaner route. Coefficient facts: ComplexSLE/Internal/Stationary/Coefficients.lean (betaCrit, µ at degenerate
points), ComplexSLE/Internal/Density/Basic.lean (D > 0 when c² < ab, D-structure). Abstract diffusion:
ComplexSLE.IsDiffusionSolution (ComplexSLE/Frozen/Defs/IsDiffusionSolution.lean); everywhere-continuous paths can be
arranged with IsDiffusionSolution.exists_continuous_version.
The paper's L1226 omits finiteness of ω(R) / of the exit time at a degenerate endpoint; R27 supplies the bound
(µ ≤ −m/2 near the endpoint ⇒ E[exit] ≤ 2ε₀/m) — prove it.
Allowed inputs: Mathlib; sealed defs and anchors; Internal/Infrastructure lemmas; EXTERNALs scale_function_hit,
timeChange_isContLocalMartingale, ito_formula. No DRAFT anchor or provider.
Ownership: new files under ComplexSLE/Internal/Recurrence/. No other edits.
Checks: lake build of your modules; `python3 -I tools/leanprobe.py externals <module> <decl>` per main theorem;
`tools/check.sh --quick`. Don't run full tools/check.sh. Budget ~5 hours; land what is proved, report the rest precisely.

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

Handoff: files changed; exact statements of main lemmas; approach; commands and outputs; externals status; anything
unproved (with precise statements).
