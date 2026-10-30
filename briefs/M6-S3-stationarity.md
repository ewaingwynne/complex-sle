# M6 / S3 — stationarity: Lemmas A.1, A.2 and the abstract part of Lemma 2.14 (prover brief, Fable, HARD)

Goal: INTERNAL lemmas (no frozen anchors) for the Kolmogorov forward equation for periodic 1-D diffusions (Lemma A.1,
source/arxiv-2203.07313v4/complex-sle-final.tex L2318-2400; note typo T12: α, β are real-valued) and its Hörmander input
(Lemma A.2, L2340-2350), stated for an abstract diffusion in martingale form, so that a later step can apply them to the
time-changed argument process θ̂ (being built concurrently under ComplexSLE/Internal/Polar/ — do not depend on it).

Target statement (shape; refine honestly): let α, β : ℝ → ℝ be smooth with α and β² π-periodic and the Hörmander condition
(β u ≠ 0 ∨ β' u · α u ≠ 0 for all u). Let p satisfy the hypotheses of Lemma A.1 (compare ComplexSLE.IsAdmissibleDensity,
ComplexSLE/Frozen/Defs/IsAdmissibleDensity.lean, which is the same with α = µ, β²/2 = D — state a bridge lemma that an
admissible density for (a,b,c) satisfies A.1's hypotheses with α = µ, β² = 2D). If X is a ComplexSLE.IsDiffusionSolution
ℱ α β X P (ComplexSLE/Frozen/Defs/IsDiffusionSolution.lean) with X₀ having law p(u)1_{[0,π]}(u)du, then the law of
(e^{2iX_t})_{t ≥ 0} is stationary — encode as: for every t₀ and finite set of times, the joint law of (e^{2iX_{t₀+s}})_s
equals that of (e^{2iX_s})_s; at minimum the one-time marginals law(e^{2iX_t}) = law(e^{2iX_0}) for all t, and say which
form downstream (Lemma 2.14 → Prop 3.1/3.2, Lemma 2.16) needs (read graph nodes lem-stationary, lem-kolmogorov,
step:kol-*, step:stat-* in DEPGRAPH.md).

Tools: EXTERNALs `ComplexSLE.External.hormander_oneDim` (HormanderOneDim.lean: smooth transition density p t u v,
smooth semigroup, and law(X_t) = p t u dv for every IsDiffusionSolution started at u — i.e. uniqueness in law) and
`ComplexSLE.External.ito_formula` (ItoFormula.lean) for E f(X_t) − E f(X_0) = E∫(f'α + ½f''β²). The paper's proof also
uses the Markov property E_p(T_s f(X_t)) = E_p(f(X_{t+s})) (step:kol-markov-semigroup). That is NOT directly any current
external (strongMarkov_sleDriver is for the driver). Try to derive it from hormander_oneDim's uniqueness-in-law clause
plus conditioning; if that genuinely needs a further classical input (e.g. "solutions of a well-posed martingale problem
are Markov", Stroock–Varadhan / Ethier–Kurtz 4.4.2), STOP that part and report the exact Lean statement you would need
(it would go to the author's approval packet), and land everything else.

Allowed inputs: Mathlib; sealed defs; Internal/Infrastructure lemmas (Density/*, Driver/*); EXTERNALs hormander_oneDim,
ito_formula. No DRAFT anchor or provider.
Ownership: new files under ComplexSLE/Internal/Stationary/ and helpers under ComplexSLE/Infrastructure/Stochastic/
(coordinate file names with the concurrent Polar prover: use the prefix Stationary_ for files you add there).
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

Handoff: files changed; exact statements of main lemmas; approach; commands and outputs; externals status; any needed
new external with an exact Lean draft; anything unproved.
