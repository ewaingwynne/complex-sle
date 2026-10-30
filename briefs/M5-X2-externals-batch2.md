# M5 / X2 — draft EXTERNAL batch 2 (drafting brief, Fable)

You DRAFT statements; you do not freeze or prove anything. Deliverable: one scratch file
`.lake/probes/ExtDraft2.lean` (a `module`, compiling with `lake env lean`, every body `by sorry`) plus a report.
Do not create or edit any tracked file.

Context: arXiv:2203.07313v4 (source/arxiv-2203.07313v4/complex-sle-final.tex). Project rules: CLAUDE.md, ERRATA.md
(esp. R1, R6, R9, R12, R23, R24), PLAN.md §7. Batch 1 (already frozen; read for style): ComplexSLE/External/*.lean.
Definitions available to externals: sealed ComplexSLE/Frozen/Defs/* (IsSLEDriver, covMatrix, complexGaussian,
leftHull, loewnerMap, centeredLoewnerMap, rightHull, …) and Mathlib.

Ruling R24: stochastic inputs are stated in martingale / law form using only Mathlib notions (Filtration, stopping
times `IsStoppingTime`, `Martingale`, `condExp`, `HasLaw`, `IndepFun`/`Indep`, `IsBrownianReal`, …); no stochastic
integral. Each external must be (1) TRUE for every instance of its binders, (2) a classical theorem or a mild,
clearly-true specialisation of one — never shaped to the paper's conclusion, (3) sufficient for every consumer node.

Externals to draft (graph node → consumers; find them in DEPGRAPH.md by searching the ext ID, read each consumer's
record and the cited source lines to see exactly what form is needed):
- ext:strong-markov-bm (step:markov-driver, step:kol-markov-semigroup, step:rec-monotone-in-y, step:rec-renewal,
  step:sde-regeneration) — strong Markov property of the SLE_Σ driver at a stopping time of its natural filtration
  (post-τ increments independent of F_τ and again a driver). Decide the filtration convention once and state it.
- ext:blumenthal (step:disc-b-blumenthal), ext:kolmogorov-zero-one (step:sde-limit-deterministic) — check first
  whether Mathlib already proves what is needed (Mathlib has Kolmogorov 0-1 for independent σ-algebras); if so,
  say so and draft nothing.
- ext:birkhoff (step:sde-birkhoff-limit), ext:durrett-7.3.2 (step:recurrent-durrett-adaptation),
  ext:scale-function (step:rec-scale-function-hit).
- ext:koebe-quarter, ext:koebe-distortion (consumers listed in DEPGRAPH.md; classical univalent-function statements on a
  disc are preferred, consumers then rescale).
- ext:ito-complex (step:kol-ito-expectation, step:polar-ito-log), ext:levy-characterization (step:c0-bdy-martingale-bm,
  step:polar-W-law, step:rec-time-change-omega, step:stat-martingale-qv), ext:girsanov (step:disc-a-hit-Lambda,
  step:prop-ii-b-hit-lambda-prime), ext:hormander-1d (step:horm-apply-hairer). These are the hard ones: design a small,
  coherent martingale-form vocabulary (it may need a few auxiliary *definitions* — list them separately; they would
  have to be author-approved definition anchors, so keep them minimal and literal, e.g. "continuous local martingale
  w.r.t. a filtration" if Mathlib lacks it, or quadratic covariation characterised by martingale property of
  M N − ⟨M,N⟩). For Itô in martingale form a natural shape is: for the driver U with natural filtration and a process
  A that is adapted with C¹ paths, and F of class C² (as a function of real coordinates), the process
  F(A_t, U_t) − F(A_0, U_0) − ∫₀ᵗ (D_A F · A'_s + (1/2) Σ_{ij} Σ_{ij} ∂_i∂_j F) ds is a local martingale. Hörmander may be
  stated as the conclusion the consumer needs (smooth transition semigroup for the specific 1-D diffusion class) only
  if the general statement is unreasonably far from Mathlib — flag it if so.

For each external also state whether a faithful statement is impossible without new definitions, and if a consumer
seems to need more than any classical theorem gives, say so explicitly (that is a source gap, not something to absorb
into an external).

Report (concise, ≤ 1500 words): per external — Lean name, the statement summary, which classical theorem it is (with a
reference), which consumers it serves and how, any auxiliary definitions, Mathlib coverage, and doubts. Then the file
path. Compile check: `cd /home/ewain/complex-sle && export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH" &&
lake env lean .lake/probes/ExtDraft2.lean` must succeed (sorry warnings only). Another agent is building under
ComplexSLE/Internal/Hull/ — don't run lake build on the whole project. Budget ~3 hours.
