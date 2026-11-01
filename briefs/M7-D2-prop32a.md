# M7 / D2 — Proposition 3.2(a) (prover brief, Sonnet)

Goal: ComplexSLE.Internal.proposition_3_2_a with EXACTLY the type of the frozen anchor ComplexSLE.proposition_3_2_a
(ComplexSLE/Frozen/Proposition_3_2_A.lean, read-only), in new files ComplexSLE/Internal/Phases/Prop32A*.lean (and Ergodic
helpers prefixed ErgodicRatio*). Use the approved EXTERNAL ComplexSLE.External.markov_oneDim directly (discharging the
MarkovOneDim hypotheses of the existing lemmas). Source: Lemma 3.7 (lem-integral-ii, L1430-1455) and the proof of Prop 3.2(a)
(L1456-1466).
Steps:
1. Ratio limit for the random point (Lemma 3.7 + Lemma 3.4): on μ = P.prod (admissibleMeasure p), with
   R_s = log‖f̂'_s(e^{iu})‖ − log‖f̂_s(e^{iu})‖ (sigmaLogRatio, Polar/PolarDerivSigma.lean; R_s = −Y_s − 2∫₀ˢ cos 2θ̂ with
   Y = logFHat, using sigmaLogDeriv_eq / ae_sigmaLogRatio_eq), prove R_s / s → −integralII a b c p μ-a.e.
   Route: Y_s/s → integralI (Phases/ErgodicConst.lean birkhoff_logFHat_const) and (1/s)∫₀ˢ cos 2θ̂ → ∫₀^{2π} cos(2u) p(u) du a.e.
   — the latter by the same Birkhoff + constancy machinery applied to the additive functional C_s = ∫₀ˢ cos 2θ̂: its increments
   ∫_n^{n+1} cos 2θ̂ are a measurable functional of the observable after n (Stationary/PathStat.lean pathObs; cos 2θ̂_{n+r} =
   Re(e^{2iθ̂_n} e^{2i(θ̂_{n+r} − θ̂_n)})), so stationary (as in Phases/ErgodicStat.lean), bounded, mean ∫cos(2u)p (one-time
   stationarity, Stationary/SLEStat.lean); Birkhoff (EXTERNAL birkhoff_stationary) + constancy — generalise
   Phases/ErgodicConstFibre.lean / ErgodicConst.lean to an arbitrary bounded measurable functional of the restarted observable
   if that is cleaner than duplicating. Check integralII = integralI + 2∫cos(2u)p (Frozen/Defs/IntegralII.lean).
2. If integralII < 0 then R_s → +∞, so by Phases/KoebeHitSigma.lean (ae_exists_infDist_leftHull_lt_of_tendsto or its fixed-ω
   form at z = e^{iu}) the R14 ε-form "∀ ε > 0, ∃ t < T_z, infDist z (L_t) < ε" holds for the random point (Fubini: Phases/Prop31Core.lean
   ae_prod_unit_of_ae_ae / ae_event_of_ae_ae_unit).
3. All z via Lemma 3.3 (Phases/AllZ.lean lemma_3_3, through Prop31Core.ae_event_of_ae_ae_unit): E u z := the ε-form;
   MeasurableEvents: Phases/EventMeasEvents.lean measurableEvents_hull_approach; prove ScaleInvariantEvents (scaling of hulls
   Frozen/Scaling_LeftHull + absorbingTime_scale, infDist scales by r) and FutureDependentEvents (concatenation (2.3):
   Frozen/Concatenation_LeftHull, Internal/Loewner/Concatenation.lean; T_z = s + T^V_{f_s z}; the distance from z to L_{s+t}
   is controlled by the distance from f_s(z) to L^V_t? — CAREFUL: the paper's event {lim dist(z, L_t) = 0} is future-dependent
   because L_{s+t} = L_s ∪ f_s^{-1}(L^V_t ∖ R_s) and f_s is a homeomorphism near z with f_s^{-1} uniformly continuous on compacts,
   so dist(z, L_{s+t}) → 0 iff dist(f_s z, L^V_t) → 0 — prove this carefully, it is the substantive step; if it fails for the
   ε-form as stated, report precisely).
4. Provider: assemble into the exact frozen type.
Allowed inputs: Mathlib; sealed defs/anchors; Internal/Infrastructure lemmas; approved EXTERNALs (markov_oneDim, birkhoff_stationary,
koebe_quarter, strongMarkov_sleDriver, hormander_oneDim, ito_formula, timeChange). Ownership: new files as named above only.
Checks: lake build of your modules; exact-type probe; leanprobe externals; tools/check.sh --quick. Budget ~4 hours; land what is
proved, report the rest precisely.

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
