# M7 / A5a — Lemma 3.4, first half: Birkhoff for log|f̂(𝐳)| (prover brief, Sonnet)

Goal (INTERNAL, new files ComplexSLE/Internal/Phases/Ergodic*.lean): on Ω × ℝ with P.prod ν (ν = admissibleMeasure p), with
Y_s(ω,u) := log‖f̂_s(e^{iu})(ω)‖ (Y_0 = 0 since |e^{iu}| = 1 and U 0 = 0 — check), prove
 (1) integrability: ξ_n := Y_{n+1} − Y_n is integrable, with ∫ ξ_0 = integralI a b c p (Frozen/Defs/IntegralI.lean; the paper's
     (2.36)/(eqn-integral-nu): E Y_s = s · ∫ ν p — use the decomposition Y_s = ∫₀ˢ ν(θ̂) + M_s with M = sigmaLogMart
     (Polar/PolarTimeChange.lean, ae_sigmaLogMart_eq in PolarThetaHat.lean), one-time stationarity (Stationary/SLEStat.lean:
     law of θ̂_s mod π is p du mod π; ν is π-periodic) for the drift, and E M_s = 0: M is a continuous local martingale with
     bracket ∫₀ˢ Γ̂, Γ̂ ≤ a + b + |c| bounded, hence an L²-bounded true martingale on [0, s] — prove that lemma (localise,
     optional stopping, Fatou/Doob or E[M_{τ∧s}²] = E[⟨M⟩_{τ∧s}] ≤ C s, then uniform integrability) in
     ComplexSLE/Infrastructure/Stochastic/ (new file prefixed BoundedBracket*); also E sup_{r ≤ 1}|Y_{n+r} − Y_n| < ∞ for the
     noninteger-time step (Doob's L² inequality is in Mathlib for discrete time — use a dyadic/continuity argument, or bound
     sup |M| via the same localisation).
 (2) stationarity of (ξ_n): from Stationary/PathStat.lean map_pathObs_eq_zero (law of the increment path after n equals that
     after 0), so the laws of (ξ_{n+k})_k and (ξ_k)_k agree — the hypothesis shape of EXTERNAL birkhoff_stationary
     (ComplexSLE/External/BirkhoffStationary.lean; read it: measurability of each ξ_n, equality of P.map of shifted sequences).
 (3) Birkhoff: ∃ integrable L with ∫ L = integralI and Y_n/n → L a.s.; then Y_s/s → L a.s. along real s → ∞ (noninteger
     times via (1)'s sup bound + Borel–Cantelli or the stationary L¹ sup bound / n → 0).
Take hMO : MarkovOneDim as an explicit hypothesis (as PathStat does). Allowed inputs: Mathlib; sealed defs; Internal/
Infrastructure lemmas; EXTERNALs birkhoff_stationary plus upstream ones. Ownership: new files ComplexSLE/Internal/Phases/Ergodic*.lean
and ComplexSLE/Infrastructure/Stochastic/BoundedBracket*.lean. Another Sonnet works on Phases/Swallow*.lean and
Hull/EndpointCont.lean. Checks: lake build of your modules; leanprobe externals; tools/check.sh --quick. Budget ~4 hours;
land what is proved and report the rest precisely.

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
