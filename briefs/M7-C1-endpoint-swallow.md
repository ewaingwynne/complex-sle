# M7 / C1 — Lemma 2.5 (endpoint continuity), Lemma 3.5 (swallow distance), Prop 3.1(b) ODE comparison (prover brief, Sonnet)

All deterministic; INTERNAL lemmas in new files ComplexSLE/Internal/Phases/Swallow*.lean (and Internal/Hull/EndpointCont.lean).
1. Lemma 2.5 (lem-endpt-cont, source L667-690): for continuous U and z with T_z < ∞, ‖fPath U hU z t‖ → 0 as t → T_z⁻
   (within lifeSet; Internal/Polar/Path.lean). The liminf is already proved (exists_norm_fPath_lt); replace it by a limit with
   the paper's upcrossing argument (uniform continuity of U on [0, T_z], each upcrossing of [α, β] takes time ≥ ε, so finitely
   many). Note the paper's bound |f_{t₂} − f_{t₁}| ≤ ∫2/|f| + |U_{t₁} − U_{t₂}| uses g' = 2/f (solPath derivative).
2. Lemma 3.5 (lem-swallow-distance, L1389-1398) in σ-time: for continuous U, z ≠ 0 with clockSup = ⊤ (sigmaDom = Ici 0) and
   T_z < ∞: log‖f̂_s(z)‖ → −∞ as s → ∞ (f̂_s = fPath at sigmaTime s; sigmaTime s → T_z as s → ∞ since σ_z maps [0, ∞) onto
   [0, T_z), Internal/Polar/Sigma.lean image_sigmaTime, monotonicity). Also the a.s. form for an adapted driver via
   ae_sigmaDom_eq_Ici (Polar/PolarSigmaTop.lean).
3. Prop 3.1(b) ODE comparison (L1405-1418, eqn-neg-I1-bd): deterministic — for continuous U and z with T_z > 0, if there are
   α > 0 and s₀ with log‖f̂_s(z)‖ ≤ −α s/2... precisely: if log‖f̂_s(z)‖ / s → −α < 0 as s → ∞ (and clockSup = ⊤), then T_z < ∞.
   Paper's route: with F(t) = clock U z t (F' = |f_t|⁻²), log|f_t| < −(α/2) F(t) for t near T_z gives F'(t)e^{−αF(t)} > 1, hence
   T_z ≤ t_* + α⁻¹ e^{−αF(t_*)} < ∞. Transcribe honestly in σ-time or original time (clock_sigmaTime, hasDerivWithinAt_clock).
Allowed inputs: Mathlib; sealed defs; Internal lemmas. No externals (target PROVED), except the a.s. wrapper in 2 which inherits
PROVED_REL{ito_formula} from ae_sigmaDom_eq_Ici.
Ownership: new files ComplexSLE/Internal/Phases/Swallow*.lean and ComplexSLE/Internal/Hull/EndpointCont.lean only. Another
Sonnet works on Stationary/PathStat*.lean. Checks: lake build of your modules; leanprobe externals; tools/check.sh --quick.
Budget ~3 hours.

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
