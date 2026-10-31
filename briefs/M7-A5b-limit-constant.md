# M7 / A5b — Lemma 3.3, second half: the Birkhoff limit is a.s. constant; recurrence when (I) = 0 (prover brief, Sonnet)

Goal (INTERNAL, new files ComplexSLE/Internal/Phases/ErgodicConst*.lean). Setting as in Phases/ErgodicBirkhoff.lean
(μ = P.prod (admissibleMeasure p), Y = logFHat hU, L from exists_birkhoff_logFHat_ae, hMO : MarkovOneDim hypothesis).
1. L = integralI a b c p μ-a.e. Paper's regeneration argument (source L1361-1372, step:sde-limit-deterministic,
   step:sde-regeneration): choose a deterministic x̄ such that X_s = e^{2iθ̂_s} hits x̄ at arbitrarily large times a.s.
   (Lemma 2.16: Internal/Recurrence/Recurrence2.lean sle_recurrence' / sle_recurrence_nonpos with hstat from
   Recurrence/StatBridge.lean and one-time stationarity Stationary/SLEStat.lean; this applies to θ̂ from each point start
   e^{iu}, or on the product — pick the clean route). Let τ_k be the successive hitting times with τ_{k+1} ≥ τ_k + 1
   (σ-time stopping times: Recurrence/HittingTime.lean isStoppingTime_hittingAfter_of_isClosed for the σ-time filtration;
   then σ_z(τ_k) is an ℱ-stopping time — Polar/PolarTimeSigma.lean). By the restart identity (Polar/PolarRestartSigma.lean,
   applied pathwise at t̃ = τ_k(ω)) and the strong Markov property at σ_z(τ_k) (Phases/AllZMarkov.lean,
   Stationary/PathStatMarkov.lean lintegral_comp_scale_postPath), L = Φ(V_k, e^{iθ̂_{τ_k}}) where V_k is the scaled post-σ_z(τ_k)
   driver and Φ the limit functional of the restarted observable; e^{iθ̂_{τ_k}} ∈ {w, −w} (w² = x̄), and by the reflection
   identity (Stationary/PathStatNeg.lean, obsC_neg) Φ(V, −w) = Φ(−V, w) with −V =_d V, so the conditional law of L given
   ℱ_{σ_z(τ_k)} (and given u, which is ℱ''_0-measurable) does not depend on the past: L is independent of ℱ_{σ_z(τ_k)} ∨ σ(u).
   Since τ_k ≥ k and σ_z(k) → T_z, ⋁_k (ℱ_{σ_z(τ_k)} ∨ σ(u)) makes L measurable, so L is independent of itself, hence a.s.
   constant (Mathlib measure_eq_zero_or_one_of_indep_self / ae_eq_const_of_indep_self-type lemmas), and the constant is ∫ L =
   integralI. If an existing lemma already gives the conditional law of the whole restarted observable at a stopping time, reuse
   it; state precisely any measurability you need and prove it.
2. Recurrence when integralI = 0: a.s. for every ε > 0 there are arbitrarily large s with |Y_s| < ε — apply EXTERNAL
   recurrence_stationary (ComplexSLE/External/RecurrenceStationary.lean) to ξ_n = Y_{n+1} − Y_n (stationary: ErgodicStat.lean
   xiInc_stationary; integrable; S_n/n → 0 by 1.).
Final shape for consumers (Prop 3.1): (a) integralI ≥ 0 ⇒ μ-a.s. ¬ (Y_s → −∞); (b) integralI < 0 ⇒ μ-a.s. Y_s/s → integralI.
Allowed inputs: Mathlib; sealed defs; Internal/Infrastructure lemmas; EXTERNALs strongMarkov_sleDriver, recurrence_stationary,
birkhoff_stationary and the upstream ones. Ownership: new files ComplexSLE/Internal/Phases/ErgodicConst*.lean only.
Checks: lake build of your modules; leanprobe externals; tools/check.sh --quick. Budget ~4 hours; if part 1 needs a missing
general fact about conditional laws at stopping times, STOP and report the exact statement; land what is proved.

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
