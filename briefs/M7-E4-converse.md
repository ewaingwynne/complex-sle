# M7 / E4 — Lemma 3.9 (lem-converse-w-o-upgrade) (prover brief, Sonnet)

Source: L1475-1480 (statement), L1640-1700 (Steps 1-2 of the proof). Goal (INTERNAL, new files
ComplexSLE/Internal/Phases/Converse*.lean): if integralII a b c p > 0 then, on μ = P.prod (admissibleMeasure p) with z = e^{iu},
μ(the R14 "stays away" event ∃ ε > 0, ∀ t < T_z, ε ≤ infDist z (L_t)) > 0, for every adapted SLE driver
(IsSLEDriverAdapted, Ω : Type, a, b > 0, c² ≤ ab, admissible p). Note: t ↦ infDist z (L_t) is antitone, so "lim_{t→T_z} dist > 0" is
exactly the ε-form; the source proves the contrapositive "lim dist = 0 a.s. ⇒ (II) ≤ 0".
Ingredients (all proved):
- (eqn-dist-3) deterministic: Phases/KoebeChain.lean koebe_chain (C = log 16) at t = σ_z(t̃), t + s = σ_z(s̃ + t̃), event koebeEvent;
  eventually_koebeEvent (Phases/KoebeChainDisplays.lean) gives 1_{E_s} → 1 as s̃ → ∞ IF dist(z, L_{s+t}) → 0 — supply the
  probabilistic half: under the contrapositive assumption, dist(z, L_u) → 0 as u → T_z, and σ_z(s̃ + t̃) → T_z (Remark 2.12,
  Polar/PolarSigmaTop.lean; Phases/SwallowDistance.lean tendsto_sigmaTime_nhdsWithin).
- Lemma 3.7: Phases/Lemma37.lean lemma_3_7 / integral_comp_lemma_3_7 (law of dist(f_t z, L_{t,s+t})/|f_t z| = law of dist(z, L_{σ(s̃)})).
- Lemma 3.8: Phases/Lemma38Admissible.lean integrable_log_inv_distSigma_admissible (log(1/dist) integrable at every σ-time).
- Lemma 3.6 in expectation: E log(|f'|/|f|)_{σ(t̃)} = −t̃ · integralII (from the decomposition R_t̃ = −2C_t̃ − Y_t̃,
  Phases/Prop32ARatio.lean sigmaLogRatio_eq_cos_sub_logFHat, E Y_t̃ = t̃·integralI (Phases/ErgodicMean.lean integrable_integral_logFHat),
  E C_t̃ = t̃·∫cos(2u)p (Phases/ErgodicRatio*.lean integral_cos_thetaHat), integralII_eq); integrability of R_t̃.
Step 2 of the paper: take expectations of (eqn-dist-3); dominated convergence as s̃ → ∞ (the left side has nonnegative expectation by
Lemma 3.7 + monotonicity dist(z, L_{s+t}) ≤ dist(z, L_s) + Lemma 3.8; the right side tends to E log(|f'|/|f|) + C = −t̃·(II) + C);
so 0 ≤ −t̃·(II) + C for all t̃, hence (II) ≤ 0. Careful with the a.s. sets (sigmaDom = Ici 0 a.s.) and with the derivative factor: koebe_chain
uses derivPath and fPath at the original time t = σ_z(t̃); relate to sigmaLogRatio (Polar/PolarDerivSigma.lean).
Allowed inputs: Mathlib; sealed defs/anchors; Internal lemmas; approved EXTERNALs as already used upstream. Ownership: new files
ComplexSLE/Internal/Phases/Converse*.lean only; scratch in your own .lake/probes subdirectory. Another Sonnet works on
Phases/Prop32BUp*.lean. Checks: lake build; leanprobe externals; tools/check.sh --quick. Budget ~4 hours.

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
