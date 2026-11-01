# M7 / F2b — Lemma 3.12 (lem-c0-bdy): c = 0, a − b = 8 is in the hitting phase (prover brief, Sonnet)

Goal: ComplexSLE.Internal.lemma_3_12 : ∀ a b, 0 < a → 0 < b → a − b = 8 → IsHittingPhase a b 0
(ComplexSLE/Frozen/Defs/IsHittingPhase.lean), in new files ComplexSLE/Internal/Phases/C0Bdy*.lean. Source L1910-1930.
Per fixed z ≠ 0 (no Lemma 3.3 needed), for hU : IsSLEDriver a b 0 U P on Ω : Type:
1. T_z < ∞ a.s.: Prop 3.1(b) (the SEALED anchor ComplexSLE.proposition_3_1_b, Frozen/Proposition_3_1_B.lean — you may import
   it, it is SEALED) with integralI < 0, which holds since a − b = 8 > 4 (Phases/C0Integrals.lean integralI_c0_neg_iff; you need
   an admissible density: Frozen/Lemma_2_13_Exists.lean exists_admissibleDensity, SEALED).
2. Closure clause: with the adapted version of the driver (Driver/Bridge*.lean IsSLEDriver.exists_adapted) and the ratio
   R_s = sigmaLogRatio (Polar/PolarDerivSigma.lean): for c = 0 and a − b = 8, ratioDriftHat = ν + 2cos 2θ̂ ≡ 0, so R_s = −M_s
   with M = sigmaLogMart (sigmaLogRatio_eq; log|f_0| = log|z| constant — include it); M is a continuous local martingale with
   M² − ∫ Γ̂ a continuous local martingale, Γ̂ = a cos²θ̂ + b sin²θ̂ ≥ min(a, b) > 0 (logBracketFn, PolarTimeChange.lean;
   isContLocalMartingale_sigmaLogMart / …Sq). EXTERNAL dambis_dubins_schwarz (ComplexSLE/External/DambisDubinsSchwarz.lean)
   gives a Brownian motion β with M_t = β_{A_t}, A_t = ∫₀ᵗ Γ̂ → ∞; Infrastructure/Stochastic/BrownianOscillation.lean
   ae_forall_exists_le_of_timeChange gives liminf M = −∞, i.e. limsup R = +∞ (check the sign!). Then Phases/KoebeHitSigma.lean
   (ae_mem_closure_iUnion_leftHull_of_limsup or the fixed-ω version with sigmaDom = Ici 0 from ae_sigmaDom_eq_Ici) gives
   z ∈ closure (⋃_{t < T_z} L_t).
3. Transfer from the adapted version back to U (Driver/BridgeTransfer.lean) and assemble IsHittingPhase.
Allowed inputs: Mathlib; sealed defs/anchors (proposition_3_1_b, exists_admissibleDensity are SEALED); Internal/Infrastructure
lemmas; approved EXTERNALs (dambis_dubins_schwarz, koebe_quarter, ito_formula, timeChange, and those upstream). No DRAFT anchor
or provider (theorem_1_8_c_zero is still DRAFT — do not import it). Ownership: new files ComplexSLE/Internal/Phases/C0Bdy*.lean.
Checks: lake build of your modules; leanprobe externals; tools/check.sh --quick. Budget ~3 hours.

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
