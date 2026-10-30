# M6 / S5 — stochastic infrastructure: optional stopping, sums, continuity transfer (prover brief)

Goal: source-independent lemmas in ComplexSLE/Infrastructure/Stochastic/ (new files only; read the existing
StoppedLocalMartingale.lean and Stationary_LocalMartingale.lean first and reuse/deduplicate where natural, without
editing them):
1. Optional stopping for continuous-time martingales with continuous paths (Revuz–Yor II.3.3):
     theorem Martingale.stoppedProcess_of_continuous {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ P)
         (hc : ∀ ω, Continuous fun t => M t ω) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) :
         Martingale (stoppedProcess M τ) ℱ P
   Route: dyadic approximations τ_m ↓ τ with countable range (Mathlib: stoppedValue_ae_eq_condExp_of_le_of_countable_range
   or similar discrete optional stopping), right-continuity of paths, uniform integrability of {condExp} family
   (Integrable.uniformIntegrable_condExp), Vitali / tendsto_Lp_finite_of_tendstoInMeasure to pass to the limit.
2. IsContLocalMartingale is closed under addition and scalar multiplication (needs a common localising sequence: min of
   two localisers, plus 1. to show the stopped-at-min processes are martingales); also smul, neg, sub:
     theorem IsContLocalMartingale.add (hM : IsContLocalMartingale ℱ M P) (hN : IsContLocalMartingale ℱ N P)
         (hMc : ∀ ω, Continuous (M · ω)) (hNc : ∀ ω, Continuous (N · ω)) : IsContLocalMartingale ℱ (M + N) P
   (drop the everywhere-continuity hypotheses if not needed).
3. Continuity transfer: if IsDiffusionSolution ℱ α β X P (a.s. continuous paths), there is X' indistinguishable from X
   (∀ᵐ ω, ∀ t, X' t ω = X t ω) with ∀ ω continuous paths and IsDiffusionSolution ℱ' α β X' P for the filtration
   ℱ' t = ℱ t ⊔ (measurable P-null sets) — compare the completed-filtration clause of
   ComplexSLE/External/LevyCharacterization.lean. If the filtration change is a problem, find the honest weakest form and
   report it.
Definitions: ComplexSLE/Frozen/Defs/{PathIntegral,IsContLocalMartingale,IsDiffusionSolution}.lean.
Allowed inputs: Mathlib; sealed defs; no Externals unless genuinely necessary (report if so — prefer PROVED). The
existing `IsContLocalMartingale.stopped_min` uses the timeChange external; if 1. makes that unnecessary, add an
external-free version.
Ownership: new files under ComplexSLE/Infrastructure/Stochastic/ only.
Checks: lake build of your modules; `python3 -I tools/leanprobe.py externals <module> <decl>` per main theorem (target
PROVED); `tools/check.sh --quick`. Don't run full tools/check.sh. Budget ~4 hours; land what is proved.

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

Handoff: files changed; exact statements; approach; commands and outputs; externals status; anything unproved.
