# M6 / S11 — polar decomposition: Itô step for the argument θ (prover brief, Fable, HARD)

Goal (INTERNAL lemmas): the θ half of step:polar-real-imag (source/arxiv-2203.07313v4/complex-sle-final.tex L904-922) in
martingale form: with τ_n the annulus exit times, the process
  Θ^n_t = θ_{t∧τ_n} − θ_0 − ∫₀^{t∧τ_n} µ(θ_s)|f_s|⁻² ds
is a continuous ℱ-local martingale with everywhere-continuous paths, and (Θ^n)² − ∫₀^{t∧τ_n} (a sin²θ + b cos²θ − 2c sinθ cosθ)|f|⁻²
and the cross term Θ^n N^n − ∫₀^{t∧τ_n} (cross bracket)|f|⁻² (derive it from eqn-theta-t / eqn-abs-zt, L870-885) are continuous
local martingales, where N^n = logMart hU z n (ComplexSLE/Internal/Polar/PolarItoLog.lean).
The previous prover's validated plan (follow or improve): sector times S_0 = 0 < S_1 < … (S_{k+1} = first time after S_k with
|θ_t − θ_{S_k}| ≥ π/2, capped at τ_n); on [S_k, S_{k+1}] use the 4-dim state (f_{t∧S_{k+1}}, f_{t∧S_k}) with F(w, v) = Arg(w·v̄)
(smooth off {w v̄ ≤ 0}) so that F = θ_{t∧S_{k+1}} − θ_{t∧S_k}; apply EXTERNAL ito_formula; sum over k < K (sums of local
martingales: ComplexSLE/Infrastructure/Stochastic/LocalMartingaleAlgebra.lean), then IsContLocalMartingale.of_stopped_seq
(ProgressiveTools.lean) with ρ_K = S_K ∧ τ_n (S_K → ∞ by uniform continuity of θ on [0, τ_n]). Missing ingredients listed by
the previous prover: stopping-time proof for the recursive S_k (analogue of Polar/ExitTimes.lean), progressiveness of θ_{t∧S_k}
(isStronglyProgressive_of_rightContinuous + measurable_argPath), derivatives of Arg on Fin 4 → ℝ (Arg = Im ∘ log). For the
bracket and cross terms use the augmented-state trick of PolarItoLog.lean (state with an extra integral coordinate; F² type
functions) — read it closely, and the helper files PolarItoState.lean, PolarItoCalculus.lean.
Read first: ComplexSLE/Internal/Polar/*.lean (especially PolarItoLog, PolarItoState, PolarItoCalculus, Argument, ExitTimes,
ClockArg, DriverMeasurability), ComplexSLE/Infrastructure/Stochastic/*.lean.
Allowed inputs: Mathlib; sealed defs and anchors; Internal/Infrastructure lemmas; EXTERNAL ito_formula. Note: ito_formula is
stated for Ω : Type — use Ω : Type in consumer sections (a Type* section caused an isDefEq timeout).
Ownership: new files under ComplexSLE/Internal/Polar/ prefixed PolarTheta*. Another prover concurrently adds files prefixed
PolarTime* and PolarSigma* — don't touch those. Do not edit existing files.
Checks: lake build of your modules; `python3 -I tools/leanprobe.py externals <module> <decl>`; `tools/check.sh --quick`.
Don't run full tools/check.sh. Budget ~5 hours; land what is proved; report the rest precisely.

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
