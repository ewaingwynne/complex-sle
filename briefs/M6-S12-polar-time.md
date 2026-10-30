# M6 / S12 — polar decomposition: Remark 2.12 and the time change for log|f| (prover brief, Fable, HARD)

Goal (INTERNAL lemmas):
1. Remark 2.12 (remark-sigma, L893-900; graph SOURCE_GAP): for hU : IsSLEDriverAdapted a b c U P ℱ and z ≠ 0 (a, b > 0,
   c² ≤ ab), a.s. clockSup = ⊤, i.e. the clock A(t) = ∫₀ᵗ |f_s(z)|⁻² ds tends to ∞ as t → T_z, so σ_z maps [0, ∞) onto [0, T_z).
   Plan (previous prover): (i) exit times with a separate time cap m (new stopping-time proof, analogue of Polar/ExitTimes.lean),
   (ii) the L² bound E[(N^n_{ρ∧τ_n})²] ≤ (sup Γ)·T for ρ = σ_z(T), by optional sampling of ((N^n)² − ∫Γ) stopped along a
   localising sequence (Infrastructure/Stochastic/ContinuousOptionalStopping.lean) + Fatou, where N^n = logMart and Γ = logBracket
   (Polar/PolarItoLog.lean; Γ|f|² is bounded by a+b), (iii) Chebyshev with |log|f_τ|| ≥ log n on {clockSup < T}. The T_z = ∞
   case (DEPGRAPH note) is covered since |f| unbounded ⇒ every annulus is exited.
2. Time change for log|f|: with σ^n_s = sigmaTime (min s (clock τ_n)) (no junk), 𝒢_s = ℱ_{σ_s}, ρ̂_s = log|f_{σ_s}|, prove
   ρ̂_s − ρ̂_0 − ∫₀ˢ ν(θ̂_u) du and its square minus ∫₀ˢ (a cos²θ̂ + b sin²θ̂ + 2c sinθ̂ cosθ̂) du are continuous 𝒢-local
   martingales. Route: stopping times {σ^n_s ≤ u} = {τ_n ≤ u} ∪ ({u ∈ lifeSet} ∩ {s ≤ clock u}) (measurable_clock_…);
   continuity/monotonicity from Polar/Sigma.lean; EXTERNAL timeChange_isContLocalMartingale applied to logMart and
   logMart² − ∫logBracket (everywhere continuous: continuous_logMart); change of variables ∫₀^{σ r} ν(θ)|f|⁻² = ∫₀ʳ ν(θ̂)
   (HasDerivWithinAt version, intervalIntegral.integral_comp_mul_deriv'''-type lemmas); filtration transfer from ℱ_{τ_n∧σ_s} to
   ℱ_{σ_s} (generalise isContLocalMartingale_of_min_const in Infrastructure/Stochastic/StoppedLocalMartingale.lean to hypotheses
   𝒢' s ≤ 𝒢 s and A ∈ 𝒢 s ⇒ A ∩ {s < ρ} ∈ 𝒢' s); then n → ∞ via IsContLocalMartingale.of_stopped_seq (ProgressiveTools.lean),
   using 1. Design the θ̂ analogue's interface so the concurrent θ prover's results (files PolarTheta*: Θ^n local martingale with
   brackets, same shape as logMart) plug in by the same proof — ideally a generic lemma "time change of a stopped-integral
   decomposition" that both apply.
Read first: ComplexSLE/Internal/Polar/*.lean, ComplexSLE/Infrastructure/Stochastic/*.lean.
Allowed inputs: Mathlib; sealed defs/anchors; Internal/Infrastructure lemmas; EXTERNALs ito_formula (already upstream),
timeChange_isContLocalMartingale. Use Ω : Type in sections consuming externals.
Ownership: new files under ComplexSLE/Internal/Polar/ prefixed PolarTime* or PolarSigma*, and new helpers under
ComplexSLE/Infrastructure/Stochastic/ prefixed Time*. Another prover concurrently adds PolarTheta* files — don't touch those.
Do not edit existing files.
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
