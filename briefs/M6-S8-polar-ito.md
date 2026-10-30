# M6 / S8 — polar decomposition, probabilistic stratum: Itô step, Remark 2.12, time change (prover brief, Fable, HARD)

Goal: finish Lemma 2.11 (source/arxiv-2203.07313v4/complex-sle-final.tex L831-935) as INTERNAL lemmas in martingale form
(ERRATA R24). What exists (read first; all sorry-free, committed):
- ComplexSLE/Internal/Polar/{Path,Argument,Sigma}.lean — deterministic: lifeSet U z = [0,T_z), solPath/fPath (f_t(z)),
  exitTime n (annulus exits, τ_n → T_z), clock A(t) = ∫₀ᵗ|f|⁻², sigmaTime/sigmaDom/clockSup (Def 2.9), argPath θ_t (Def 2.10),
  fPath = |f| e^{iθ}, exists_norm_fPath_lt (liminf |f| = 0 at finite T_z), clockSup_eq_top_of_norm_le.
- ComplexSLE/Internal/Polar/{Stability,PathSpace,Measurability,ExitTimes,Riemann,ClockArg,DriverMeasurability}.lean —
  measurability: T_z and exitTime n are ℱ-stopping times; fPath, solPath, clock, argPath at fixed t are ℱ t-measurable
  (… _of_isSLEDriverAdapted wrappers).
- ComplexSLE/Internal/Polar/DriverBridge.lean — for hU : IsSLEDriverAdapted a b c U P ℱ: Re U, Im U, (Re U)²−a t, (Im U)²−b t,
  Re U·Im U − c t are ℱ-martingales and IsContLocalMartingale.
- ComplexSLE/Infrastructure/Stochastic/{ContinuousOptionalStopping,LocalMartingaleAlgebra,ContinuousModification}.lean —
  optional stopping for continuous martingales, add/sub/smul of continuous local martingales, external-free
  stopped_min_of_continuous, continuous versions under completed filtrations. (StoppedLocalMartingale.lean has an older
  PROVED_REL version; prefer the PROVED ones.)
Remaining items (from the previous prover's precise plan):
1. Itô step (graph step:polar-ito-log, step:polar-real-imag): X = (Re f, Im f) stopped at τ_n; apply EXTERNAL
   ComplexSLE.External.ito_formula with F = ½ log(x₀² + x₁²) on the annulus to get N^n_t = log|f_{t∧τ_n}| − log|f_0| −
   ∫₀^{t∧τ_n} ν(θ)|f|⁻² as a continuous local martingale, and brackets via F²-type functions; for θ (no global C² function:
   winding) apply Itô to Arg(w₁/w₂) between successive sector exit times and sum (sums now available).
2. Remark 2.12 (remark-sigma): a.s. clockSup = ⊤ (σ_z maps [0,∞) onto [0,T_z)), via the L² argument in the original time.
3. Time change: with σ_s the inverse clock and 𝒢_s = ℱ_{σ_s}, θ̂_s = θ_{σ_s}, ρ̂_s = log|f_{σ_s}|, prove
   IsDiffusionSolution 𝒢 (mu a b c) (fun u => √(2 * diffusionD a b c u)) θ̂ P (check the β² convention: bracket
   2D(θ̂) = a sin²θ̂ + b cos²θ̂ − 2c sinθ̂ cosθ̂, eqn-theta-t L870-875) and the ρ̂ analogue with drift ν(θ̂) and the cross
   bracket. Use EXTERNAL timeChange_isContLocalMartingale with σ^n_s = τ_n ∧ σ_s. Junk off sigmaDom is a null event by 2.
State the final results in the form Thm 1.8 / Props 3.1–3.2 will consume (read DEPGRAPH.md nodes lem-polar, prop-i.*, prop-ii.*
and their steps briefly) — at least the θ̂ diffusion statement and the ρ̂ = log|f̂| decomposition.
Allowed inputs: Mathlib; sealed defs and anchors; Internal/Infrastructure lemmas; EXTERNALs ito_formula,
timeChange_isContLocalMartingale (and levy_characterization only if genuinely needed). No DRAFT anchor or provider.
Ownership: new files under ComplexSLE/Internal/Polar/ (prefix them PolarIto*, PolarTime*, …; do not edit existing Polar
files) and new helpers under ComplexSLE/Infrastructure/Stochastic/. Another prover works under ComplexSLE/Internal/Recurrence/.
Checks: lake build of your modules; `python3 -I tools/leanprobe.py externals <module> <decl>` per main theorem;
`tools/check.sh --quick`. Don't run full tools/check.sh. Stop condition: if an external is too weak for a use, STOP that
part and report the exact statement you'd need. Budget ~5 hours; land what is proved, report the rest precisely.

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

Handoff: files changed; exact statements of main lemmas; approach; commands and outputs; externals status; anything
unproved (precise statements).
