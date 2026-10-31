# M6 / S13 — θ bracket, cross bracket, and the time change: θ̂ is a diffusion (prover brief, Fable, HARD)

Goal (INTERNAL lemmas) — finish Lemma 2.11 for θ:
1. Bracket: (Θⁿ)² − ∫₀^{t∧τ_n} (a sin²θ + b cos²θ − 2c sinθ cosθ)|f|⁻² is a continuous local martingale (Θⁿ = thetaMart,
   Polar/PolarThetaMart.lean); cross term Θⁿ Nⁿ − ∫₀^{t∧τ_n} (cross density)|f|⁻² likewise (Nⁿ = logMart, PolarItoLog.lean;
   derive the cross density from eqn-theta-t / eqn-abs-zt, source L870-885: with Re-part coefficients (√a cos, √b sin) and
   θ-coefficients (−√a sin, √b cos) and correlation c/√(ab), the cross density is (b − a) sinθ cosθ + c(cos²θ − sin²θ)).
   The previous prover's plan: per sector, E1 (ito_formula) with an augmented state and F = (argProd − d)² (resp. a 6-dim state
   for the cross term); mixed terms are "bounded ℱ_ρ-measurable multiplier × post-ρ increment", handled by
   IsContLocalMartingale.mul_sub_min (PolarThetaMultiplier.lean); then the telescoping/localisation of PolarThetaMart.lean.
2. Time change for θ: apply the generic σ-time layer (Polar/PolarTimeChange.lean: isContLocalMartingale_comp_sigmaStop',
   isContLocalMartingale_sigma_of_stopped; PolarTimeSigma.lean: pathIntegral_sigmaStop_eq) exactly as for log|f|
   (isContLocalMartingale_sigmaLogMart / …Sq) to get, in 𝒢 = sigmaFiltration hU z, θ̂_s − θ̂_0 − ∫₀ˢ µ(θ̂) and its square minus
   ∫₀ˢ 2D(θ̂) as continuous 𝒢-local martingales, plus the time-changed cross term.
3. Conclude `ComplexSLE.IsDiffusionSolution (sigmaFiltration hU z) (mu a b c) (fun u => √(2 * diffusionD a b c u)) θ̂ P`
   for the honest θ̂ (θ̂_s := argPath at sigmaTime s on sigmaDom, junk only on the null set where sigmaDom ≠ Ici 0 —
   check how IsDiffusionSolution (Frozen/Defs/IsDiffusionSolution.lean) wants X off a null set; use
   IsDiffusionSolution-compatible modifications, Infrastructure/Stochastic/ContinuousModification.lean, if needed) — and
   record the bracket identity 2D(u) = a sin²u + b cos²u − 2c sin u cos u (diffusionD def). Also state the joint
   (θ̂, log|f̂|) decomposition (drifts µ, ν; brackets 2D, Γ̂ = a cos² + b sin² + 2c sin cos; cross bracket) that Lemma 3.3
   (lem-stationary-sde) will consume.
Read first: ComplexSLE/Internal/Polar/{PolarTheta*,PolarIto*,PolarTime*,PolarSigmaTop,PolarDerivSigma}.lean and the
Infrastructure/Stochastic files.
Allowed inputs: Mathlib; sealed defs/anchors; Internal/Infrastructure lemmas; EXTERNALs ito_formula, timeChange_isContLocalMartingale.
Use Ω : Type in consumer sections.
Ownership: new files under ComplexSLE/Internal/Polar/ prefixed PolarThetaBr*, PolarThetaHat*. Don't edit existing files. A
Sonnet prover works concurrently under ComplexSLE/Internal/Hull/ (suffix NoExt).
Checks: lake build; `python3 -I tools/leanprobe.py externals <module> <decl>`; `tools/check.sh --quick`. Don't run full
check.sh. Budget ~5 hours; land what is proved, report the rest precisely.

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
