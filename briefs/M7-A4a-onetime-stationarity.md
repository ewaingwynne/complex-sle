# M7 / A4a — one-time stationarity of θ̂(𝐳) on the product space (prover brief, Sonnet)

Goal (INTERNAL lemma, new files ComplexSLE/Internal/Stationary/SLEStat*.lean): for a, b > 0, c² ≤ ab, an adapted driver
hU : IsSLEDriverAdapted a b c U P ℱ (Ω : Type), an admissible density p (IsAdmissibleDensity a b c p) and the probability
measure ν := p(u) 1_{[0,2π]}(u) du on ℝ, prove that for every s : ℝ≥0 the law of (ω, u) ↦ e^{2iθ̂_s(e^{iu})(ω)} under P.prod ν
equals the law of u ↦ e^{2iu} under ν (and the AddCircle π version: θ̂_s mod π has law (p du on [0,2π]) mod π).
Ingredients:
- θ̂ (thetaHat, Polar/PolarThetaHat.lean) from a point start is an IsDiffusionSolution (isDiffusionSolution_thetaHat) with
  α = mu a b c, β = √(2D); its start θ̂_0(e^{iu}) = argPath at 0 ∈ [0, 2π) equals u for u ∈ [0, 2π) — check (Polar/Argument.lean:
  argPath_zero_mem_Ico, fPath_eq_norm_mul_exp; with U 0 = 0 the start is e^{iu} itself).
- Point-start law: the law_eq clause of EXTERNAL hormander_oneDim (ComplexSLE/External/HormanderOneDim.lean) for these
  coefficients (hypotheses discharged via Stationary/Coefficients.lean: smoothness — careful, √(2D) is smooth only when
  c² < ab; in the critical case use betaCrit (signed root, β² = 2D) and note IsDiffusionSolution depends on β only through
  β², so restate isDiffusionSolution_thetaHat for betaCrit if needed).
- Kernel invariance: Stationary/KernelLaw.lean map_exp_transition_eq / map_addCircle_transition_eq with an
  IsDiffusionKernel (KernelBasic.lean). Its fields markov and equivariant are the conclusions of the PENDING external
  markov_oneDim (review/approvals/drafts/MarkovOneDim.lean.txt): take them as explicit hypotheses of your lemma (do not
  import or assume the external). exists_solution comes from isDiffusionSolution_thetaHat with z = e^{iu} (on Ω : Type).
- Fubini: joint measurability from Polar/PolarContMeas.lean (measurable_exp_thetaHat_unit etc.), Measure.prod, integral over
  the product of a bounded measurable test function = ∫ (∫ … dP) dν.
- The IsKolmogorovDensity of 2p (bridge IsAdmissibleDensity.isKolmogorovDensity, Stationary/KolmogorovDensity.lean; note the
  normalisation ∫₀^π vs ∫₀^{2π} and the factor 2, ruling R9).
Allowed inputs: Mathlib; sealed defs; Internal/Infrastructure lemmas; EXTERNALs hormander_oneDim, ito_formula, timeChange
(upstream). Ownership: new files ComplexSLE/Internal/Stationary/SLEStat*.lean only. Another Sonnet works on
ComplexSLE/Internal/Phases/AllZ*.lean. Checks: lake build of your modules; leanprobe externals; tools/check.sh --quick.
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
