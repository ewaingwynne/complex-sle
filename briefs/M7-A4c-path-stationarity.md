# M7 / A4c — path-level stationarity of the polar data started at 𝐳 (prover brief, Sonnet)

Goal (INTERNAL lemma; fills graph SOURCE_GAP step:sde-stationary-increments; new files
ComplexSLE/Internal/Stationary/PathStat*.lean): on Ω × ℝ with P.prod ν, ν = admissible law p(u)1_{[0,2π]}du
(Internal/Phases/AllZLebesgue.lean admissibleLaw or Internal/Stationary/SLEStat.lean admissibleMeasure — unify), for the adapted
driver hU : IsSLEDriverAdapted a b c U P ℱ and the random point z = e^{iu}, define the path observable
  Ξ_s(ω,u) := (e^{2iθ̂_s(z)}, (θ̂_{s+r}(z) − θ̂_s(z))_{r ≥ 0}, (log|f̂_{s+r}(z)| − log|f̂_s(z)|)_{r ≥ 0})
(as a measurable map into ℂ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) with product σ-algebras) and prove: for every s, the law of Ξ_s equals the
law of Ξ_0 (in fact show the law of (e^{iθ̂_s}·, increments) is that of Ξ_0 with the same conventions; finite-dimensional
laws suffice if that is easier — state precisely what you prove).
Route: (1) restart identity (Internal/Polar/PolarRestartSigma.lean: at T = σ_z(s) the increments of θ̂, log|f̂| after s are the
polar data of the scaled-shifted driver V started at z' = e^{iθ̂_s(z)}); (2) strong Markov at the stopping time σ_z(s)
(EXTERNAL strongMarkov_sleDriver; the conditional form already proved in Internal/Phases/AllZMarkov.lean; sigmaTop /
measurable_fHat in AllZFHat.lean / PolarTimeSigma.lean): the post-T driver is an SLE driver independent of ℱ_T, scaling
(Internal/Driver/Transform.lean IsSLEDriver.scale) keeps it an SLE driver, and the scale r = |f_T(z)| and z' are ℱ_T-measurable
— so conditionally on ℱ_T, V is an SLE driver independent of z' (path-law uniqueness: Internal/Phases/AllZDriverLaw.lean);
(3) one-time stationarity (Internal/Stationary/SLEStat.lean map_exp_thetaHat_prod_eq*: the law of e^{2iθ̂_s(z)} is that of
e^{2iu}) — note the polar increments started at z' depend on z' only through e^{2i arg z'}? CHECK: the coefficients are
π-periodic but the starting angle enters θ̂ mod 2π; decide whether the observable should use e^{iθ̂} (needs law of θ̂ mod 2π,
which is NOT given — only mod π) or e^{2iθ̂}, and whether the increment processes started at z' and at −z' have the same
law (by the symmetry U ↦ −U, which maps SLE_Σ drivers to SLE_Σ drivers and z' to −z' — Internal/Driver/Transform.lean neg,
Internal/Loewner/Transform.lean neg). Resolve this honestly and report it. (4) Joint measurability: Polar/PolarContMeas.lean.
Take the Markov external as an explicit hypothesis only where one-time stationarity needs it (MarkovOneDim from SLEStatKernel.lean).
Allowed inputs: Mathlib; sealed defs; Internal lemmas; EXTERNALs strongMarkov_sleDriver, hormander_oneDim, ito_formula,
timeChange (upstream). Ownership: new files ComplexSLE/Internal/Stationary/PathStat*.lean only. Another Sonnet works on
Phases/EventMeas*.lean. Checks: lake build of your modules; leanprobe externals; tools/check.sh --quick. Budget ~4 hours;
land what is proved and report the rest precisely.

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

Handoff: files changed; exact statements; approach (including the resolution of the mod-π vs mod-2π point); commands and
outputs; externals; anything unproved.
