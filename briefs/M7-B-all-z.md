# M7 / B — Lemma 3.3 (lem-all-z): from the random point 𝐳 to every z (prover brief, Sonnet)

Source: source/arxiv-2203.07313v4/complex-sle-final.tex L1294-1325. Goal (INTERNAL lemmas, new files
ComplexSLE/Internal/Phases/AllZ*.lean):
1. Positivity of admissible densities (open ERRATA modeling item "an admissible p vanishes only on a null set"): for a, b > 0,
   c² ≤ ab and IsAdmissibleDensity a b c p (Frozen/Defs/IsAdmissibleDensity.lean), p u > 0 for every u off the lattice
   x + πℤ of the definition (in particular off a null set). Route: IsAdmissibleDensity.exists_hasDerivAt
   (Internal/Phases/C0Density.lean, valid for all (a,b,c)) gives (Dp)' = J + µp; at a zero u₀ of p with D(u₀) > 0, u₀ is a
   minimum so p'(u₀) = 0 and J = 0; then the linear ODE (Dp)' = µp with Dp(u₀) = 0 forces p ≡ 0 on the component of {D > 0},
   which is all of ℝ mod π (D > 0 off x + πℤ: Internal/Density/Basic.lean, Stationary/Coefficients.lean), contradicting
   ∫ p = 1. (For c² < ab, D > 0 everywhere.)
2. Lemma 3.3 in the following form (proposed route, simpler than the paper's stopping-time choice, which is one-sided in the
   critical case): an event family E(z), formalised as a predicate on (driver path, point), with (i) scale invariance and
   (ii) future dependence exactly as in the source (state them pathwise for continuous drivers, using
   Internal/Loewner/Transform.lean scaling and Internal/Loewner/Concatenation.lean), and P(E(𝐳)) = 1 for the random point of
   the product extension (Internal/Driver/Bridge*.lean, ν = law of arg 𝐳 with density p 1_{[0,2π]}). Conclude P(E(z)) = 1 for
   every z ≠ 0. Proof: Λ := {u : P(E(e^{iu})) = 1} is conull for p du, hence Lebesgue-conull on [0,2π] by 1. Fix t̃ > 0 and
   τ = σ_z(t̃) (an ℱ-stopping time — Polar/PolarTimeSigma.lean / sigmaTop). By (ii), scaling (i) and the strong Markov
   property at τ (EXTERNAL strongMarkov_sleDriver, ComplexSLE/External/StrongMarkovSLEDriver.lean, applied to the adapted
   driver from Bridge*), P(E(z)) = E[ P(E(e^{iθ_τ}) ) ] (state the precise conditional form you need). θ̂_{t̃}(z) has a density
   (law_eq clause of EXTERNAL hormander_oneDim for the diffusion θ̂ from a point start, Polar/PolarThetaHat.lean
   isDiffusionSolution_thetaHat; coefficients mu, √(2D) satisfy its hypotheses by Stationary/Coefficients.lean — check the
   Hörmander condition holds in both cases), so e^{iθ̂_{t̃}} ∈ Λ a.s. and P(E(z)) = 1.
   If the strong Markov step needs a joint-measurability fact in z (z ↦ P(E(z))), state it; a concurrent prover is proving
   continuity of θ̂_s(z) in z (Polar/PolarCont*.lean, in progress — do not edit, you may import once committed).
Allowed inputs: Mathlib; sealed defs/anchors; Internal/Infrastructure lemmas; EXTERNALs strongMarkov_sleDriver,
hormander_oneDim (and ito_formula/timeChange upstream). Report which externals each main theorem uses.
Ownership: new files ComplexSLE/Internal/Phases/AllZ*.lean only. Checks: lake build of your modules; leanprobe externals;
tools/check.sh --quick. If the step "P(E(z)) = E[P(E(e^{iθ_τ}))]" turns out to need substantially more than the strong
Markov external plus deterministic identities, STOP after part 1 and the deterministic identities and report precisely.
Budget ~4 hours.

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
