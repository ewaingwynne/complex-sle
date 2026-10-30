# M6 / S0 — existence of an SLE_Σ driver (prover brief)

Goal: prove `ComplexSLE.Internal.exists_sleDriver` with EXACTLY the type of the frozen anchor
`ComplexSLE.exists_sleDriver` (ComplexSLE/Frozen/ExistsSLEDriver.lean, read-only; ERRATA R13):

    theorem exists_sleDriver (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b) :
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
          (U : ℝ≥0 → Ω → ℂ), IsSLEDriver a b c U P

Definition (sealed): ComplexSLE/Frozen/Defs/IsSLEDriver.lean (a.s. continuous, U 0 = 0 a.s., HasIndepIncrements,
increments have law complexGaussian ((t − s) • covMatrix a b c)); complexGaussian is the pushforward of Mathlib's
multivariateGaussian under (x0, x1) ↦ x0 + x1·i (ComplexSLE/Frozen/Defs/ComplexGaussian.lean).

Allowed inputs: Mathlib (Probability/BrownianMotion/Basic.lean: IsBrownianReal, IsPreBrownianReal.hasIndepIncrements,
hasLaw_sub, …; Probability/Distributions/Gaussian/Multivariate.lean; product measures, independence of
product coordinates); the EXTERNAL `ComplexSLE.External.exists_isBrownianReal` (module
ComplexSLE.External.ExistsIsBrownianReal; R23). No other external; no DRAFT anchor or provider.

Suggested route: take (Ω₀, P₀, B) from the external; Ω := Ω₀ × Ω₀ with P := P₀.prod P₀ (probability, two
independent copies B₁ = B ∘ fst, B₂ = B ∘ snd); set U_t = √a·B₁_t + i·(c/√a·B₁_t + √(b − c²/a)·B₂_t)
(b − c²/a ≥ 0 by hc, ha). Then: continuity and U 0 = 0 a.s. from the components; independent increments of the
pair (B₁, B₂) (independence of the two factors + each has independent increments) transported through a linear map;
increment law: (B₁_t − B₁_s, B₂_t − B₂_s) is a standard Gaussian on ℝ² scaled by (t − s), and the linear image of a
multivariateGaussian is multivariateGaussian with covariance A S Aᵀ — find the Mathlib lemma (e.g. for
`multivariateGaussian` under a continuous linear map) and compute A Aᵀ (t−s) = (t − s)·covMatrix a b c. Plan the
Gaussian API carefully before writing; if Mathlib lacks the linear-image lemma for multivariateGaussian, prove it
(characteristic functions are in Mathlib) as an Infrastructure lemma.

Ownership: ComplexSLE/Internal/ExistsSLEDriver.lean (provider; keep header/docstring), new files under
ComplexSLE/Internal/Driver/ and source-independent Gaussian facts under ComplexSLE/Infrastructure/Gaussian/.
Checks: `lake build ComplexSLE.Internal.ExistsSLEDriver`; exact-type probe in .lake/probes/ (deleted after);
`python3 -I tools/leanprobe.py externals ComplexSLE.Internal.ExistsSLEDriver ComplexSLE.Internal.exists_sleDriver`
(expected PROVED_REL{exists_isBrownianReal}); `tools/check.sh --quick`. Don't run full tools/check.sh.
Stop condition: if the frozen statement looks false, STOP and report. Budget ~4 hours.

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

Handoff: files changed; approach; exact commands and outputs; externals status for every new public theorem;
anything unproved or uncertain.
