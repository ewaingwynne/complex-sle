# M7 / B2 — joint measurability of the hull events in (driver path, point) (prover brief, Sonnet)

Goal (INTERNAL lemmas, new files ComplexSLE/Internal/Phases/EventMeas*.lean): discharge `MeasurableEvents`
(ComplexSLE/Internal/Phases/AllZEvents.lean — read its exact definition) for the event families the §3 roots need:
 (a) E u z := absorbingTime u z < ⊤ (and = ⊤),
 (b) E u z := ∀ ε > 0, ∃ t < T_z, infDist z (leftHull u t) < ε, and its negation-type form ∃ ε > 0, ∀ t < T_z, ε ≤ infDist …
     (the R14 ε-forms used by the frozen Prop 3.2 anchors — read ComplexSLE/Frozen/Proposition_3_2_{A,B}.lean, read-only),
 (c) E u z := z ∉ closure (⋃ t, leftHull u t) and the swallowing/hitting predicates as they appear in
     ComplexSLE/Frozen/Defs/{IsThinPhase,IsSwallowingPhase,IsHittingPhase,IsDensePhase}.lean, as far as they are needed.
Key fact: (path, z) ↦ T_z(path) is lower semicontinuous on (continuous paths with the topology of locally uniform
convergence) × ℂ — combine the driver stability (Internal/Polar/Stability.lean exists_stability) with the initial-point
perturbation (Internal/Polar/PolarDerivShift.lean exists_lipschitz_initial: perturbing z is perturbing the driver by a
constant). Then relate the product σ-algebra on ℝ≥0 → ℂ restricted to continuous paths to the Borel σ-algebra of the
locally-uniform topology (continuous paths are determined by rational times; a lower semicontinuous function of countably
many coordinates in the sup norm on compacts is measurable — e.g. {T_z > t} is open, hence a countable union of basic sets
determined by finitely many rational-time values). infDist z (leftHull u t) is handled via {w : T_w ≤ t} closed and
countable dense sets.
Allowed inputs: Mathlib; sealed defs; Internal lemmas. No externals (target PROVED).
Ownership: new files ComplexSLE/Internal/Phases/EventMeas*.lean only. Another Sonnet works on Polar/PolarRestart*.lean.
Checks: lake build of your modules; leanprobe externals; tools/check.sh --quick. Budget ~3 hours; land what is proved.

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
