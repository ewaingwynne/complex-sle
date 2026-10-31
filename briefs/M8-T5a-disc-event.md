# M8 / T5a — The disconnection event: definition, measurability, openness, scaling, restart (prover brief, Sonnet)

Context: arXiv:2203.07313v4 §4, proof of Theorem 1.10(a) (L2199-2217) and (b) (L2220-2224); orchestrator plan
review/plans/M8.md §4. The frozen anchor `ComplexSLE.theorem_1_10_a` (ComplexSLE/Frozen/Theorem_1_10_A.lean, DRAFT, read-only:
do NOT import it or its provider) concludes `∀ᵐ ω, ∃ t, 0 < t ∧ z ∉ leftHull (U · ω) t ∧ DisconnectsFromInfinity (leftHull (U · ω) t) {z}`.
This packet builds the deterministic and measurability layer for that event; the probabilistic upgrade is a later packet (T5b).
No EXTERNAL is needed.

Ownership: new files `ComplexSLE/Internal/Disconnect/DiscEvent*.lean` (namespace `ComplexSLE.Internal`). Nothing else.
Scratch only in `.lake/probes/m8-t5a/`. Another Sonnet works concurrently on `Internal/Disconnect/ZeroDriver.lean` and
`Internal/Disconnect/LineApprox*.lean`.

Available (proved, committed): `ComplexSLE/Infrastructure/Planar/*.lean` (namespace `ComplexSLE.Planar`):
`disconnectsFromInfinity_singleton_iff`, `disconnectsFromInfinity_mono`, `disconnectsFromInfinity_of_preconnected`,
`exists_ball_disconnectsFromInfinity`, `connectedComponentIn_eq_of_unbounded`, `disconnectsFromInfinity_image`,
`disconnectsFromInfinity_mul`, `disconnectsFromInfinity_conj`, `disconnectsFromInfinity_pullback` (Pullback.lean);
`ComplexSLE/Internal/Disconnect/Growth.lean`: `centeredLoewnerMap_norm_ge`, `continuous_centeredLoewnerMap`.
Sealed anchors: `concatenation_leftHull`, `scaling_leftHull`, `lemma_2_4_leftHull`. Hull facts: `isClosed_leftHull'`,
`isBounded_leftHull'` (Internal/Hull/ConnectedNoExt.lean), `leftHull_nonempty` (Internal/Hull/Basic.lean).
Measurability infrastructure: Internal/Phases/EventMeasPath.lean, EventMeasDist.lean (`measurable_infDist_leftHull` on
`ContPath × ℂ`, `measurable_restrictPath`), EventMeasEvents.lean; the event-family vocabulary `MeasurableEvents`,
`ScaleInvariantEvents` (Internal/Phases/AllZEvents.lean); how M7 proved ℱ_t-measurability of hull events for an adapted
driver (Internal/Phases/Prop32BUpZeroOne.lean `measurableSet_hitSetN`, Prop32BUpEvents.lean, EventMeasEvents.lean).

Deliverables (adjust inessential details; keep at least this strength; report final statements):

1. Definitions:
   `DiscAt (u : ℝ≥0 → ℂ) (z : ℂ) (t : ℝ≥0) : Prop := z ∉ leftHull u t ∧ DisconnectsFromInfinity (leftHull u t) {z}`;
   `Disc (u : ℝ≥0 → ℂ) (z : ℂ) : Prop := ∃ t : ℝ≥0, 0 < t ∧ DiscAt u z t` (literally the frozen 1.10(a) event);
   `BallDiscAt u c r t : Prop := Disjoint (ball c r) (leftHull u t) ∧ DisconnectsFromInfinity (leftHull u t) (ball c r)`.
2. Monotonicity/rational times (continuous u): `DiscAt u z t → t ≤ t' → z ∉ leftHull u t' → DiscAt u z t'`;
   `Disc u z ↔ ∃ q : ℚ, 0 < q ∧ DiscAt u z q.toNNReal` (pick a rational time in (t, T_z)).
   Also `BallDiscAt u c r t ↔ r ≤ infDist c (leftHull u t) ∧ DiscAt u c t` for r > 0 (ball is connected; use
   `disconnectsFromInfinity_of_preconnected`), and `BallDiscAt` is monotone in t.
3. Openness (continuous u): `IsOpen {z | DiscAt u z t}` (from `exists_ball_disconnectsFromInfinity` and closedness of `L_t`);
   hence `IsOpen {z | Disc u z}`.
4. **Measurability (main work).** `MeasurableEvents Disc` and, for each `t`, a measurable `M_t ⊆ ContPath × ℂ` (or
   `(ℝ≥0 → ℂ) × ℂ`) with `DiscAt u z t ↔ (u, z) ∈ M_t` for continuous u, depending on `u` only through `restrictPath t u`.
   Consequence to deliver: for an adapted driver (`IsSLEDriverAdapted a b c U P ℱ`), every `z` and `t`,
   `MeasurableSet[ℱ t] {ω | DiscAt (U · ω) z t}` and `MeasurableSet[ℱ t] {ω | BallDiscAt (U · ω) c r t}`.
   Countable criterion (blueprint): for compact `K` and `z ∉ K`, `z` is in a bounded component of `Kᶜ` iff
   `∃ c ∈ ℚ[i], ∃ r ∈ ℚ>0, ‖z - c‖ < r ∧ r < infDist c K ∧ ∃ R : ℕ, ∀ rational polygonal path c = v₀, v₁, …, v_m
   (vertices in ℚ[i]) all of whose segments avoid `K`, every `‖v_j‖ ≤ R`` — because the component of `c` in the open
   set `Kᶜ` is the closure-in-`Kᶜ` of the rational points reachable by such paths (open connected subsets of ℂ are
   connected by polygonal paths with rational interior vertices: the reachable set is clopen). "Segment `[v, v']` avoids
   `K`" ⟺ `∃ m : ℕ, ∀ s ∈ ℚ ∩ [0,1], 1/(m+1) ≤ infDist (v + s (v' - v)) K` (K closed, infDist continuous). With
   `K = leftHull u t`, each atom is measurable by `measurable_infDist_leftHull`; the conditions on `z` are open.
   (If a simpler correct criterion is available in Mathlib or the repo, use it.)
5. Scale invariance: `ScaleInvariantEvents Disc` (from `scaling_leftHull` and `disconnectsFromInfinity_mul`).
6. **Restart (one direction)**: for continuous `u`, `s : ℝ≥0`, `z ∉ leftHull u s`:
   `Disc (fun r => u (r + s) - u s) (centeredLoewnerMap u hu s ⟨z, hz⟩) → Disc u z`
   (time `s + t'` works: `concatenation_leftHull` writes `L_{t'+s}` as `L_s ∪ {pullback}`; `z ∉` it; disconnection by
   `disconnectsFromInfinity_pullback` with F = f_s, R = R_s, L' = the restarted hull, from mono R_s ∪ L' ⊇ L').
   (The converse is false in general, so `Disc` is NOT a `FutureDependentEvents`; do not try to prove that.)

Checks: `lake build ComplexSLE.Internal.Disconnect.DiscEvent` (and each file); `tools/check.sh --quick`; `#print axioms`
for every public theorem (expect propext, Classical.choice, Quot.sound only). Budget ~4 hours; priorities: 1, 2, 3, 5, 6
first (quick), then 4. Land what is proved; report the rest precisely.

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
11. Do not spawn subagents, forks or parallel workers of your own (the orchestrator enforces a two-agent cap).

Handoff: files changed; exact statements; approach; commands and outputs; axioms; anything unproved.
