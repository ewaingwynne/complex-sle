# M8 / T6 — Theorem 1.10(b) from Lemma 4.1: scaling, Blumenthal, monotonicity (prover brief, Sonnet)

Source: arXiv:2203.07313v4 proof of Theorem 1.10(b), L2220-2224. Orchestrator plan: review/plans/M8.md.

Goal (new files `ComplexSLE/Internal/Disconnect/Thm110B*.lean`, namespace `ComplexSLE.Internal`): a theorem
`theorem_1_10_b_of_lemma41` with EXACTLY the binders and conclusion of the frozen `ComplexSLE.theorem_1_10_b`
(ComplexSLE/Frozen/Theorem_1_10_B.lean — read-only; DRAFT: do NOT import it or Internal/Theorem_1_10_B.lean):
`∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → (interior {w | DisconnectsFromInfinity (leftHull (U · ω) t) {w}}).Nonempty`,
plus one extra explicit hypothesis placed after `hc` (the statement of Lemma 4.1, proved separately):
```lean
(hL41 : ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (U' : ℝ≥0 → Ω' → ℂ),
  IsSLEDriver a b c U' P' → ∃ (V : Set ℂ) (t : ℝ≥0), IsOpen V ∧ Bornology.IsBounded V ∧ V.Nonempty ∧ 0 < t ∧
    0 < P' {ω | Disjoint V (leftHull (U' · ω) t) ∧ DisconnectsFromInfinity (leftHull (U' · ω) t) V})
```

Available (committed): `ComplexSLE/Internal/Disconnect/DiscEvent*.lean` (`BallDiscAt`, `ballDiscAt_iff`, `BallDiscAt.mono`,
`measurableSet_setOf_ballDiscAt` (ℱ_t-measurable for adapted drivers), `discAtSet`, `measurableSet_discAtSet`,
`discAt_iff_mem_discAtSet`, `discAt_congr_restrictPath`, scaling `discAt_scale`); `ComplexSLE/Infrastructure/Planar/Disconnect.lean`
(`disconnectsFromInfinity_mono`, `disconnectsFromInfinity_mul`); sealed `scaling_leftHull`; `IsSLEDriver.scale`
(Internal/Driver/Transform.lean); path-law equality `IsSLEDriver.measure_path_preimage_eq` (Internal/Phases/AllZDriverLaw.lean,
used the same way in `evProb_mul`, Internal/Phases/Prop32BUpMarkov.lean); `MeasurableEvents.of_measurableSet`
(Internal/Phases/EventMeasPath.lean); `measurable_driverPath` (Internal/Polar/Measurability.lean, for any filtration to which
U is adapted, e.g. the natural one); `IsSLEDriver.exists_adapted`. EXTERNAL allowed: `blumenthal_sleDriver`
(ComplexSLE/External/BlumenthalSLEDriver.lean; it asks for approximants measurable for ⨆_{s ≤ ε} comap (U s)).

Blueprint (L2220-2224):
1. Pass to an everywhere-continuous version U' (exists_adapted; U' = U a.s.). Let G_s := {ω | ∃ c r, 0 < r ∧
   BallDiscAt (U' · ω) c r s} (equivalently with c ∈ ℚ[i], r ∈ ℚ — shrink to a rational sub-ball), measurable w.r.t. the
   natural σ-algebra σ(U'_r : r ≤ s). On G_s the ball lies in {w | DisconnectsFromInfinity (L_s) {w}}, and by monotonicity of
   hulls (L_s ⊆ L_t, `disconnectsFromInfinity_mono`) in the same set for every t ≥ s.
2. P(G_s) does not depend on s > 0: the scaled driver λ U'(·/λ²) is an SLE driver (`IsSLEDriver.scale`) whose G_s is G_{s/λ²}
   of U' (`scaling_leftHull`, `disconnectsFromInfinity_mul`); compare laws with `measure_path_preimage_eq` (express G_s as a
   measurable path set, as `evProb_mul` does). P(G_{t₀}) > 0 at the t₀ of hL41 (a rational ball inside V; outer measure ≤).
3. A_n := ⋃_{rational s ∈ (0, 1/(n+1))} G_s has P(A_n) ≥ p := P(G_1) > 0; A := ⋂_n A_n (decreasing) has P(A) ≥ p; A is
   germ-measurable (A = ⋂_{n ≥ N} A_n ∈ σ(U'_r : r ≤ 1/(N+1)) for each N), so Blumenthal gives P(A) = 1.
4. On A, for every t > 0 pick s < t with ω ∈ G_s; step 1 gives a ball inside the interior. Transfer back to U.

Ownership: new files `ComplexSLE/Internal/Disconnect/Thm110B*.lean` only; scratch in `.lake/probes/m8-t6/`. Other Sonnets work
on Internal/Disconnect/Lemma41*.lean and Thm110A*.lean (do not touch). Checks: `lake build ComplexSLE.Internal.Disconnect.Thm110B`;
`tools/check.sh --quick`; `python3 -I tools/leanprobe.py externals ComplexSLE.Internal.Disconnect.Thm110B
ComplexSLE.Internal.theorem_1_10_b_of_lemma41` (expect PROVED_REL{blumenthal_sleDriver}). Budget ~4 hours; land what is
proved, report the rest precisely.

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

Handoff: files changed; exact statements; approach; commands and outputs; externals; anything unproved.
