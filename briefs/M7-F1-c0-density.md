# M7 / F1 — c = 0: explicit stationary density and the sign of the phase integrals (prover brief)

Goal (INTERNAL lemmas, new files under ComplexSLE/Internal/Phases/C0*.lean): the deterministic part of Lemma 3.11
(lem-c0-phases, source/arxiv-2203.07313v4/complex-sle-final.tex L1824-1910):
1. Uniqueness: for a, b > 0 and c = 0, every p with ComplexSLE.IsAdmissibleDensity a b 0 p
   (ComplexSLE/Frozen/Defs/IsAdmissibleDensity.lean; R7: every admissible p) equals the explicit density (3.30):
   p(u) = Z⁻¹ (a + b + (b − a) cos 2u)^{4/(b−a)} if a ≠ b, Z⁻¹ exp((4/a) cos² u) if a = b, with Z normalising ∫₀^{2π} p = 1.
   (Route: D > 0 when c² < ab, so Dp is C¹ and the ODE −µp + (Dp)' = J holds on ℝ with a constant J, using the
   ContDiff ℝ 1 (D·p) clause and continuity across the lattice x + πℤ; π-periodicity plus positivity force J = 0 for c = 0 —
   or more generally show the periodic solution space is one-dimensional; then solve (Dp)' = µp explicitly. Check the
   exponents yourself — the paper's formula is to be verified, and if it is wrong report the correct one.)
   Existing related facts: ComplexSLE/Internal/Density/{Basic,Regular}.lean (the Case-1 construction q = e^Φ∫e^{−Φ}),
   ComplexSLE/Internal/Stationary/KolmogorovDensity.lean.
2. Sign: ∫₀^{2π} cos(2u) p(u) du > 0 for every such p (eqn-c0-phase-show, via π-periodicity, the symmetry u ↦ π − u and
   the reflection across π/4, eqn-cos-reflect, three cases a < b, a > b, a = b).
3. Closed forms: with ν(u) = (2 − a/2 + b/2) cos 2u for c = 0 (ComplexSLE/Frozen/Defs/Nu.lean), integralI a b 0 p =
   (2 − a/2 + b/2) ∫cos(2u)p and integralII a b 0 p = (4 − a/2 + b/2) ∫cos(2u)p (ComplexSLE/Frozen/Defs/{IntegralI,IntegralII}.lean),
   hence: 0 ≤ integralI ↔ a − b ≤ 4, 0 < integralII ↔ a − b < 8, integralI < 0 ↔ 4 < a − b, integralII < 0 ↔ 8 < a − b,
   integralII = 0 ↔ a − b = 8 — exactly the case split consumed by the frozen anchors
   ComplexSLE/Frozen/Theorem_1_8.lean and Theorem_1_8_CZero.lean (read both, read-only).
Allowed inputs: Mathlib; sealed defs; Internal lemmas. No externals (target PROVED).
Ownership: new files under ComplexSLE/Internal/Phases/ only.
Checks: lake build; `python3 -I tools/leanprobe.py externals <module> <decl>`; `tools/check.sh --quick`. Don't run full
tools/check.sh (a Fable prover is building under ComplexSLE/Internal/Polar/). Budget ~4 hours.

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

Handoff: files changed; exact statements; approach (incl. verification of (3.30)); commands and outputs; externals; anything unproved.
