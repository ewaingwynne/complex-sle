# M4 / D1 — Loewner well-definedness (prover brief)

Goal: prove `ComplexSLE.Internal.loewner_wellDefined` with EXACTLY the type of the frozen anchor
`ComplexSLE.loewner_wellDefined` in `ComplexSLE/Frozen/LoewnerWellDefined.lean` (read it; read-only):

    theorem loewner_wellDefined (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) :
        (∃ γ, IsLoewnerSolution U z (absorbingTime U z) γ) ∧
          ∀ (τ : ℝ≥0∞) (γ₁ γ₂ : ℝ → ℂ), IsLoewnerSolution U z τ γ₁ → IsLoewnerSolution U z τ γ₂ →
              Set.EqOn γ₁ γ₂ {t | 0 ≤ t ∧ ENNReal.ofReal t < τ}

Definitions (sealed, importable): `ComplexSLE/Frozen/Defs/IsLoewnerSolution.lean`, `ComplexSLE/Frozen/Defs/AbsorbingTime.lean`.
Source: paper.tex:L251-268 (`source/arxiv-2203.07313v4/complex-sle-final.tex`), Def 1.1.

Ownership: `ComplexSLE/Internal/LoewnerWellDefined.lean` (the provider; currently an empty module — keep its header
and docstring) plus any new files under `ComplexSLE/Internal/Loewner/` and reusable ODE facts under
`ComplexSLE/Infrastructure/ODE/`. No other edits.

Allowed inputs: Mathlib (Picard–Lindelöf: `IsPicardLindelof` and its existence theorems; Grönwall /
`ODE_solution_unique*`), the two sealed definitions above. Graph node `defn-loewner.well-defined` depends only on
`ext:picard-lindelof`, which Mathlib supplies: use Mathlib's theorems, do NOT create any External file.
No other ComplexSLE module may be imported (in particular not `ComplexSLE.Frozen.LoewnerWellDefined`).

Suggested route (yours to change):
1. Uniqueness: for t₀ with ofReal t₀ < τ, both solutions are continuous on [0,t₀] (HasDerivWithinAt ⇒ continuity
   within Ici 0), so γᵢ(t) − U(t) is bounded away from 0 on [0,t₀] by compactness; on that tube the field
   (t,w) ↦ 2/(w − U t) is Lipschitz in w uniformly in t. Apply Mathlib's ODE uniqueness on [0,t₀]
   (watch: derivative is within Ici 0; on [0,t₀] use within-Icc / right-derivative versions).
   Also handle τ = ⊤ and t₀ = 0.
2. Existence on [0, T_z): the set S = {τ | ∃ γ, IsLoewnerSolution U z τ γ} is downward closed and contains 0.
   Take τₙ ∈ S with τₙ → sSup S (or τₙ = ⊤ if ⊤ ∈ S), glue the solutions using uniqueness (they agree on overlaps),
   and check the glued γ solves on [0, sSup S). Local existence is NOT needed for this conjunct (absorbingTime
   is defined as the sup), but do not assume S has a maximum. If S = {0}, any γ with γ 0 = z works.
   Note `ENNReal.ofReal t < sSup S` ⇒ ∃ τ ∈ S, ofReal t < τ (`lt_sSup_iff`).

Checks (run them, paste output):
- `lake build ComplexSLE.Internal.LoewnerWellDefined`
- exact-type probe: a scratch file `.lake/probes/D1_probe.lean` (module, imports the provider and the two Defs)
  containing `example : <the frozen statement, verbatim, as a ∀-type> := ComplexSLE.Internal.loewner_wellDefined`;
  compile with `lake env lean .lake/probes/D1_probe.lean`; delete it afterwards.
- `python3 -I tools/leanprobe.py axioms ComplexSLE.Internal.LoewnerWellDefined ComplexSLE.Internal.loewner_wellDefined`
  (must be only propext, Classical.choice, Quot.sound).
- `tools/check.sh --quick`

Stop condition: if the frozen statement looks false or unprovable as stated (e.g. an edge case such as z = U 0,
τ = 0, or the Ici 0 derivative convention), STOP and report the exact obstruction — do not work around it.
Also stop after ~3 hours of wall time with a report of what is done.

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

Handoff: files changed; approach; exact commands and outputs; #print axioms for every new public theorem;
anything unproved or uncertain.
