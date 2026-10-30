# M4 / D1b — scaling (2.1) and reflection (2.2) for left hulls (prover brief)

Goal: prove two provider theorems, each with EXACTLY the type of its frozen anchor (read-only):
- `ComplexSLE.Internal.scaling_leftHull` for `ComplexSLE.scaling_leftHull` (ComplexSLE/Frozen/Scaling_LeftHull.lean):
      theorem scaling_leftHull (U : ℝ≥0 → ℂ) (hU : Continuous U) (r : ℝ≥0) (hr : 0 < r) (t : ℝ≥0) :
          leftHull (fun s => (r : ℂ) * U (s / r ^ 2)) t = (fun z => (r : ℂ) * z) '' leftHull U (t / r ^ 2)
- `ComplexSLE.Internal.reflection_leftHull` for `ComplexSLE.reflection_leftHull` (ComplexSLE/Frozen/Reflection_LeftHull.lean):
      theorem reflection_leftHull (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) :
          leftHull (fun s => conj (U s)) t = conj '' leftHull U t ∧
            leftHull (fun s => -U s) t = Neg.neg '' leftHull U t
(Check the exact `open`s / notation in each frozen file so that your statement elaborates identically.)

Definitions (sealed): ComplexSLE/Frozen/Defs/{IsLoewnerSolution,AbsorbingTime,LeftHull}.lean. Source: paper.tex:L549-557.
Allowed inputs: Mathlib; the sealed definitions; the SEALED, PROVED anchor `ComplexSLE.loewner_wellDefined`
(module ComplexSLE.Frozen.LoewnerWellDefined) and the public helpers in ComplexSLE.Internal.LoewnerWellDefined
(e.g. isLoewnerSolution_mono). Do not import any DRAFT_SORRY anchor or its provider (see manifest).

Ownership: ComplexSLE/Internal/Scaling_LeftHull.lean and ComplexSLE/Internal/Reflection_LeftHull.lean (providers;
keep header/docstring), new shared files under ComplexSLE/Internal/Loewner/ (e.g. Transform.lean). No other edits.

Suggested route: the whole point is that solutions transform. Show
(a) γ solves for (U, z, τ) ⇒ t ↦ r·γ(t/r²) solves for (r·U(·/r²), r z, r²τ), and the converse (apply with 1/r);
    hence absorbingTime (rU(·/r²)) (r z) = r² · absorbingTime U z;
(b) γ solves for (U,z,τ) ⇒ conj ∘ γ solves for (conj ∘ U, conj z, τ) (conj is ℝ-linear; derivative of conj ∘ γ is
    conj γ'; 2/conj w = conj(2/w)), and likewise −γ for −U; involutions give equality of absorbing times;
then unfold leftHull. Watch the time carrier: U is read at t.toNNReal, γ is ℝ-indexed, τ ∈ ℝ≥0∞; you need
(t/r²).toNNReal = t.toNNReal / r² and the ℝ≥0∞ arithmetic for r²·τ. Note that 0 < r is a source premise.

Checks (run them, paste output):
- `lake build ComplexSLE.Internal.Scaling_LeftHull ComplexSLE.Internal.Reflection_LeftHull`
- exact-type probes in .lake/probes/ (module; import provider + Defs.LeftHull, same opens as the frozen file) with
  `example : <frozen statement verbatim as a ∀-type> := ComplexSLE.Internal.<name>`; `lake env lean <probe>`; delete afterwards.
- `python3 -I tools/leanprobe.py axioms <module> <decl>` for both exports.
- `tools/check.sh --quick`

Stop condition: if a frozen statement looks false (e.g. a carrier/normalisation mismatch in s / r ^ 2 or t / r ^ 2),
STOP and report precisely. Budget ~3 hours.

Concurrency: a Fable prover is working in ComplexSLE/Internal/Density/ and ComplexSLE/Internal/Lemma_2_13_Exists.lean;
don't touch those; don't run a full `lake build` or `tools/check.sh` without --quick.

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
