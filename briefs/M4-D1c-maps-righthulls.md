# M4 / D1c — scaling and reflection for f_t and right hulls (prover brief)

Goal: prove four provider theorems, each with EXACTLY the type of its frozen anchor (read-only; copy statements
verbatim, including the `(by fun_prop)` continuity terms and the `open scoped NNReal ComplexConjugate`):
- `ComplexSLE.Internal.scaling_centeredLoewnerMap`  ← ComplexSLE/Frozen/Scaling_CenteredLoewnerMap.lean
- `ComplexSLE.Internal.scaling_rightHull`           ← ComplexSLE/Frozen/Scaling_RightHull.lean
- `ComplexSLE.Internal.reflection_rightHull`        ← ComplexSLE/Frozen/Reflection_RightHull.lean
- `ComplexSLE.Internal.reflection_centeredLoewnerMap` ← ComplexSLE/Frozen/Reflection_CenteredLoewnerMap.lean
Do NOT touch ComplexSLE/Frozen/Lemma_2_4_RightHull.lean or its provider (out of scope).

Source: paper.tex:L549-557 (source/arxiv-2203.07313v4/complex-sle-final.tex). Rulings: ERRATA.md R16, R21, R22.
Allowed inputs: Mathlib; sealed definitions ComplexSLE/Frozen/Defs/*; the SEALED PROVED anchors
`ComplexSLE.loewnerMap_eq` (ComplexSLE.Frozen.LoewnerMap_Eq), `ComplexSLE.loewnerMap_exists_solution`
(ComplexSLE.Frozen.LoewnerMap_ExistsSolution), `ComplexSLE.scaling_leftHull`, `ComplexSLE.reflection_leftHull`,
`ComplexSLE.loewner_wellDefined`; and the public lemmas in ComplexSLE/Internal/Loewner/Transform.lean
(isLoewnerSolution_scale/conj/neg, absorbingTime_*, leftHull_*). Do not import any DRAFT_SORRY anchor or its provider.
Use the characterization theorems; never unfold `loewnerMap`'s `Classical.choose`.

Ownership: the four provider files ComplexSLE/Internal/{Scaling_CenteredLoewnerMap,Scaling_RightHull,Reflection_RightHull,
Reflection_CenteredLoewnerMap}.lean (keep header/docstring; add `public import`s, `public section`, namespace
ComplexSLE.Internal) and new files under ComplexSLE/Internal/Loewner/ (e.g. MapTransform.lean). You may ADD lemmas
to ComplexSLE/Internal/Loewner/Transform.lean but not change existing statements. No other edits.

Route: map identities — take the solution γ from loewnerMap_exists_solution for (U, z/r) (resp. conj z, −z),
transform it with isLoewnerSolution_scale/conj/neg into a solution for the transformed driver from z on the
transformed interval, then loewnerMap_eq for the transformed driver at time t (check t < r²·T_{z/r} from hz').
Right hulls: R_t = (range f_t)ᶜ, so the map identities plus the left-hull identities (bijection of domains
ℂ∖L) give the set equalities; for scaling, use z ↦ r z / z ↦ z / r as mutually inverse on the domains.
Mind the subtype proofs: you will need to produce membership proofs for transformed points (from scaling_leftHull /
reflection_leftHull or the Transform lemmas) — proof irrelevance makes any proof fine.

Checks (paste output): `lake build` of the four provider modules; an exact-type probe in .lake/probes/ per theorem
(`example : <frozen statement as ∀-type> := ComplexSLE.Internal.<name>`, compiled with `lake env lean`, then deleted);
`python3 -I tools/leanprobe.py axioms <module> <decl>` for all four; `tools/check.sh --quick`.
Stop condition: if a frozen statement looks false, STOP and report precisely. Budget ~3 hours.

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
