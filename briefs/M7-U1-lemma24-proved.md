# M7 / U1 — upgrade Lemma 2.4 from PROVED_REL{loewnerMap_conformal} to PROVED (prover brief)

Context: `ComplexSLE.lemma_2_4_leftHull` and `lemma_2_4_rightHull` are SEALED and PROVED_REL{loewnerMap_conformal}. The
provider (ComplexSLE/Internal/Hull/Connected.lean, used by ComplexSLE/Internal/Lemma_2_4_LeftHull.lean) uses the external only
for (i) openness of ℂ ∖ L_s, (ii) boundedness of L_t, (iii) holomorphy of g_s on ℂ ∖ L_s (via the external's extension G).
New in-project results now provide (i) and (iii) without the external:
`ComplexSLE.Internal.Polar.isOpen_compl_leftHull` (Polar/PolarDerivShift.lean) and
`differentiableOn_solPath_initial` (Polar/PolarDeriv.lean; the extension w ↦ solPath U hU w t agrees with loewnerMap on
ℂ ∖ L_t by `loewnerMap_eq_solPath` in Polar/Path.lean).
Goal: write a new external-free version of the core argument, e.g. `leftHull_separation_eq_empty'`, and a new provider
theorem `ComplexSLE.Internal.lemma_2_4_leftHull'` with exactly the frozen type of ComplexSLE.lemma_2_4_leftHull, plus
`lemma_2_4_rightHull'` (via the existing duality route in ComplexSLE/Internal/Lemma_2_4_RightHull.lean / Loewner/Duality.lean),
both PROVED (no externals). Prove (ii) directly: if |z| ≥ M + 1 + 2t with M = sup_{[0,t]}|U|, then |γ'| ≤ 2 keeps γ at
distance ≥ 1 from U on [0, t], so z ∉ L_t (use Hull/LocalExistence.lt_absorbingTime_of_norm_sub_ge or a direct argument).
Do NOT edit existing files: the orchestrator will repoint the providers afterwards. Ownership: new files
ComplexSLE/Internal/Hull/ConnectedNoExt.lean (and helpers under ComplexSLE/Internal/Hull/ with suffix NoExt).
Checks: lake build; `python3 -I tools/leanprobe.py externals <module> <decl>` must report PROVED for lemma_2_4_leftHull' and
lemma_2_4_rightHull'; exact-type probes against the frozen statements; `tools/check.sh --quick`. Don't run full check.sh
(a Fable prover is building under ComplexSLE/Internal/Polar/). Budget ~3 hours.

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

Handoff: files changed; exact statements; approach; commands and outputs; externals status; anything unproved.
