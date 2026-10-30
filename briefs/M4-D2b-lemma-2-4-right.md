# M4 / D2b — Lemma 2.4 for right hulls via duality (2.4) (prover brief)

Goal: prove `ComplexSLE.Internal.lemma_2_4_rightHull` with EXACTLY the type of the frozen anchor
`ComplexSLE.lemma_2_4_rightHull` (ComplexSLE/Frozen/Lemma_2_4_RightHull.lean, read-only):

    theorem lemma_2_4_rightHull (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) :
        IsConnected (rightHull U hU t)

Source: paper.tex:L658-666 ("The duality property (2.4) implies that R_t is also connected") and the duality property
(2.4) at L566-570: L_t^U = i R_t^{i(U(t) − U(t−·))} and R_t^U = i L_t^{i(U(t) − U(t−·))}. Rulings: ERRATA R16, R21, R22.
(2.4) is not a frozen anchor; prove whatever duality statement you need as an internal lemma. FIRST verify the exact
form (signs/centering of the reversed driver, behaviour of the reversed driver for times > t — the hull at time t
only depends on the driver on [0, t]) by computing the time reversal yourself: if γ solves γ' = 2/(γ − U) from z on
[0,t], set k(s) = i(γ(t−s) − U t) and find the driver V with k' = 2/(k − V). If the paper's formula has a sign error,
use the correct one and REPORT the discrepancy precisely (it becomes an ERRATA item).

Allowed inputs: Mathlib; sealed definitions ComplexSLE/Frozen/Defs/*; PROVED / PROVED_REL sealed anchors
(loewner_wellDefined, loewnerMap_eq, loewnerMap_exists_solution, scaling_*, reflection_*, lemma_2_4_leftHull);
public lemmas under ComplexSLE/Internal/Loewner/ and ComplexSLE/Internal/Hull/ (read them: Hull/LocalExistence.lean has
local existence and gluing, Hull/Basic.lean basic hull facts). The EXTERNAL `ComplexSLE.External.loewnerMap_conformal`
may be used if genuinely needed (lemma_2_4_leftHull already depends on it). No DRAFT anchor or provider.
Hint: R_t^U = (range f_t)ᶜ; w ∈ range f_t iff the reversed ODE from the corresponding point survives up to time t;
multiplication by i is a homeomorphism, so connectedness transfers from lemma_2_4_leftHull of the reversed driver
(which is continuous; you'll need a concrete continuous extension for times > t, e.g. constant).

Ownership: ComplexSLE/Internal/Lemma_2_4_RightHull.lean (provider; keep header/docstring, update the quarantine line
only if you like), new files under ComplexSLE/Internal/Loewner/ (e.g. Duality.lean). No other edits.
Checks: `lake build ComplexSLE.Internal.Lemma_2_4_RightHull`; exact-type probe in .lake/probes/ (deleted after);
`python3 -I tools/leanprobe.py externals ComplexSLE.Internal.Lemma_2_4_RightHull ComplexSLE.Internal.lemma_2_4_rightHull`
(report PROVED/PROVED_REL and the externals); `tools/check.sh --quick`. Do not run full tools/check.sh.
Stop condition: if the frozen statement looks false, STOP and report. Budget ~3 hours.

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

Handoff: files changed; approach (including the exact duality statement you proved and any discrepancy with (2.4));
exact commands and outputs; externals status for every new public theorem; anything unproved or uncertain.
