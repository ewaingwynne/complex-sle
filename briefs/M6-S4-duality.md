# M6 / S4 — Proposition 1.5 (SLE_Σ duality), coupling form (prover brief)

Goal: prove `ComplexSLE.Internal.sle_duality` with EXACTLY the type of the frozen anchor `ComplexSLE.sle_duality`
(ComplexSLE/Frozen/Proposition_1_5.lean, read-only; ruling R28 in ERRATA.md). Read the statement carefully: driver part
(Ũ s = i(U(t − s) − U t) + i(U(max s t) − U t), ℝ≥0 truncated subtraction, is an IsSLEDriver b a (−c)), and the a.s.
pathwise hull/map identities L̃_t = i R_t, R̃_t = i L_t, f̃_t(w) = i z where f_t z = −i w.

Existing ingredients (read them):
- ComplexSLE/Internal/Loewner/Duality.lean: `revDriver U t s = I * (U (t − s) − U t)` (constant for s ≥ t),
  `rightHull_eq_image_leftHull_revDriver : R_t^U = (−i)·L_t^{revDriver}`, `mem_range_centeredLoewnerMap_iff`,
  closedSol / time reversal / endpoint uniqueness. Ũ agrees with revDriver on [0, t]; hulls and maps at time t depend only
  on the driver on [0, t] — prove that locality lemma (two drivers equal on [0,t] ⇒ same L_t, same f_t, same R_t).
- ComplexSLE/Internal/Loewner/{Transform,MapTransform,Injective,Concatenation}.lean (reflection: L^{−U} = −L^U etc.,
  injectivity of f_t).
- ComplexSLE/Internal/Driver/*.lean: `IsSLEDriver.mul_I` (i·U is IsSLEDriver b a (−c)), `neg`, `shift`,
  `indep_shift_past`, `map_timeReversal` (finite-dimensional time reversal on [0,T]), Gaussian linear images.
  For the driver part you need: increments of Ũ over intervals inside [0,t] are −i·(increments of U reversed), over
  intervals inside [t,∞) are i·(increments of U), and the two families are independent (indep_shift_past); then
  HasIndepIncrements and the Gaussian increment laws across the junction s ≤ t ≤ s' (sum of two independent Gaussians).
  Continuity a.s. and Ũ 0 = 0 hold pointwise. No positivity of a, b is needed (the statement has 0 ≤ a, 0 ≤ b).
- The map clause uses U 0 = 0 (available a.s. from hU.zero) — see the reviewer's derivation in review/approvals/M6.md.

Allowed inputs: Mathlib; sealed defs and PROVED/PROVED_REL sealed anchors; Internal/Infrastructure lemmas. No Externals
are needed (the result should be PROVED); no DRAFT anchor or provider.
Ownership: ComplexSLE/Internal/Proposition_1_5.lean (provider; keep header/docstring), new files under
ComplexSLE/Internal/Duality/. You may add new lemmas in new files only (do not edit existing Internal files).
Checks: lake build of the provider; exact-type probe in .lake/probes/ (deleted after); `python3 -I tools/leanprobe.py
externals ComplexSLE.Internal.Proposition_1_5 ComplexSLE.Internal.sle_duality`; `tools/check.sh --quick`.
Don't run full tools/check.sh (another prover is mid-build). Stop condition: if the frozen statement looks false, STOP
and report precisely. Budget ~4 hours.

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
