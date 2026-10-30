# M4 / D2 — Lemma 2.4 for left hulls: L_t is connected (prover brief, Fable, HARD)

Goal: prove `ComplexSLE.Internal.lemma_2_4_leftHull` with EXACTLY the type of the frozen anchor
`ComplexSLE.lemma_2_4_leftHull` (ComplexSLE/Frozen/Lemma_2_4_LeftHull.lean, read-only):

    theorem lemma_2_4_leftHull (U : ℝ≥0 → ℂ) (hU : Continuous U) (t : ℝ≥0) :
        IsConnected (leftHull U t)

Source: paper.tex:L658-666 (proof: a loop not surrounding 0 and missing L_t; (r,s) ↦ f_s(L(r)) is a homotopy in
ℂ∖{0}; so the region bounded by the loop misses L_t). That proof is a sketch (ERRATA T5, graph SOURCE_GAP); you may
use any correct route. Graph closure of node lem-connected.left (for orientation):
- claim:gt-conformal | g_t : C\L_t -> C\(R_t+U_t) is holomorphic and bijective, and lim z(g_t(z)-z) = 2t
- claim:hull-nonempty | U_0 in L_t, so L_t is nonempty
- defn-hulls.left | L_t = {z in C : T_z <= t} is the complement of the domain of f_t
- defn-hulls.right | R_t = C minus the range of f_t, so f_t : C\L_t -> C\R_t
- defn-loewner.absorbing-time | T_z in [0,infinity] is the time up to which the solution of (1.1) started at z exists
- defn-loewner.solution | for each z in C, g_t(z) solves g_t(z)-dot = 2/(g_t(z)-U_t), g_0(z) = z; centered chain f_t(z) = g_t(z) - U_t
- defn-loewner.well-defined | the IVP (1.1) started at z has a solution on [0,T_z), and any two solutions on a common interval [0,tau) agree
- ext:lawler-4.5 | Lawler Theorem 4.5: g_t is conformal onto H minus hull; z(g_t-z) -> 2t
- ext:picard-lindelof | Picard-Lindelof ODE existence and uniqueness
- lem-connected.left | L_t is connected (and nonempty)
- step:connected-homotopy | (r,s) -> f_s(mcl L(r)) is continuous on [0,1]x[0,t] with values in C\{0}, hence f_t o mcl L is homotopic to mcl L in C\{0}
- step:connected-loop-criterion | it suffices that the region bounded by every loop mcl L in C\L_t not surrounding the origin does not meet L_t
- step:connected-region-misses-hull | f_t o mcl L does not surround the origin, hence the region bounded by mcl L does not intersect L_t
- step:flow-continuity | (s,w) -> f_s(w) is continuous on {(s,w) : s < T_w}, and {w : T_w > t} is open for each t
- step:hull-closed | L_t is closed, i.e. the domain C \ L_t of f_t is open
- step:hulls-compact | L_t, R_t (and L_{t,s+t}, R_{t,s+t}, L_t u R_t, L_{t,s+t} u R_t) are compact subsets of C
- step:loewner-global-uniqueness | gamma1 = gamma2 on [0,tau) (the agreement set is nonempty, closed and open, by local uniqueness)
- step:loewner-glue-maximal | using uniqueness, solutions on [0,tau) with increasing tau patch together to a solution on [0,T_z), where T_z = sup of such tau
- step:loewner-local-solution | near any time t0 with g(t0) != U_{t0} the ODE g-dot = 2/(g-U_t) has a solution, and two solutions that agree at a time t0 agree on a neighbourhood of t0 (local uniqueness only)

Allowed inputs: Mathlib; sealed definitions ComplexSLE/Frozen/Defs/*; PROVED anchors loewner_wellDefined,
loewnerMap_eq, loewnerMap_exists_solution, scaling/reflection anchors; public lemmas in ComplexSLE/Internal/Loewner/*;
and the EXTERNAL input `ComplexSLE.External.loewnerMap_conformal` (module ComplexSLE.External.LoewnerMapConformal:
ℂ∖L_t open, L_t bounded, g_t extends holomorphic and injective on ℂ∖L_t, z(g_t z − z) → 2t). No other External,
no DRAFT_SORRY anchor or provider (the right-hull Lemma 2.4 anchor is DRAFT — do not use it).
Using the external is allowed but not required: a proof without it is better (it would make the result PROVED
rather than PROVED_REL). Think about routes before coding. Ideas: nonemptiness (U 0 ∈ L_0 ⊆ L_t); compactness from
the external (or prove closedness/boundedness directly); for connectedness, an argument by contradiction from a
separation L_t = A ⊔ B into disjoint nonempty compact sets with U 0 ∈ A: take a small neighbourhood of B whose
boundary misses L_t, and show the flow f_s on that boundary for s ≤ t gives a contradiction (e.g. via the argument
principle / winding number of f_t around 0, or via a maximum-principle argument for 1/f_s, or via the fact that every
z ∈ B is absorbed, |f_s(z)| → 0, while the boundary stays away). Mathlib has winding-number-free tools such as the
maximum modulus principle, open mapping, and Complex.circleIntegral; choose what is actually available.

Ownership: ComplexSLE/Internal/Lemma_2_4_LeftHull.lean (provider; keep header/docstring), new files under
ComplexSLE/Internal/Hull/ and reusable topology/complex analysis under ComplexSLE/Infrastructure/. No other edits.
Checks: `lake build ComplexSLE.Internal.Lemma_2_4_LeftHull`; exact-type probe in .lake/probes/ (example : <frozen
statement as ∀-type> := ComplexSLE.Internal.lemma_2_4_leftHull), deleted after; `python3 -I tools/leanprobe.py externals
ComplexSLE.Internal.Lemma_2_4_LeftHull ComplexSLE.Internal.lemma_2_4_leftHull` (must be PROVED or PROVED_REL, report
which); `tools/check.sh --quick`.
Stop condition: if after a serious attempt the statement needs an input not listed (e.g. a Jordan-curve-type
theorem absent from Mathlib), STOP and report exactly which statement you would need, with a precise Lean draft.
Budget ~5 hours. Don't run full tools/check.sh (only --quick).

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

Handoff: files changed; approach; exact commands and outputs; #print axioms / externals status for every new public
theorem; anything unproved or uncertain.
