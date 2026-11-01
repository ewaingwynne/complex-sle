# M10-A8: remove the use of Dambis–Dubins–Schwarz from C0Bdy

Goal: `ComplexSLE/Internal/Phases/C0Bdy.lean` currently obtains a Brownian motion from the EXTERNAL
`External.dambis_dubins_schwarz` only to conclude `liminf M = -∞` (`Infrastructure.ae_forall_exists_le_of_timeChange`).
Replace that step by a direct, external-free lemma, and make C0Bdy (and everything else) stop importing
`ComplexSLE.External.DambisDubinsSchwarz`. No frozen statement changes.

New lemma (put it in a new file `ComplexSLE/Infrastructure/Stochastic/BracketInfinity.lean`, name as you see fit):
for a filtration `ℱ` on a probability space, `N A : ℝ≥0 → Ω → ℝ` with `IsContLocalMartingale ℱ N P`,
`N 0 = 0` a.s., `IsContLocalMartingale ℱ (fun t ω => N t ω ^ 2 - A t ω) P`, a.s. `A` continuous, monotone,
`A 0 = 0`, `A → ∞` (exactly the hypotheses C0Bdy currently feeds to DDS; check them there), conclude
`∀ᵐ ω ∂P, ∀ K : ℝ, ∃ s, N s ω ≤ -K` (or whatever exact form C0Bdy consumes; also the symmetric `K ≤ N s ω`
if it is free).
Proof route (classical): for `K, L > 0` let `τ` be the exit time of `(-K, L)`. The stopped `N^τ` is a bounded
martingale, so `E[N_{τ∧t}] = 0`; and `E[A_{τ∧t}] = E[N_{τ∧t}²] ≤ max(K,L)²`, so `A_τ < ∞` a.s., hence `τ < ∞`
a.s. because `A → ∞`. Then `0 = E N_τ = -K·P(N_τ = -K) + L·P(N_τ = L)`, so `P(N hits -K) ≥ L/(K+L) → 1`.
Countable intersection over `K ∈ ℕ`. Mind that `IsContLocalMartingale` only gives a.s. continuous paths:
work with the localizing sequence it provides, or pass to an a.s.-equal version; look first at the existing
infrastructure in `ComplexSLE/Infrastructure/Stochastic/` (`ContinuousOptionalStopping`, `StoppedLocalMartingale`,
`LocalMartingaleAlgebra`, `BoundedBracket`, `BoundedBracketMaximal`, `TimeChangeTransfer`) and reuse it.

Then rewrite the DDS step of `C0Bdy.lean` (only that file, plus your new file) to use the new lemma, remove the
`public import ComplexSLE.External.DambisDubinsSchwarz`, and update C0Bdy's docstrings (they mention DDS).
Do not touch any other file; if another file also imports the DDS external, report it.

Checks: `lake build ComplexSLE.Internal.Phases.C0Bdy` and the frozen consumer
`lake build ComplexSLE.Frozen.Lemma_3_12` if that module exists (find the frozen anchor that consumes
`lemma_3_12`/`ae_mem_closure_c0_bdy` via `grep -rl C0Bdy ComplexSLE`), then
`python3 -I tools/leanprobe.py externals <frozen module> <export>` for `ComplexSLE.theorem_1_8_c_zero`
(module `ComplexSLE.Frozen.Theorem_1_8_CZero`): `dambis_dubins_schwarz` must no longer be listed.
`#print axioms` (via `tools/leanprobe.py axioms`) for the new lemma: only propext, Classical.choice, Quot.sound.
Stop condition: a precise obstruction, with the failing goal.
Handoff: files changed, approach, exact commands and output, axioms, anything unproved.

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
