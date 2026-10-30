# M6 / S9 — conditioning a diffusion on the past; discharging the renewal hypothesis (prover brief)

Goal (INTERNAL lemmas, no frozen anchors; target PROVED or PROVED_REL{ito_formula}):
1. Conditioning lemma. If `IsDiffusionSolution ℱ α β X P` (ComplexSLE/Frozen/Defs/IsDiffusionSolution.lean) with
   everywhere-continuous paths, s : ℝ≥0, and A ∈ ℱ s with 0 < P A, then the shifted process Y t = X (s + t) is an
   IsDiffusionSolution for the shifted filtration (t ↦ ℱ (s + t)) under the conditional probability ProbabilityTheory.cond
   P A (= P[|A]), with Y 0 = X s. Proof sketch: martingale property under P[|A] for B ∈ ℱ (s+t): integrals over A ∩ B;
   localising times (τ_n − s)⁺ (stopping times for the shifted filtration); progressive measurability and continuity
   transfer; pathIntegral shifts by a ℱ s-measurable constant. Use the existing stochastic infrastructure
   (ComplexSLE/Infrastructure/Stochastic/*), and state a general IsContLocalMartingale version first.
2. Discharge the renewal hypothesis. In ComplexSLE/Internal/Recurrence/{Renewal,SLE}.lean, `ae_frequently_mem_latticeSet`
   takes `hren` and `sle_recurrence` takes `hMarkov`. Using 1. and `sle_angle_hit_unif` (which quantifies over ALL
   solutions on ANY probability space started in Icc x (x+π−ε)), plus π-periodicity of µ and β² (shift X by nπ to move
   X s into Icc x (x+π−ε) — check IsDiffusionSolution is invariant under X ↦ X − nπ for an ℱ s-measurable integer n, or
   split A by the value of n), prove a version `sle_recurrence'` WITHOUT the hMarkov hypothesis (keep hstat).
3. The c < 0 case of Lemma 2.16 (graph step:wlog-c-nonneg-arg): by reflection X ↦ −X (isDiffusionSolution_neg, mu_neg_c in
   the Recurrence/Stationary files), derive the recurrence statement for c ≤ 0 with the reflected recurrence point
   (ERRATA R19: tan x = sgn(c)√(b/a)).
Read first: ComplexSLE/Internal/Recurrence/*.lean (all), ComplexSLE/Internal/Stationary/ItoReal.lean, the Infrastructure
Stochastic files. Allowed inputs: Mathlib; sealed defs; Internal/Infrastructure lemmas; EXTERNAL ito_formula (already used
upstream). No other externals; no DRAFT anchor/provider.
Ownership: new files under ComplexSLE/Internal/Recurrence/ (prefix Cond*, Recurrence2*) and ComplexSLE/Infrastructure/Stochastic/
(prefix Cond*). Do not edit existing files. Another prover works under ComplexSLE/Internal/Polar/.
Checks: lake build of your modules; `python3 -I tools/leanprobe.py externals <module> <decl>` per main theorem;
`tools/check.sh --quick`. Don't run full tools/check.sh. Budget ~4 hours; land what is proved.

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
