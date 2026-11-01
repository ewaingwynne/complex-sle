# M10-B1: Birkhoff's pointwise ergodic theorem (from scratch)

Goal: a sorry-free proof of the EXACT statement of `ComplexSLE.External.birkhoff_stationary`
(`ComplexSLE/External/BirkhoffStationary.lean`, read only) as
`ComplexSLE.Internal.ExternalProofs.birkhoff_stationary` in
`ComplexSLE/Internal/ExternalProofs/BirkhoffStationary.lean`; general ergodic theory in new files under
`ComplexSLE/Infrastructure/Ergodic/` (e.g. `MaximalErgodic.lean`, `PointwiseErgodic.lean`). Copy the theorem type
verbatim. Import no `ComplexSLE.External.*` module. Neither Mathlib (only the L² mean ergodic theorem
`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`, `MeasurePreserving`, `birkhoffSum`,
`birkhoffAverage` in `Mathlib/Dynamics/BirkhoffSum/`) nor the third-party repo has the pointwise theorem.
`ComplexSLE/Infrastructure/Ergodic/SeparatedCount.lean` (recurrence helpers) exists; reuse if useful.

Route:
1. Pointwise ergodic theorem for a measure-preserving `T : α → α` on a probability space and integrable `f`:
   Birkhoff averages `(1/n) ∑_{k<n} f (T^k x)` converge a.e. to an integrable `f̄` with `∫ f̄ = ∫ f`.
   - Maximal ergodic lemma (Garsia's proof): with `M_n = max(0, S_1, …, S_n)`, `S_k = ∑_{j<k} f ∘ T^j`,
     `∫_{M_n > 0} f ≥ 0`; hence `∫_{sup_n S_n > 0} f ≥ 0`, and the same restricted to a `T`-invariant set.
   - For rationals `a < b`, `E = {liminf A_n f < a < b < limsup A_n f}` is invariant (`A_n f ∘ T - A_n f → 0`);
     applying the maximal lemma to `(f - b) 1_E` and `(a - f) 1_E` gives `b μ E ≤ ∫_E f ≤ a μ E`, so `μ E = 0`.
     Countable union over rational pairs: `liminf = limsup` a.e.
   - Finiteness and integrability via Fatou (`∫ liminf |A_n f| ≤ ∫ |f|`); `∫ f̄ = ∫ f` by uniform integrability of
     `A_n f` (convex combinations of the identically distributed `f ∘ T^k`; Mathlib has
     `uniformIntegrable_of_identDistrib`-type lemmas and Vitali's theorem `tendsto_Lp_finite_of_tendsto_ae`).
2. Transfer: `μ = P.map (fun ω n => ξ n ω)` on `ℕ → ℝ` is invariant under the shift `x ↦ (n ↦ x (n + 1))`
   (from `hstat 1`); apply step 1 to `f x = x 0`; `L = f̄ ∘ (fun ω n => ξ n ω)`; the a.e. statement and the
   integrals pull back along the measurable map (`ae_map_iff`, `integral_map`).

Checks: `lake build ComplexSLE.Internal.ExternalProofs.BirkhoffStationary`;
`python3 -I tools/leanprobe.py axioms ComplexSLE.Internal.ExternalProofs.BirkhoffStationary ComplexSLE.Internal.ExternalProofs.birkhoff_stationary`
(only propext, Classical.choice, Quot.sound). Every new file a module, at most 1500 lines.
Stop condition: a precise obstruction, with the failing goal.
Handoff: files created, approach, exact commands and output, axioms, anything unproved.

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
