# M10-A7: support theorem for the SLE_Σ driver (elementary chaining)

Goal: a sorry-free proof of the EXACT statement of `ComplexSLE.External.support_sleDriver`
(`ComplexSLE/External/SupportSLEDriver.lean`, read only) as
`ComplexSLE.Internal.ExternalProofs.support_sleDriver` in
`ComplexSLE/Internal/ExternalProofs/SupportSLEDriver.lean` (helpers in new files under
`ComplexSLE/Internal/ExternalProofs/` or `ComplexSLE/Infrastructure/`). Copy the theorem type verbatim. Import no
`ComplexSLE.External.*` module, directly or transitively. Definitions: `ComplexSLE/Frozen/Defs/{IsSLEDriver,
ComplexGaussian,CovMatrix}.lean`. Reuse driver lemmas in `ComplexSLE/Internal/Driver/` (check their import closures).

Route (no Cameron–Martin needed). Let `R = range(Σ)` viewed in `ℂ ≅ ℝ²` (`hφS` says `φ t ∈ R`); all increments of
`U` lie in `R` a.s. (Gaussian law `N(0,(t-s)Σ)` is supported on `R`).
1. Short-time oscillation: `P(sup_{s ≤ h} |U (u + s) - U u| ≥ r) → 0` as `h → 0`, uniformly in `u` (the law of the
   increment process does not depend on `u`; at `u = 0` use a.s. continuity and `U 0 = 0`). Work with sups over
   rational times so that events are countable intersections/unions.
2. Uniform one-step bound: for `ε > 0` there are `h₀ > 0` and `q > 0` such that for `h ≤ h₀` and every `x ∈ R` with
   `|x| < ε/2` and every `w ∈ R` with `|w| ≤ ε/8`,
   `P(sup_{s ≤ h} |ΔU_s| < ε/2 ∧ x + ΔU_h - w ∈ ball 0 (ε/2)) ≥ q`, with `ΔU_s = U (u+s) - U u`.
   (Lens argument: `ball (w - x) (ε/2) ∩ ball 0 (ε/4)` contains a ball of radius `ε/8` centred in `R`, of
   `N(0,hΣ)`-probability bounded below as `h → 0` on the subspace `R`; subtract the oscillation probability from step 1.)
3. Chaining: choose `h ≤ h₀` with `T/h = n ∈ ℕ` and with `|φ (u+s) - φ u| ≤ ε/8` for `s ≤ h` (uniform continuity of
   `φ` on `[0, T+1]`). Step `k` asks that the increment on `[kh, (k+1)h]` satisfies the event of step 2 with
   `x = U (kh) - φ (kh)` and `w = φ((k+1)h) - φ(kh)`. By independence of increments (`HasIndepIncrements`) and Fubini
   (the conditional probability of step `k` given the past is a function of `x` that is `≥ q`), all `n` steps hold with
   probability `≥ qⁿ > 0`. On that event `|U t - φ t| < ε` for every `t ≤ T`. Take `ε = δ`.
Measurability: `IsSLEDriver` gives only a.e.-measurability (via `HasLaw`) and a.s. continuity, and the target set is an
arbitrary set (outer measure). Prove positivity for a measurable subset: use countably many measurable versions of
`U q` at rational `q` together with a measurable full-measure subset of the continuity event.

Checks: `lake build ComplexSLE.Internal.ExternalProofs.SupportSLEDriver`;
`python3 -I tools/leanprobe.py axioms <module> ComplexSLE.Internal.ExternalProofs.support_sleDriver`
(only propext, Classical.choice, Quot.sound). Every new file a module, at most 1500 lines.
Stop condition: a precise obstruction (e.g. the statement is false as written), with the failing goal.
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
