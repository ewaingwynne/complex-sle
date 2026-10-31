# M8 / T3 — Lemmas 4.4–4.6 in deterministic form: a driver path and ODE estimates (prover brief, Sonnet)

Context: arXiv:2203.07313v4 §4, Lemma 4.4 (`lem-pos-hits-before-neg`, L2036-2039, proof L2118-2138), Lemma 4.5
(`lem:re-im-bounds`, L2043-2076) and Lemma 4.6 (`lem-c-event`, L2082-2107). Orchestrator blueprint: review/plans/M8.md §3.
We replace the probabilistic c-event (Lemma 4.6) by a single deterministic path φ in the range of Σ, so that the
support theorem (EXTERNAL `support_sleDriver`, used later by the orchestrator, not by you) gives positive probability.
What you prove is purely deterministic: a pathwise ODE estimate for every continuous driver V uniformly close to φ on [0, 2].

Target statement (new file `ComplexSLE/Internal/Disconnect/Lemma44.lean`, plus helpers in `Lemma44*.lean`; namespace
`ComplexSLE.Internal`). Adjust inessential details if convenient, keeping it at least this strong:

```lean
theorem exists_lemma44_path (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc0 : 0 ≤ c) (hc : c ^ 2 ≤ a * b) :
    ∃ (φ : ℝ≥0 → ℂ) (C M η : ℝ), Continuous φ ∧ φ 0 = 0 ∧
      (∀ t, ∃ v : Fin 2 → ℝ, (covMatrix a b c).mulVec v 0 = (φ t).re ∧
        (covMatrix a b c).mulVec v 1 = (φ t).im) ∧
      2 ≤ C ∧ 0 < η ∧
      ∀ (V : ℝ≥0 → ℂ) (hV : Continuous V), (∀ t ≤ 2, ‖V t - φ t‖ < η) →
        ∀ z : ℂ, 2 * C - 1 ≤ z.re → z.re ≤ 7 * C + 1 → |z.im| ≤ 1 →
          ∃ h : z ∈ (leftHull V 2)ᶜ,
            z.re - 6 * C ≤ (centeredLoewnerMap V hV 2 ⟨z, h⟩).re ∧
            (centeredLoewnerMap V hV 2 ⟨z, h⟩).re ≤ z.re - 3 * C ∧
            |(centeredLoewnerMap V hV 2 ⟨z, h⟩).im| ≤ M
```
(`covMatrix` = !![a, c; c, b], ComplexSLE/Frozen/Defs/CovMatrix.lean; the range condition is exactly the hypothesis
`hφS` of ComplexSLE/External/SupportSLEDriver.lean. Note `V 0` need not be 0, only within η of φ 0 = 0.)

Blueprint:
1. **The path.** φ(t) = s(t)·(√a + i√b) with s real and piecewise linear. This lies in the range of Σ for every c ≥ 0
   with c² ≤ ab: if c² < ab, Σ is invertible; if c = √(ab), Σ·(1, 0)ᵀ ∝ (√a, √b). The two coordinates play the
   roles of the paper's √a·B and √b·B̃, with B = B̃ = s.
   - Choose s(t) = κ₁·t on [0,1], with √b·s(1) ≥ 5. This is cond-1 with a margin: h⁺(0,1;b) = 2 − √b s(1) ≤ −3.
   - Choose s(t) = s(1) + κ₂·(t − 1) on [1,2], with √a·κ₂ ≈ 4.5C. This is cond-3: √a(s(2) − s(1)) ∈ [2+4C, 5C−2],
     with margins.
   - Then cond-2 (√a|s(t)| ≤ C − 2t on [0,1], with margin) and cond-4 (√b(s(t) − s(1)) ≥ 2t − 3 on [1,2], with
     margin) hold once C is large.
   Take η small compared with all the margins.
2. **ODE.** For z with the Loewner solution γ existing on [0, t] (ClosedSol), f_r = γ(r) − V(r) satisfies
   f_t − f_s = ∫_s^t 2/f_r dr − (V_t − V_s). While |f_r| ≥ 1, the drift has modulus ≤ 2. This gives (4.5)/(4.6) with
   V in place of the paper's Brownian path: h^±(s,t) = ±2(t−s) − (Re/Im)(V_t − V_s).
3. **Bootstrap (proof of Lemma 4.4, L2118-2138).** Let z have Re z ∈ [2C−1, 7C+1] and |Im z| ≤ 1.
   - On [0,1]: Re f_t ≥ Re z − C − O(η) ≥ C − 1 − O(η) ≥ 1, so |f| ≥ 1 there.
   - Then Im f₁ ≤ Im z − 3 + O(η) ≤ −2 + O(η), and on [1,2], Im f_t ≤ Im f₁ + 1 + O(η) ≤ −1/2 (adjust margins so that
     |f| ≥ 1).
   So the solution exists on [0,2] with |f| ≥ 1, and z ∉ L_2.
   - For the estimate: Re f₂ − Re f₁ ∈ [−5C, −4C] ± O(η) and Re f₁ − Re z ∈ [−C, C] ± O(η), which gives
     Re f₂ − Re z ∈ [−6C, −3C] (with margins).
   - |Im f₂| is bounded by M (from |Im z| ≤ 1 and the bounds on [0,2]).
   Use `centeredLoewnerMap_eq_of_closedSol` and `notMem_leftHull_iff_exists_closedSol`
   (ComplexSLE/Internal/Duality/Locality.lean) to connect ODE solutions with `leftHull` and `centeredLoewnerMap`.
   Existence of the solution while |f| ≥ 1 needs a local-existence/continuation argument. Look at
   ComplexSLE/Internal/Hull/LocalExistence.lean, ComplexSLE/Internal/Loewner/*.lean and
   ComplexSLE/Internal/Polar/Path.lean (whose `fPath` / `sigmaDom` API may already give "no blow-up while |f| stays
   bounded below"), and Infrastructure/ODE/GronwallBootstrap.lean. Reuse what exists before writing new ODE theory.

Allowed inputs: Mathlib; sealed defs/anchors; existing Internal/Infrastructure lemmas. No EXTERNAL.
Ownership: new files `ComplexSLE/Internal/Disconnect/Lemma44*.lean` only; scratch in `.lake/probes/m8-t3/`.
Another Sonnet works concurrently on `ComplexSLE/Infrastructure/Planar/*.lean` and `Internal/Disconnect/Growth.lean`.
Checks: `lake build ComplexSLE.Internal.Disconnect.Lemma44`; `tools/check.sh --quick`; `#print axioms exists_lemma44_path`
(expect only propext, Classical.choice, Quot.sound). Budget ~4 hours; land what is proved, report the rest precisely.

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

Handoff: files changed; exact statements; approach; commands and outputs; axioms; anything unproved.
