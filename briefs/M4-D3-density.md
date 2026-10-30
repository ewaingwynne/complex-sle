# M4 / D3 — Lemma 2.13 existence of an admissible density (prover brief, Fable)

Goal: prove `ComplexSLE.Internal.exists_admissibleDensity` with EXACTLY the type of the frozen anchor
`ComplexSLE.exists_admissibleDensity` in `ComplexSLE/Frozen/Lemma_2_13_Exists.lean` (read-only):

    theorem exists_admissibleDensity (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b) :
        ∃ p, IsAdmissibleDensity a b c p

Definitions (sealed, importable): `ComplexSLE/Frozen/Defs/{IsAdmissibleDensity,Mu,DiffusionD}.lean`. Read
`IsAdmissibleDensity` carefully: continuous, ≥ 0, π-periodic, ∫₀^{2π} p = 1, and ∃ x with p C² on {u | ∀ n:ℤ, u ≠ x+nπ},
the stationary Fokker–Planck equation −(µp)' + (Dp)'' = 0 there (with `deriv`), and D·p C¹ on ℝ.
Source: paper.tex:L941-955 (statement), proof ≈L1000-1105; rulings ERRATA.md R5, R7, R19 (for c = −√(ab) the
degenerate point x satisfies tan x = sgn(c)·√(b/a)).

Ownership: `ComplexSLE/Internal/Lemma_2_13_Exists.lean` (provider; keep header/docstring), new files under
`ComplexSLE/Internal/Density/`, reusable calculus facts under `ComplexSLE/Infrastructure/`. No other edits.
Allowed inputs: Mathlib and the sealed definitions above. No External files, no other ComplexSLE modules.

Case 1, c² < ab (D > 0 everywhere). The orchestrator authorizes a route simpler than the paper's p₀ + r_*p₁ (which
needs a closed-form antiderivative): let Φ(u) = ∫₀ᵘ µ/D, λ = Φ(π) (Φ(u+π) = Φ(u)+λ by π-periodicity of µ/D) and
    q(u) = exp(Φ(u)) · ∫_u^{u+π} exp(−Φ(s)) ds,   p = k · q / D.
Then q > 0, q is π-periodic, q' = (µ/D) q + (e^{−λ} − 1), so −µp + (Dp)' = k(e^{−λ}−1) is constant and
−(µp)' + (Dp)'' = 0 on ℝ (take any x; the C² set condition then holds on all of ℝ). Choose k > 0 to normalise.
No sign condition on c and no WLOG is needed. Record in your report that this route replaces the source's
`step:p-case1-*` nodes.

Case 2, c² = ab (c = ±√(ab)). D = β²/2 with β(u) = √a sin u ∓ √b cos u, vanishing exactly on x + πℤ (x as in R19).
Follow paper (2.32): on (x, x+π) p(u) = (∫_x^u e^{−Ψ(s)} ds) / (D(u) e^{−Ψ(u)}) with Ψ(u) = ∫_{x+π/2}^u µ/D;
show it is finite, smooth, solves −µp + (Dp)' = 1, has limit −1/µ(x) = (a+b)/(4√(ab)) at both ends (µ(x) =
−4√(ab)/(a+b) < 0), extend π-periodically and continuously, show (Dp)' → 0 at x+πℤ so Dp is C¹ on ℝ, then
normalise. You may do c = √(ab) and transport to c = −√(ab) by u ↦ −u (graph node step:p-wlog-c-nonneg), or treat
both signs directly. This is the hard part: plan the API (one-sided limits, `HasDerivAt` of parametric integrals,
the "limit of derivative ⇒ derivative" lemma) before writing.

Checks (run them, paste output):
- `lake build ComplexSLE.Internal.Lemma_2_13_Exists`
- exact-type probe `.lake/probes/D3_probe.lean` (module; imports provider + Defs) with
  `example : <frozen statement verbatim as a ∀-type> := ComplexSLE.Internal.exists_admissibleDensity`;
  `lake env lean .lake/probes/D3_probe.lean`; delete afterwards.
- `python3 -I tools/leanprobe.py axioms ComplexSLE.Internal.Lemma_2_13_Exists ComplexSLE.Internal.exists_admissibleDensity`
- `tools/check.sh --quick`

Stop condition: if the frozen definition makes the statement false or unprovable (e.g. the `deriv`-based ODE
clause, the C² set, or the periodicity convention), STOP and report the obstruction. If Case 1 is done but Case 2 is
not, land Case 1 as a separately named theorem (`ComplexSLE.Internal.exists_admissibleDensity_of_sq_lt`) and
report Case 2's status; do not put a partial proof in the provider export. Budget ~4 hours wall time.

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
