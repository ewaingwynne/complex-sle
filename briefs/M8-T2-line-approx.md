# M8 / T2 — Lemmas 4.2/4.3 in deterministic form: drivers near 0 have hulls near the zero-driver slits (prover brief, Sonnet)

Context: arXiv:2203.07313v4 §4, Lemma 4.2 (`lem-line-approx`, L1991-1993, proof L2021-2025) and Lemma 4.3 (`lem-haus`,
L1998-2019). Orchestrator blueprint: review/plans/M8.md §2. The paper's second bullet of Lemma 4.3 (a Hurwitz /
normal-families argument) is NOT needed. Lower semicontinuity of the hulls comes from the Koebe distance bound instead.
Everything here is deterministic (no probability).

Allowed EXTERNALs (import from ComplexSLE/External/): `loewnerMap_tendstoUniformly` (E12, LoewnerMapTendstoUniformly.lean)
and `koebe_quarter` (KoebeQuarter.lean). Also use the existing in-project lemmas below.

Ownership: new files `ComplexSLE/Internal/Disconnect/ZeroDriver.lean` and `ComplexSLE/Internal/Disconnect/LineApprox*.lean`
(namespace `ComplexSLE.Internal`). Nothing else. Scratch only in `.lake/probes/m8-t2/`.

## Part 1: the zero driver (file ZeroDriver.lean; no external)

Let `slitI T := segment ℝ (-(2 * √T) * I) ((2 * √T) * I)` (the paper's [−2T^{1/2} i, 2T^{1/2} i]) and
`slitR T := segment ℝ (-(2 * √T) : ℂ) (2 * √T)`. Define `zeroMap T z := z * (1 + 4 * T / z ^ 2) ^ (1/2 : ℂ)` (principal
branch). Then `zeroMap T z ^ 2 = z ^ 2 + 4T`, and zeroMap is ∼ z at ∞, holomorphic and continuous off `slitI T`.
1+4T/z² ∈ (−∞,0] iff z ∈ slitI T \ {0}. Prove:
- `leftHull (fun _ => 0) T = slitI T`. The solution from z is γ(s) = zeroMap s z, since γ² = z² + 4s by uniqueness
  (d(γ²)/ds = 4). It hits 0 at s = −z²/4 iff z ∈ slitI.
- for z ∉ slitI T, `centeredLoewnerMap (fun _ => 0) _ T ⟨z, _⟩ = zeroMap T z` (use `centeredLoewnerMap_eq_of_closedSol`,
  `notMem_leftHull_iff_exists_closedSol` in ComplexSLE/Internal/Duality/Locality.lean);
- `rightHull (fun _ => 0) _ T = slitR T`;
- surjectivity: every `w ∉ slitR T` equals `zeroMap T z` for some `z ∉ slitI T`, with an explicit preimage
  `z = w * (1 - 4T/w²)^(1/2)`. This is needed later to place the R20 sets U^± near x ± 2iε.

## Part 2: approximation (files LineApprox*.lean)

Target (adjust inessential details; keep at least this strength; report the final form):

```lean
theorem lineApprox (T : ℝ≥0) (hT : 0 < T) (δ : ℝ) (hδ : 0 < δ) :
    ∃ η > 0, ∀ (V : ℝ≥0 → ℂ) (hV : Continuous V), V 0 = 0 → (∀ t ≤ T, ‖V t‖ < η) →
      (∀ z ∈ leftHull V T, infDist z (slitI T) < δ) ∧
      (∀ w ∈ rightHull V hV T, infDist w (slitR T) < δ) ∧
      (∃ z ∈ leftHull V T, 2 * √T - δ < z.im) ∧ (∃ z ∈ leftHull V T, z.im < -(2 * √T - δ)) ∧
      (∃ w ∈ rightHull V hV T, 2 * √T - δ < w.re) ∧ (∃ w ∈ rightHull V hV T, w.re < -(2 * √T - δ)) ∧
      ∀ z (h : z ∈ (leftHull V T)ᶜ), δ ≤ infDist z (slitI T) →
        ‖centeredLoewnerMap V hV T ⟨z, h⟩ - zeroMap T z‖ < δ
```
(Here `√T` means `Real.sqrt T`.)

Blueprint:
1. **From sequences to η.** E12 is stated for sequences `V n → U` locally uniformly. Argue by contradiction: if no η
   works for one clause, pick V_n with sup_{t≤T} |V_n| < 1/n violating it. Replace V_n by V_n(min t T), which does not
   change hulls or maps up to time T (`leftHull_congr`, `centeredLoewnerMap_congr`, `rightHull_congr` in
   Duality/Locality.lean). Then V_n → 0 locally uniformly, and E12 with U = 0 (Part 1 identifies L^0_T = slitI) gives
   the upper bound on L_T and the uniform approximation of f_T = g_T − V_T (V_T is small).
2. **Right hulls by duality.** `leftHull_dualDriver` / `rightHull_dualDriver` / `centeredLoewnerMap_dualDriver`
   (ComplexSLE/Internal/Duality/Deterministic.lean) give `i R_T(V) = L_T(Ṽ)` with Ṽ = dualDriver V T, which is
   continuous with Ṽ 0 = 0 and sup_{s≤T} |Ṽ s| ≤ 4 sup_{t≤T} |V t|. So the R_T clauses follow from the L_T clauses for
   Ṽ, rotated by −i.
3. **Lower bound: points of L_T near ±2√T i (Koebe).** Let z₀ = i(2√T + δ'), with δ' small relative to δ.
   - The bound `norm_deriv_fPath_mul_infDist_le` (ComplexSLE/Internal/Phases/KoebeHit.lean) gives
     |f_T'(z₀)| · dist(z₀, L_T) ≤ 4|f_T(z₀)|. It already uses the Koebe quarter theorem.
   - For the zero driver, |f⁰(z₀)| = √((2√T+δ')² − 4T) = O(√δ') and |f⁰'(z₀)| = |z₀|/|f⁰(z₀)| = O(1/√δ').
   - f^V → f⁰ uniformly on a disc around z₀ at positive distance from slitI (step 1, applied with a smaller tolerance).
     The Cauchy estimate then gives f^V'(z₀) → f⁰'(z₀): apply
     `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` or similar to the difference. Relate `fPath` and its
     `deriv` to `centeredLoewnerMap` via the Polar/Path.lean API (fPath is the total extension).
   - Hence dist(z₀, L^V_T) ≤ 4|f^V(z₀)|/|f^V'(z₀)| ≈ 8δ' < δ/2. So L^V_T has a point z with Im z > 2√T − δ. The point
     −z₀ is symmetric.
   - The R_T points near ±2√T then follow by duality (step 2).

Search Mathlib first (lean-search-discovery skill): `Complex.cpow`, `Complex.sqrt`-type lemmas, `segment`, `infDist`,
Cauchy estimates (`Complex.norm_deriv_le_aux`, `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`),
`TendstoLocallyUniformly`, `tendstoLocallyUniformly_iff_forall_isCompact`.

Checks: `lake build ComplexSLE.Internal.Disconnect.ZeroDriver ComplexSLE.Internal.Disconnect.LineApprox`;
`tools/check.sh --quick`; `python3 -I tools/leanprobe.py externals ComplexSLE.Internal.Disconnect.LineApprox
ComplexSLE.Internal.lineApprox` (expect PROVED_REL with only loewnerMap_tendstoUniformly, koebe_quarter). Budget ~4 hours;
land what is proved (Part 1 alone is valuable), report the rest precisely.

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

Handoff: files changed; exact statements; approach; commands and outputs; externals; anything unproved.
