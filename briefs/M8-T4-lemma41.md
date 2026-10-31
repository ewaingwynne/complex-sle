# M8 / T4 — Lemma 4.1 (with R20): deterministic core and probability assembly (prover brief, Sonnet)

Source: arXiv:2203.07313v4 Lemma 4.1 (`lem-disconnect-2`, L1960-1963), proof L2159-2195, with ERRATA.md R20 (two-scale
choice of U^± — here: small balls around zero-map preimages) and the orchestrator blueprint review/plans/M8.md.
All building blocks are proved and committed; this packet assembles them. Read their statements first:
- `ComplexSLE/Internal/Disconnect/Lemma44.lean`: `exists_lemma44_path` (φ, C ≥ 2, M, η₂; drivers within η₂ of φ on
  [0,2]: every z with Re z ∈ [2C−1, 7C+1], |Im z| ≤ 1 is ∉ L₂ and Re f₂ z ∈ [Re z − 6C, Re z − 3C], |Im f₂ z| ≤ M). Needs c ≥ 0.
- `ComplexSLE/Internal/Disconnect/LineApprox.lean`: `lineApprox` (drivers with sup_{t≤T}|V| < η: L_T within δ of slitI T,
  R_T within δ of slitR T, points of L_T/R_T within δ of the tips, f_T within δ of zeroMap T away from slitI);
  `ZeroDriver.lean`: `slitI`, `slitR`, `zeroMap`, `exists_zeroMap_eq`, `mem_slitI_iff`, `mem_slitR_iff`.
- `ComplexSLE/Infrastructure/Planar/`: `disconnectsFromInfinity_of_two_connected` (Separation.lean),
  `exists_mem_image_of_chain_crossing` (CrossingLimit.lean), `exists_chain_of_isPreconnected` (Chain.lean),
  `disconnectsFromInfinity_pullback` (Pullback.lean), `disconnectsFromInfinity_conj`, `disconnectsFromInfinity_image`.
- `ComplexSLE/Internal/Disconnect/Growth.lean`: `centeredLoewnerMap_norm_ge`, `continuous_centeredLoewnerMap`.
- Sealed: `concatenation_leftHull`, `lemma_2_4_leftHull`, `lemma_2_4_rightHull`, `reflection_leftHull`.
  Also `zero_mem_rightHull` (Internal/Phases/KoebeHit.lean), `driver_zero_mem_leftHull`, `isClosed_leftHull'`,
  `isBounded_leftHull'`, duality `rightHull_dualDriver`/`leftHull_dualDriver` (for compactness of R_T if needed).
- Driver: `IsSLEDriver.shift`, `IsSLEDriver.indep_shift_past` (Internal/Driver/Shift.lean), `IsSLEDriver.conjugate`
  (Transform.lean), `IsSLEDriver.exists_adapted` (Driver/BridgeAdapted.lean).
- EXTERNAL allowed: `support_sleDriver` (ComplexSLE/External/SupportSLEDriver.lean) — Part B only.

Ownership: new files `ComplexSLE/Internal/Disconnect/Lemma41*.lean` (namespace `ComplexSLE.Internal`). Nothing else.
Scratch only in `.lake/probes/m8-t4/`. Another Sonnet works concurrently on `Internal/Disconnect/DiscEvent*.lean`.

## Part A — deterministic core (priority; no probability, no external except those inside lineApprox)

Statement (adjust inessential details): for `0 < a, 0 < b, 0 ≤ c, c² ≤ ab` there exist `T K η₁ η₂ η₃ r > 0`, `φ` (from
Lemma 4.4) and `p₊ p₋ : ℂ` such that for every continuous `u` with `u 0 = 0` satisfying
 (E1) `∀ t ≤ T, ‖u t‖ < η₁`, (E23) `∀ t ≤ 2, ‖u (t + T) - u T - φ t‖ < η₂`,
 (E4) `∀ t ≤ K, ‖u (t + (2 + T)) - u (2 + T)‖ < η₃`,
with `t₀ := K + 2 + T` (match the form produced by `concatenation_leftHull`), one of `V = ball p₊ r`, `V = ball p₋ r` satisfies
`Disjoint V (leftHull u t₀) ∧ DisconnectsFromInfinity (leftHull u t₀) V`.

Blueprint (all constants deterministic):
- From Lemma 4.4: φ, C ≥ 2, M, η₂. Put x := 2C, ε := 1/4, w± := x ± 2εi. Choose T with 2√T ≥ 7C + 4.
- `exists_zeroMap_eq` gives p± ∉ slitI T with zeroMap T p± = w± (w± ∉ slitR T as Im ≠ 0). d := min of
  infDist p± (slitI T) > 0; by continuity of zeroMap at p± pick r < d/2 with zeroMap T '' ball p± r ⊆ ball w± (ε/2).
  δ := min (d/2) (ε/2). η₁ := the η of `lineApprox T δ`.
- Choose K with 2√K ≥ M + 4 and η₃ := the η of `lineApprox K (1/2)`.
- Let W := fun t => u (t + T) - u T (continuous, W 0 = 0), W' := fun t => W (t + 2) - W 2 (= u (t + (2+T)) − u (2+T)),
  F := f₂^W (centeredLoewnerMap W _ 2), L' := leftHull W (K + 2) (by `concatenation_leftHull` for W, t = 2, s = K:
  L' = L₂(W) ∪ {z | ∃ h, F z ∈ L_K(W') \ R₂(W)}), N := {z | 2C−1 ≤ Re z ≤ 7C+1, |Im z| ≤ 1} (compact).
- On E1 (lineApprox at T, δ): balls B± := ball p± r miss L_T(u); f_T(B±) ⊆ ball w± ε; R_T(u) ⊆ {|Im| < δ} (δ ≤ ε);
  ∃ q ∈ R_T(u) with Re q > 2√T − δ ≥ 7C + 2; 0 ∈ R_T(u); R_T(u) compact & connected.
- On E23 (Lemma 4.4 with V = W): N ⊆ L₂(W)ᶜ and the Re/Im estimates for F on N.
- On E4 (lineApprox at K, 1/2 for W'): B := L_K(W') ⊆ {|Re| < 1/2} (slitI K lies on iℝ), connected (`lemma_2_4_leftHull`),
  closed; ∃ b₁ ∈ B with Im b₁ > 2√K − 1/2 ≥ M + 3, ∃ b₂ ∈ B with Im b₂ < −(M + 3).
- **Hit point** via `exists_mem_image_of_chain_crossing` with S := R_T(u) ∩ N, the strip half-width 1/2, h := M + 2:
  for ρ ∈ (0, 1/2], uniform continuity of F on N gives ρ' ≤ min ρ 1 with F-steps < ρ; take a ρ'-chain in R_T(u) from 0 to q
  (`exists_chain_of_isPreconnected`); let i be the last index with Re β_i < 2C − 1/2 and j the first index > i with
  Re β_j > 7C + 1/2; the sub-chain β_{i+1..j−1} is nonempty (a ρ'-step cannot jump 5C), lies in N (|Im| < δ ≤ 1), and its
  F-image starts at Re ≤ (2C − 1/2 + ρ') − 3C ≤ −1/2, ends at Re ≥ (7C + 1/2 − ρ') − 6C ≥ 1/2, with |Im| ≤ M ≤ h − 2ρ.
  Conclusion: β* ∈ R_T(u) ∩ N with F β* ∈ B; then β* ∈ L' (concatenation; F β* ∉ R₂(W) since F maps into R₂ᶜ), and
  Re β* ≥ Re F β* + 3C > 3C − 1/2 ≥ x + ε.
- **L' avoids ball x (3ε)**: ball x (3/4) ⊆ N so it misses L₂(W), and there Re F z ≤ Re z − 3C < −1/2, so F z ∉ B.
- **Separation** (`disconnectsFromInfinity_of_two_connected`, x0 := x, ε := 1/4): A := R_T(u), B := L' (compact, connected,
  0 ∈ L' as W 0 = 0), q := 0 (Re 0 ≤ x − ε), p := β*. For every z₁ ∈ f_T(B₊), z₂ ∈ f_T(B₋): R_T ∪ L' disconnects z₁ or z₂.
  Hence R_T ∪ L' disconnects all of f_T(B₊) or all of f_T(B₋) (DisconnectsFromInfinity K W is pointwise in W).
- **Pullback** (`disconnectsFromInfinity_pullback` with L = L_T(u), F = f_T^u, R = R_T(u), L' as above; growth from
  `centeredLoewnerMap_norm_ge`, continuity `continuous_centeredLoewnerMap`), and `concatenation_leftHull` for u with t = T,
  s = K + 2: L_{K+2+T}(u) disconnects B₊ or B₋. Disjointness: B± miss L_T(u) and f_T(B±) ⊆ ball x (3ε) misses L'.

## Part B — probability (uses EXTERNAL `support_sleDriver`)

Target (this exact form is consumed by the Thm 1.10 packets):
```lean
theorem lemma_4_1 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ℝ≥0 → Ω → ℂ) (hU : IsSLEDriver a b c U P) :
    ∃ (V : Set ℂ) (t : ℝ≥0), IsOpen V ∧ Bornology.IsBounded V ∧ V.Nonempty ∧ 0 < t ∧
      0 < P {ω | Disjoint V (leftHull (U · ω) t) ∧ DisconnectsFromInfinity (leftHull (U · ω) t) V}
```
Blueprint: (1) c ≥ 0 first. Pass to the everywhere-continuous adapted version U' (`exists_adapted`; U' = U a.s., U' 0 = 0),
sets for U and U' differ by a null set. (2) The events E1, E23, E4 for U' are measurable (by continuity they equal countable
intersections over rational times of closed conditions with a margin: `∀ t ≤ T, ‖·‖ < η` ⟺ `∃ m, ∀ rational t ≤ T,
‖·‖ ≤ η − 1/(m+1)` using compactness of [0,T]) and have positive probability by `support_sleDriver` applied to U' (φ = 0),
to `IsSLEDriver.shift` at T (φ from Lemma 4.4, its range condition), and to the shift at 2 + T (φ = 0).
(3) Independence: E1 is measurable w.r.t. σ(U' r : r ≤ T), E23 ∩ E4 w.r.t. σ(shifted process at T)
(`indep_shift_past` at T), and E23, E4 are separated by `indep_shift_past` for the shifted driver at 2. Hence
P(E1 ∩ E23 ∩ E4) = P(E1) P(E23) P(E4) > 0. (4) Part A: E1 ∩ E23 ∩ E4 ⊆ S₊ ∪ S₋ (S± the target sets for V = ball p± r), so
by outer-measure subadditivity P S₊ > 0 or P S₋ > 0. (5) c < 0: apply the c ≥ 0 case to the conjugate driver
(`IsSLEDriver.conjugate`, parameter −c) and transport by conj (`reflection_leftHull` pathwise on continuous paths,
`disconnectsFromInfinity_conj`; V ↦ conj '' V); handle a.s. continuity by the adapted version again.

Checks: `lake build ComplexSLE.Internal.Disconnect.Lemma41`; `tools/check.sh --quick`;
`python3 -I tools/leanprobe.py externals ComplexSLE.Internal.Disconnect.Lemma41 ComplexSLE.Internal.lemma_4_1`
(expect PROVED_REL{koebe_quarter, loewnerMap_tendstoUniformly, support_sleDriver}). Budget ~5 hours; Part A first. Land what
is proved; report the rest precisely (e.g. Part A done, Part B open with the exact obstruction).

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
