# AU-M2-roots: statement audit of `.lake/probes/M2Roots.lean`

Auditor: independent, refute-first. Source: `paper.tex` = `source/arxiv-2203.07313v4/complex-sle-final.tex`.
Target: `/home/ewain/complex-sle/.lake/probes/M2Roots.lean`. It compiles; it contains **11** `sorry`
theorems (the brief said 12; the file has: 1.8, 1.8 c=0, 1.10a, 1.10b, 3.1a, 3.1b, 3.2a, 3.2b, 2.4, scaling, reflection).
No manifest entry exists for a probe, so identity is by content as read. All verdicts are DRAFT-level
(DECLARATION_FIDELITY); PROOF_STATUS: FROZEN_UNPROVED for every theorem.
Frozen defs read: `ComplexSLE/Frozen/Defs/*.lean` (all 17) and `AU-M1-carriers.md`.

## Summary verdicts

| Draft | Verdict |
|---|---|
| theorem_1_8 | ACCEPT |
| theorem_1_8_c_zero | ACCEPT |
| theorem_1_10_a | ACCEPT |
| theorem_1_10_b | ACCEPT |
| proposition_3_1_a | ACCEPT-WITH-NOTE (N1: p-universality extends R7 to Props 3.1/3.2) |
| proposition_3_1_b | ACCEPT-WITH-NOTE (N1) |
| proposition_3_2_a | ACCEPT-WITH-NOTE (N1, N2: R8 carrier is not what is encoded; equivalence verified, a.s. only) |
| proposition_3_2_b | ACCEPT-WITH-NOTE (N1, N2) |
| lemma_2_4_leftHull | ACCEPT-WITH-NOTE (N3: unruled left-only split) |
| scaling_leftHull | ACCEPT-WITH-NOTE (N3, N4: L545 typo; hU not needed, but is a source premise) |
| reflection_leftHull | ACCEPT-WITH-NOTE (N3, N4) |

No REJECT. One **required** addition (C1: non-vacuity root for `IsSLEDriver`) and three **required author
acknowledgements** (C2 R8 amendment, C3 R7 extension to Props 3.1/3.2, C4 split ruling for the deterministic lemmas).
No Lean text of any of the 11 statements needs to change.

## Required changes

**C1 (required companion root; vacuity).** Every probabilistic root here (1.8, 1.10, 3.1, 3.2) quantifies over
`IsSLEDriver a b c U P`. If no such driver existed for `a,b>0, c²≤ab`, all of them would be vacuous, and
`IsThinPhase` etc. would be trivially true. AU-M1 called inhabitation "a true fact, not needed for the audit"; for roots
it is needed (same logic as AU-M1 R3 for `exists_admissibleDensity`). Mathlib has `IsBrownianReal`
(`Mathlib/Probability/BrownianMotion/Basic.lean`) but I found no existence theorem there, so this is a real obligation
(external or proved). Replacement (elaborated, scratch b6, only the `sorry` warning):
```lean
theorem exists_sleDriver (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (U : ℝ≥0 → Ω → ℂ), IsSLEDriver a b c U P := by
  sorry
```
Binders: ha, hb, hc RULED R5 / PSD standing; nothing else. This is not a source theorem (the paper takes existence
of complex BM for granted), so it needs an author ruling to be frozen (suggest R13), or it must be recorded as the
`EXTERNAL`/proved existence of planar BM with covariance Σ. Without it, no PROVED claim for the roots below is meaningful.

**C2 (R8, required acknowledgement).** R8/P5 says the carrier is `⨅ t < T_z, infDist z (L t)`. The drafts do not use any
`⨅`; they use the ε-formulations. This is the right call, and the literal `⨅` encoding would be wrong (see N2). Record
the amendment: "R8': `lim_{t→T_z-} dist(z,L_t)=0` is encoded as `∀ ε>0, ∃ t<T_z, dist<ε`; `lim>0` as
`∃ ε>0, ∀ t<T_z, ε ≤ dist`" and fix the docstring wording (the docstring is correct but says "ruling R8"; R8 literally says `⨅`).

**C3 (R7 extension, required acknowledgement).** P4/R7 speaks of Thm 1.8 only. The drafts of Props 3.1/3.2 bind
`p` with `IsAdmissibleDensity a b c p` (every admissible p, as for Thm 1.8). The paper (L1265-1286) says "let (I) be as in
Theorem 1.8", so inheriting the same reading is consistent, but the ruling text should say so explicitly.

**C4 (split ruling).** `lemma_2_4_leftHull`, `scaling_leftHull`, `reflection_leftHull` state only the left-hull
part of paper items that also assert `f_t`, `R_t` (L549-557, L658-666; the paper's item "scaling" includes
`f_t^{rU(·/r²)}(z)=r f_{t/r²}(z/r)` and `R_t`; the reflection item says "the same is true with right hulls"; Lemma 2.4
includes `R_t`). R2 deferred only Lemma 2.6. No ruling R4-R12 authorizes a left-hull-only split. Ask the author to approve:
"the left-hull parts are frozen now as separate anchors; the right-hull/`f_t` parts are separate anchors added when
`g_t`, `R_t` are defined; the source node of Lemma 2.4 / (2.1) / (2.2) is PROVED only when both anchors are".
Until then these three must not be recorded as proving the source items.

## Per-theorem audit (binder bins)

Bin legend: S = SOURCE, ST = STANDING, TY = TYPING, RU = RULED(id), EX = EXCESS. Expanded structures:
`IsAdmissibleDensity` = (Continuous, ≥0, π-periodic, ∫₀^{2π}p=1, ∃x C²-off-x+πℤ ∧ ODE ∧ D·p ∈ C¹): one RU(R7) bundle that
is the R7 text verbatim (checked against ruling P4 and `IsAdmissibleDensity.lean`). `IsSLEDriver` = (cont a.s., U0=0 a.s.,
HasIndepIncrements, law_increment): ST (P3/R6). `IsProbabilityMeasure P`: TY (R12).

### theorem_1_8 (paper.tex:L437-449; R5, R7, R11) ACCEPT
| binder | bin | cite |
|---|---|---|
| a b c | TY | |
| ha : 0<a, hb : 0<b | RU(R5/P2) | ERRATA P2 |
| hc : c²≤ab | ST (PSD) | L301-308 + P3; with a,b>0 equivalent to |c|≤√(ab) |
| p, hp | RU(R7/P4) | "every admissible p" |
Counts: S 0, ST 1, TY 3, RU 3 (ha, hb, p/hp), EX 0.
Conclusion: four implications, signs verified against L441-448: (I≥0,II>0)→thin; (I<0,II>0)→swallowing;
(I<0,II<0)→hitting; (I≥0,II<0)→dense. `integralI/II` are the frozen defs (∫₀^{2π} ν p; ∫₀^{2π}(ν+2cos2u)p), exact.
Quantifier order: parameters, p, then implications; the phases are `∀ Ω P U z, ∀ᵐ` inside the frozen defs, so no
p-dependence on Ω (correct, p depends only on Σ). Strength: same as source+R7; not vacuous (R3 `exists_admissibleDensity`
frozen; C1 for drivers). Split into two anchors loses no shared witness: the c=0 bullet has no p. One note: because `p` is
universal, the theorem implies the signs of (I),(II) are independent of the admissible p (else two phases would hold
a.s. simultaneously, impossible once drivers exist); that is exactly P4's recorded SOURCE_GAP, not an error here.

### theorem_1_8_c_zero (paper.tex:L450, Lemmas 3.11/3.12 L1824-1938; R5, R11/P8) ACCEPT
Binders: a, b TY; ha, hb RU(R5). No hc (c=0 so c²=0≤ab, PSD automatic). EX 0.
Conclusion: thin if a−b≤4; swallowing if 4<a−b<8; hitting if 8≤a−b. Exactly L450. a−b=8 is Lemma 3.12 (L1900-1925), a−b=4
thin per the statement; the three ranges partition ℝ. Implications (not iff, not exclusive), as the source. `IsThinPhase a b 0` etc.
are applied at c=0 where `IsSLEDriver a b 0` uses the PSD matrix `diag(a,b)`.

### theorem_1_10_a (L502-507; R4, R5, R10) ACCEPT
Binders: a b c Ω P U z TY; ha hb RU(R5, AU-M1 R1); hc ST; hU ST; hz : z≠0 RU(R4/P1). EX 0.
Quantifiers: `∀ z ≠ 0` outside `∀ᵐ ω` = "for each z, a.s." exactly (not a.s. for each z). Conclusion:
`∃ t>0, z ∉ L_t ∧ DisconnectsFromInfinity (L_t) {z}`. Matches L506-507 ("there exists t>0 such that z∉L_t and L_t disconnects z
from infinity"); `t : ℝ≥0` with `0<t`; `{z}` is the singleton set and the frozen definition quantifies over unbounded
components of ℂ∖L_t, so `{z}` disjoint from them = z disconnected (checked against Def 1.9, L497-499). Not vacuous: for z with
T_z=∞ the conclusion forces a bounded component containing z.
Note: prose L495 says "a≠b" while Thm 1.10 (L503-504) does not; the theorem governs and the proof (L2199ff) does not use a≠b
(Lemma 3.? `lem-disconnect-2` is for general Σ). Same remark as AU-M1.

### theorem_1_10_b (L508-509; R7) ACCEPT
Binders as 1.10(a) minus z. Conclusion `∀ᵐ ω, ∀ t:ℝ≥0, 0<t → (interior {w | Disconnects (L_t) {w}}).Nonempty` is verbatim P7 text
("a.s., for each t>0" uniform in t; the paper's proof L2224-2230 gets uniformity by monotonicity of L_t). `interior` is in ℂ.
Carry-forward warning (already in ERRATA P7 audit note): the disconnected set includes L_t itself, so (b) does not say ℂ∖L_t
is disconnected.

### proposition_3_1_a / _b (L1265-1270; R4, R5, R7, R12) ACCEPT-WITH-NOTE (C3)
Binders: ha hb RU(R5); hc ST; p/hp RU(R7 extended, C3); hI S ("(I)≥0" / "(I)<0"); hU ST; hz RU(R4). EX 0 (modulo C3).
Quantifier: `∀ z≠0, ∀ᵐ ω` = "for each z∈ℂ∖{0}, a.s." Conclusion (a) `T_z = ∞`, (b) `T_z < ∞` in `ℝ≥0∞`, exact.
Hypothesis order (p, hp, hI before Ω,P,U) is fine; hI mentions only p, a, b, c.

### proposition_3_2_a / _b (L1276-1283) ACCEPT-WITH-NOTE (C2, C3, N2)
Binders as 3.1 with hII in place of hI: (a) `(II)<0`, (b) `0<(II)`. Quantifier `∀ z≠0, ∀ᵐ ω` exact.
Conclusions: (a) `∀ ε>0, ∃ t:ℝ≥0, ↑t < T_z ∧ infDist z (L_t) < ε`; (b) `∃ ε>0, ∀ t, ↑t<T_z → ε ≤ infDist z (L_t)`.
See N2 for the verified equivalence with the paper's limit. Both are stated for all T_z∈[0,∞] as the paper insists (L1285).

### lemma_2_4_leftHull (L658-666) ACCEPT-WITH-NOTE (C4)
`hU : Continuous U` is the source premise (L658 "continuous driving function"). `IsConnected` = Nonempty ∧ preconnected;
nonemptiness is true and proved (`U 0 ∈ leftHull U t` for all t: `absorbingTime U (U 0) = 0`, scratch b2 `abs_U0`, `U0_mem`),
so "connected" in Lean is not stronger than the paper's. Not a typo of "a.s." issue: the proof's "a.s." is T5 (graph note).
The Lean statement is a deterministic ∀U ∀t, as the lemma.

### scaling_leftHull (L549-552, eq. 2.1) ACCEPT-WITH-NOTE (C4, N4)
Elaborated: `leftHull (fun s => ↑↑r * U (s / r ^ 2)) t = (fun z => ↑↑r * z) '' leftHull U (t / r ^ 2)` with `r : ℝ≥0`,
`↑↑r = ((r:ℝ):ℂ)`, `s / r^2` and `t / r^2` division in `ℝ≥0` (r>0, so true division, no junk). Source: `L_t^{rU(·/r²)} = r L_{t/r²}`, r>0. Matches.
**Proved in scratch** (b4, axioms `[propext, Classical.choice, Quot.sound]`, no `sorryAx`) for *every* U, i.e. continuity is
not used: `absorbingTime (r U(·/r²)) (r z) = r² · absorbingTime U z`. So the statement is true, with the premise `hU` merely
copying the source.

### reflection_leftHull (L553-557, eq. 2.2) ACCEPT-WITH-NOTE (C4, N4)
Elaborated: `leftHull (fun s => (starRingEnd ℂ) (U s)) t = ⇑(starRingEnd ℂ) '' leftHull U t ∧ leftHull (fun s => -U s) t = Neg.neg '' leftHull U t`.
`conj ''` is image under complex conjugation, `Neg.neg ''` image under negation on ℂ. Matches L^{U*} = (L^U)*, L^{-U} = -L^U.
**Proved in scratch** (b3, axioms clean) for every U (hU unused).

## Notes

**N1.** See C3. Also: Props 3.1(a)/(b) and 3.2(a)/(b) split of Props 3.1 and 3.2: no shared witness is lost (the only shared
datum is p, bound identically in each).

**N2 (R8 carrier; the main refute attempt).** Facts, all machine-checked in scratch b2 (compiles, no `sorry`):
1. `leftHull U s ⊆ leftHull U t` for `s ≤ t`, for *every* U (literally: `T_z ≤ s ≤ t`). So `L_t` is increasing in the frozen def, no continuity needed.
2. `U 0 ∈ leftHull U t` always (`abs_U0`), so `L_t` is nonempty and `infDist z (L_t)` is a genuine distance (never Mathlib's `infDist z ∅ = 0`).
3. Hence `t ↦ infDist z (leftHull U t)` is `Antitone` (`d_anti`), and `Tendsto d (𝓝[<] T) (𝓝 (sInf (d '' Iio T)))` for finite T and
   `Tendsto d atTop (𝓝 (⨅ t, d t))` for T=∞ (both elaborated). So the limit exists and equals the infimum over `t<T_z`, including T_z=∞.
4. For index set `{t : ℝ≥0 // ↑t < T}` **nonempty** (i.e. T_z>0): `(∀ ε>0, ∃ t<T, d t<ε) ↔ ⨅ t:{t//↑t<T}, d t = 0` (`eq_zero_iff`) and
   `(∃ ε>0, ∀ t<T, ε ≤ d t) ↔ 0 < ⨅ t:{t//↑t<T}, d t` (`pos_iff`). Neither uses monotonicity (monotonicity is only needed to identify the inf with the limit, item 3).
5. **The literal nested form `⨅ t : ℝ≥0, ⨅ (_ : ↑t < T), f t` in ℝ is junk**: for `T=1` and any `f ≥ 0` it equals 0 (`junk`), because
   the inner `⨅` over an empty Prop is `sInf ∅ = 0` for `t ≥ T`. So a swallowing-phase `lim>0` (T_z<∞) could never hold in that encoding. The drafts' ε-form
   avoids this; R8's wording must not be implemented as the nested `⨅` in ℝ (a subtype index or `ℝ≥0∞`-valued `infEdist` is needed).
6. **T_z = 0**: the drafts' (a) is *false* and (b) is *true* (index set empty: `∀ ε, ∃ t<0` fails; `∀ t<0` vacuous), while
   a `⨅` over an empty set gives 0 (a true, b false); a limit `t→0⁻` within `[0,∞)` does not exist. The paper says nothing at T_z=0.
   This is harmless for the stated theorems because T_z>0 a.s. for z≠0: `T_z = 0` iff `z = U 0` (⇐ `abs_U0`; ⇒ Peano local existence for
   `γ' = 2/(γ−U)` near `(0,z)` with `z≠U 0`, U continuous), and `U 0 = 0 ≠ z` a.s. So the two encodings agree a.s., and the drafts' statements are
   equivalent to the R8 carrier on the a.s. event. Mathematical proof burden: T_z>0 a.s. is a (routine) proof step inside the roots, not a premise.
7. T_z=∞: index set is all of ℝ≥0, nonempty; everything above applies.
Verdict: equivalence verified (a.s.; exact for T_z>0); the drafts are preferred over the literal R8 carrier. Needs C2.

**N3.** See C4.

**N4 (L545 typo).** `paper.tex:L545` says `U : [0,∞) → ℝ`, but the same paragraph defines `L^{U*}` and uses Def 1.1 (complex driving function) and
Lemma 2.4 says `U : [0,∞)→ℂ`; with U real, (2.2) would be vacuous and (2.1) would not be the SLE scaling. It is a typo for ℂ. Add as a graph note (T7).
Premise `Continuous U` in (2.1)/(2.2) is a source premise (L545 "continuous"), unnecessary for the truth (I proved both without it), accepted because
removing a premise of the source is also a change of statement; the author may prefer to freeze the stronger no-hypothesis form; if so both are fine.

## Source results in range that should be (or may be) in the batch
- `Lemma 3.11` (L1824, c=0, a−b>8) and `Lemma 3.12` (L1900ff, a−b=8): covered by `theorem_1_8_c_zero` (R11/P8); fine as graph nodes below the root.
- Missing: **C1** driver existence (not a numbered result).
- Deferred (need `g_t`/`R_t`): concatenation property (2.3) (L558-570), duality (2.4), right-hull halves of (2.1), (2.2), Lemma 2.4, `f_t`-part of (2.1). See C4.
- `lem-scaling` (L774), `lem-endpt-cont` (L666ff): outside the listed ranges; not audited.
- Left hulls increasing (L277: "by definition L_s ⊂ L_t") is a trivial lemma (`leftHull_mono`, proved in b2), needed by Thm 1.10(b) proof; not a root.

## Commands run and outputs
All with `export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"; cd /home/ewain/complex-sle`; canonicalize/getpwuid warnings filtered.
1. `lake env lean .lake/probes/M2Roots.lean` -> warnings `declaration uses sorry` at lines 22, 31, 41, 50, 64, 72, 80, 89, 101, 106, 113 (11); no errors.
2. `.lake/probes/audit2/b1.lean` (elaboration): `leftHull (fun s => ↑↑r * U (s / r ^ 2)) t = (fun z => ↑↑r * z) '' leftHull U (t / r ^ 2) : Prop`;
   `leftHull (fun s => (starRingEnd ℂ) (U s)) t = ⇑(starRingEnd ℂ) '' leftHull U t ∧ leftHull (fun s => -U s) t = Neg.neg '' leftHull U t : Prop`.
3. `b2.lean`: compiles, no errors, no `sorry` (only style linter warnings): `abs_U0`, `U0_mem`, `leftHull_mono`, `d_anti`, `junk`, `eq_zero_iff`, `pos_iff`,
   `Tendsto` examples, T=0 counterexample.
4. `b3.lean`: `reflection_leftHull` proved; `#print axioms` -> `[propext, Classical.choice, Quot.sound]`.
5. `b4.lean`: `scaling_leftHull` proved (+ `abs_scale`); `#print axioms` -> `[propext, Classical.choice, Quot.sound]`.
6. `b6.lean`: `exists_sleDriver` statement elaborates (one `sorry` warning).
Scratch proofs b2/b3/b4/b6 copied to
`/tmp/claude-636356804/-home-ewain/a85056b9-2799-4efd-8570-39a1fdaca1a1/scratchpad/au2/` (outside the project; usable as proof seeds for the left-hull deterministic roots,
b2's `junk` is only an audit artifact). `.lake/probes/audit2/` deleted at the end.
