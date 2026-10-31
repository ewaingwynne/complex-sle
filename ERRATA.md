# Errata and author rulings

Source: `paper.tex` = `source/arxiv-2203.07313v4/complex-sle-final.tex` (sha256 6f182d3a…).

## Rulings

- R1 (2026-10-30) External inputs: relative-to-externals (PLAN.md §7 option (a)).
- R2 (2026-10-30) Scope: skip §2.4, §5, Remarks 1.3/1.6/1.11, footnote 2; Lemma 2.6 deferred.
- R3 (2026-10-30) GitHub: private `ewaingwynne/complex-sle`, push at each milestone.

- R4–R12 (2026-10-30) The author approved proposals P1–P9 below, as amended by audit AU-M1,
  together with the carrier declarations in the M1 probe (definitions, `loewner_wellDefined`,
  `exists_admissibleDensity`). P1→R4, P2→R5, P3→R6, P4→R7, P5→R8, P6→R9, P7→R10, P8→R11, P9→R12.

- R13 (2026-10-30) Adopt the non-source root `exists_sleDriver` (for a, b > 0, c² ≤ ab, some
  probability space carries an SLE_Σ driver), so the probabilistic roots are not vacuous
  (audit AU-M2 C1). Its proof may consume an external input for the existence of Brownian motion.
- R14 (2026-10-30) Amends R8: lim_{t→T_z−} dist(z, L_t) = 0 is encoded as
  `∀ ε > 0, ∃ t < T_z, infDist z (L t) < ε`, and lim > 0 as `∃ ε > 0, ∀ t < T_z, ε ≤ infDist z (L t)`
  (AU-M2 C2). The literal ℝ-valued nested ⨅ equals 0 whenever T_z < ∞; the ε-forms agree
  with the limit whenever T_z > 0, which holds a.s. for z ≠ 0.
- R15 (2026-10-30) R7 extends to Props 3.1 and 3.2: they hold for every admissible p (AU-M2 C3).
- R16 (2026-10-30) Lemma 2.4, (2.1) and (2.2) are split, and their left-hull parts frozen now. The
  right-hull and f_t parts are frozen once g_t is defined. Each source node counts as proved only
  when all of its parts are proved (AU-M2 C4).

- R17 (2026-10-30) Splits approved with the M2 batch: Thm 1.8 → `theorem_1_8` + `theorem_1_8_c_zero`;
  Thm 1.10 → (a), (b); Prop 3.1 → (a), (b); Prop 3.2 → (a), (b). They are independent anchors: no
  witness or constant is shared across them.
- R18 (2026-10-30) P11 accepted: the third formula of (2.3) reads f_t(L_{s+t} ∖ L_t) = L_{t,s+t} ∖ R_t
  (typo T8).
- R19 (2026-10-30) P12 accepted: in Lemma 2.16 with c = −√(ab), choose x with tan x = sgn(c)·√(b/a), so the
  recurrence point is e^{2ix} as printed (typo T9).
- R20 (2026-10-30) P10 resolved: the two-scale construction of U^± and E_1(δ) proposed below replaces the
  printed choice at L2163-2169 in the proof of Lemma 4.1. The statement of Lemma 4.1 and the Thm 1.10 anchors
  are unchanged.
- R21 (2026-10-30) The author approved, as written, the definitions `loewnerMap` (g_t on ℂ∖L_t, by unique
  choice from `loewner_wellDefined`), `centeredLoewnerMap` (f_t = g_t − U_t) and `rightHull` (R_t = complement of
  the range of f_t), with the characterization theorems `loewnerMap_eq` and `loewnerMap_exists_solution`, as one
  semantic unit (pre-approval review: reviewer-M4-gt/sonnet). The two characterizations are separate (not split) exports.
- R22 (2026-10-30) The author approved, as written, the remaining R16 parts: `scaling_centeredLoewnerMap`,
  `scaling_rightHull` ((2.1)), `reflection_rightHull` ((2.2)), `lemma_2_4_rightHull` (Lemma 2.4), and
  `reflection_centeredLoewnerMap` (reflection for the maps f_t, which the source uses at L984/L1165 but states only for
  hulls; resolves that ERRATA modeling question). Pre-approval review: reviewer-M4-R/sonnet.
- R23 (2026-10-30) EXTERNAL batch 1 approved as written (pre-approval review: reviewer-M5-ext1/sonnet):
  `External.exists_isBrownianReal` (ext:bm-existence), `External.support_sleDriver` (ext:bm-support, E13; any PSD Σ),
  `External.loewnerMap_conformal` (ext:lawler-4.5), `External.loewnerMap_tendstoUniformly` (ext:loewner-convergence,
  E12; the source's K_T read as L_T). Graph externals ext:dct, ext:martingale-convergence and ext:picard-lindelof are
  supplied by Mathlib and get no EXTERNAL file.
- R24 (2026-10-30) Stochastic externals (Itô, Lévy characterization, strong Markov, Girsanov, Hörmander, Blumenthal,
  Kolmogorov 0-1, Birkhoff, …) are stated in martingale / law form using only Mathlib notions (filtrations, stopping
  times, `Martingale`, conditional expectation, `HasLaw`, independence); no stochastic integral is built in-project.
- R25 (2026-10-30) EXTERNAL batch 2 approved as drafted (reviews reviewer-M5-ext2/sonnet, then reviewer-M5-ext2b/sonnet
  after fixes): definitions `pathIntegral`, `IsContLocalMartingale`, `IsSLEDriverAdapted` (everywhere-continuous paths),
  `IsDiffusionSolution`; externals `strongMarkov_sleDriver`, `blumenthal_sleDriver`, `birkhoff_stationary`,
  `recurrence_stationary`, `scale_function_hit` (with "drift bounded above near l", truncated exit times),
  `koebe_quarter`, `koebe_distortion`, `ito_formula`, `levy_characterization`, `dambis_dubins_schwarz`,
  `timeChange_isContLocalMartingale` (σ 0 = 0), `girsanov_law_equiv` (bounded h), `hormander_oneDim`. Kolmogorov 0-1 is
  Mathlib-supplied (no file). This completes the graph's external boundary.
- R27 (2026-10-30, M6 packet) P13 fix approved: the Girsanov step in Prop 3.2(b) and Thm 1.10(a) is replaced by the hitting
  lemma ("Proposed fix for P13" below); Λ' is a single point and `girsanov_law_equiv` is no longer consumed.
- R28 (2026-10-30, M6 packet) Prop 1.5 frozen as the pathwise coupling `sle_duality` (hypotheses a, b ≥ 0, c² ≤ ab, t > 0;
  driver Ũ(s) = i(U((t−s)⁺) − U t) + i(U(max s t) − U t), the opposite sign to the paper's (2.4) driver, needed pathwise).
- AUTO-1 and T12 confirmed by the author (M6 packet).
- R26 (2026-10-30) Approval policy: the author delegates approval of mechanical companions, literal source
  transcriptions (two fresh ACCEPT reviews) and unambiguous typos to the orchestrator (`AUTO-n` items, retroactive
  veto); EXTERNAL inputs, modeling choices, P-item corrections and scope changes are batched into one approval packet
  per milestone; milestones roll over without a question. Full text: CLAUDE.md "Approvals (ruling R26)".

### Auto-approved items (R26; author may veto retroactively)

- AUTO-1 (2026-10-30, M6) Concatenation property (2.3) frozen as four DRAFT_SORRY anchors in the R21/R22 pattern
  (one per formula; third formula read per R18): `concatenation_centeredLoewnerMap`, `concatenation_leftHull`,
  `concatenation_image_leftHull`, `concatenation_rightHull`. Two independent ACCEPT reviews
  (reviewer-M6-conc-1/sonnet, reviewer-M6-conc-2/sonnet), who also checked the four together are equivalent to (2.3).

## Rulings P1–P9 (approved 2026-10-30 as R4–R12)

Each item gives the problem, where it is, and the **proposed ruling**. "Substantive" items
change what a frozen statement says. "Typo" items only affect graph notes.

### Substantive

**P1. The point z = 0 in Def 1.7 and Thm 1.10(a).** `paper.tex:L409-417, L502-511`.
With U₀ = 0 the ODE is singular at z = 0, so T₀ = 0 and 0 ∈ L₀. Taken literally with
"for each z ∈ ℂ", the thin phase fails at z = 0 (0 ∈ ⋃ L_t), the hitting phase fails at
z = 0 (⋃_{t<0} L_t = ∅), and Thm 1.10(a) fails at z = 0 (0 ∈ L_t for all t). Props 3.1 and
3.2 already say z ∈ ℂ∖{0}.
**Proposed:** Def 1.7 and Thm 1.10(a) quantify over z ∈ ℂ∖{0}.

**P2. Degenerate Σ (ab = 0) in Lemma 2.13 and Thm 1.8.** `paper.tex:L941-955, L1086-1135`.
When ab = 0 we have c = 0 = √(ab), so Case 2 applies. But tan x = √(b/a) is undefined for
a = 0, and the proof needs µ(x) = −4√(ab)/(a+b) ≠ 0 (the L'Hôpital limits (2.32)–(2.33),
and the Hörmander condition µβ′ ≠ 0 in Lemma 2.14). With ab = 0 we get µ(x) = 0, and θ = x
is a fixed point of the SDE (the real axis when b = 0, the imaginary axis when a = 0), so
the construction breaks down. Σ = 0 is trivially degenerate as well. The c = 0 part of
Lemma 3.11 explicitly uses "a, b > 0" (L1851-1856).
**Proposed:** Lemmas 2.13, 2.14, 2.16, Props 3.1, 3.2 and Thm 1.8 (both parts) assume
a > 0 and b > 0. The classical case b = 0 (SLE_a) and the reverse case a = 0 < b are out of scope; this is a scope reduction relative to the literal Thm 1.8, which includes them. Thm 1.10 ("a, b ≠ 0") is frozen with 0 < a, 0 < b, which is equivalent under PSD; the draft's a ≠ 0, b ≠ 0 admitted a = b = −1, where the Gaussian law degenerates to a point mass (audit AU-M1, R1). (Audit addition: at Σ = 0 the c = 0 bullet of Thm 1.8 is false, since U ≡ 0 and z = i give T_z = 1/4.)

**P3. Def 1.4 does not make (B, B̃) jointly Gaussian.** `paper.tex:L301-308`.
"B, B̃ standard BMs with Cov(B_t, B̃_t) = ct/√(ab)" does not say that (B, B̃) is a
two-dimensional BM, and ct/√(ab) is 0/0 when ab = 0. §2.4 (L819ff) and the proofs use the
intended meaning: (Re U, Im U) is a planar BM with covariance Σ.
**Proposed:** positive semidefiniteness of Σ (0 ≤ a, 0 ≤ b, c² ≤ ab) is a standing assumption of every theorem. SLE_Σ is driven by U : ℝ≥0 → Ω → ℂ with a.s. continuous paths, U₀ = 0,
independent increments, and U_t − U_s ~ N(0, (t−s)Σ) on ℂ ≅ ℝ² for s ≤ t. The
representation U = √a B + i√b B̃ (when ab > 0) becomes a lemma.

**P4. Which p Thm 1.8 refers to.** `paper.tex:L428-453`, footnote 1, and Lemma 2.14
(L963-967). Eq. (1.11) says "2π-periodic". Lemmas 2.13 and 2.14 say π-periodic, and the
uniqueness of p is not proved.
**Proposed:** Thm 1.8 reads "for **every** p that is admissible in the sense of Lemma 2.14
(continuous, ≥ 0, π-periodic, ∫₀^{2π} p = 1, C² and solving (2.24) off x + πℤ for some x,
D·p ∈ C¹(ℝ)), the four sign implications hold", together with the existence of such a p
(Lemma 2.13). Footnote 1 asserts exactly this generality. The graph will carry an explicit
step "every admissible p vanishes only on a Lebesgue-null set", which Lemma 3.3 needs and
which Lemma 2.14's hypotheses do not state (SOURCE_GAP). The weaker alternative "∃ p from
Lemma 2.13 such that …" is available if you prefer it.

Companion root (audit R3): Lemma 2.13's existence part, `∃ p, IsAdmissibleDensity a b c p` for a, b > 0 and c² ≤ ab, is frozen together with Thm 1.8 so that Thm 1.8 cannot be vacuous. π-periodicity (not 2π) is kept, because Lemma 2.14's proof uses it (−z has the same law as z).

**P5. The meaning of lim_{t→T_z−} dist(z, L_t).** `paper.tex:L1276-1286`.
L_t is increasing, so t ↦ dist(z, L_t) is non-increasing and the limit always exists,
including when T_z = ∞. L_t ∋ U₀ is nonempty, which avoids Mathlib's `infDist z ∅ = 0`.
**Proposed:** the carrier is `⨅ t < T_z, infDist z (L t)` (inf over real t with t < T_z).

**P6. Lemma A.1's normalization, and the sign constraint on α.** `paper.tex:L2318-2330`.
A.1 normalizes ∫₀^π p = 1 and samples X₀ ~ p·1_{[0,π]}, whereas Lemma 2.14 uses ∫₀^{2π} p = 1
(it is applied with p ↦ 2p). A.1 also states α, β : ℝ → [0,∞), but the drift µ changes sign
and β = √a sin ∓ √b cos takes both signs.
**Proposed:** α, β : ℝ → ℝ, and the application in Lemma 2.14 uses 2p (an explicit graph step).

**P7. Thm 1.10(b) uniformity.** `paper.tex:L508-509`. "Almost surely, for each t > 0" is
uniform in t (the proof uses monotonicity of L_t).
**Proposed:** freeze it as `∀ᵐ ω, ∀ t > 0, (interior {z | L_t disconnects z from ∞}).Nonempty`.

Audit note: by Def 1.9 the points of L_t themselves count as disconnected from ∞, so (b) does not by itself say that ℂ∖L_t is disconnected (the prose at L513 and L1950 suggests more). Downstream nodes must not use (b) that way.

**P8. Thm 1.8's c = 0 bullet vs. Lemmas 3.11/3.12.** "Hitting if a − b ≥ 8" is Lemma 3.11
(a − b > 8) plus Lemma 3.12 (a − b = 8), so the two are consistent.
**Proposed:** one frozen c = 0 theorem with three conclusions (thin / swallowing / hitting),
for a, b > 0 (see P2).

**P9. "SLE_Σ is in phase X" quantifies over probability spaces.**
**Proposed:** "for every probability space (Ω : Type, P) and every driving process U as in
P3 …". Ω is in universe 0 (Type). Statements are about a.s. events, and a.s. is read as
"the complement is P-null", so no measurability of the event is presupposed.

### Open (found during M3; awaiting the author)

**P10. Lemma 4.1's sets U^± cannot be at distance ≥ 2ε from the imaginary axis.** `paper.tex:L2163-2167`
(proof of Lemma 4.1, found by reviewer-D and confirmed by the orchestrator). With the zero driver
f_T(z) = √(z² + 4T), x = 2C (Lemma 4.4) and T > y²/2 = 24.5C², the preimage of B_{ε/2}(x ± 2iε)
has |Re z| ≈ 2Cε/√(T − C²) ≤ 0.42ε (numerically 0.577ε at C=1, T=13; 0.41ε at T=24.6). So no
U^± with both required properties exists, and U^± lies inside the ε-neighbourhood of iℝ, where L_T
may be. The argument needs a repair (for example, take U^± ⊂ ℂ∖L_T directly from the event E_1, or
change how ε and the neighbourhood of L_T are chosen). It is recorded as a SOURCE_GAP on
`step:disc-setup`. **Needed from the author:** a corrected argument, or a ruling on how to model it.

**Fix for P10, approved as R20 (two scales; the statement of Lemma 4.1 is unchanged).** Keep x < y, ε and K from Lemma 4.4
as in the paper, with also ε < x/2, and fix T > y²/2. Let φ_T(z) = √(z² + 4T) be the zero-driver map (the branch
~ z at ∞) and set U^± := φ_T^{-1}(B_{ε/2}(x ± 2iε)). The closed balls miss ℝ and iℝ, so the closures of U^± are
compact subsets of {Re z > 0}, and η := dist(U^+ ∪ U^-, iℝ) > 0 is deterministic (η ≈ 1.5Cε/√(T−C²)).
Set δ := min(η/2, ε/2, (2√T − y)/2) and replace E_1 by E_1(δ), which is E_1 with δ in place of ε in its first
three clauses (L_T, R_T and the uniform approximation of f_T); the crossing of [x,y]×[−ε,ε] is kept.
P(E_1(δ)) > 0 by Lemma 4.3 at scale δ, and E_1(δ) is still F_T-measurable. Then U^± ∩ L_T = ∅,
f_T(U^±) ⊂ B_{ε/2+δ}(x ± 2iε) ⊂ B_ε(x ± 2iε) ⊂ B_{3ε}(x) ∖ R_T, and E_1(δ) implies the printed E_1,
so the rest of the proof goes through verbatim. The bound δ < 2√T − y gives the R_T point with Re ≥ y that the
crossing argument needs; the paper leaves the same condition on ε implicit. (Proposed by the orchestrator;
η > 0, quantifier order and the downstream uses were checked by a fresh Sonnet reviewer, verdict HOLDS_WITH_CAVEATS,
with both caveats folded in above.)
The same review noted gaps that predate the fix and are already modeled as SOURCE_GAP steps: the choice of ε and K
in E_2/E_3 from Lemma 4.4, the uniformity argument in Lemma 4.3, "by topological considerations" (L2194), and the
transfer through concatenation (2.3)/R18.

**P11 (T8; accepted as R18). The third formula of (2.3) as printed.** `paper.tex:L556-565`.
f_t(L_{s+t} ∖ L_t) = L_{t,s+t} cannot hold, since f_t maps ℂ∖L_t onto ℂ∖R_t and 0 ∈ R_t ∩ L_{t,s+t}.
**Proposed:** read it as f_t(L_{s+t} ∖ L_t) = L_{t,s+t} ∖ R_t, which agrees with the second formula
(found by global-reviewer, confirmed by global-verifier).

**P12 (T9; accepted as R19). Lemma 2.16 for c = −√(ab).** `paper.tex:L1155-1163`. When c = −√(ab), D vanishes on
−x + πℤ, so the argument proves recurrence at e^{−2ix} rather than e^{2ix}.
**Proposed:** in the critical case, choose x with tan x = sgn(c)·√(b/a). Downstream (Lemma 3.4) only needs some
deterministic recurrent point, so nothing else changes (found by global-verifier, checked by the orchestrator).

**Further open modeling questions from the global reviews** (graph/reviews/global.review.md §6), currently
modeled as SOURCE_GAP steps:
- (2.2) is used for the maps f_t and not only the hulls (L984, L1165).
- Right-hull connectedness and (2.4) enter the Thm 1.10 closure as ordinary nodes.
- An admissible p vanishes only on a null set (needed by Lemma 3.3, under R7/R15). **Resolved in M7 (proved, not a ruling):** every admissible p is positive off a countable set, in particular off a null set (`Internal/Phases/AllZPositivity.lean`, PROVED).
- Lemma 3.4's Markov state: the diffusion coefficients are only 2π-periodic in θ̂.
- The independence claim in Lemma 3.10.
- T_z < ∞ in Lemma 3.12.
- The product-space extension for the random point 𝐳 (Props 3.1/3.2 over arbitrary Ω).
- The new external `ext:kolmogorov-zero-one`.

**P13 (resolved by R27; found in M5). Girsanov steps in Prop 3.2(b) and Thm 1.10(a).** `paper.tex:L1799-1802` and the reuse
in the proof of Thm 1.10(a). The paper infers P(τ < ∞) > 0 "from the SDE and Girsanov's theorem". The drift ratio
h = µ/√(2D) is bounded only when c² < ab, so in the critical case c² = ab Girsanov does not apply as used; and even
for c² < ab the argument that the driftless diffusion hits the target set with positive probability is not given.
Both are SOURCE_GAP steps in the graph (step:prop-ii-b-hit-lambda-prime, step:disc-a-hit-Lambda); the external
`girsanov_law_equiv` covers only bounded h. **Needed from the author:** an argument for the critical case (e.g. a
localisation or a direct comparison), or a ruling on how to treat it.

**Fix for P13, approved as R27 (no Girsanov).** Reviewed by p13-reviewer/sonnet:
HOLDS_WITH_CAVEATS, with every caveat folded in below. Replace the Girsanov step by a hitting lemma for θ̂.
- *Lemma (hitting levels).* Let a, b > 0, c² ≤ ab and c ≥ 0. For c < 0 apply the symmetry θ ↦ −θ, c ↦ −c, under
  which µ_c(−u) = −µ_{−c}(u). Then θ̂ started at any y hits every level θ* < y with positive probability. If c² < ab
  it also hits every level θ* > y.
- *Proof, c² < ab.* Let S' = exp(−∫ µ/D). Then µS' + DS'' = 0, so S(θ̂) is a local martingale (Itô, martingale form).
  D ≥ d₀ > 0, so the exit time from [θ*, y+1] is a.s. finite. Optional stopping gives
  P(exit at θ*) = (S(y+1) − S(y)) / (S(y+1) − S(θ*)) > 0. The same holds for upper levels.
- *Proof, c = √(ab).* D vanishes exactly on x + πℤ, with double zeros, and µ(x) = −4√(ab)/(a+b) < 0. Let
  I_n = (x + (n−1)π, x + nπ). Three facts are needed:
  (1) Inside I_n the upper endpoint is unattainable, since S(u⁻) = +∞. The lower endpoint is hit with positive
      probability: S(l⁺) is finite, as at L1210-1223. The exit time is finite because µ ≤ −m/2 near l gives
      E[exit] ≤ 2ε₀/m. The paper does not state this finiteness for ω(R) at L1226; the same bound covers it.
  (2) A degenerate level x + jπ is left downward immediately: the diffusion coefficient is Lipschitz and vanishes
      there, the drift is negative, and the occupation time of the level is 0.
  (3) Chaining. If y and θ* lie in the same I_m, go directly through the scale function on (θ*, x + mπ). Otherwise
      pass through the degenerate levels between them one at a time, using (1) and (2) and the strong Markov property
      at a small positive time after each level. Then finish on (θ*, x + mπ).
- *Correction to Prop 3.2(b), L1801-1802, and Thm 1.10(a), ≈L2205-2207.* Λ ≠ ∅ because E q(𝐳) > 0. Pick θ* with
  e^{iθ*} ∈ Λ and θ* < arg z (θ* > arg z if c < 0). Take Λ' := {e^{iθ*}}. By the lemma θ̂(z) hits θ* with positive
  probability, so P(τ < ∞) > 0. The rest is unchanged. Positive Lebesgue measure of Λ is no longer needed beyond
  Λ ≠ ∅, and the external `girsanov_law_equiv` is no longer consumed.
- *Adjacent (modeling question, not part of P13).* The step "find τ with P(e^{iθ_τ} ∈ Λ) ≥ q" in Lemma all-z
  (≈L1319) is one-sided at degenerate points in the critical case. It uses no Girsanov.

### Typos (graph notes only)

- T1 Lemma 2.6 proof `paper.tex:L732`: "f_t = f_{s,t} ∘ f_s|_{L_t}" should be "f_s|_{ℂ∖L_t}".
- T2 Lemma 3.4 `paper.tex:L1341`: "E(f⁰(X₀⁰))" should be "E(f⁰(X₀))".
- T3 Lemma 4.4 proof `paper.tex:L2138`: "ℜf₁(x) ≤ −C, ℜf₁(y) ≥ C" should be ℜf₂.
- T4 Fig. 8 caption `paper.tex:L1653`: "s = σ(s+t) − σ(s)" should be "− σ(t)".
- T5 Lemma 2.4 proof `paper.tex:L658-666`: "a.s." in a deterministic lemma. The step
  "f_t ∘ L homotopic to L in ℂ∖{0}, hence the region bounded by L misses L_t" is a sketch
  and will be a SOURCE_GAP step node.
- T7 §2.1.1 `paper.tex:L545`: "U : [0,∞) → ℝ" should be "→ ℂ".
- T10 Lemma 4.3 `paper.tex:L1995`: "[−2T^{−1/2} i, 2T^{1/2} i]" should be "[−2T^{1/2} i, 2T^{1/2} i]".
- T11 §2.1 `paper.tex:L281`: "lim_{t→∞} z(g_t(z) − z) = 2t" should be "lim_{z→∞}".
- T12 Lemma A.1 `paper.tex:L2321`: "α, β : ℝ → [0,∞)" should be "→ ℝ" (µ and √a sin − √b cos change sign). AUTO (R26).
- T6 Lemma 4.3 `paper.tex:L1991-2030`: [Law05, Prop 4.43] "extends to ℂ by replacing ℍ by
  ℂ". This is an external input whose extension is asserted, not proved (SOURCE_GAP, and
  part of E12).
