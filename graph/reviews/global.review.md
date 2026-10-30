# Global root-closure review

REVIEWER: global-reviewer/sonnet
SCOPE: all 14 roots of DEPGRAPH.md (282 node records, 767 EDGE lines, 303 coverage items; `GRAPH_VERSION: 4`), reviewed against the whole source `source/arxiv-2203.07313v4/complex-sle-final.tex` (L225-L2406 read in full, comment blocks excluded), ERRATA.md (R1-R17, P10, T1-T7), graph/EXTRACTION_SPEC.md, graph/anchor-table.md, frozen-anchor-manifest.json (identity fields only), the statement text of the 14 root files and of the frozen definition files under ComplexSLE/Frozen/, DEPGRAPH.md, DEPGRAPH_COVERAGE.md, and the four slice reviews (context only). I did not read ComplexSLE/Internal/, proof bodies, sorry/axioms, STATUS.md or Lean status, I did not run Lean, and I edited no file other than this report. (While comparing manifest identity fields I printed the manifest `state` column once by mistake; I did not use it.)
MECHANICAL CHECKS (own script over the merged files): every DEPS id resolves; DEPS equals the EDGE-target set for every record (no ROUTES exist); no cycle; every node reaches a root (no unreachable nodes); all 31 anchor records match anchor-table.md and the manifest (anchor id, path, export, ABI hash, contract id and version) and `FROZEN_MANIFEST` equals the sha256 of frozen-anchor-manifest.json (2828acc4...ef3ed); every non-anchor has all four `FROZEN_*` fields equal to `-`; each of the 31 anchor definitions is consumed by some node; every node appears in a coverage item and every coverage reference resolves. Source line coverage of L225-L2406 by coverage items has no mathematical gap (the uncovered lines are blank, figure, caption, `comment` blocks or expository sentences already inside node ranges).
TALLY: roots 6 PASS / 8 FAIL (every FAIL is repairable by the fixes below except the P10 block on the two Theorem 1.10 roots); reviewer/orchestrator-authored records: nodes 5 PASS / 3 FAIL, coverage items 15 PASS / 0 FAIL; 33 fixes (F1-F33), of which 4 new nodes, 5 new or replaced coverage items.

## 1. Root-by-root verdicts

For each root I reconstructed the four source-statement fields (SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION, CONSTANT_SCOPE) directly from the source as modified by the rulings, compared them with the record and with the frozen statement, then traced the closure backward.

### defn-loewner.well-defined -- PASS
- Fields (source L251-L268, Def 1.1, absorbing time; rulings none): U continuous; quantified over U and z; conclusion 'the IVP has a solution on [0,T_z) and two solutions on a common [0,tau) agree'. The frozen `loewner_wellDefined` states exactly this (existence on `[0,absorbingTime U z)`, uniqueness on `{t | 0 <= t and ofReal t < tau}`). The record matches. The limit |f_t(z)| -> 0 stated in the same sentence (L268) is correctly kept out (lem-endpt-cont).
- Closure: solution predicate, absorbing time, local existence/uniqueness (Picard-Lindelof, external), global uniqueness, gluing to [0,T_z). The source gives no proof at L268; all three steps are SOURCE_GAP, which is the right modeling. The case z = U_0 (T_z = 0, empty interval) is mentioned.

### lem-p.exists -- PASS
- Fields (L941-L955, Lemma 2.13; R5, R7, R9): a,b > 0, c^2 <= ab; exists p admissible in the sense of Lemma 2.14 (pi-periodic, int_0^{2pi} p = 1, C^2 off x + pi Z, ODE (2.13), D p in C^1). Frozen `exists_admissibleDensity` matches. The 'positive off a discrete set' and 'stationary argument process' parts of Lemma 2.13 correctly sit in `lem-p`, not in the root (R7).
- Closure: WLOG c >= 0 (L1026, with p~(u) = p(-u): I checked mu~(u) = -mu(-u), D~(u) = D(-u) and that -[mu~ p~]' + [D~ p~]'' is the reflection of the original equation), Case 1 (L1029-L1088), Case 2 (L1091-L1110). The normalization int_0^{2pi} p = 1 is explicit in Case 1 (constant k) and a SOURCE_GAP in Case 2 (a positive multiple suffices; correctly flagged). The record notes that p_1 >= 0 only on [0,pi] (used there) and the singular prefactor at a = b, c = 0. Carriers: pi-periodic p, integral over [0,2pi] (R9) consistent.

### nonsource.exists-sle-driver -- PASS
- Fields (R6, R13; L301-L308): a,b > 0, c^2 <= ab; exists a probability space and a planar BM U with covariance Sigma. Frozen `exists_sleDriver` matches (Omega : Type). Closure: defn-sle (driver structure, Gaussian law, covariance matrix) and the external existence of planar BM (`ext:bm-existence`). Nothing else is needed.

### thm-phases -- FAIL (repairable: F8-F20, F22-F24 touch its closure)
- Fields (L437-L449; R4, R5, R7, R15, R17): a,b > 0, c^2 <= ab, every admissible p; the four sign implications with exactly the strict/non-strict signs of L445-L448 ((I) >= 0 and (II) > 0 thin; (I) < 0 and (II) > 0 swallowing; (I) < 0 and (II) < 0 hitting; (I) >= 0 and (II) < 0 dense). The record and the frozen `theorem_1_8` agree. The phase predicates quantify over all probability spaces, drivers and z != 0 (R4, R9), carried by the four phase definition anchors.
- Assembly (`thm-phases#assembly-sign-cases`) is a SOURCE_GAP and correctly so: the translation from (T_z, lim dist) to the closure statements of Def 1.7 is not written. I checked the four translations: thin = T_z = infinity (Prop 3.1a) plus epsilon <= inf dist for all t (Prop 3.2b); swallowing = T_z < infinity plus the positive lower bound; hitting = T_z < infinity plus 'for every epsilon some t < T_z with dist < epsilon' (so z in the closure of the union); dense = T_z = infinity (so z not in any L_t = {T <= t}) plus the closure statement. Each uses the same (omega, z), so intersecting the two a.s. events is legitimate.
- Why FAIL: the closure runs through Props 3.1/3.2, which inherit defects of premise supply: the argument-process WLOG (G3, F9-F11), the map-level reflection in the stationarity proof (G2, F8, F12), the sigma-domain circularity (G6, F18-F20), the product extension (G7, F13-F17), spurious lem-p edges (G8, F22-F24). None changes the statement fields.

### thm-phases.c-zero -- FAIL (repairable: F21, plus F8-F20, F22-F24 through Lemma 3.11)
- Fields (L450; P8, R5, R17): a,b > 0; thin if a-b <= 4, swallowing if 4 < a-b < 8, hitting if a-b >= 8; does not mention p. Record and frozen `theorem_1_8_c_zero` agree. The Lean statement has no c (c = 0 is built into the phase predicates), consistent with L450.
- Closure: Lemma 3.11 (a-b <= 4, 4 < a-b < 8, a-b > 8) plus Lemma 3.12 (a-b = 8) gives a-b >= 8; Lemma 3.12 correctly acquires T_z < infinity from Prop 3.1b via (I) = -2 int cos(2u) p du < 0, which the source never states (SOURCE_GAP, a good catch). I verified the c = 0 algebra: D = (a+b+(b-a) cos 2u)/4, mu - D' = -2 sin 2u, so p_0 = (a+b+(b-a) cos 2u)^{4/(b-a)} (exp((4/a)cos^2 u) for a = b); nu = (2-a/2+b/2) cos 2u, nu + 2cos 2u = (4-a/2+b/2) cos 2u.
- Why FAIL: (a) `step:c0-explicit-density` states the explicit formula for every admissible p (G9, F21), a claim the source does not make; the root only needs the constructed p. (b) The sign-case assembly it consumes inherits the Props defects (above).

### thm-disconnects.a -- FAIL (author-blocked: ERRATA P10; also F1-F6, F27-F30)
- Fields (L502-L507; R4, R5 audit): a,b > 0, c in [-sqrt(ab), sqrt(ab)]; for each z != 0, a.s. exists t > 0 with z not in L_t and L_t disconnects z from infinity (Def 1.9). Matches frozen `theorem_1_10_a` (including `0 < t` and `DisconnectsFromInfinity (leftHull ..) {z}`). Quantifier order forall z, a.s., exists t is correct.
- Closure: Lemma 4.1 (positive-probability disconnection of a fixed open set), then the argument 'very similar to Prop 3.2(b)' (L2200-L2217) modeled by explicit step:disc-a-* nodes, plus the reused concatenation transfer. The modeling of 'exactly as in Prop 3.2(b)' as an inequality (not an equality) is correct and well argued.
- Why FAIL: (1) the proof of Lemma 4.1 contains the refuted construction of U^+- (P10, §5); the graph records a SOURCE_GAP that understates a false step (F27-F30). (2) `step:right-hull-connected` (reviewer-D) is mislocated and loses the duality and left-hull dependencies (F1-F4). (3) `step:disc-concat-disconnect-general` lacks the dependencies that make bounded components pull back to bounded components (F5). (4) The WLOG c >= 0 is correctly consumed as hull conjugation here (L1951 is a statement about hulls), and `step:c-event-E2` uses it where c >= 0 is needed (L2107): PASS on this point.

### thm-disconnects.b -- FAIL (author-blocked: P10; F1-F6, F27-F30)
- Fields (L502-L509; P7, R5): a.s., for every t > 0 (uniform), the set of points disconnected from infinity by L_t has non-empty interior. Matches frozen `theorem_1_10_b` (interior of `{w | DisconnectsFromInfinity (leftHull ..) {w}}`). The warning that by Def 1.9 the points of L_t count as disconnected, so (b) does not say that C\L_t is disconnected, is correct and keeps downstream consumers honest.
- Closure: scale invariance (P(A_t) independent of t), positivity from Lemma 4.1, Blumenthal (arbitrarily small times, as the limsup of A_{t_n} lies in the germ field), monotonicity (L_s contains L_t, points of L_t count as disconnected). The quantifier closure 'a.s. simultaneously for all t > 0' is a separate node, correctly. Same P10 block through lem-disconnect-2.

### prop-i.a -- FAIL (repairable: F8-F20, F22-F24)
- Fields (L1265-L1269; R4, R5, R7/R15, R9, R17): a,b > 0, c^2 <= ab, admissible p, (I) >= 0, any probability space and driver, z != 0; a.s. T_z = infinity. Frozen `proposition_3_1_a` agrees. The Section-3 package ('zz sampled from p, independent of U', L1255) is correctly not a hypothesis of the statement but a local hypothesis package discharged in steps (spec Section 4).
- Closure (Lemma 3.6, Lemma 3.4, Lemma 3.3, Remark 2.12, Lemma 2.16, Lemma 2.14, Lemma A.1): the case split (I) > 0 / (I) = 0 is a node; the carrier changes theta -> e^{2 i theta}, capacity time -> sigma-time are explicit nodes. All conditional applications were traced: Lemma A.1 (premises: 2p for the int_0^pi normalization, mu smooth, beta^2 = 2D or beta = sqrt(a) sin -+ sqrt(b) cos smooth, alpha and beta^2 pi-periodic, Hormander condition mu beta' != 0 at the zeros of beta, p continuous/C^2 off x + pi Z, beta^2 p in C^1) are supplied by step:stat-kolmogorov-normalization, step:stat-apply-kolmogorov-*, step:D-structure and the admissible-density definition; Lemma 3.4 premises by step:stationary-sde-X-form (SOURCE_GAP: the diffusion coefficients are only 2 pi-periodic, so they are not functions of X = e^{2 i theta}) and lem-recurrence; Lemma 3.3 premises by step:all-z-apply-Tz (SOURCE_GAP) plus step:all-z-null-set-density (SOURCE_GAP, the R7 gap).
- Why FAIL: G2 (map-level reflection), G3 (argument-process WLOG), G6 (circularity lem-polar/remark-sigma), G7 (product extension), G8 (spurious lem-p edges).

### prop-i.b -- FAIL (repairable, same defects as prop-i.a)
- Fields (L1265-L1270): (I) < 0 gives T_z < infinity. Frozen agrees. Closure: Lemma 3.4 gives log|f^_t|/t -> -alpha, the pathwise bound (3.2) in capacity time via sigma(infinity) = T_zz (Remark 2.12), then the comparison F' e^{-alpha F} > 1 giving T_zz < infinity (the case T_zz = infinity is included in the contradiction), then Lemma 3.3. Defects as for prop-i.a.

### prop-ii.a -- FAIL (repairable, same defects)
- Fields (L1276-L1281; R14): (II) < 0 gives, for every epsilon, some t < T_z with dist(z,L_t) < epsilon (the frozen `infDist z (leftHull ..) < epsilon`). Matches; the remark that L_t is increasing so the limit is the infimum is carried (claim:hulls-monotone). Closure: Lemma 3.7 (divergence of |f'|/|f| via Lemma 3.4), the Koebe estimate (3.5) with 0 in R_t (SOURCE_GAP), compactness (SOURCE_GAP), Lemma 3.3 extension. Defects as above.

### prop-ii.b -- FAIL (repairable, same defects)
- Fields (L1276-L1283; R14): (II) > 0 gives epsilon > 0 with epsilon <= dist(z,L_t) for all t < T_z. Matches frozen. Closure: Lemma 3.8 (contrapositive via (3.6), Lemma 3.9, Lemma 3.10, Lemma 3.7) giving positive probability, then the positive-measure/Girsanov/Koebe-distortion/compactness/martingale chain (L1786-L1816). The SOURCE_GAPs (Girsanov hitting, Koebe ball, future dependence of the event) are faithful. I checked the key identity of Step 2 (L1693-L1698): the law identity of Lemma 3.9 is for dist(zz, L_{sigma(s^)}) and the comparison needs dist(zz,L_{sigma(s^+t^)}) <= dist(zz,L_{sigma(s^)}); the source's symbol L_s with the random s = sigma(s^+t^)-sigma(t^) is a notational slip but the argument is intact (not a graph defect). Defects as above.

### lem-connected.left -- PASS
- Fields (L658-L666; R16, T5): continuous U : [0,infinity) -> C, every t; L_t connected. Frozen `lemma_2_4_leftHull` states `IsConnected` (non-empty and connected); the nonemptiness (U_0 in L_t, since T_{U_0} = 0 by the frozen `IsLoewnerSolution` requirement gamma t != U t) is correctly modeled as a SOURCE_GAP claim. Note the source says 'does not surround the origin' where the starting point U_0 is meant for general U (node records the doubt); the frozen statement is for general continuous U.
- Closure: loop criterion, homotopy, winding argument, with the added reviewer-A nodes for closedness of L_t and continuity of the flow (both genuinely used and unstated). The T5 sketch is a SOURCE_GAP. The right-hull part is not part of this root (R16).

### eqn-scale.left -- PASS
- Fields (L549-L552; R16, T7): continuous U (T7: codomain C), r > 0, t >= 0, L_t^{rU(./r^2)} = r L_{t/r^2}. Frozen `scaling_leftHull` agrees (r : NNReal, 0 < r). Closure: solution predicate, absorbing time, hull definition, well-definedness (uniqueness identifies the rescaled trajectory). The source proof is only a citation to [Lu, Sect. 2]; nothing is filled. PASS.

### eqn-reflect.left -- PASS
- Fields (L553-L557; R16): L_t^{U*} = (L_t^U)* and L_t^{-U} = -L_t^U for continuous U. Frozen `reflection_leftHull` agrees (both conjuncts). Closure as for scaling. PASS. (The map-level identity is a different, unstated claim; it is modeled in F8 and does not belong to this root.)

## 2. Global findings

Severity: S1 = changes a root verdict; S2 = wrong or missing dependency without changing the root's statement; S3 = annotation.

- G1 (S1) P10 confirmed; see §5. The two Theorem 1.10 roots cannot be certified from the source as it stands. F27-F30.
- G2 (S1 for the probabilistic roots) Map-level reflection is used but never stated. The source states (2.2) for hulls only (L553-L558; the 'f_t' identity appears in (2.1) but not in (2.2)). Lemma 2.14's proof (L984: (f_t(zz)) =_d (f_t(-zz)) =_d (-f_t(zz))) and the Lemma 2.16 WLOG need f_t^{-U}(-z) = -f_t^U(z) and f_t^{U*}(z*) = conj f_t^U(z). The graph cites `eqn-reflect` (hull-level) and `step:wlog-c-nonneg` (hull-level). F8, F9, F12.
- G3 (S1 for the probabilistic roots) The WLOG c >= 0 appears at three places with three different meanings: L323/L1951 (hulls; `step:wlog-c-nonneg`, correct for Theorem 1.10), L1026 (density p -> p(-.); `step:p-wlog-c-nonneg`, correct), L1165 (argument process in Lemma 2.16). The third was routed through the hull-level node. F9-F11.
- G4 (S1 for Theorem 1.10 roots) Right-hull connectedness is stated in Lemma 2.4 (L659) and proved by duality (L662-L663). Reviewer D recorded it as a node that the source 'never states' with locators at L2169, and coverage still says 'right-hull part excluded' and '(2.4) feeds no root'. Both exclusions are now stale because step:disc-E1-positive consumes the right-hull claim. F1-F4.
- G5 (S2) `step:disc-concat-disconnect-general` (reviewer D) pulls 'bounded component' back through f_s without depending on conformality/behaviour at infinity and compactness. F5.
- G6 (S2) Local circularity lem-polar <-> remark-sigma. The statement of Lemma 2.11 is for all t~ >= 0 and presupposes sigma_z defined on (0,infinity), which Remark 2.12 deduces from the SDEs. The graph avoids a cycle by an informal 'local' reading; the dependency (lem-polar -> remark-sigma) is missing. The fix routes Remark 2.12 through the local time-changed SDE steps and makes lem-polar depend on Remark 2.12. F18-F20.
- G7 (S2) The probabilistic roots are over arbitrary (Omega,P,U) while the proofs use zz independent of U. The product extension is a carrier change and is unmodeled. F13-F17.
- G8 (S2) Spurious edges to `lem-p` in eqn-integral-nu, step:prop-i-apply-stationary-sde and eqn-wt-L-dist. Under R7/R15 stationarity is supplied by lem-stationary for every admissible p; edges to lem-p would force the construction (and the positivity statement) to be proved before Prop 3.1 for a given p. F22-F24. (The edge lem-p -> step:all-z-null-set-density is kept: it records the source's cited justification, but note that lem-p proves positivity only for the constructed p, so the node stays an open SOURCE_GAP.)
- G9 (S2) `step:c0-explicit-density` asserts the explicit formula for every admissible p. The source (L1829-L1836 with Remark 2.15) identifies only the constructed density. The c = 0 root needs one p. F21.
- G10 (S2) Typo candidate T8 in (2.3), see F25 and §6.
- G11 (S2) `step:hulls-compact` lacks the edge to `step:hull-closed`. F7.
- G12 (S3) The generated dashboard inside DEPGRAPH.md is stale: it reports 274 nodes, 716 edges, 41 source gaps, 300 coverage items, 34 dependency leaves; the merged records contain 282 nodes, 767 EDGE lines, about 70 nodes whose NOTE carries a SOURCE_GAP, 303 coverage items and 33 leaves. It was generated before the eight reviewer-authored nodes were merged. Regenerate after applying the fixes (not a record fix).
- G13 (S3) Spec Section 5 says new `ext:` ids must be reported: `ext:kolmogorov-zero-one` is not in the table (its coverage item cites EXTRACTION_SPEC Section 5 as the reason, which is inaccurate). Report it as an addition. No other external is missing: Hormander (hairer), Koebe (Lawler 3.18, 3.23), scale function (Lawler 1.24), Prop 4.43, Girsanov, Birkhoff, Durrett, Ito (Protter), Levy/DDS, Blumenthal, Picard-Lindelof, martingale convergence, dominated convergence, Brownian support and existence, strong Markov are all present as leaves. The Koebe quarter external is stated in the graph for conformal maps of C minus a compact set; Lawler 3.18 is for discs/half-planes. I checked that the two-sided distance estimate follows from the disc version applied to phi and phi^{-1}, so this is fine.
- G14 (S3) Edge-locator audit (script: every EDGE locator against the consumer's own source ranges): 19 locators fall outside the consumer's recorded ranges. 14 are harmless (the consumer's range is a single narrow line or a statement vs proof split). Real defects: step:disc-choose-U (F6). Questionable: step:re-im-drift-bound -> lem-endpt-cont @L2049 (the use is the inference rho_z < T_z of the later proof, L2134, already an edge of step:pos-segment-disjoint-L2; keep but note). step:p-positive-off-discrete -> step:p-wlog-c-nonneg @L1026 is outside its recorded ranges (L953, L1086-L1110); harmless.
- G15 (S3) Quantifier, carrier and normalization audit with no defect found: z vs the stationary point (Lemma 3.3 is the only bridge, hypotheses and the apply-nodes recorded); theta vs e^{2 i theta} vs e^{i theta} (Lemma A.1 gives the process law of e^{2 i X}; stat-pi-reduction upgrades; Lemma 3.4 uses e^{2 i theta^}, recurrence is in the same carrier); int_0^pi vs int_0^{2pi} (R9: A.1 applied to 2p; item (I), (II) and Lemma 2.13 normalize with 2 pi; eqn-integral-nu uses the law p 1_{[0,2pi]}); capacity time vs sigma-time (Remark 2.12 supplies sigma(infinity) = T_z in step:swallow-time-change, eqn-neg-I1-bd, step:prop-ii-a-capacity-time, step:c0-bdy-capacity-time); a,b > 0 (R5: steps requiring B, B~ carry it; lem-scaling/markov/wlog are stated for general PSD, which is stronger and harmless; `remark-sigma` claims no R5 while depending on a lemma that needs it, F18); c >= 0 (see G3); z != 0 (R4: the zero point is handled by step:zero-in-left-hull); R14 epsilon forms (consistent in the four Prop roots and the assembly).
- G16 (S3) AND/OR: the graph has no route nodes and the source has no alternatives, so nothing is required. DEPS are conjunctive everywhere; I found no place where a DEP is only needed on one branch except the case splits already modeled (|c| < sqrt(ab) / c = sqrt(ab); (I) > 0 / (I) = 0).
- G17 (S3) Proof-paragraph coverage. Every proof paragraph with a substantive obligation in a root closure has a node or an explicit exclusion; the exclusions that the closure relies on are all justified (Lemma 2.6, Section 2.4, Section 5, Remarks 1.3/1.6/1.11, Prop 1.5, outlines restating later displays) except the two stale ones in G4. Unstated arguments that are modeled as SOURCE_GAP and that I agree must stay open: local/global Picard-Lindelof, flow continuity, closedness and compactness of hulls, 0 in R_t, claim:gt-conformal, argument lift, Remark 2.12 range claim, Kolmogorov process stationarity, Hormander application (t > 0), SDE form of X (sign flip), regeneration, Durrett adaptation, Lemma 3.3 apply-nodes and stopping time choice, p vanishing on a null set, Koebe ball, Girsanov hitting, c0 integration, finiteness of T_z at a-b = 8, the sign-case assembly, existence of U^+- (blocked), E_2/E_3 bridge, topological separation. Extra candidates not recorded as gaps (notes only): (i) step:log-finite-iid and step:log-finite-q-choice rely on a law that is uniform over the starting point on the circle; the node already says the k-independence is unjustified, and I add that tau_k is a stopping time, so stationarity at fixed times does not apply. (ii) In `step:all-z-stopping-time-choice` the source argument ('non-constant, continuous, Lambda dense') cannot give P(e^{i theta_tau} in Lambda) >= q; the node says so.
- G18 (S3) Statement-strength audit of non-anchors that feed roots: `lem-hormander` as stated is false at t = 0 (noted), `lem-kolmogorov` has alpha, beta mapping into [0,infinity) in the source (P6 corrected), `lem-line-approx` writes the segment with T^{-1/2} (typo noted), `lem-pos-hits-before-neg` and `lem-c-event` need c >= 0 beyond the lemma statement (noted, supplied at consumers). `lem-disconnect-2` is trivial for U = empty (noted); the pigeonhole choice is a node. No weakening or strengthening that changes a root was found other than G9.

## 3. PASS/FAIL for reviewer- and orchestrator-authored records

Nodes (EXTRACTOR reviewer-A/sonnet, reviewer-C/sonnet, reviewer-D/sonnet; none are orchestrator-authored):
- PASS step:loewner-global-uniqueness (reviewer-A): local-to-global uniqueness via an open-closed argument; deps (local solution, solution predicate) correct; SOURCE_GAP right.
- PASS step:flow-continuity (reviewer-A): joint continuity of (s,w) -> f_s(w) and openness of {T_w > t}; genuinely used at L662; statement and deps correct. Note: continuous dependence on the initial point is not covered by the `ext:picard-lindelof` statement (existence and uniqueness); the SOURCE_GAP is the right status.
- PASS step:hull-closed (reviewer-A): closedness of L_t from openness of {T_w > t}; used by the loop criterion, step:haus-subsequence-limit-contained and step:disc-a-open-condition; F7 adds the missing consumer edge from step:hulls-compact.
- PASS step:endpt-upcrossing-reduction (reviewer-A): quantifier closure over alpha < beta and extraction of an upcrossing; deps correct.
- PASS step:zero-in-future-left-hull (reviewer-C): 0 in L_{t,s+t} because the shifted driver starts at 0; the split gives each EDGE its own use site (L1768). Only the sibling's TITLE is stale (F26).
- FAIL step:disc-choose-U (reviewer-D): statement and dependencies are right (the 'union' reading is correctly withdrawn; pigeonhole over the sign), but the three EDGE locators cite the paragraphs where the prerequisites were proved (L2181, L2165), not the use site L2194 (F6). It also depends on the refuted step:disc-setup (P10), which is not this node's fault.
- FAIL step:right-hull-connected (reviewer-D): the source states the claim at L659 and proves it by duality at L662-L663; STATEMENT_SOURCE/PROOF_SOURCE at L2169 are wrong, the 'never states' NOTE is wrong, DEPS omit the duality property (needs a new node) and lem-connected.left (F1-F4).
- FAIL step:disc-concat-disconnect-general (reviewer-D): the claim is right and well motivated (inequality, not equality), and the generality (any z, any stopping time) is the right reuse; but DEPS miss claim:gt-conformal and step:hulls-compact, which are what make bounded components pull back to bounded components (F5).

Coverage items (reviewer-A, reviewer-D, orchestrator):
- PASS inv:L644:reverse-remark (reviewer-A): L644 is the reversal remark and step:reverse-via-mult-by-i contains it.
- PASS inv:L2023:bm-support (reviewer-D): the uncited positive-chance statement at L2023 is the support theorem; ext:bm-support is reachable.
- PASS inv:cite:L2223:blumenthal (reviewer-D): L2223 invokes Blumenthal's law by name; ext:blumenthal is consumed by step:disc-b-blumenthal.
- PASS (11 orchestrator items) inv:ext:picard-lindelof, inv:ext:strong-markov-bm, inv:ext:bm-existence, inv:ext:levy-characterization, inv:ext:martingale-convergence, inv:ext:dct, inv:ext:birkhoff, inv:ext:girsanov, inv:ext:kolmogorov-zero-one, inv:ext:bm-support, inv:ext:blumenthal: each maps to an existing external node whose STATEMENT_SOURCE equals the item SOURCE; each external is consumed in a root closure. Minor: inv:ext:kolmogorov-zero-one's reason cites spec Section 5 although the id is a new addition (G13).
- PASS inv:L268:loewner-ivp-solvability (orchestrator): L268 is the claim that the solution is defined up to T_z; mapping to the three SOURCE_GAP steps is complete.
- Dispositions of other items that became stale and need repair (not authored by the above tags): inv:eqn-duality and inv:lem-connected (F3, F4).



## 4. Fixes

Conventions: `global-reviewer/sonnet` is the EXTRACTOR tag on every new or fully replaced record below. Where only changed lines are given, every other field and every EDGE line to an unchanged target stays as in the merged record. F1-F13 and F31-F33 repair structural topology errors (new or replaced records); F14-F24 repair premise supply, spurious dependencies and statement scope; F25-F30 are annotations. Every DEPS change carries its new EDGE lines, or an explicit 'delete the EDGE line(s)' note.

### F1 step:right-hull-connected
The source states right-hull connectedness in Lemma 2.4 itself (L659) and gives a one-line proof by duality (2.4) (L662-L663). So it is not an unstated sketch, the locators L2169 are wrong, and the true dependencies are the duality property and the left-hull connectedness lemma. Replace the whole record:

```
NODE: step:right-hull-connected
KIND: step
TITLE: Right hulls R_t are connected (Lemma 2.4, right-hull part)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L658-L660
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L663
CONTRACT_ID: paper.step:right-hull-connected
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U : [0,infinity) -> C continuous
SOURCE_QUANTIFIERS: U; t >= 0
SOURCE_CONCLUSION: R_t is connected
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-hulls.right, eqn-duality, lem-connected.left
ROUTES: -
ROUTE_FOR: -
EDGE: defn-hulls.right | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L659-L659 | statement is about R_t
EDGE: eqn-duality | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L663 | "The duality property (2.4) implies that R_t is also connected": R_t^U = i L_t^{i(U(t)-U(t-.))}
EDGE: lem-connected.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L663 | left-hull connectedness applied to the dual driver s -> i(U(t)-U(t-s)) (extended by a constant after time t)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: global-reviewer/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: R16: right-hull part of Lemma 2.4, ordinary non-anchored node, consumed by step:disc-E1-positive (crossing of [x,y]x[-eps,eps] by R_T) and step:disc-topological-separation. The source states the claim (L659) and proves it in one sentence by duality (L662-L663); the duality identity (2.4) itself is only cited to Lu (eqn-duality). Unstated in the source: that L_t depends only on U restricted to [0,t], needed to extend the dual driver beyond time t. Replaces the reviewer-D proposal, which mislocated the statement at L2169 and called it a source gap.
```

### F2 new eqn-duality
The duality property (2.4) is now consumed (by F1), so the exclusion in coverage (inv:eqn-duality) is stale. Prop 1.5 itself stays excluded.

```
NODE: eqn-duality
KIND: display
TITLE: Duality property (2.4)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-duality@L567-L570
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-duality@L547-L547
CONTRACT_ID: paper.eqn-duality
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U : [0,infinity) -> C continuous
SOURCE_QUANTIFIERS: U; t >= 0
SOURCE_CONCLUSION: L_t^U = i R_t^{i(U(t)-U(t-.))} and R_t^U = i L_t^{i(U(t)-U(t-.))} (the driver on the right is s -> i(U(t)-U(t-s)), s in [0,t])
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-loewner.solution, defn-loewner.well-defined, defn-hulls.left, defn-hulls.right
ROUTES: -
ROUTE_FOR: -
EDGE: defn-loewner.solution | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-duality@L547-L547 | time-reversed driver and the ODE
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-duality@L547-L547 | uniqueness identifies the time-reversed flow
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-duality@L569-L569 | left hull of the original chain
EDGE: defn-hulls.right | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-duality@L569-L569 | right hull of the dual chain
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: global-reviewer/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Canonical (2.4). The source gives no proof ("easily consequences of Definition 1.1; see [Lu, Section 2]", L547). Do not fill. Consumed only through step:right-hull-connected; Prop 1.5 (the other consumer) is excluded.
```

### F3 inv:eqn-duality
```
ITEM: inv:eqn-duality
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-duality@L568-L568
DISPOSITION: NODE eqn-duality
REASON: (2.4) duality, consumed by step:right-hull-connected (right-hull part of Lemma 2.4, itself consumed by step:disc-E1-positive); Prop 1.5 stays EXCLUDED (feeds no root)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: global-reviewer/sonnet
REVIEWER: -
```

### F4 inv:lem-connected
```
ITEM: inv:lem-connected
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L658-L660
DISPOSITION: NODE lem-connected.left, claim:hull-nonempty, step:right-hull-connected
REASON: Lemma 2.4: left-hull part (root) and nonemptiness; the right-hull part is consumed by step:disc-E1-positive and is modeled by step:right-hull-connected (replaces 'right-hull part excluded')
COVERAGE_STATUS: PROPOSED
EXTRACTOR: global-reviewer/sonnet
REVIEWER: -
```

### F5 step:disc-concat-disconnect-general
The pull-back of 'bounded component' through f_s needs f_s to be a homeomorphism C\L_s -> C\R_s that respects neighbourhoods of infinity (z(g_s(z)-z) has a limit, so f_s(w) ~ w) and compact hulls; otherwise a bounded component could pull back to an unbounded one. Both are nodes of the graph and are missing from DEPS. Changed lines:

```
DEPS: eqn-conc, def-disconnect, defn-hulls.left, defn-hulls.right, claim:gt-conformal, step:hulls-compact
EDGE: claim:gt-conformal | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | f_s: C\L_s -> C\R_s is a conformal bijection with f_s(w) - w bounded near infinity, so the bounded components of C\L_{s+t} correspond to the bounded components of C\(L_{s,s+t} u R_s)
EDGE: step:hulls-compact | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | L_s, R_s, L_{s,s+t} compact, so a component of the complement is unbounded iff its image is
```

### F6 step:disc-choose-U
The EDGE locators cite the paragraphs where the prerequisites were proved (L2181, L2165); the use site of this step is L2194 ('this gives the lemma statement for t = T+2+K'). DEPS unchanged. Replace the three EDGE lines:

```
EDGE: step:disc-independence-product | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | P(E_1 cap ... cap E_4) > 0 is what lets one of the two sets be chosen
EDGE: step:disc-pullback-conclusion | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | on the four events one of U^-, U^+ is avoided and disconnected by L_{T+2+K}
EDGE: step:disc-setup | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | U^+- are deterministic, bounded, open (and needed non-empty)
```

### F7 step:hulls-compact
The source's Koebe applications use compact L_t, R_t. Compactness of L_t needs closedness (step:hull-closed, which the graph proves from flow continuity) and R_t closed needs the range of f_t to be open, i.e. its domain to be open; this edge is missing. Changed lines:

```
DEPS: claim:gt-conformal, defn-hulls.left, defn-hulls.right, step:hull-closed
EDGE: step:hull-closed | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1702-L1705 | L_t closed (domain of f_t open); R_t closed because f_t is an open map on an open domain
```

### F8 new step:reflect-map-identity
The source states the reflection property (2.2) for hulls only (L553-L558), but the proofs use the map-level identity: L984 uses (f_t(zz)) =_D (f_t(-zz)) =_D (-f_t(zz)), L1165 uses 'assume WLOG c >= 0' for the argument process. A hull identity does not supply this. The identity is not stated in the source, so the node carries SOURCE_GAP:

```
NODE: step:reflect-map-identity
KIND: step
TITLE: Map-level reflection: f_t^{U*}(z*) = (f_t^U(z))*, f_t^{-U}(-z) = -f_t^U(z), absorbing times unchanged
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-reflect@L553-L558
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-reflect@L547-L547
CONTRACT_ID: paper.step:reflect-map-identity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U : [0,infinity) -> C continuous
SOURCE_QUANTIFIERS: U; z in C; t < T_z
SOURCE_CONCLUSION: T_{z*}^{U*} = T_z^U and f_t^{U*}(z*) = (f_t^U(z))*; T_{-z}^{-U} = T_z^U and f_t^{-U}(-z) = -f_t^U(z); in particular theta_t^{-U}(-z) = theta_t^U(z) + pi and theta_t^{U*}(z*) = -theta_t^U(z) (mod 2 pi) for the continuous lift
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-loewner.solution, defn-loewner.absorbing-time, defn-loewner.well-defined
ROUTES: -
ROUTE_FOR: -
EDGE: defn-loewner.solution | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-reflect@L547-L547 | the conjugated / negated trajectory solves the ODE for the conjugated / negated driver
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-reflect@L547-L547 | T_z is preserved
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-reflect@L547-L547 | uniqueness identifies the transformed trajectory with the chain of the transformed driver
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: global-reviewer/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: (2.2) is stated for hulls only; the map-level identity behind it is used at L984 and L1165 but never written. Not supplied by eqn-reflect.left, which is hull-level. Do not fill beyond the ODE-uniqueness reading.
```

### F9 new step:wlog-c-nonneg-arg
step:wlog-c-nonneg is the hull-level reduction used at L1951. Lemma 2.16's 'Assume without loss of generality that c >= 0' (L1165) is a statement about the stationary argument process e^{2 i theta^} under conjugation (theta^ -> -theta^, p -> p(-.)); a conjugation of hulls does not give it. New node:

```
NODE: step:wlog-c-nonneg-arg
KIND: step
TITLE: WLOG c >= 0 for the stationary argument process (conjugation, p -> p(-.))
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1165-L1165
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1165-L1165
CONTRACT_ID: paper.step:wlog-c-nonneg-arg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a, b > 0; c in [-sqrt(ab), 0); p admissible for (a,b,c); zz on the unit circle independent of U with angle density p 1_[0,2pi]
SOURCE_QUANTIFIERS: forall a,b,c; p
SOURCE_CONCLUSION: the conclusion of lem-recurrence for (a,b,c,p) follows from that for (a,b,-c, p~) with p~(u) = p(-u): conjugating U gives an SLE_{Sigma~} driver, Sigma~ = [[a,-c],[-c,b]], conj(zz) has angle density p~, theta^ becomes -theta^ and e^{2i theta^} becomes its conjugate, and recurrence at w (resp. e^{2ix}) is equivalent to recurrence at conj(w)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-sle, eqn-cov-matrix, step:reflect-map-identity, step:p-wlog-c-nonneg, def-arg, defn-sigma
ROUTES: -
ROUTE_FOR: -
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1165-L1165 | conjugate of an SLE_Sigma driver is an SLE_{Sigma with -c} driver
EDGE: eqn-cov-matrix | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1165-L1165 | Sigma with c replaced by -c
EDGE: step:reflect-map-identity | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1165-L1165 | map-level conjugation identity f_t^{U*}(z*) = conj(f_t^U(z)), so theta^ -> -theta^
EDGE: step:p-wlog-c-nonneg | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1165-L1165 | p~(u) = p(-u) is admissible for (a,b,-c)
EDGE: def-arg | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1165-L1165 | the continuous lift of the conjugated process is the negated lift
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1165-L1165 | sigma-time is unchanged by conjugation (|f_s| is unchanged)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: global-reviewer/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: the source writes only 'Assume without loss of generality that c >= 0' for a statement about the argument process. Distinct from step:wlog-c-nonneg (hull level, used at L323/L1951) and from step:p-wlog-c-nonneg (admissibility of p~ only).
```

### F10 lem-recurrence
The premise 'c >= 0' of its proof is supplied by step:wlog-c-nonneg-arg, not by the hull-level step:wlog-c-nonneg. Changed lines:

delete the EDGE line(s) to `step:wlog-c-nonneg`

```
DEPS: lem-stationary, step:wlog-c-nonneg-arg, step:rec-reduction-to-x, step:rec-renewal, step:rec-tau-finite, step:rec-angle-hit-unif
EDGE: step:wlog-c-nonneg-arg | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1165-L1165 | c>=0 WLOG for the argument process
```

### F11 step:rec-reduction-to-x
delete the EDGE line(s) to `step:wlog-c-nonneg`

```
DEPS: step:D-structure, step:wlog-c-nonneg-arg
EDGE: step:wlog-c-nonneg-arg | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1165-L1165 | WLOG c>=0 for the argument process
```

### F12 step:stat-pi-reduction
It cites (2.2) for the identity (f_t(zz))_t =_D (f_t(-zz))_t =_D (-f_t(zz))_t, which is a statement about f_t, while the graph's `eqn-reflect` states hulls only. Replace the dependency:

delete the EDGE line(s) to `eqn-reflect`

```
DEPS: step:reflect-map-identity, step:driver-negation-symmetry, def-arg, step:stat-apply-kolmogorov-noncritical, step:stat-apply-kolmogorov-critical, lem-stationary.admissible
EDGE: step:reflect-map-identity | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L984-L984 | f_t^{-U}(-z) = -f_t^U(z); with -U =_d U and -zz =_d zz this gives (f_t(zz)) =_d (-f_t(zz))
```

### F13 new step:section3-product-extension
Every probabilistic root quantifies over an arbitrary (Omega, P) with an SLE_Sigma driver (R9), while the proofs of Props 3.1/3.2 use a point zz independent of U (L1255). The carrier change Omega -> Omega x circle and the transfer of a.s. statements are not modeled and are not in the source (the extractor mentions 'enlarge by sigma(zz)' only in a NOTE). New node:

```
NODE: step:section3-product-extension
KIND: step
TITLE: Product extension carrying zz: a.s. statements for (Omega,P,U) from the product space with the stationary point
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#sec-phases@L1255-L1255
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#sec-phases@L1255-L1255
CONTRACT_ID: paper.step:section3-product-extension
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (Omega,P) probability space with an SLE_Sigma driver U (R6, R9); a,b>0; c^2<=ab; p admissible
SOURCE_QUANTIFIERS: forall (Omega,P,U); p
SOURCE_CONCLUSION: on Omega x [0,2pi) with P (x) p(u)du and U~(omega,u) = U(omega): U~ is an SLE_Sigma driver, zz(omega,u) = e^{iu} is independent of U~ with angle density p 1_[0,2pi], and an event depending only on U has the same probability (a.s. read as: complement contained in a null set, R9), so a.s. statements proved on the product space descend to (Omega,P,U)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-sle, lem-stationary.admissible
ROUTES: -
ROUTE_FOR: -
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#sec-phases@L1255-L1255 | the lifted process is again a planar BM with covariance Sigma
EDGE: lem-stationary.admissible | source/arxiv-2203.07313v4/complex-sle-final.tex#sec-phases@L1255-L1255 | p is a density on [0,2pi], so P (x) p du is a probability measure
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: global-reviewer/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: the source says only that zz is 'independent from the driving Brownian motion' (L1255, L939). Carrier change Omega -> Omega x circle; R9 reads 'a.s.' as null complement without presupposing measurability.
```

### F14 prop-i.a
Changed lines (add one DEPS entry and its EDGE; all existing EDGE lines stay):

```
DEPS: item-I, defn-loewner.absorbing-time, step:prop-i-a-not-to-minus-infinity, lem-swallow-distance, step:all-z-apply-Tz, lem-all-z, step:section3-product-extension
EDGE: step:section3-product-extension | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1402-L1402 | the proof works with zz sampled from p independently of the driver, on the product extension of the given probability space
```

### F15 prop-i.b
```
DEPS: item-I, defn-loewner.absorbing-time, eqn-neg-I1-bd, step:prop-i-b-ode-comparison, step:all-z-apply-Tz, lem-all-z, step:section3-product-extension
EDGE: step:section3-product-extension | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1402-L1402 | the proof works with zz sampled from p independently of the driver, on the product extension of the given probability space
```

### F16 prop-ii.a
```
DEPS: item-II, defn-hulls.left, defn-loewner.absorbing-time, step:prop-ii-a-koebe-limit, step:all-z-apply-dist, lem-all-z, step:section3-product-extension
EDGE: step:section3-product-extension | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1459-L1459 | the proof works with zz sampled from p independently of the driver, on the product extension of the given probability space
```

### F17 prop-ii.b
```
DEPS: item-II, defn-hulls.left, defn-loewner.absorbing-time, step:prop-ii-b-martingale-zero-one, step:section3-product-extension
EDGE: step:section3-product-extension | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1793-L1793 | Fubini over the independent pair (zz, U) requires the product extension of the given probability space
```

### F18 remark-sigma
Its DEPS use lem-polar, whose own statement ('for all t~ >= 0') presupposes that sigma_z is defined on all of (0,infinity), which is what Remark 2.12 deduces from the SDEs. The graph avoids a cycle only by an informal 'local' reading. Break the circle formally: Remark 2.12 depends on the local, time-changed SDEs (steps), and lem-polar depends on Remark 2.12 (F20). The record also claims no R5 while depending on lem-polar (which needs ab>0). Changed lines:

delete the EDGE line(s) to `lem-polar`

```
SOURCE_HYPOTHESES: (f_t) centered SLE_Sigma; z in C; a,b>0 (R5, inherited from the polar SDEs; the source states the remark without it)
DEPS: step:polar-time-change, step:polar-derivative-sde, step:sigma-bounded-coefficients, lem-endpt-cont, defn-sigma
EDGE: step:polar-time-change | source/arxiv-2203.07313v4/complex-sle-final.tex#remark-sigma@L894-L894 | SDE (2.26) for log|hat f| on the domain of sigma, with bounded coefficients
EDGE: step:polar-derivative-sde | source/arxiv-2203.07313v4/complex-sle-final.tex#remark-sigma@L894-L894 | SDE (2.27) for log|hat f-prime| on the domain of sigma, with bounded coefficients
```

### F19 step:sigma-bounded-coefficients
delete the EDGE line(s) to `lem-polar`

```
DEPS: step:polar-time-change, step:polar-derivative-sde
EDGE: step:polar-time-change | source/arxiv-2203.07313v4/complex-sle-final.tex#remark-sigma@L894-L894 | (2.26) on the domain of sigma gives the semimartingale decomposition of log|hat f| with bounded coefficients
EDGE: step:polar-derivative-sde | source/arxiv-2203.07313v4/complex-sle-final.tex#remark-sigma@L894-L894 | (2.27) gives the semimartingale decomposition of log|hat f-prime| with bounded coefficients
```

### F20 lem-polar
```
DEPS: defn-sigma, def-arg, eqn-def-ft, eqn-nu-D.mu, eqn-nu-D.nu, step:polar-time-change, step:polar-W-law, step:polar-derivative-sde, remark-sigma
EDGE: remark-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L865-L868 | the statement fixes sigma = sigma_z and evaluates for all t~ >= 0: sigma_z is defined on (0,infinity) by Remark 2.12
```

### F21 step:c0-explicit-density
As recorded, the node asserts the explicit formula for every admissible p (a uniqueness claim the paper does not prove and that the NOTE itself calls a gap). The source only identifies the constructed density (Remark 2.15). The c = 0 root only needs one admissible p, so the node should be stated for the constructed density and the gap shrinks to the explicit integration. Changed lines (DEPS unchanged):

```
SOURCE_HYPOTHESES: a,b > 0; c = 0; p = the density constructed in the proof of Lemma 2.13 (case 1, c = 0), equal to k p_0 by Remark 2.15
SOURCE_CONCLUSION: this p is admissible (lem-p.exists, case 1) and p(u) = Z^{-1}(a+b+(b-a)cos 2u)^{4/(b-a)} for a != b, p(u) = Z^{-1} exp((4/a)cos^2 u) for a = b, with Z = Z(a,b) > 0 the normalizing constant for int_0^{2pi} p = 1
NOTE: SOURCE_GAP: the explicit integration of (mu - D')/D for c = 0 (the Mathematica check sits in a %-comment, L1140-L1146) and the check of normalization/regularity at a = b are not written. The identification is for the constructed p (Remark 2.15); the source never claims it for every admissible p and uniqueness of the normalized pi-periodic solution is not argued, but the c = 0 root does not need it: the later Lemmas 3.11/3.12 are applied to this p only. Consumers that cite 'p admissible' in this section (step:c0-bdy-finite-time, lem-c0-phases) are read with p := this density.
```

### F22 eqn-integral-nu
The edge to lem-p is spurious under R7/R15: the identity holds for every admissible p by lem-stationary, and lem-p (existence of one p with extra properties) is not used. DEPS are conjunctive, so the edge would force the full Lemma 2.13 before (3.1) for a given p. delete the EDGE line(s) to `lem-p`:

```
DEPS: item-I, item-II, eqn-nu-D.nu, defn-sigma, def-arg, lem-stationary, lem-stationary.admissible
```

### F23 step:prop-i-apply-stationary-sde
Same: delete the EDGE line(s) to `lem-p`:
```
DEPS: lem-stationary-sde, step:stationary-sde-X-form, lem-polar, lem-recurrence, lem-stationary, eqn-integral-nu
```

### F24 eqn-wt-L-dist
Same: delete the EDGE line(s) to `lem-p`:
```
DEPS: step:computation-scaling-markov, lem-stationary
```

### F25 eqn-conc
As printed, (2.3) says f_t(L_{s+t} \ L_t) = L_{t,s+t} (L563). This cannot hold: f_t maps C\L_t onto C\R_t, while 0 lies in L_{t,s+t} (the shifted driver starts at 0) and 0 lies in R_t (L1463). The consistent version is f_t(L_{s+t} \ L_t) = L_{t,s+t} \ R_t, which is what L562 and the footnote at L522 use. Keep the literal transcription and flag it for an author ruling (proposed typo T8, see §6). Changed line:

```
NOTE: Canonical (2.3). Proof not in source (cited to Lu Sect. 2). Used by Lemma 2.8 and slices C, D. The source writes f_{t,s+t} with a time-shifted chain, defined in the item itself (no separate node). TYPO CANDIDATE T8 (author ruling needed): the third formula of (2.3), f_t(L_{s+t}\L_t) = L_{t,s+t}, contradicts the second formula, L_{s+t} = L_t cup f_t^{-1}(L_{t,s+t}\R_t), because f_t(C\L_t) = C\R_t omits 0 in R_t cap L_{t,s+t}; read as f_t(L_{s+t}\L_t) = L_{t,s+t}\R_t. Consumers that use the third formula (step:future-point-outside-hulls, step:log-finite-exit-times, step:converse-event-converges) must be read with this correction.
```

### F26 step:zero-in-left-hull
TITLE and NOTE still claim the future hulls after the split into step:zero-in-future-left-hull. Changed lines:
```
TITLE: 0 belongs to every left hull
NOTE: R4: U_0 = 0, so T_0 = 0 and 0 in L_t for all t. Used at L1558. The shifted-driver statement for L_{t,s+t} used at L1768 is step:zero-in-future-left-hull.
```

### F27 step:disc-setup
The construction of U^+- is not an unstated argument but is impossible for the stated x, y (P10, confirmed in §5). Mark it as blocked by the author so that no Lean task is scheduled on its dependents. Changed line:
```
NOTE: AUTHOR_BLOCKED (ERRATA P10): the construction at L2165 is refuted for x = 2C, y = 7C, not merely unstated. SOURCE_GAP: existence of non-empty open U^+- satisfying both requirements (distance >= 2 eps from the imaginary axis; mapped by z -> sqrt(z^2+4T) into B_{eps/2}(x -+ 2 i eps)) is asserted at L2165, not shown. Reviewer computation (to be confirmed by the orchestrator): the preimage of w = x -+ 2 i eps is z with z^2 = w^2-4T, |Re z| ~ 2 x eps / sqrt(4T-x^2), and the preimage of B_{eps/2}(w) has |Re z| <= ~ 2.5 x eps / sqrt(4T-x^2) as eps -> 0. A point at distance >= 2 eps from the imaginary axis therefore needs x / sqrt(4T-x^2) >~ 0.8. For the choice made in the proof of Lemma 4.4 (x = 2C, y = 7C, so x/y = 2/7) and any T > y^2/2 one has x / sqrt(4T-x^2) < 0.21 (numerically max |Re z|/eps = 0.72 at C = 1, T = 13, eps = 0.01), so U^+- would be empty. Lemma 4.4 is stated existentially ('we can choose 0<x<y'), so the proof of Lemma 4.1 may not re-pick x, y. The text also writes (B_t) for measurability; the hulls depend on U = (B, B~). Global review: confirmed. For any T with y < 2T^{1/2} the exact linearization gives max |Re z|/eps over the preimage of B_{eps/2}(x -+ 2 i eps) of about 2.5 x/sqrt(4T-x^2) < 0.7, below the required 2; the required 2 would need T <= 0.64 x^2, incompatible with y < 2T^{1/2} unless y < 1.6 x, while Lemma 4.4 forces y/x > 2 (Re f_2(z) - Re z lies in [-6C,-3C]); the preimage lies within eps of the segment [-2T^{1/2} i, 2T^{1/2} i], where L_T may lie and where the uniform closeness of f_T to z -> sqrt(z^2+4T) is not available. Dependents modeled as if the construction held: step:disc-E1-positive, step:disc-concatenation-transfer, step:disc-topological-separation, step:disc-pullback-conclusion, step:disc-choose-U, lem-disconnect-2 and everything downstream.
```

### F28 lem-disconnect-2
```
NOTE: SOURCE_GAP: as stated the lemma is trivial for U = empty (the empty set is open, bounded, disjoint from L_t and disconnected from infinity). Non-emptiness of U (U = U^- or U^+ of the proof) is implicit and is read as part of the statement; consumers (proof-a, proof-b) need it. The hypothesis c>=0 is supplied at consumers by step:wlog-c-nonneg. AUTHOR_BLOCKED (ERRATA P10): the proof as written goes through step:disc-setup, whose construction of U^+- is refuted; the statement itself is not claimed false.
```

### F29 thm-disconnects.a
```
NOTE: Root. The source says "for each z in C"; R4 excludes z = 0 (0 in L_t for all t). AUTHOR_BLOCKED (ERRATA P10): the root closure contains lem-disconnect-2 and through it the refuted step step:disc-setup; this root cannot be counted as source-supported until the author supplies a corrected argument.
```

### F30 thm-disconnects.b
```
NOTE: Root. P7: uniform in t: a.s., for every t > 0. By Definition 1.9 points of L_t count as disconnected, so (b) does not itself say that C\L_t is disconnected. AUTHOR_BLOCKED (ERRATA P10): same as thm-disconnects.a (closure through lem-disconnect-2 and step:disc-setup).
```

### F31 new inv:L554:reflect-map-identity
```
ITEM: inv:L554:reflect-map-identity
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L554:reflect-map-identity@L553-L558
DISPOSITION: NODE step:reflect-map-identity
REASON: map-level form of the reflection property (2.2), used at L984 and L1165 but stated in the source for hulls only; SOURCE_GAP
COVERAGE_STATUS: PROPOSED
EXTRACTOR: global-reviewer/sonnet
REVIEWER: -
```

### F32 new inv:L1165:wlog-arg
```
ITEM: inv:L1165:wlog-arg
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L1165:wlog-arg@L1165-L1165
DISPOSITION: NODE step:wlog-c-nonneg-arg
REASON: 'Assume without loss of generality that c >= 0' in the proof of Lemma 2.16, a reduction for the argument process under conjugation (not the hull-level reduction of L323)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: global-reviewer/sonnet
REVIEWER: -
```

### F33 new inv:L1255:product-extension
```
ITEM: inv:L1255:product-extension
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L1255:product-extension@L1255-L1255
DISPOSITION: NODE step:section3-product-extension
REASON: 'independent from the driving Brownian motion' (also L939): carrier change from the given probability space to the product with the circle, not stated in the source; SOURCE_GAP
COVERAGE_STATUS: PROPOSED
EXTRACTOR: global-reviewer/sonnet
REVIEWER: -
```


## 5. Unreachable-node findings, and the assessment of P10

Unreachable nodes: none. All 282 records reach at least one root (own script, DEPS only). After the fixes, the new nodes eqn-duality, step:reflect-map-identity, step:wlog-c-nonneg-arg and step:section3-product-extension are each reachable through their consumers (F1, F9, F12, F14-F17). The generated 'Nodes outside every root closure: none' is correct for the merged records (the dashboard is otherwise stale, G12). `lem-p` stays reachable only through remark-p0, step:c0-explicit-density and step:all-z-null-set-density after F22-F24, as intended. Coverage items now stale: inv:eqn-duality and inv:lem-connected (F3, F4).

### Open item P10 (Lemma 4.1, L2163-L2167)
Is the reviewer-D/orchestrator computation right? Yes, and the failure is stronger than the ERRATA entry states.
1. Setup: phi(z) = sqrt(z^2+4T) maps C minus [-2T^{1/2} i, 2T^{1/2} i] onto C minus [-2T^{1/2}, 2T^{1/2}]. For w = x + i eta with eta = -+2 eps, the preimage satisfies z^2 = w^2 - 4T, so z = i s + x eta / s + O(eta^2/s^3) with s = sqrt(4T - x^2). Thus |Re z| = 2 x eps / s at the centre of the ball and at most 2.5 x eps / s over B_{eps/2}(w) as eps -> 0.
2. The requirement 'distance >= 2 eps from the imaginary axis' therefore needs 2.5 x / s >= 2, i.e. 4T <= 2.5625 x^2, i.e. T <= 0.64 x^2.
3. Lemma 4.1 also requires y < 2T^{1/2} (the source writes T > y^2/2 'so that y < 2 T^{1/2}'; the equivalence is actually T > y^2/4, so the printed inequality is stronger than needed and does not change the conclusion). With T > y^2/4, T <= 0.64 x^2 forces y < 1.6 x.
4. Lemma 4.4's proof gives x = 2C, y = 7C (y/x = 3.5). Its bounds are Re f_2(z) - Re z in [-6C,-3C] on [x,y], so the sign change they certify happens only between about 3C and 6C; any pair (x',y') certified by them has y'/x' > 2, and shrinking [2C,7C] cannot reach y/x < 1.6. Lemma 4.4 is stated existentially, but the proof of Lemma 4.1 cannot re-pick x, y without a new argument. At x = 2C, y = 7C the maximum of |Re z|/eps over the preimage is below 0.7 for every T > y^2/4 (I recomputed it numerically with the exact branch: 0.67 at C = 1, T = 12.3; 0.46 at C = 1, T = 24.6; the ERRATA's 0.577 at T = 13 and 0.41 at T = 24.6 are the values at the centre of the ball and T = 13 violates the printed T > y^2/2, but this is immaterial).
5. Structural reason: the preimage of B_{eps/2}(x -+ 2 i eps) lies within about 0.7 eps of the vertical segment [-2T^{1/2} i, 2T^{1/2} i] (its imaginary part is about s < 2T^{1/2}). That is inside the eps-neighbourhood of the segment, where L_T may lie and where the uniform closeness of f_T to phi (Lemma 4.2 as used in E_1) is not available. So even if the sets were allowed to be that close, E_1's two conclusions on them (L_T avoids them, f_T maps them into B_eps(x +- 2 i eps)) cannot be obtained as stated.
6. The failure is in the choice of constants, not necessarily in the strategy: the two roles of eps (width of the neighbourhood that contains L_T and R_T, and radius/offset of the target balls) are coupled. One candidate repair (for the author to rule on, not to be filled by the graph) is to use a smaller width eps_1 << eps for L_T and R_T (and for the Hausdorff/uniform closeness from Lemmas 4.2/4.3) and require U^+- at distance >= 2 eps_1 from the imaginary axis. The author may prefer taking U^+- inside C minus L_T directly from the event E_1, as the ERRATA suggests.
Adequacy of the modeling: partly adequate, not sufficient. The SOURCE_GAP on step:disc-setup (with the computation in its NOTE) makes the problem visible, and step:disc-E1-positive and step:disc-choose-U cross-reference it. Two defects: (a) SOURCE_GAP means 'an argument is unstated and may be supplied', but here the stated argument is wrong; the status should say the step is blocked by the author, so that no Lean task is scheduled on step:disc-setup or its descendants and no one fills the gap by changing x, y. (b) The roots thm-disconnects.a/.b, which depend on it through lem-disconnect-2, carry no marker at all. F27-F30 add the marker (NOTE only, no change to DEPS or EDGE lines, no repair filled). The statement of Lemma 4.1 is not claimed false.

## 6. Final unresolved-question list for the author

1. P10: corrected argument (or ruling) for the sets U^+- in the proof of Lemma 4.1 (L2165), for the Theorem 1.10 roots. Candidate repair in §5, item 6.
2. T8 (new): (2.3), third formula, f_t(L_{s+t} \ L_t) = L_{t,s+t} cannot hold as printed since 0 is in R_t and in L_{t,s+t}; confirm the reading L_{t,s+t} \ R_t. Affects consumers listed in F25.
3. Right-hull connectedness (Lemma 2.4, right-hull part) and (2.4) are now in a root closure. Confirm that they are ordinary non-anchored nodes (R16) and that (2.4) is consumed as a cited, unproved property (F1-F2), or ask for an anchor.
4. Map-level reflection (F8): the source states (2.2) for hulls only but uses it for f_t (L984, L1165). Confirm it may be modeled as one SOURCE_GAP step rather than strengthening the frozen reflection anchor (which is hull-level by R16).
5. R7/R15: `step:all-z-null-set-density` (an admissible p vanishes only on a Lebesgue-null set) is still an unproved SOURCE_GAP that Lemma 3.3 needs for every admissible p. I sketched why it is plausible (the ODE with C^1 D p forces zeros to be isolated), but the source does not give it. Either accept it as a Lean-provable step, or restrict Props 3.1/3.2 and Theorem 1.8 to the constructed p (the 'weaker alternative' of P4). The same question applies to uniqueness of the c = 0 density (F21 removes the need).
6. Props 3.1/3.2 over arbitrary probability spaces (R9): confirm that the product extension (F13) is an acceptable SOURCE_GAP and that 'a.s.' on a space where the event may be non-measurable is read as null-complement (R9).
7. Lemma 3.5 / `step:recurrent-durrett-adaptation` and `step:sde-regeneration` rely on 'essentially identical to Durrett' and on uniqueness in law of the SDE solutions; `step:stationary-sde-X-form` points out that the diffusion coefficients are only 2 pi-periodic in theta^ (sign flip), so Lemma 3.4's hypothesis 'g^j measurable functions of X' fails literally for X = e^{2 i theta^}. Decide whether to leave these as SOURCE_GAP or to state Lemma 3.4 with the pair (e^{2 i theta^}, sign) as the Markov state.
8. `step:log-finite-iid` (Lemma 3.10): the independence of the integral from F_{tau_k} and the k-independence of its law, with tau_k a stopping time and a random starting angle, need an extra argument (uniformity over the angle); unresolved in the source.
9. `step:c0-bdy-finite-time` (Lemma 3.12): T_z < infinity is not argued in the source; modeled via Prop 3.1b. Confirm.
10. `ext:kolmogorov-zero-one` is a new external id (G13); confirm adoption.
11. Generated dashboard (DEPGRAPH.md) must be regenerated after the fixes; the GLOBAL_REVIEWER and GLOBAL_REVIEW_REF header fields are not set by me.
