# Slice D topology review

Reviewer: reviewer-D/sonnet
Scope: slice D, records with EXTRACTOR extractor-D/sonnet: 51 nodes in DEPGRAPH.md and 46 items in DEPGRAPH_COVERAGE.md (paper.tex L1947-L2311: Section 4, Lemmas 4.1-4.6, the proof of Theorem 1.10, and the Section 5 exclusion).
Spans re-read in the raw source: L1947-L2311 in full (comment-free; figures and captions skimmed), plus L551-L560 ((2.3) concatenation), L608-L650 (Lemmas 2.2, 2.3), L1786-L1816 (proof of Proposition 3.2(b), for the reuse check), L495-L511 (Definition 1.9, Theorem 1.10), L860-L895 (sigma, Remark 2.12). Also read: REVIEWER_BRIEF, EXTRACTION_SPEC, ERRATA, anchor-table, INVENTORY (slice D rows), the statement of ComplexSLE/Frozen/Theorem_1_10_A.lean, and the context records of slices A, B, C that slice D cites (lem-endpt-cont, claim:gt-conformal, eqn-conc, lem-markov, lem-scaling, defn-sigma, remark-sigma, lem-polar, step:hull-closed, step:hulls-compact, step:zero-in-*, defn-hulls.right, lem-forward-reverse-ext, lem-mult-by-i, the slice C Prop 3.2(b) step nodes).
Mechanical checks done: all 51 slice D nodes have DEPS and EDGE lists that agree and every DEPS id resolves; slice D owns no frozen anchor (all FROZEN_* are `-`); slice A's roots thm-disconnects.a/.b depend on thm-disconnects#proof-a/#proof-b.

Tally: nodes 34 PASS / 17 FAIL (of 51); coverage items 44 PASS / 2 FAIL (of 46), plus 2 missing items proposed; fixes F1-F24 (new nodes F5, F8, F12; new items F23, F24).

Most important findings:
1. Reuse of Prop 3.2(b) (L2200-L2207, L2212): the restart steps (step:disc-a-markov-restart, eqn-disconnect-mart) consume step:disc-pullback-conclusion, which is the Lemma 4.1 instance (points U^+-, time T, and it depends on the Lemma-4.1-only separation step). A general concatenation transfer for an arbitrary z and stopping time sigma_z(tau) is the reused claim and is missing (F12, F11, F15, F17). Prop 3.2(b) used an equality of conditional probability; here it is an inequality that needs this transfer. remark-sigma, the scale-invariance reduction, and closedness of L_t (needed in place of the Koebe step) were also not discharged (F15-F17, F16).
2. Lemma 4.1 proof: the existence of the sets U^+- (L2165) fails for the explicit x=2C, y=7C of Lemma 4.4 (F6); R_T connectedness is used and not modeled (F7, F8); a pigeonhole step choosing the deterministic U is missing and the extractor's 'union' reading is invalid (F4, F5); B_{3eps}(x) is not shown disjoint from L_{T,T+2} (F9, F20).

## 1. Node verdicts

PASS ext:loewner-convergence
PASS ext:bm-support
PASS ext:blumenthal
PASS lem-haus
PASS step:haus-maps-converge
FAIL step:haus-subsequence-limit-contained: missing DEPS step:hull-closed and step:hulls-compact: 'By compactness' (L2015) needs uniformly bounded compact hulls, and L' subset B_eps(L_t) for all eps gives L' subset L_t only for closed L_t (Fix F1)
PASS step:haus-limit-conformal-extension
PASS step:haus-contradiction-L-t
PASS step:haus-subsubsequence-closure
PASS step:haus-right-hull-reduction
PASS lem-line-approx
PASS step:line-zero-driver-chain
PASS step:line-small-driver-positive
PASS step:line-apply-haus
PASS lem:re-im-bounds
PASS step:re-im-ft-sde
FAIL step:re-im-drift-bound: missing DEPS lem-endpt-cont: the statement takes s,t in [0,rho_z], which presupposes rho_z < T_z (f_rho(z) defined); the source never cites it here (Fix F2)
PASS lem-c-event
PASS step:c-event-E1
PASS step:c-event-E2
PASS step:c-event-combine
PASS lem-pos-hits-before-neg
PASS step:pos-choose-C-x-y
PASS step:pos-real-part-lower-bound
PASS step:pos-imag-part-bound
PASS step:pos-segment-disjoint-L2
FAIL step:pos-real-part-sign-change: missing direct DEPS step:pos-choose-C-x-y: L2138 uses x=2C and y=7C numerically (Fix F3)
FAIL lem-disconnect-2: missing quantifier-closure bridge: the proof yields 'U^- or U^+' (random), the statement needs one deterministic U; DEPS must go through a new pigeonhole step (Fix F4, new node F5)
FAIL step:disc-setup: SOURCE_GAP understated: for x=2C, y=7C (Lemma 4.4) and any T>y^2/2 the zero-driver preimages of B_{eps/2}(x -+ 2i eps) lie within about 0.72 eps of the imaginary axis, so U^+- as required do not exist (Fix F6)
FAIL step:disc-E1-positive: missing DEPS: 'R_T contains a left-right crossing' needs R_T connected; no node supplies it (new node step:right-hull-connected) (Fix F7, new node F8)
PASS step:disc-E4-positive
FAIL step:disc-E2E3-positive: SOURCE_GAP incomplete: E3 presupposes B_{3eps}(x) disjoint from L_{T,T+2} (domain of f_{T,T+2}), stronger than Lemma 4.4's [x,y] disjoint from L_2 (Fix F20)
PASS step:disc-independence-product
FAIL step:disc-concatenation-transfer: hidden gap not recorded: 'L_{T,T+2+K} avoids B_{3eps}(x)' needs L_{T,T+2} disjoint from B_{3eps}(x), but E2 only gives disjointness from the thin rectangle [x,y]x[-eps,eps] (Fix F9)
FAIL step:disc-topological-separation: missing direct DEPS step:disc-setup: the proof invokes E1 facts (R_T in eps-nbhd of real axis, f_T(U^+-) in B_eps(x+-2i eps)) at L2194 (Fix F10)
FAIL step:disc-pullback-conclusion: used as a black box by the Thm 1.10 restart but is specific to U^+-/time T and consumes the Lemma 4.1-only separation step; missing DEPS step:disc-setup (U^+- cap L_T empty); NOTE 'deterministic union (read)' is wrong (Fix F11, new node F12)
FAIL step:disc-a-q-scale-invariance: missing DEPS def-disconnect: the event is defined through disconnection, and its invariance under z -> z/|z| consumes that notion (Fix F13)
FAIL step:disc-a-positive-measure-set: missing DEPS step:zero-in-left-hull: 0 not in U is derived from 0 in L_t (stated in NOTE, not in DEPS) (Fix F14)
PASS step:disc-a-hit-Lambda
FAIL step:disc-a-markov-restart: misuses step:disc-pullback-conclusion (specific to U^+-/T); missing DEPS: general concatenation transfer, step:disc-a-q-scale-invariance (reduction of q(f_s(z)) to the unit circle), remark-sigma (sigma_z(tau) < T_z) (Fix F15, new node F12)
PASS step:disc-a-q-positive-all-z
FAIL step:disc-a-open-condition: missing DEPS step:hull-closed: openness of C minus L_t is what makes nearby w stay in the bounded component and outside L_t (Fix F16)
PASS step:disc-a-uniform-lower-bound
FAIL eqn-disconnect-mart: same defect as step:disc-a-markov-restart: black-box use of step:disc-pullback-conclusion, missing remark-sigma (Fix F17, new node F12)
PASS step:disc-a-martingale-limit-one
FAIL thm-disconnects#proof-a: EDGE locator to step:wlog-c-nonneg cites the producer (L1950-L1951), not the consumer's use site (the Lemma 4.1 invocation at L2206) (Fix F18)
PASS step:disc-b-scale-invariance
PASS step:disc-b-positive-for-all-t
PASS step:disc-b-blumenthal
PASS step:disc-b-monotone-extension
FAIL thm-disconnects#proof-b: EDGE locator to step:wlog-c-nonneg cites the producer (L1950-L1951), not the consumer's use site (the Lemma 4.1 invocation at L2222) (Fix F19)

## 2. Coverage verdicts

PASS inv:heading:L1947
PASS inv:lem-disconnect-2
PASS inv:item-behavior-a
PASS inv:item-behavior-b
PASS inv:lem-line-approx
PASS inv:lem-haus
PASS inv:proof:L2010
PASS inv:cite:L2011:lawler-book
PASS inv:proof:L2022
PASS inv:lem-pos-hits-before-neg
PASS inv:eqn-re-ft.2
PASS inv:eqn-re-ft
PASS inv:eqn-im-ft
PASS inv:proof:L2069
PASS inv:eqn-re-im-ft
PASS inv:cond-2.2
PASS inv:cond-2
PASS inv:cond-3
PASS inv:cond-1
PASS inv:cond-4
PASS inv:proof:L2105
PASS inv:proof:L2120
FAIL inv:proof:L2160: disposition must list the new nodes step:right-hull-connected, step:disc-concat-disconnect-general and step:disc-choose-U (Fix F21)
FAIL inv:proof:L2199: disposition must list the new node step:disc-concat-disconnect-general (Fix F22)
PASS inv:eqn-disconnect-mart
PASS inv:heading:L2230
PASS inv:ques:L2237
PASS inv:cite:L2242:bp-lqg-notes
PASS inv:cite:L2242:shef-zipper
PASS inv:cite:L2242:ss-contour
PASS inv:ques:L2246
PASS inv:cite:L2252:wang-ld-survey
PASS inv:ques:L2254
PASS inv:cite:L2269:zhan-duality1
PASS inv:ques:L2271
PASS inv:cite:L2275:lawler-werness-multipoint
PASS inv:ques-transient
PASS inv:cite:L2283:beffara-dim
PASS inv:ques:L2285
PASS inv:ques:L2299
PASS inv:L1950:wlog
PASS inv:L1953:notation
PASS inv:L1966:outline
PASS inv:L2027:outline-b
PASS inv:L2041:reduction
PASS inv:L2162:def-crossing
FAIL (missing item) inv:L2023:bm-support: the uncited support-theorem claim at L2023 has no inventory item although ext:bm-support is first cited there (Fix F23, new item)
FAIL (missing item) inv:cite:L2223:blumenthal: Blumenthal's zero-one law is invoked by name at L2223 but has no item (Fix F24, new item)

## 3. Fixes

### F1 step:haus-subsequence-limit-contained

The two existing EDGE lines are repeated with unchanged locators; two EDGE lines are new.

```
DEPS: step:haus-maps-converge, defn-hulls.left, step:hull-closed, step:hulls-compact
EDGE: step:haus-maps-converge | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2017-L2017 | g^n_t -> g_t on C minus B_eps(L_t) gives L' subset B_eps(L_t) for each eps
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2017-L2017 | L_t = {T_z <= t}
EDGE: step:hull-closed | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2017-L2017 | L_t closed, so the intersection over eps of B_eps(L_t) is L_t and L' subset L_t
EDGE: step:hulls-compact | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2015-L2015 | "By compactness": the L^n_t and L_t are compact and uniformly bounded, so Hausdorff-convergent subsequences exist
NOTE: Existence of a Hausdorff-convergent subsequence uses compactness/uniform boundedness of L^n_t (step:hulls-compact, itself a SOURCE_GAP of slice C) and closedness of L_t (step:hull-closed, SOURCE_GAP of slice A); neither is cited at L2015-L2017.
```

### F2 step:re-im-drift-bound

```
DEPS: step:re-im-ft-sde, lem-endpt-cont
EDGE: step:re-im-ft-sde | source/arxiv-2203.07313v4/complex-sle-final.tex#lem:re-im-bounds@L2076-L2076 | SDEs applied on the interval [s,t]
EDGE: lem-endpt-cont | source/arxiv-2203.07313v4/complex-sle-final.tex#lem:re-im-bounds@L2049-L2049 | s,t in [0,rho_z] with rho_z < T_z so that f_t(z) exists at the endpoint; |f_t(z)| -> 0 at T_z < infinity forces rho_z < T_z
NOTE: The source uses |f_r|>=1 on [s,t] where the definition of rho gives |f_r|>1 on [0,rho). SOURCE_GAP: existence of f_rho(z) (rho < T_z; also the case T_z = infinity with |f_t|>1 for all t, where [0,rho] is not an interval of definition) is not addressed in L2043-L2077; lem-endpt-cont is the ingredient the proof of Lemma 4.4 later cites (L2134) for the same inference.
```

### F3 step:pos-real-part-sign-change

```
DEPS: lem:re-im-bounds, lem-c-event, step:pos-imag-part-bound, step:pos-choose-C-x-y
EDGE: lem:re-im-bounds | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2136-L2137 | eqn-re-ft with (s,t)=(1,2) and (0,1)
EDGE: lem-c-event | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2136-L2137 | (cond-3) and (cond-2)
EDGE: step:pos-imag-part-bound | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2136-L2136 | rho_z>=2 so the bounds are valid on [0,2]
EDGE: step:pos-choose-C-x-y | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2138-L2138 | Re f_2(x) <= 2C-3C and Re f_2(y) >= 7C-6C use x=2C, y=7C
```

### F4 lem-disconnect-2

delete the EDGE line(s) to `step:disc-independence-product` and `step:disc-pullback-conclusion`

```
DEPS: step:disc-choose-U
EDGE: step:disc-choose-U | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | "this gives the lemma statement for t = T+2+K": choice of the deterministic U among U^-, U^+ with positive probability (the former edges to step:disc-independence-product and step:disc-pullback-conclusion are now consumed by step:disc-choose-U)
```

### F5 new step:disc-choose-U

```
NODE: step:disc-choose-U
KIND: step
TITLE: Choice of the deterministic set U in {U^-, U^+} by pigeonhole
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194
CONTRACT_ID: paper.step:disc-choose-U
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: P(E_1 cap E_2 cap E_3 cap E_4) > 0 for the chosen T, eps, K; on E_1..E_4, t = T+2+K has U^- cap L_t = empty and L_t disconnects U^-, or the same for U^+ (step:disc-pullback-conclusion)
SOURCE_QUANTIFIERS: T, eps, K fixed deterministic; then a sign s in {-,+}
SOURCE_CONCLUSION: there is a deterministic sign s with P(U^s cap L_t = empty and L_t disconnects U^s from infinity) > 0 for t = T+2+K, hence the statement of Lemma 4.1 with U = U^s (non-empty, bounded, open) and t = T+2+K
CONSTANT_SCOPE: T, eps, K, s deterministic
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:disc-independence-product, step:disc-pullback-conclusion, step:disc-setup
ROUTES: -
ROUTE_FOR: -
EDGE: step:disc-independence-product | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2181-L2181 | P(E_1 cap ... cap E_4) > 0
EDGE: step:disc-pullback-conclusion | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | on the four events one of U^-, U^+ is disconnected by L_{T+2+K} and avoided by it
EDGE: step:disc-setup | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2165-L2165 | U^+- are deterministic, bounded, open and (needed) non-empty
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: reviewer-D/sonnet (proposed by reviewer; orchestrator to adopt)
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Quantifier closure / witness choice. SOURCE_GAP: the source says only 'this gives the lemma statement for t = T+2+K'. The disconnected set is random (U^- or U^+ depending on omega), and the lemma needs one deterministic U; P(A^-) + P(A^+) >= P(E_1 cap ... cap E_4) > 0 selects a sign. The extractor's reading 'U is the deterministic union' (NOTE of step:disc-pullback-conclusion) is not valid: on the event only one of the two sets is disconnected, so the union is not. Non-emptiness of U^+- depends on step:disc-setup (see F6).
```

### F6 step:disc-setup

```
NOTE: SOURCE_GAP: existence of non-empty open U^+- satisfying both requirements (distance >= 2 eps from the imaginary axis; mapped by z -> sqrt(z^2+4T) into B_{eps/2}(x -+ 2 i eps)) is asserted at L2165, not shown. Reviewer computation (to be confirmed by the orchestrator): the preimage of w = x -+ 2 i eps is z with z^2 = w^2-4T, |Re z| ~ 2 x eps / sqrt(4T-x^2), and the preimage of B_{eps/2}(w) has |Re z| <= ~ 2.5 x eps / sqrt(4T-x^2) as eps -> 0. A point at distance >= 2 eps from the imaginary axis therefore needs x / sqrt(4T-x^2) >~ 0.8. For the choice made in the proof of Lemma 4.4 (x = 2C, y = 7C, so x/y = 2/7) and any T > y^2/2 one has x / sqrt(4T-x^2) < 0.21 (numerically max |Re z|/eps = 0.72 at C = 1, T = 13, eps = 0.01), so U^+- would be empty. Lemma 4.4 is stated existentially ('we can choose 0<x<y'), so the proof of Lemma 4.1 may not re-pick x, y. The text also writes (B_t) for measurability; the hulls depend on U = (B, B~).
```

### F7 step:disc-E1-positive

```
DEPS: lem-haus, lem-line-approx, step:disc-setup, step:right-hull-connected
EDGE: lem-haus | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2180-L2180 | cited as the source of P(E_1)>0
EDGE: lem-line-approx | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2180-L2180 | the Hausdorff/uniform closeness statements that give containment in eps-neighborhoods and f_T(U^+-) subset B_eps(x +- 2i eps) are those of Lemma 4.2
EDGE: step:disc-setup | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2169-L2169 | definition of E_1 and of U^+-
EDGE: step:right-hull-connected | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2169-L2169 | "R_T contains a left-right crossing of [x,y]x[-eps,eps]": a connected R_T Hausdorff-close to [-2T^{1/2},2T^{1/2}] supplies the crossing
NOTE: SOURCE_GAP: (i) the source cites Lemma 4.3 directly; the closeness statements it needs are those of Lemma 4.2, recorded as an additional dependency; (ii) the crossing needs connectedness of R_T, now carried by step:right-hull-connected (itself a SOURCE_GAP); (iii) 'for each T, eps > 0' cannot hold for eps large compared with 2T^{1/2} - y, and the existence of U^+- is in doubt (see step:disc-setup, F6).
```

### F8 new step:right-hull-connected

```
NODE: step:right-hull-connected
KIND: step
TITLE: Right hulls R_t are connected
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2169-L2169
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2169-L2169
CONTRACT_ID: paper.step:right-hull-connected
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U : [0,infinity) -> C continuous; t >= 0 (used for T)
SOURCE_QUANTIFIERS: U; t >= 0
SOURCE_CONCLUSION: R_t is connected (and non-empty)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-hulls.right
ROUTES: -
ROUTE_FOR: -
EDGE: defn-hulls.right | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2169-L2169 | R_T = C minus the range of f_T
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: reviewer-D/sonnet (proposed by reviewer; orchestrator to adopt)
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: the source never states connectedness of right hulls. Slice A froze only the left-hull part of Lemma 2.4 (R16) and records that the right hull would follow from the duality (2.4) (not a node) and Lemma 2.4. E_1 (crossing of [x,y]x[-eps,eps] by R_T) and the topological step at L2194 consume it, so right-hull connectedness now feeds a root and the orchestrator must decide whether to graph eqn-duality / a right-hull analogue of lem-connected.left.
```

### F9 step:disc-concatenation-transfer

```
NOTE: Typo: the third bullet writes f_{T+2}(B_{3eps}(x)); read f_{T,T+2}. SOURCE_GAP: (i) 'L_{T,T+2+K} does not intersect B_{3eps}(x)' needs L_{T,T+2} cap B_{3eps}(x) = empty (this is also the domain condition for f_{T,T+2}(B_{3eps}(x)) in E_3), but E_2 only gives L_{T,T+2} disjoint from the thin rectangle [x,y]x[-eps,eps], which does not contain B_{3eps}(x). (ii) The transfer via (2.3) also involves the term R_{T,T+2} in L_{T,T+2+K} = L_{T,T+2} cup f_{T,T+2}^{-1}(L_{T+2,T+2+K}\R_{T,T+2}); this is not discussed. (iii) 'S avoids f_T(U^+-)' is automatic only because f_T(U^+-) lies in the range of f_T, i.e. needs U^+- cap L_T = empty.
```

### F10 step:disc-topological-separation

```
DEPS: step:disc-concatenation-transfer, def-disconnect, defn-hulls.right, step:disc-setup
EDGE: step:disc-concatenation-transfer | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | L_{T,T+2+K} meets S but not B_{3eps}(x)
EDGE: def-disconnect | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | notion of disconnection from infinity
EDGE: defn-hulls.right | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | R_T contained in the eps-neighborhood of the real axis and contains the crossing S
EDGE: step:disc-setup | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | E_1: R_T within eps of the real axis and f_T(U^+-) subset B_eps(x +- 2i eps) subset B_{3eps}(x) minus R_T
```

### F11 step:disc-pullback-conclusion

delete the EDGE line(s) to `eqn-conc`, `def-disconnect` and `defn-hulls.left`

```
DEPS: step:disc-topological-separation, step:disc-concat-disconnect-general, step:disc-setup
EDGE: step:disc-topological-separation | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | disconnection of f_T(U^+-) by L_{T,T+2+K} cup R_T
EDGE: step:disc-concat-disconnect-general | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | "By the concatenation property": instance s=T, t=2+K, point in U^+-
EDGE: step:disc-setup | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | E_1 and the choice of U^+-: U^+- cap L_T = empty, so f_T is defined on U^+-
NOTE: Carrier change z <-> f_T(z); an instance of step:disc-concat-disconnect-general. Which of U^-, U^+ occurs is random; the deterministic choice is made in step:disc-choose-U (the earlier reading 'U is the deterministic union' is withdrawn).
```

### F12 new step:disc-concat-disconnect-general

```
NODE: step:disc-concat-disconnect-general
KIND: step
TITLE: Concatenation transfer: disconnection by L_{s,s+t} cup R_s of f_s(z) pulls back to disconnection of z by L_{s+t}
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207
CONTRACT_ID: paper.step:disc-concat-disconnect-general
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U continuous; s, t >= 0; z in C with z not in L_s (T_z > s); L_{s,s+t}, R_s as in (2.3); L_{s,s+t} cup R_s disconnects f_s(z) from infinity and f_s(z) is not in L_{s,s+t}
SOURCE_QUANTIFIERS: U; s,t; z (pathwise, s may be a stopping time)
SOURCE_CONCLUSION: z not in L_{s+t} and L_{s+t} disconnects z from infinity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-conc, def-disconnect, defn-hulls.left, defn-hulls.right
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-conc | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | L_{s+t} = L_s cup f_s^{-1}(L_{s,s+t}\R_s); f_s maps C\L_s into C\R_s
EDGE: def-disconnect | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | disconnection from infinity and disjointness
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | L_{s+t}, L_s, z not in L_{s+t} iff T_z > s+t
EDGE: defn-hulls.right | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | R_s is the complement of the range of f_s, so f_s(z) not in R_s
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: reviewer-D/sonnet (proposed by reviewer; orchestrator to adopt)
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: the source states this transfer only inside the proof of Lemma 4.1 ('By the concatenation property (2.3)', instance s = T, point in U^+-) and again, tacitly, as 'exactly as in the proof of Proposition 3.2(b)' at L2207/L2212 with s = sigma_z(tau) or sigma_z(t~) and an arbitrary z. The general form is the reused claim; it is the inequality (not the equality of Prop 3.2(b)) because disconnection may already occur before s.
```

### F13 step:disc-a-q-scale-invariance

```
DEPS: lem-scaling, eqn-scale, defn-hulls.left, def-disconnect
EDGE: lem-scaling | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2205-L2205 | law of the chain is invariant under r^{-1} f_{r^2 t}(r.)
EDGE: eqn-scale | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2205-L2205 | hulls and absorbing times scale: L_t^{rU(./r^2)} = r L_{t/r^2}
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2203-L2203 | event defined through left hulls and T_z
EDGE: def-disconnect | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2205-L2205 | disconnection from infinity is preserved by the scaling z -> z/|z|
```

### F14 step:disc-a-positive-measure-set

```
DEPS: lem-disconnect-2, step:disc-a-q-scale-invariance, def-disconnect, defn-hulls.left, step:zero-in-left-hull
EDGE: lem-disconnect-2 | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2206-L2206 | positive probability that L_t disconnects U from infinity avoiding it
EDGE: step:disc-a-q-scale-invariance | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2206-L2206 | q(w)>0 for w in U transfers to z/|z|; the radial projection of a non-empty open set is a non-empty open arc set
EDGE: def-disconnect | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2206-L2206 | w in U with U cap L_t = empty is disconnected before T_w
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2206-L2206 | w not in L_t iff T_w>t
EDGE: step:zero-in-left-hull | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2206-L2206 | 0 in L_t for all t, so U cap L_t = empty gives 0 not in U and z/|z| is defined on U
```

### F15 step:disc-a-markov-restart

delete the EDGE line(s) to `step:disc-pullback-conclusion`

```
DEPS: lem-scaling, lem-markov, defn-sigma, remark-sigma, step:disc-a-q-scale-invariance, step:disc-concat-disconnect-general
EDGE: lem-scaling | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207 | rescale the restarted chain to unit-circle start (Prop 3.2(b) L1804)
EDGE: lem-markov | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207 | domain Markov property at the stopping time sigma_z(tau)
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207 | sigma_z(tau) is a stopping time for the driver filtration
EDGE: remark-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207 | sigma_z maps (0,infinity) into (0,T_z): z is not in L_{sigma_z(tau)} so f_{sigma_z(tau)}(z) exists
EDGE: step:disc-a-q-scale-invariance | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207 | q(f_s(z)) = q(f_s(z)/|f_s(z)|) = q(e^{i theta^_tau(z)}) for the restarted point
EDGE: step:disc-concat-disconnect-general | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207 | disconnection of f_s(z) by the restarted left hull (together with R_s) pulls back to disconnection of z by the original hull
```

### F16 step:disc-a-open-condition

```
DEPS: def-disconnect, defn-hulls.left, step:hull-closed
EDGE: def-disconnect | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2209-L2209 | z lies in a bounded component of the open set C minus L_t, so do nearby points
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2209-L2209 | w not in L_t iff T_w>t
EDGE: step:hull-closed | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2209-L2209 | C minus L_t is open, so a ball around z stays inside the same bounded component and outside L_t
```

### F17 eqn-disconnect-mart

delete the EDGE line(s) to `step:disc-pullback-conclusion`

```
DEPS: lem-scaling, lem-markov, defn-sigma, remark-sigma, step:disc-a-uniform-lower-bound, step:disc-concat-disconnect-general
EDGE: lem-scaling | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2212-L2212 | scale invariance of the restarted chain
EDGE: lem-markov | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2212-L2212 | strong Markov property at sigma_z(t~)
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2216-L2216 | sigma_z as in Definition 2.9
EDGE: remark-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2212-L2212 | sigma_z(t~) < T_z, so the restart point f_{sigma_z(t~)}(z) exists
EDGE: step:disc-a-uniform-lower-bound | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2212-L2212 | the uniform bound q_*
EDGE: step:disc-concat-disconnect-general | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2212-L2212 | disconnection by the restarted left hull pulls back to disconnection of z (inequality, not equality)
```

### F18 thm-disconnects#proof-a

```
EDGE: step:wlog-c-nonneg | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2206-L2206 | Lemma 4.1 (and through it Lemma 4.6) is only proved for c>=0, so the Lemma 4.1 invocation presupposes the section's WLOG reduction
```

### F19 thm-disconnects#proof-b

```
EDGE: step:wlog-c-nonneg | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2222-L2222 | Lemma 4.1 is only proved for c>=0, so the Lemma 4.1 invocation presupposes the section's WLOG reduction
```

### F20 step:disc-E2E3-positive

```
NOTE: SOURCE_GAP: Lemma 4.4 gives disjointness of the segment [x,y] from L_2 and a sign change of Re f_2 on the endpoints. E_2 requires (a) disjointness from the thickened rectangle [x,y]x[-eps,eps], (b) that the image of every left-right crossing of this rectangle contains a left-right crossing of [-eps,eps]x[-2K^{1/2}+eps,2K^{1/2}-eps] (needs continuity/compactness and a choice of eps,K, and eps small compared with |Re f_2(x)|, |Re f_2(y)|, which Lemma 4.4's statement does not quantify). E_3 needs B_{3eps}(x) cap L_{T,T+2} = empty (domain of f_{T,T+2}) and a continuity estimate near x. This bridge, including the choice 'for some eps,K', is not argued.
```

### F21 inv:proof:L2160

```
DISPOSITION: NODE step:disc-setup, step:disc-E1-positive, step:right-hull-connected, step:disc-E4-positive, step:disc-E2E3-positive, step:disc-independence-product, step:disc-concatenation-transfer, step:disc-topological-separation, step:disc-pullback-conclusion, step:disc-concat-disconnect-general, step:disc-choose-U, lem-disconnect-2
```

### F22 inv:proof:L2199

```
DISPOSITION: NODE thm-disconnects#proof-a, thm-disconnects#proof-b, step:disc-a-q-scale-invariance, step:disc-a-positive-measure-set, step:disc-a-hit-Lambda, step:disc-a-markov-restart, step:disc-a-q-positive-all-z, step:disc-a-open-condition, step:disc-a-uniform-lower-bound, eqn-disconnect-mart, step:disc-a-martingale-limit-one, step:disc-concat-disconnect-general, step:disc-b-scale-invariance, step:disc-b-positive-for-all-t, step:disc-b-blumenthal, step:disc-b-monotone-extension
```

### F23 new inv:L2023:bm-support

```
ITEM: inv:L2023:bm-support
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L2023:bm-support@L2023-L2023
DISPOSITION: NODE ext:bm-support
REASON: 'The driving Brownian motion has a positive chance to be arbitrarily close to 0 on [0,T]' is an uncited standard (support) theorem used by Lemma 4.2; first citation point of ext:bm-support (also used at L2106-2107)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: reviewer-D/sonnet (proposed by reviewer; orchestrator to adopt)
REVIEWER: -
```

### F24 new inv:cite:L2223:blumenthal

```
ITEM: inv:cite:L2223:blumenthal
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L2223:blumenthal@L2223-L2223
DISPOSITION: NODE ext:blumenthal
REASON: Blumenthal's zero-one law invoked by name in the proof of Theorem 1.10(b)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: reviewer-D/sonnet (proposed by reviewer; orchestrator to adopt)
REVIEWER: -
```
