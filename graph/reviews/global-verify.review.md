# Global root-closure review (fresh final verifier)

Reviewer tag: global-verifier/sonnet. Independent of graph/reviews/*.md (opened only after my own pass, for context). Inputs read: full source L225-L2406 (non-commented parts; L1-L224 front matter skipped), ERRATA.md, graph/EXTRACTION_SPEC.md, graph/anchor-table.md, frozen-anchor-manifest.json identity fields (id, kind, path, export, contract, abi_sha256; I did not use `state`), statement parts of all 14 root files and 17 definition files under ComplexSLE/Frozen/, DEPGRAPH.md (286 nodes) and DEPGRAPH_COVERAGE.md (306 items). No Internal/, proof bodies, sorry, axioms, STATUS.md or Lean was inspected or run. Only this file was written. (An incidental print of a manifest `state` value for one anchor occurred while probing the JSON keys; it was not used.)

Mechanical checks (own script on DEPGRAPH.md): 286 nodes, 0 dangling DEPS, 0 cycles, DEPS set = EDGE-target set for every node, 0 route nodes, every one of the 14 roots is a frozen anchor, 31 frozen nodes (17 definitions + 14 theorems) match anchor-table.md and the manifest on id, kind, path, export, contract id/version and ABI hash, every non-anchor has FROZEN_*: - and CONTRACT_ID paper.<id>/1, all 17 definition anchors have an incoming edge, 0 nodes outside every root closure (the five nodes with in-degree 0 are exactly the roots nonsource.exists-sle-driver, thm-phases, thm-phases.c-zero, thm-disconnects.a/.b). Closure sizes: well-defined 7, lem-p.exists 17, exists-sle-driver 5, thm-phases 196, c-zero 212, disconnects.a 115, .b 93, prop-i.a 125, prop-i.b 124, prop-ii.a 135, prop-ii.b 160, lem-connected.left 18, eqn-scale.left 9, eqn-reflect.left 9. EDGE-locator audit (own script, locator inside the consumer's statement or proof range): 31 outliers, all adjacent-line or statement/proof-split cases; no real use-site error.

## 1. Root-by-root verdicts

### defn-loewner.well-defined -- PASS
- Spans re-read and four-field comparison: L251-L263 (Def 1.1), L266-L268 (T_z), L674 (ODE existence remark). Fields: U continuous; any z; solution on [0,T_z) and agreement of two solutions on a common [0,tau); this equals the frozen loewner_wellDefined. Closure (7 nodes): solution/absorbing-time definitions, Picard-Lindelof external, local existence, global uniqueness, gluing; all three bridges carry SOURCE_GAP (source says only "defined up to some time T_z"). No premise or quantifier issue.

### lem-p.exists -- PASS
- Spans re-read and four-field comparison: L941-L955, L1024-L1111, L963-L966. Fields: a,b>0, c^2<=ab (R5), exists admissible p (R7); frozen exists_admissibleDensity agrees. Closure (17): WLOG c>=0, case 1 (p0,p1, periodicity, r_*>=0 via the integral of mu/D, which I checked numerically against the printed closed form; the formula is singular exactly at a=b, c=0 where the integral is 0), case 2 (L'Hopital limits, regularity). Normalization int_0^{2pi}p=1 in case 2 and p1(pi)>0 are tagged SOURCE_GAP. AND over the two cases is correct (they partition c>=0).

### nonsource.exists-sle-driver -- PASS
- Spans re-read and four-field comparison: L301-L319 and R6/R13. Fields match frozen exists_sleDriver (Omega : Type; a.s. continuity, U_0=0, independent Gaussian increments with covariance (t-s)Sigma). Closure: defn-sle, covMatrix, complexGaussian, ext:bm-existence (E14). The external states existence of the planar BM with covariance Sigma, which is exactly what the root needs.

### thm-phases -- FAIL (repairable)
- Spans re-read and four-field comparison: L437-L453, L1930-L1932, R4,R5,R7,R15,R17. Fields: a,b>0, c^2<=ab, every admissible p, four sign implications with the exact strict/non-strict signs of L445-L448; probability-space quantifier sits inside the phase definitions (R9). The four-case assembly (thm-phases#assembly-sign-cases: T_z=infinity/limit-distance dichotomies via monotonicity of L_t) is complete, and Props 3.1/3.2 premises (p admissible, hI/hII, z!=0, any (Omega,P,U)) are discharged at that node. Closure (196) reaches step:zero-in-left-hull (F4), lem-recurrence and step:wlog-c-nonneg-arg (F5, F6).

### thm-phases.c-zero -- FAIL (repairable)
- Spans re-read and four-field comparison: L450, L1824-L1927, L1930-L1932, P8,R5,R17. Fields match frozen theorem_1_8_c_zero (no p, three conclusions, a-b=8 in hitting via Lemma 3.12). Closure (212): Lemma 3.11 via the explicit density (SOURCE_GAP, identified only for the constructed p, which suffices because lem-c0-phases/lem-c0-bdy are fed that p), sign analysis, Lemma 3.12 (finite T_z via prop-i.b with (I)<0 discharged by the c=0 integrals). Same repairs as thm-phases (F4, F5, F6).

### thm-disconnects.a -- FAIL (repairable; plus AUTHOR_BLOCKED P10, which PASSES as a faithfully exposed gap)
- Spans re-read and four-field comparison: L502-L507, L1947-L1956, L2160-L2217. Fields: a,b>0 (R5), z!=0 (R4), a.s. exists t>0 with z not in L_t and L_t disconnecting z. The source-quantifier record omits the (Omega,P,U) quantifier that the frozen statement and R9 require (F1). Closure (115) reaches step:zero-in-left-hull (F4), step:connected-loop-criterion (F7). P10 chain: step:disc-setup (refuted construction of U^{+-}), lem-disconnect-2, step:disc-choose-U; the roots' NOTEs flag AUTHOR_BLOCKED. I re-derived the P10 failure (preimage of B_{eps/2}(x -+ 2i eps) under z -> sqrt(z^2+4T) has |Re z| < 0.7 eps for x=2C, y=7C, T>y^2/4, so no set at distance 2 eps from iR exists).

### thm-disconnects.b -- FAIL (repairable; plus AUTHOR_BLOCKED P10, exposed)
- Spans re-read and four-field comparison: L502-L509, L2220-L2224. Fields: a.s., for every t>0 (P7), interior of the disconnected set non-empty. Same missing (Omega,P,U) quantifier (F2); closure (93) reaches step:connected-loop-criterion (F7). The quantifier closure over all t is modeled (Blumenthal, monotonicity of L_t); P10 as for (a).

### prop-i.a -- FAIL (repairable)
- Spans re-read and four-field comparison: L1255-L1269, L1401-L1407, L1294-L1319, L1327-L1397. Fields match frozen proposition_3_1_a (every admissible p, any (Omega,P,U), z!=0, hI). Premise discharge verified: Lemma 3.4 via step:prop-i-apply-stationary-sde (X recurrence from lem-recurrence, stationarity from lem-stationary, f^0=nu, E nu = (I) from (3.1), Y_0 = 0); Lemma 3.3 via step:all-z-apply-Tz and the null-set SOURCE_GAP; product extension for zz. Closure reaches lem-recurrence/step:wlog-c-nonneg-arg (F5, F6).

### prop-i.b -- FAIL (repairable)
- Spans re-read and four-field comparison: L1265-L1270, L1408-L1416; same as prop-i.a; ODE comparison (F'e^{-alpha F}>1 gives T_zz<=t_*+e^{-alpha F(t_*)}/alpha) checked by hand. F5, F6.

### prop-ii.a -- FAIL (repairable)
- Spans re-read and four-field comparison: L1276-L1281, L1428-L1469; epsilon-form via R14; Koebe (3.5) with compactness and 0 in R_t as SOURCE_GAPs, Lemma 3.7 via Lemma 3.4. F5, F6.

### prop-ii.b -- FAIL (repairable)
- Spans re-read and four-field comparison: L1276-L1283, L1475-L1816. Lemma 3.8 (contrapositive via (3.6), Lemma 3.9, Lemma 3.10, Lemma 3.7), Girsanov step, Koebe ball step, martingale 0-1. Missing consumer edge to claim:hulls-monotone for the lim-to-epsilon conversion (F3); step:zero-in-left-hull premise (F4); F5, F6.

### lem-connected.left -- FAIL (repairable)
- Spans re-read and four-field comparison: L658-L666 (+L284, L286, L268). Fields: continuous U, each t, L_t connected; the added "(and nonempty)" matches Mathlib IsConnected and claim:hull-nonempty (SOURCE_GAP). The planar reduction step lacks the boundedness premise (F7).

### eqn-scale.left -- PASS (label fix F8)
- Spans re-read and four-field comparison: L547-L552, L545 (T7). Fields match scaling_leftHull; closure 9 nodes (definitions, well-definedness). The source gives no proof; the gap is exposed in NOTE but lacks the SOURCE_GAP token (F8).

### eqn-reflect.left -- PASS (label fix F9)
- Spans re-read and four-field comparison: L553-L558, L547. Fields match reflection_leftHull (both conjuncts); same labeling remark (F9).

Tallies: PASS 5 (well-defined, lem-p.exists, exists-sle-driver, eqn-scale.left, eqn-reflect.left; the last two with a label-only fix), FAIL repairable 9 (thm-phases, c-zero, prop-i.a/.b, prop-ii.a/.b, lem-connected.left, thm-disconnects.a/.b), of which disconnects.a/.b additionally carry the AUTHOR_BLOCKED P10 chain (passes topology as exposed). No root requires a new node.

## 2. Global findings

- G1 (S1, repaired by F5/F6) Sign defect in the critical case of Lemma 2.16. The printed bullet "if |c| = sqrt(ab) then recurrence at e^{2ix}, tan x = sqrt(b/a)" is proved by the written argument only for c = +sqrt(ab) (WLOG c >= 0, then D^{-1}(0) = x + pi Z). For c = -sqrt(ab), D = (sqrt a sin u + sqrt b cos u)^2/2 vanishes at u = -x, and the WLOG conjugation produces e^{-2ix}. step:wlog-c-nonneg-arg (a global-reviewer record) claimed "recurrence at e^{2ix} is equivalent to recurrence at conj(w)", which is wrong for that case. Consumers only need some deterministic point, so the closure is intact once the sign is stated.
- G2 (S1, repaired by F1/F2) The two Theorem 1.10 roots do not record the (Omega,P,U) quantifier (R9) in SOURCE_QUANTIFIERS although the frozen statements and every probabilistic Section 3 root carry it.
- G3 (S2, repaired by F3) prop-ii.b converts "lim dist > 0" to the frozen epsilon-form (R14) by monotonicity of L_t, but has no direct edge to claim:hulls-monotone (it is only in the closure through an unrelated use). prop-ii.a needs no such edge (R14 form follows from the definition of the limit) and has the edge through step:prop-ii-a-koebe-limit anyway.
- G4 (S2, repaired by F4) step:zero-in-left-hull states U_0 = 0 as a hypothesis but nothing in DEPS supplies it; the supplier is the driver definition (IsSLEDriver.zero). Affects lem-log-finite-exp (log(1/dist) >= 0) and step:disc-a-positive-measure-set.
- G5 (S2, repaired by F7) The planar reduction in the proof of Lemma 2.4 ("it is enough to show that the region bounded by L misses L_t") is false for unbounded closed sets and so needs L_t bounded; the node had only closedness. Also the "origin" in L662 should be U_0 for general U (noted, T5-adjacent).
- G6 (S3, labeling, F8-F13) Six nodes whose whole proof is "see [Lu, Section 2]" (eqn-scale.left, eqn-reflect.left, eqn-scale, eqn-reflect, eqn-conc, eqn-duality) expose the missing proof only in prose, without the SOURCE_GAP: token. Gap dashboards that count the token undercount them. I do not ask for new nodes (the statements are the gap).
- G7 P10 re-verified independently (see thm-disconnects.a above): AUTHOR_BLOCKED chain = step:disc-setup, step:disc-E1-positive, step:disc-concatenation-transfer, step:disc-topological-separation, step:disc-pullback-conclusion, step:disc-choose-U, lem-disconnect-2, thm-disconnects#proof-a/b and both roots. It is a faithfully exposed gap and passes topology review; no Lean task should be scheduled on these until the author rules. I also checked the neighbouring Lemma 4.4/4.6 arithmetic (cond-1..cond-4, Re f_2(x) <= -C, Re f_2(y) >= C): correct; but note y/x = 7/2 > 2 is forced by [-6C,-3C], so the ratio needed by the repaired U^{+-} cannot be reached by re-picking x,y.
- G8 T8 (new, not in ERRATA): (2.3) third formula f_t(L_{s+t}\L_t) = L_{t,s+t} cannot hold as printed (0 lies in L_{t,s+t} and in R_t = complement of the range of f_t); the graph reads it as L_{t,s+t}\R_t in eqn-conc NOTE. Consumers (step:future-point-outside-hulls, step:log-finite-exit-times, step:converse-event-converges) still quote the printed form in EDGE text; harmless but should be ruled.
- G9 Rulings coverage: R7/R15 make Thm 1.8 and Props 3.1/3.2 hold for every admissible p; Lemmas 2.16, 3.3, 3.7-3.10 are modeled for every admissible p as well (their proofs only use stationarity, absolute continuity and pi-periodicity). This is a reading, not a ruling; and the step "an admissible p vanishes only on a Lebesgue-null set" (step:all-z-null-set-density) is a SOURCE_GAP that Lemma 3.3 needs. Author should confirm both (see section 6).
- G10 Quantifier/carrier/normalization audit with no further defect: z vs zz (only via Lemma 3.3 plus product extension step:section3-product-extension, PASS below); theta vs e^{2 i theta} vs e^{i theta} (Lemma A.1 applied to 2p, step:stat-kolmogorov-normalization, step:stat-pi-reduction; the diffusion coefficients of e^{2i theta^} being only 2pi-periodic is correctly tagged in step:stationary-sde-X-form); int_0^pi vs int_0^{2pi}; capacity time vs sigma-time (remark-sigma); hull-level vs map-level reflection (step:reflect-map-identity); WLOG c >= 0 at three places with three meanings (L323/L1951 hull level, L1026 density, L1165 argument process; the third repaired by F5).
- G11 AND/OR: no alternative derivations exist in the source (the Lemma 4.4 citation of Remark 2.12 vs Lemma 2.5 is one implication cited twice, recorded as an alternate citation); case splits (Lemma 2.13 c<sqrt(ab)/c=sqrt(ab); Lemma 2.14 noncritical/critical) are correctly conjunctive; no route nodes needed.
- G12 Proof-paragraph coverage in the closure: every substantive paragraph L658-L691, L774-L797 (Prop 1.5 proof excluded: feeds no root), L836-L929, L963-L994, L1024-L1111, L1136-L1138, L1155-L1230, L1294-L1319, L1327-L1397, L1401-L1418, L1430-L1469, L1475-L1816, L1824-L1932, L1991-L2217, L2318-L2402 has a node or a justified exclusion (outline/commentary items, Lemma 2.6, Sections 2.4 and 5, Remarks 1.3/1.6/1.11). 306 coverage items: 210 NODE, 96 EXCLUDED, all targets exist, every node is referenced. Residual untagged but substantive prose in NOTEs (step:disc-a-open-condition "asserted without proof", step:c-event-E1, step:p-case1-mu-over-D-integral edge case a=b, c=0) is routine or elementary; I did not require tags for them.
- G13 External boundaries are explicit and complete for what proofs invoke (19 externals; ext:kolmogorov-zero-one is an addition outside the spec table and is correctly reported; standard tools quoted only in commented blocks or below threshold are not nodes). T6/Lawler 4.43 extension (ext:loewner-convergence, step:haus-maps-converge) and Lawler 4.5 (ext:lawler-4.5, claim:gt-conformal) are tagged SOURCE_GAP.
- G14 Count discrepancy: the task says 11 global-reviewer/sonnet records; I find 10 (5 nodes: step:right-hull-connected, eqn-duality, step:reflect-map-identity, step:wlog-c-nonneg-arg, step:section3-product-extension; 5 coverage items: inv:eqn-duality, inv:lem-connected, inv:L554:reflect-map-identity, inv:L1165:wlog-arg, inv:L1255:product-extension). I found no eleventh record carrying that EXTRACTOR tag.

## 3. PASS/FAIL for global-reviewer-authored records

Nodes
- PASS step:right-hull-connected (re-read L658-L663, L567-L570): statement R_t connected for continuous U; DEPS defn-hulls.right, eqn-duality, lem-connected.left are the right inputs (dual driver s -> i(U(t)-U(t-s)) on [0,t]); EDGE locators in L662-L663; the unstated "L_t depends only on U|[0,t]" is recorded in NOTE. It consumes the root lem-connected.left, which is acyclic (that root does not reach this node). Consumers E1 and the topological-separation step are right.
- PASS (label fix F13) eqn-duality (L567-L570, L547): fields match (2.4) including the driver s -> i(U(t)-U(t-s)); DEPS definitions plus well-definedness; "do not fill" respected; lacks the SOURCE_GAP: token only.
- PASS step:reflect-map-identity (L553-L558, L547, L984, L1165): map-level identity and the derived theta shifts (theta^{-U}(-z) = theta^U(z)+pi, theta^{U*}(z*) = -theta^U(z)) are correct; tagged SOURCE_GAP; DEPS are right and acyclic; used by step:stat-pi-reduction (source: (f_t(zz)) =_d (f_t(-zz)) =_d (-f_t(zz)) needs exactly this plus -U =_d U) and by step:wlog-c-nonneg-arg.
- FAIL (repairable, F5) step:wlog-c-nonneg-arg (L1155-L1165): conjugation/p~ bookkeeping and DEPS (defn-sle, eqn-cov-matrix, step:reflect-map-identity, step:p-wlog-c-nonneg, def-arg, defn-sigma) are right, but the SOURCE_CONCLUSION asserts that recurrence at e^{2ix} transfers under conjugation; for c = -sqrt(ab) it transfers to e^{-2ix} (finding G1).
- PASS step:section3-product-extension (L939, L1255, L1252-L1259): product space Omega x [0,2pi) with P (x) p(u)du, U~(omega,u) = U(omega) an SLE_Sigma driver, zz = e^{iu} independent with the right law, events of U alone keep their probability, a.s. read as null complement (R9); DEPS defn-sle and lem-stationary.admissible suffice; consumed by exactly the six probabilistic Section 3 roots. The internal Section 3 nodes carry the package as a local hypothesis, which is consistent with spec section 4.
Coverage items
- PASS inv:eqn-duality (L568; maps to eqn-duality).
- PASS inv:lem-connected (L658-L660; maps to lem-connected.left, claim:hull-nonempty, step:right-hull-connected; the proof items inv:proof:L661 etc. map to the connected-* steps).
- PASS inv:L554:reflect-map-identity (L553-L558; maps to step:reflect-map-identity).
- PASS inv:L1165:wlog-arg (L1165; maps to step:wlog-c-nonneg-arg; the item itself is accurate, the node needs F5).
- PASS inv:L1255:product-extension (L1255; maps to step:section3-product-extension).

## 4. Fixes (changed lines only; no new records)

### F1 thm-disconnects.a
```
SOURCE_QUANTIFIERS: a, b, c; probability space (Omega,P) and SLE_Sigma driver U (R6, R9); z in C\{0} (R4); a.s.
```

### F2 thm-disconnects.b
```
SOURCE_QUANTIFIERS: a, b, c; probability space (Omega,P) and SLE_Sigma driver U (R6, R9); a.s.; for all t > 0 (P7)
```

### F3 prop-ii.b
```
DEPS: item-II, defn-hulls.left, defn-loewner.absorbing-time, step:prop-ii-b-martingale-zero-one, step:section3-product-extension, claim:hulls-monotone
EDGE: claim:hulls-monotone | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1815-L1815 | L_t is increasing, so t -> dist(z,L_t) is non-increasing and the almost sure limit lim_{t->T_z-} dist(z,L_t) > 0 equals the infimum over t < T_z; this converts the proved limit statement into the frozen epsilon-form (R14) with epsilon := that infimum
```

### F4 step:zero-in-left-hull
```
DEPS: defn-hulls.left, defn-loewner.absorbing-time, defn-sle
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1558-L1558 | U_0 = 0 almost surely is part of the SLE_Sigma driver (R6); this supplies the premise U_0 = 0 (T_0 = 0, so 0 in L_t) that is otherwise only a hypothesis of this node
NOTE: R4: U_0 = 0, so T_0 = 0 and 0 in L_t for all t. Used at L1558. The shifted-driver statement for L_{t,s+t} used at L1768 is step:zero-in-future-left-hull. Premise U_0 = 0 is supplied by defn-sle (a.s. U_0 = 0, R6); for a general continuous driver the correct statement is U_0 in L_t (claim:hull-nonempty).
```

### F5 step:wlog-c-nonneg-arg
```
SOURCE_CONCLUSION: the conclusion of lem-recurrence for (a,b,c,p) follows from that for (a,b,-c, p~) with p~(u) = p(-u): conjugating U gives an SLE_{Sigma~} driver, Sigma~ = [[a,-c],[-c,b]], conj(zz) has angle density p~, theta^ becomes -theta^ and e^{2i theta^} becomes its conjugate, so recurrence at w for (a,b,-c,p~) is equivalent to recurrence at conj(w) for (a,b,c,p); in the critical case c = -sqrt(ab) the recurrent point obtained this way is conj(e^{2ix}) = e^{-2ix} (the zero of D(u) = (sqrt a sin u + sqrt b cos u)^2/2), not the printed e^{2ix} with tan x = sqrt(b/a)
NOTE: SOURCE_GAP: the source writes only 'Assume without loss of generality that c >= 0' for a statement about the argument process. SOURCE_GAP (sign): the printed second bullet of Lemma 2.16 (point e^{2ix}, tan x = sqrt(b/a)) is proved by the written argument only for c = +sqrt(ab); for c = -sqrt(ab) the reduction yields the point e^{-2ix}; recurrence at e^{2ix} for c = -sqrt(ab) is not supplied (it would need irreducibility of the diffusion, which is unstated). Consumers (lem-stationary-sde applications) need only some deterministic point, so e^{-2ix} suffices. Distinct from step:wlog-c-nonneg (hull level, used at L323/L1951) and from step:p-wlog-c-nonneg (admissibility of p~ only).
```

### F6 lem-recurrence
```
NOTE: R5. Statement says 'p as in Lemma 2.13': read per R7/R15 as admissible p (the proof only uses stationarity of the law of e^{2i theta}, absolute continuity of its law, and pi-periodic coefficients). In the |c|<sqrt(ab) case the source says 'Let w in bdy D'; in the critical case w = e^{2ix} is forced. SOURCE_GAP (sign): for c = -sqrt(ab) the point e^{2ix}, tan x = sqrt(b/a), is not the zero of D (that is e^{-2ix}); the written proof (WLOG c >= 0, then D^{-1}(0) = x + pi Z) gives recurrence at the zero of D, which equals e^{2ix} only for c = +sqrt(ab); see step:wlog-c-nonneg-arg.
```

### F7 step:connected-loop-criterion
```
DEPS: defn-hulls.left, step:hull-closed, step:hulls-compact
EDGE: step:hulls-compact | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L663 | the reduction "it is enough to show that the region bounded by every such loop misses L_t" separates a hypothetical splitting L_t = A u B (A containing U_0) by a loop in the complement, which needs L_t compact (a closed unbounded set such as a point plus a distant line satisfies the loop criterion yet is disconnected)
NOTE: SOURCE_GAP: planar topology reduction asserted without proof ("it is enough to show"); it silently uses that L_t is bounded/compact (step:hulls-compact) as well as closed. The source says loops that do not surround "the origin"; after the centering f_0(z) = z - U_0 the relevant point is U_0 (uncertain; T5-adjacent), which equals 0 only when U_0 = 0.
```

### F8 eqn-scale.left
label-only fix: the gap is exposed in prose but lacks the SOURCE_GAP: token the packet requires for unstated arguments.
```
NOTE: SOURCE_GAP: the source supplies no proof (L547: "easily consequences of Definition 1.1; see [Lu, Section 2] for proofs"); the whole argument is unstated and is not filled here. Root (left-hull part of (2.1), R16). Source proof: "easily consequences of Definition 1.1; see [Lu, Section 2]" (no proof in source). Typo T7: U : [0,infinity) -> R at L545 should be -> C.
```

### F9 eqn-reflect.left
label-only fix: the gap is exposed in prose but lacks the SOURCE_GAP: token the packet requires for unstated arguments.
```
NOTE: SOURCE_GAP: the source supplies no proof (L547: "easily consequences of Definition 1.1; see [Lu, Section 2] for proofs"); the whole argument is unstated and is not filled here. Root (left-hull part of (2.2), R16). Proof not in source (cited to Lu Sect. 2).
```

### F10 eqn-scale
label-only fix: the gap is exposed in prose but lacks the SOURCE_GAP: token the packet requires for unstated arguments.
```
NOTE: SOURCE_GAP: the source supplies no proof (L547: "easily consequences of Definition 1.1; see [Lu, Section 2] for proofs"); the whole argument is unstated and is not filled here. Canonical full (2.1). Proof not in source (cited to Lu Sect. 2).
```

### F11 eqn-reflect
label-only fix: the gap is exposed in prose but lacks the SOURCE_GAP: token the packet requires for unstated arguments.
```
NOTE: SOURCE_GAP: the source supplies no proof (L547: "easily consequences of Definition 1.1; see [Lu, Section 2] for proofs"); the whole argument is unstated and is not filled here. Canonical full (2.2). Proof not in source.
```

### F12 eqn-conc
label-only fix: the gap is exposed in prose but lacks the SOURCE_GAP: token the packet requires for unstated arguments.
```
NOTE: SOURCE_GAP: the source supplies no proof (L547: "easily consequences of Definition 1.1; see [Lu, Section 2] for proofs"); the whole argument is unstated and is not filled here. Canonical (2.3). Proof not in source (cited to Lu Sect. 2). Used by Lemma 2.8 and slices C, D. The source writes f_{t,s+t} with a time-shifted chain, defined in the item itself (no separate node). TYPO CANDIDATE T8 (author ruling needed): the third formula of (2.3), f_t(L_{s+t}\L_t) = L_{t,s+t}, contradicts the second formula, L_{s+t} = L_t cup f_t^{-1}(L_{t,s+t}\R_t), because f_t(C\L_t) = C\R_t omits 0 in R_t cap L_{t,s+t}; read as f_t(L_{s+t}\L_t) = L_{t,s+t}\R_t. Consumers that use the third formula (step:future-point-outside-hulls, step:log-finite-exit-times, step:converse-event-converges) must be read with this correction.
```

### F13 eqn-duality
label-only fix: the gap is exposed in prose but lacks the SOURCE_GAP: token the packet requires for unstated arguments.
```
NOTE: SOURCE_GAP: the source supplies no proof (L547: "easily consequences of Definition 1.1; see [Lu, Section 2] for proofs"); the whole argument is unstated and is not filled here. Canonical (2.4). The source gives no proof ("easily consequences of Definition 1.1; see [Lu, Section 2]", L547). Do not fill. Consumed only through step:right-hull-connected; Prop 1.5 (the other consumer) is excluded.
```

No EDGE line is to be deleted. F3, F4 and F7 change DEPS and add one EDGE line each (shown).

## 5. Required new nodes

None. The candidates I considered were (i) a node for "L_t is bounded" (covered by the existing step:hulls-compact, whose own SOURCE_GAP already says the source never argues compactness), (ii) a separate node for the lim-to-epsilon conversion (a one-line use of monotonicity, handled by the F3 edge), and (iii) an irreducibility node for c = -sqrt(ab) at e^{2ix} (not needed: consumers need only some recurrent point, which F5/F6 state correctly).

## 6. Final unresolved-question list and overall verdict

Unresolved for the author (none blocks the topology review itself):
1. P10 (Lemma 4.1, L2165): corrected construction of U^{+-} or a modeling ruling; the Theorem 1.10 roots stay AUTHOR_BLOCKED.
2. T8: (2.3) third formula read as f_t(L_{s+t}\L_t) = L_{t,s+t}\R_t.
3. R7/R15 reading for Lemmas 2.16, 3.3, 3.7-3.10 (every admissible p) and acceptance of step:all-z-null-set-density as a SOURCE_GAP step (or restriction to the constructed p).
4. Frozen lem-connected.left states IsConnected, i.e. non-empty and connected; the source says only "connected" (nonemptiness via U_0 in L_t is tagged SOURCE_GAP). Confirm the anchor reading.
5. Sign statement of Lemma 2.16 for c = -sqrt(ab) (G1): confirm the e^{-2ix} reading as a typo-level ruling (T8-style).
6. Props 3.1/3.2 over arbitrary probability spaces: confirm the product extension and the null-complement reading of a.s. (R9) as a SOURCE_GAP.
7. Source-gap-heavy but modeled steps that Lean will need new mathematics for: Loewner ODE well-definedness, conformality of g_t, compactness of hulls, the Koebe ball step, Girsanov hitting step, disconnection transfers (F-listed above are labeling/edges, not mathematics).

Overall verdict: NOT PUBLISHABLE (topology) as it stands, because of seven repairable record-level defects (F1-F7: missing (Omega,P,U) quantifier on both Theorem 1.10 roots, missing consumer edge in prop-ii.b, unsupplied premise U_0 = 0, the critical-case sign error in step:wlog-c-nonneg-arg/lem-recurrence, the missing boundedness dependency in the Lemma 2.4 reduction) plus six label-only fixes (F8-F13); no new node is needed and no source-topology failure is unrepairable. After F1-F13 are applied I would expect PUBLISHABLE, with the P10 chain published as an AUTHOR_BLOCKED, faithfully exposed gap.
