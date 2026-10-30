# Slice C topology review

REVIEWER: reviewer-C/sonnet
SCOPE: slice C, paper.tex L1250-L1946 (Section 3: (3.1), Props 3.1/3.2, Lemmas 3.3-3.12, proof of Thm 1.8 at L1930-1932); 101 node records and 83 coverage items whose EXTRACTOR is extractor-C/sonnet in the merged DEPGRAPH.md / DEPGRAPH_COVERAGE.md (re-read from disk at review time).
SPANS RE-READ (raw source, in full): L1250-L1946, plus L405-L452 (Def 1.7, (1.10), Thm 1.8 statement) for the assembly nodes and L1253-L1260 re-checked line by line for locators. Also read ERRATA.md rulings, EXTRACTION_SPEC.md, INVENTORY.md / inventory.json (slice C rows), anchor-table.md, the statements (not proofs) of Proposition_3_1_A, Proposition_3_2_A and Proposition_3_2_B, and the merged slice A/B nodes that slice C cites (lem-polar, lem-p, lem-stationary, lem-recurrence, remark-sigma, remark-p0, eqn-conc, eqn-scale, lem-scaling, lem-markov, claim:gt-conformal, claim:hulls-monotone, defn-hulls.right, lem-endpt-cont, item-I/II, thm-phases, thm-phases.c-zero). No Lean implementation, proof bodies, sorry/axioms or status files were opened.
MECHANICAL CHECKS PASSED: all DEPS targets of the 101 slice-C nodes resolve; DEPS equals the set of EDGE targets for every record; no cycle through slice C in the merged graph; the four anchors prop-i.a/.b, prop-ii.a/.b match anchor-table.md (ID, file, decl, ABI hash, contract) and their source-statement fields match the frozen statements (a,b>0, c^2<=ab, admissible p, SLE driver, z != 0, sign hypothesis, epsilon-form conclusions per R14); all 71 inventory rows of slice C have a coverage record (except the two id mismatches below); every non-anchor has FROZEN_* = -; Lemma 3.3 and Lemma 3.4 premises are discharged at each application (step:all-z-apply-Tz/-dist; step:stationary-sde-X-form, lem-recurrence, lem-stationary, step:*-apply-stationary-sde).
TALLY: nodes 70 PASS / 31 FAIL (of 101); coverage items 79 PASS / 4 FAIL (of 83); fixes F1-F36 (3 brand-new records: node step:zero-in-future-left-hull, items inv:eqn-two-formulas' and inv:eqn-c0-phase-show').

OBSERVATIONS THAT DO NOT FAIL A RECORD (for the orchestrator): (1) the extractor-recorded SOURCE_GAP nodes are faithful and complete (all-z null set / stopping time / apply-*, sde stationarity / continuity / regeneration, Durrett adaptation, X-form sign flip, Girsanov, Koebe ball, hulls-compact, 0 in R_t, c0 explicit density / finite time, assembly); (2) several edges to lem-p (eqn-integral-nu, eqn-wt-L-dist, step:prop-i-apply-stationary-sde) are redundant under R7/R15 once lem-stationary is a DEP, but they mirror explicit source citations of Lemma 2.13 and are kept; (3) the notation 'L_s' with s = sigma(s^+t^)-sigma(t^) at L1695-1697 is a source-notation clash for L_{sigma(s^)} and does not change the topology; (4) eqn-sde-ratio and step:prop-ii-b-koebe-ball use typo-level readings already noted in their NOTE fields; (5) the 14 extra coverage items added by the extractor (claim items L1303, L1345, L1403, L1463, L1558, L1702, L1707, L1806 and exclusions L1426, L1471, L1481, L1504 and the two -prime ids) are sound additions to the inventory.

## 1. Node verdicts

PASS ext:birkhoff
PASS ext:durrett-7.3.2
PASS ext:koebe-quarter
PASS ext:koebe-distortion
PASS ext:girsanov
PASS ext:kolmogorov-zero-one
FAIL eqn-integral-nu: EDGE locators cite L1253/L1254/L1256/L1258 but the uses are at L1255 ('as in Lemma 2.13', sigma, theta^), L1257 (stationarity) and L1259/L1260 (the two identities); STATEMENT_SOURCE starts on blank L1256 (Fix F1)
PASS prop-i.a
PASS prop-i.b
PASS prop-ii.a
PASS prop-ii.b
PASS lem-all-z
PASS step:all-z-null-set-density
PASS step:all-z-lambda-conull
PASS step:all-z-markov-transfer
FAIL step:all-z-stopping-time-choice: q is an arbitrary level and tau a witness depending on it (L1318); CONSTANT_SCOPE is none (Fix F25)
PASS step:all-z-apply-Tz
PASS step:all-z-apply-dist
FAIL lem-stationary-sde: CONSTANT_SCOPE is none, but xbar is a deterministic point (L1335) fixed before the randomness; the later conclusion 'limit is a.s. a deterministic constant' relies on it (Fix F4)
PASS step:sde-stationary-increments
FAIL step:sde-continuity-noninteger: SOURCE_HYPOTHESES lists stationary increments, which is the conclusion of step:sde-stationary-increments, but DEPS is empty (Fix F2)
PASS step:sde-birkhoff-limit
PASS step:sde-regeneration
PASS step:sde-limit-deterministic
PASS step:sde-mean-zero
FAIL step:sde-recurrence-zero: Lemma 3.5 is applied to 'the stationary sequence xi_n' (L1378); its premise 'stationary' is the conclusion of step:sde-stationary-increments, which is not a direct DEP (only reachable through step:sde-birkhoff-limit) (Fix F3)
PASS lem-recurrent
PASS step:recurrent-durrett-adaptation
PASS lem-swallow-distance
PASS step:swallow-time-change
PASS step:stationary-sde-X-form
PASS step:prop-i-apply-stationary-sde
PASS step:prop-i-a-not-to-minus-infinity
FAIL eqn-neg-I1-bd: alpha = -(I) is deterministic whereas t_* is random (depends on omega); scope not recorded (Fix F26)
FAIL step:prop-i-b-ode-comparison: random t_* and deterministic alpha not scoped (Fix F27)
PASS eqn-sde-ratio
PASS lem-integral-ii
PASS step:integral-ii-expectation
PASS step:integral-ii-apply-stationary-sde
FAIL step:zero-in-left-hull: DEPS/EDGE to eqn-conc cites L1768 but the node's only source is L1558 (a statement about L_{sigma(t^)}); the L_{t,s+t} part belongs to a separate node (Fix F18, F19)
PASS step:zero-in-right-hull
PASS step:hulls-compact
FAIL eqn-hit-koebe: SOURCE_HYPOTHESES adds 'f_t : C\L_t -> C\R_t conformal with L_t, R_t compact' (proof ingredients discharged by claim:gt-conformal and step:hulls-compact; the display (3.5) states none); universal constants not scoped (Fix F5)
PASS step:prop-ii-a-capacity-time
PASS step:prop-ii-a-koebe-limit
PASS lem-converse-w-o-upgrade
PASS step:future-point-outside-hulls
FAIL eqn-two-formulas: lem-markov is not used at L1708-1714 (Koebe on f_{t,s+t} with (2.3) only; f_{t,s+t} is the Loewner map of the shifted driver, a deterministic fact), so the edge is unnecessary; the future-point EDGE cites L1707 instead of the use site L1708-1712; universal constants not scoped (Fix F6)
FAIL eqn-two-formulas-b: CONSTANT_SCOPE is none but the display carries universal implicit constants (L1708-1722: 'with universal implicit constants') (Fix F7)
FAIL eqn-two-dist-ratio: CONSTANT_SCOPE is none but the display carries universal implicit constants (L1708-1722: 'with universal implicit constants') (Fix F8)
FAIL eqn-koebe-t: Koebe is applied to the conformal map f_t on C\L_{s+t}, but claim:gt-conformal (premise used for every other Koebe application) is not a DEP; universal constants not scoped (Fix F12)
FAIL eqn-dist-1: CONSTANT_SCOPE is none but the display carries universal implicit constants (L1708-1722: 'with universal implicit constants') (Fix F9)
PASS eqn-dist-event
PASS step:converse-event-converges
PASS eqn-dist-cases
FAIL eqn-koebe-union: CONSTANT_SCOPE is none but the display carries universal implicit constants (L1708-1722: 'with universal implicit constants') (Fix F10)
FAIL eqn-dist-es: CONSTANT_SCOPE is none but the display carries universal implicit constants (L1708-1722: 'with universal implicit constants') (Fix F11)
FAIL eqn-dist-2: 0 in L_{t,s+t} is used at L1768 but the DEP step:zero-in-left-hull only has source L1558 (about L_{sigma(t^)}); needs the new node step:zero-in-future-left-hull; universal constants not scoped (Fix F13, F19)
FAIL eqn-dist-esc: last asymp is Koebe quarter for f_t : C\L_t -> C\R_t, but claim:gt-conformal is not a DEP (every other Koebe use lists it); universal constants not scoped (Fix F14)
FAIL eqn-dist-3: C is 'a universal constant' (L1674) but CONSTANT_SCOPE is none (Fix F15)
FAIL step:converse-rhs-limit: C of (3.6) is universal/independent of t^ and s^, not scoped (Fix F16)
PASS step:converse-lhs-nonneg
FAIL step:converse-conclude: EDGE to step:converse-rhs-limit cites L1691 (the producer's last sentence) rather than the use site L1697 ('By combining this with the previous paragraph'); 'C does not depend on t^' (L1697) not scoped (Fix F17)
PASS eqn-computation-tilde-f
PASS step:computation-scaling-markov
PASS eqn-wt-L-dist
PASS step:computation-time-change-identity
PASS lem-computation
PASS lem-log-finite-exp
PASS step:log-finite-distortion
PASS step:log-finite-exit-times
PASS step:log-finite-iid
FAIL step:log-finite-q-choice: q = q(Sigma) (L1612) is a witness with a dependence restriction, but CONSTANT_SCOPE is none (Fix F21)
FAIL step:log-finite-binomial: C_N is 'a combinatorial constant depending only on N' (L1617) but CONSTANT_SCOPE is none (Fix F22)
FAIL eqn-log-finite-end: C_N scope not recorded (Fix F23)
FAIL eqn-log-finite-show: C_t^ = C(t^,Sigma) must be uniform in k and N = N(t^,Sigma) is a witness with qN >= t^ (L1573, L1629); CONSTANT_SCOPE is none (Fix F24)
FAIL step:log-finite-tail-to-expectation: EDGE to step:zero-in-left-hull cites L1558 (where the fact is stated) instead of the consumer's use site L1577 (Fix F20)
PASS step:prop-ii-b-scale-reduction
PASS step:prop-ii-b-lambda-positive-measure
PASS step:prop-ii-b-hit-lambda-prime
PASS step:prop-ii-b-markov-transfer
FAIL step:prop-ii-b-lambda-full: conclusion includes 'hence for every z in C\{0}' which needs step:prop-ii-b-scale-reduction (q(z) = q(z/|z|)); not a DEP (Fix F28)
PASS step:prop-ii-b-koebe-ball
FAIL step:prop-ii-b-compactness: epsilon is deterministic but depends on z (and on r with P(lim dist >= r) >= q(z)/2); q_* depends only on Sigma and is uniform in z; CONSTANT_SCOPE is none (Fix F29)
FAIL step:prop-ii-b-conditional-lower-bound: q_* scope not recorded (Fix F30)
FAIL step:prop-ii-b-martingale-zero-one: q_* scope not recorded (Fix F31)
FAIL step:c0-explicit-density: Z = Z(a,b) is a normalizing constant depending only on a, b; scope not recorded (Fix F32)
PASS eqn-c0-integrals
PASS step:c0-positivity-reduction
PASS step:c0-positivity-reflection
PASS eqn-c0-phase-show
PASS step:c0-sign-analysis
PASS lem-c0-phases
PASS step:c0-bdy-drift-vanishes
PASS step:c0-bdy-martingale-bm
PASS step:c0-bdy-capacity-time
PASS step:c0-bdy-hitting-from-limsup
PASS step:c0-bdy-finite-time
PASS lem-c0-bdy
PASS thm-phases#assembly-sign-cases
PASS thm-phases#assembly-c-zero

## 2. Coverage verdicts

PASS inv:heading:L1250
PASS inv:eqn-integral-nu
PASS inv:prop-i
PASS inv:prop-ii
PASS inv:item-ii-a
PASS inv:item-ii-b
PASS inv:heading:L1290
PASS inv:lem-all-z
PASS inv:proof:L1305
PASS inv:eqn-nohit-set
PASS inv:lem-stationary-sde
PASS inv:lem-recurrent
PASS inv:proof:L1355
PASS inv:cite:L1356:durrett
FAIL inv:proof:L1360: proof region contains the citations/uses of ext:birkhoff (L1361) and ext:kolmogorov-zero-one (L1372) and ext:strong-markov-bm (L1367), but the DISPOSITION omits them, so the owned external nodes ext:birkhoff and ext:kolmogorov-zero-one are mapped by no coverage item (Fix F35)
PASS inv:cite:L1374:revuz-yor
PASS inv:heading:L1383
PASS inv:lem-swallow-distance
PASS inv:proof:L1394
PASS inv:proof:L1401
PASS inv:eqn-neg-I1-bd
PASS inv:heading:L1421
PASS inv:lem-integral-ii
PASS inv:proof:L1440
PASS inv:eqn-sde-ratio
PASS inv:proof:L1458
PASS inv:cite:L1463:lawler-book
PASS inv:eqn-hit-koebe
PASS inv:lem-converse-w-o-upgrade
PASS inv:eqn-dist-3-outline
PASS inv:eqn-stationary-outline
PASS inv:lem-computation
PASS inv:proof:L1515
PASS inv:eqn-computation-tilde-f
PASS inv:eqn-wt-L-dist
PASS inv:lem-log-finite-exp
PASS inv:proof:L1572
PASS inv:eqn-log-finite-show
PASS inv:cite:L1581:lawler-book
PASS inv:eqn-finite-exp-1
PASS inv:eqn-finite-exp-2
PASS inv:eqn-finite-exp-3
PASS inv:eqn-finite-exp-4
PASS inv:eqn-log-finite-end
PASS inv:proof:L1638
PASS inv:eqn-converse-show0
PASS inv:eqn-dist-3
PASS inv:cite:L1705:lawler-book
PASS inv:eqn-two-formulas
FAIL inv:eqn-two-formulas-prime: ITEM id is not an inventory id (inventory.json: inv:eqn-two-formulas'); the record must carry the inventory id (Fix F33)
PASS inv:eqn-two-dist-ratio
PASS inv:eqn-koebe-t
PASS inv:eqn-dist-1
PASS inv:eqn-dist-event
PASS inv:eqn-dist-cases
PASS inv:eqn-koebe-union
PASS inv:eqn-dist-es
PASS inv:eqn-dist-2
PASS inv:eqn-dist-esc
FAIL inv:proof:L1786: proof region cites Girsanov (L1802), the Koebe distortion theorem (L1806) and martingale convergence (L1815); ext:girsanov (owned by C) is mapped by no coverage item (Fix F36)
PASS inv:heading:L1819
PASS inv:lem-c0-phases
PASS inv:proof:L1828
PASS inv:eqn-c0-p
PASS inv:eqn-c0-integrals
PASS inv:eqn-c0-phase-show
FAIL inv:eqn-c0-phase-show-prime: ITEM id is not an inventory id (inventory.json: inv:eqn-c0-phase-show'); (Fix F34)
PASS inv:eqn-cos-reflect
PASS inv:lem-c0-bdy
PASS inv:proof:L1914
PASS inv:proof:L1930
PASS inv:L1303:all-z-examples
PASS inv:L1345:recurrence-premise
PASS inv:L1403:sde-premises
PASS inv:L1463:zero-in-right-hull
PASS inv:L1558:zero-in-left-hull
PASS inv:L1702:koebe-premise
PASS inv:L1707:future-point-outside
PASS inv:L1806:koebe-ball
PASS inv:L1471:prop-ii-b-commentary
PASS inv:L1481:outline
PASS inv:L1426:asymp-notation
PASS inv:L1504:stationarity-intro

## 3. Fixes

### F1 eqn-integral-nu
```
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1257-L1260
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1257-L1257
EDGE: item-I | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1259-L1259 | left side of the first identity
EDGE: item-II | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1260-L1260 | left side of the second identity
EDGE: eqn-nu-D.nu | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1257-L1260 | nu is pi-periodic and enters both integrands
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1255-L1255 | sigma-time change defining theta^_t
EDGE: def-arg | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1255-L1255 | argument process theta behind theta^
EDGE: lem-p | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1255-L1255 | 'as in Lemma 2.13': p 1_[0,2pi] is the law of arg zz (stationary p of Lemma 2.13)
EDGE: lem-stationary | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1257-L1257 | stationarity of e^{i theta^_t(zz)} for every admissible p (R7/R15); the source cites only Lemma 2.13
EDGE: lem-stationary.admissible | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1255-L1257 | p ranges over admissible densities (R7/R15)
```

### F2 step:sde-continuity-noninteger
```
DEPS: step:sde-stationary-increments
EDGE: step:sde-stationary-increments | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1361-L1363 | stationarity of the increments of Y is used to compare Y_t/t with Y_{floor(t)}/floor(t)
```

### F3 step:sde-recurrence-zero
```
DEPS: lem-recurrent, step:sde-stationary-increments, step:sde-birkhoff-limit, step:sde-limit-deterministic, step:sde-mean-zero
EDGE: lem-recurrent | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1378-L1378 | applied to the stationary sequence xi_n
EDGE: step:sde-stationary-increments | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1378-L1378 | discharges the premise 'stationary sequence' of Lemma 3.5 for xi_n = Y_n - Y_{n-1}
EDGE: step:sde-birkhoff-limit | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1378-L1378 | E(xi_1 | I) is the a.s. limit of Y_n/n
EDGE: step:sde-limit-deterministic | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1378-L1378 | the limit is deterministic
EDGE: step:sde-mean-zero | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1378-L1378 | that constant equals E f^0(X_0) = 0, hence E(xi_1 | I) = 0
```

### F4 lem-stationary-sde
```
CONSTANT_SCOPE: xbar is a deterministic point of C (independent of omega, chosen before X); m, f^j, g^j are deterministic
```

### F5 eqn-hit-koebe
```
SOURCE_HYPOTHESES: t < T_zz; Section-3 package (L1255-1257): zz is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); the display is deterministic given t < T_zz
CONSTANT_SCOPE: implicit constants in the asymp / lesssim relations are universal: independent of Sigma, p, t^, s^, zz and omega; the relation holds for every t < T_zz
```

### F6 eqn-two-formulas
delete the EDGE line(s) to `lem-markov`.

```
DEPS: ext:koebe-quarter, step:hulls-compact, claim:gt-conformal, eqn-conc, step:future-point-outside-hulls
EDGE: ext:koebe-quarter | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-two-formulas@L1708-L1712 | Koebe quarter theorem for f_{t,s+t} : C\L_{t,s+t} -> C\R_{t,s+t}
EDGE: step:hulls-compact | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-two-formulas@L1708-L1708 | compactness premise
EDGE: claim:gt-conformal | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-two-formulas@L1708-L1708 | conformality of the future map f_{t,s+t}
EDGE: eqn-conc | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-two-formulas@L1708-L1712 | f_{t,s+t}(f_t(zz)) = f_{s+t}(zz)
EDGE: step:future-point-outside-hulls | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-two-formulas@L1708-L1712 | f_t(zz) not in L_{t,s+t}
CONSTANT_SCOPE: implicit constants in the asymp / lesssim relations are universal: independent of Sigma, p, t^, s^, zz and omega
```

### F7 eqn-two-formulas-b
```
CONSTANT_SCOPE: implicit constants in the asymp / lesssim relations are universal: independent of Sigma, p, t^, s^, zz and omega
```

### F8 eqn-two-dist-ratio
```
CONSTANT_SCOPE: implicit constants in the asymp / lesssim relations are universal: independent of Sigma, p, t^, s^, zz and omega
```

### F9 eqn-dist-1
```
CONSTANT_SCOPE: implicit constants in the asymp / lesssim relations are universal: independent of Sigma, p, t^, s^, zz and omega
```

### F10 eqn-koebe-union
```
CONSTANT_SCOPE: implicit constants in the asymp / lesssim relations are universal: independent of Sigma, p, t^, s^, zz and omega
```

### F11 eqn-dist-es
```
CONSTANT_SCOPE: implicit constants in the asymp / lesssim relations are universal: independent of Sigma, p, t^, s^, zz and omega
```

### F12 eqn-koebe-t
```
DEPS: ext:koebe-quarter, step:hulls-compact, claim:gt-conformal, eqn-conc, eqn-two-dist-ratio, step:future-point-outside-hulls
EDGE: ext:koebe-quarter | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-koebe-t@L1727-L1728 | Koebe quarter theorem for f_t : C\L_{s+t} -> C\(L_{t,s+t} u R_t)
EDGE: step:hulls-compact | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-koebe-t@L1727-L1727 | compactness
EDGE: claim:gt-conformal | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-koebe-t@L1727-L1728 | f_t is conformal (injective holomorphic) on C\L_t, hence on C\L_{s+t}
EDGE: eqn-conc | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-koebe-t@L1727-L1727 | f_t maps C\L_{s+t} onto C\(L_{t,s+t} u R_t)
EDGE: eqn-two-dist-ratio | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-koebe-t@L1728-L1728 | second asymp via (3.9)
EDGE: step:future-point-outside-hulls | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-koebe-t@L1727-L1727 | zz not in L_{s+t}
CONSTANT_SCOPE: implicit constants in the asymp / lesssim relations are universal: independent of Sigma, p, t^, s^, zz and omega
```

### F13 eqn-dist-2
delete the EDGE line(s) to `step:zero-in-left-hull`.

```
DEPS: eqn-two-dist-ratio, step:zero-in-future-left-hull, eqn-dist-cases
EDGE: eqn-two-dist-ratio | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-2@L1768-L1768 | the asymp via (3.9)
EDGE: step:zero-in-future-left-hull | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-2@L1768-L1768 | 0 in L_{t,s+t}, so dist(f_t(zz),L_{t,s+t}) <= |f_t(zz)|
EDGE: eqn-dist-cases | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-2@L1768-L1768 | on E^c the union distance equals dist(f_t(zz),R_t)
CONSTANT_SCOPE: implicit constants in the asymp / lesssim relations are universal: independent of Sigma, p, t^, s^, zz and omega
```

### F14 eqn-dist-esc
```
DEPS: eqn-dist-1, eqn-dist-2, ext:koebe-quarter, step:hulls-compact, claim:gt-conformal
EDGE: eqn-dist-1 | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-esc@L1773-L1773 | left side of (3.11)
EDGE: eqn-dist-2 | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-esc@L1773-L1773 | upper bound for the ratio of R-distances on E^c
EDGE: ext:koebe-quarter | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-esc@L1778-L1778 | Koebe quarter for f_t : C\L_t -> C\R_t gives the last asymp
EDGE: step:hulls-compact | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-esc@L1778-L1778 | compactness
EDGE: claim:gt-conformal | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-esc@L1778-L1778 | f_t conformal C\L_t -> C\R_t
CONSTANT_SCOPE: implicit constants in the asymp / lesssim relations are universal: independent of Sigma, p, t^, s^, zz and omega
```

### F15 eqn-dist-3
```
CONSTANT_SCOPE: C is universal: independent of Sigma, p, t^, s^, zz and omega (the implicit asymp constants of (3.15), (3.17) are absorbed into C)
```

### F16 step:converse-rhs-limit
```
CONSTANT_SCOPE: C is the universal constant of (3.6); independent of t^, s^, Sigma, omega; the limit s^ -> infinity is taken with t^ fixed
```

### F17 step:converse-conclude
```
EDGE: step:converse-rhs-limit | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1697-L1697 | limit of the right side, combined with the left side at L1697
CONSTANT_SCOPE: C is the universal constant of (3.6), independent of t^ (this is what allows t^ -> infinity); t^ is arbitrary
```

### F18 step:zero-in-left-hull
delete the EDGE line(s) to `eqn-conc`.

```
SOURCE_QUANTIFIERS: t >= 0
SOURCE_CONCLUSION: 0 in L_t, hence dist(zz, L_t) <= |zz| = 1 and log(1/dist(zz,L_{sigma(t^)})) >= 0
DEPS: defn-hulls.left, defn-loewner.absorbing-time
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1558-L1558 | L_t = {z : T_z <= t}
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1558-L1558 | T_0 = 0 because the driver starts at the singular point 0
```

### F19 new step:zero-in-future-left-hull
```
NODE: step:zero-in-future-left-hull
KIND: step
TITLE: 0 belongs to the future left hulls L_{t,s+t}
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-2@L1768-L1768
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-2@L1768-L1768
CONTRACT_ID: paper.step:zero-in-future-left-hull
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U_0 = 0 (R4); t, s >= 0
SOURCE_QUANTIFIERS: t >= 0; s >= 0
SOURCE_CONCLUSION: 0 in L_{t,s+t}, hence dist(f_t(zz), L_{t,s+t}) <= |f_t(zz)|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-hulls.left, defn-loewner.absorbing-time, eqn-conc, step:zero-in-left-hull
ROUTES: -
ROUTE_FOR: -
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-2@L1768-L1768 | L_{t,s+t} is a left hull
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-2@L1768-L1768 | T_0 = 0 for the shifted driver U(.+t)-U(t), which starts at 0
EDGE: eqn-conc | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-2@L1768-L1768 | L_{t,s+t} is the left hull of the chain driven by U(.+t)-U(t)
EDGE: step:zero-in-left-hull | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-2@L1768-L1768 | same argument as for L_t, applied to the shifted driver
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: reviewer-C/sonnet (proposed split of step:zero-in-left-hull)
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The source writes 'the fact that 0 in L_{t,s+t}' at L1768 without argument (read as the shifted-driver version of L1558; not a SOURCE_GAP beyond what L1558 already assumes). Split out of step:zero-in-left-hull so each EDGE locator cites its own use site.
```

### F20 step:log-finite-tail-to-expectation
```
EDGE: step:zero-in-left-hull | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1577-L1577 | log(1/dist(zz,L_{sigma(t^)})) >= 0 so the tail integral formula applies
```

### F21 step:log-finite-q-choice
```
CONSTANT_SCOPE: q = q(Sigma) > 0 depends only on Sigma (and p); independent of k and omega
```

### F22 step:log-finite-binomial
```
CONSTANT_SCOPE: C_N depends only on N (combinatorial); independent of k, Sigma and omega; N is fixed before k
```

### F23 eqn-log-finite-end
```
CONSTANT_SCOPE: C_N depends only on N, as in the binomial bound; independent of k; N in N arbitrary
```

### F24 eqn-log-finite-show
```
CONSTANT_SCOPE: C_t^ depends only on t^ and Sigma (and p), not on k or omega; chosen before k; N = N(t^,Sigma) with qN >= t^
```

### F25 step:all-z-stopping-time-choice
```
CONSTANT_SCOPE: q in (0,1) is arbitrary; tau = tau(z,q) is a stopping time chosen after q; no dependence of Lambda on q
```

### F26 eqn-neg-I1-bd
```
CONSTANT_SCOPE: alpha = -(I) > 0 is deterministic (depends on Sigma, p); t_* < T_zz is random (depends on omega), a.s. finite
```

### F27 step:prop-i-b-ode-comparison
```
CONSTANT_SCOPE: alpha > 0 deterministic; t_* is the random time of (3.2); the bound t_* + e^{-alpha F(t_*)}/alpha is random
```

### F28 step:prop-ii-b-lambda-full
```
DEPS: step:prop-ii-b-hit-lambda-prime, step:prop-ii-b-markov-transfer, step:prop-ii-b-scale-reduction
EDGE: step:prop-ii-b-hit-lambda-prime | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1802-L1803 | P(tau < infinity) > 0
EDGE: step:prop-ii-b-markov-transfer | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1804-L1805 | q(z) >= E[q(e^{i theta^_tau}) ; tau < infinity] > 0 since e^{i theta^_tau} in Lambda' subset Lambda
EDGE: step:prop-ii-b-scale-reduction | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1799-L1799 | q(z) > 0 on the unit circle gives q(z) > 0 on C\{0}
```

### F29 step:prop-ii-b-compactness
```
CONSTANT_SCOPE: epsilon = epsilon(z) depends on z; q_* > 0 depends only on Sigma (and p), uniform in z in C\{0} and independent of omega
```

### F30 step:prop-ii-b-conditional-lower-bound
```
CONSTANT_SCOPE: q_* is the deterministic constant of step:prop-ii-b-compactness, depending only on Sigma (and p), independent of z and t^
```

### F31 step:prop-ii-b-martingale-zero-one
```
CONSTANT_SCOPE: q_* is the deterministic constant of step:prop-ii-b-compactness, depending only on Sigma (and p), independent of z and t^
```

### F32 step:c0-explicit-density
```
CONSTANT_SCOPE: Z = Z(a,b) > 0 depends only on a and b (c = 0)
```

### F33 new inv:eqn-two-formulas'
delete the record `ITEM: inv:eqn-two-formulas-prime` and replace it by the record below (identical content, inventory id).

```
ITEM: inv:eqn-two-formulas'
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-two-formulas'@L1720-L1720
DISPOSITION: NODE eqn-two-formulas-b
REASON: display (3.8)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
```

### F34 new inv:eqn-c0-phase-show'
delete the record `ITEM: inv:eqn-c0-phase-show-prime` and replace it by the record below (identical content, inventory id).

```
ITEM: inv:eqn-c0-phase-show'
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-c0-phase-show'@L1851-L1851
DISPOSITION: NODE step:c0-positivity-reduction
REASON: display (3.22)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
```

### F35 inv:proof:L1360
```
DISPOSITION: NODE lem-stationary-sde, step:sde-stationary-increments, step:sde-continuity-noninteger, step:sde-birkhoff-limit, step:sde-regeneration, step:sde-limit-deterministic, step:sde-mean-zero, step:sde-recurrence-zero, ext:birkhoff, ext:kolmogorov-zero-one, ext:strong-markov-bm
```

### F36 inv:proof:L1786
```
DISPOSITION: NODE prop-ii.b, step:prop-ii-b-scale-reduction, step:prop-ii-b-lambda-positive-measure, step:prop-ii-b-hit-lambda-prime, step:prop-ii-b-markov-transfer, step:prop-ii-b-lambda-full, step:prop-ii-b-koebe-ball, step:prop-ii-b-compactness, step:prop-ii-b-conditional-lower-bound, step:prop-ii-b-martingale-zero-one, ext:girsanov, ext:koebe-distortion, ext:martingale-convergence
```
