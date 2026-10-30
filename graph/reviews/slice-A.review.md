# Slice A topology review

REVIEWER: reviewer-A/sonnet
SCOPE: slice A, paper.tex L225-L804; 57 node records and 95 coverage items whose EXTRACTOR is extractor-A/sonnet (merged DEPGRAPH.md / DEPGRAPH_COVERAGE.md).
SPANS RE-READ (raw source): L225-L330 (Def 1.1, 1.2, 1.4, (1.5)-(1.6), WLOG), L405-L460 (Def 1.7, (1.10), Thm 1.8), L495-L511 (Def 1.9, Thm 1.10), L543-L650 (2.1.1, Def 2.1, Lemmas 2.2, 2.3, 2.4), L655-L692 (Lemmas 2.4, 2.5 and proofs), L772-L804 (Lemmas 2.7, 2.8, Prop 1.5 proof). Also read ERRATA.md, EXTRACTION_SPEC.md, anchor-table.md, INVENTORY, the statements (not proofs) of the nine owned frozen theorems and the frozen definition headers for identity, and the cross-slice nodes thm-phases#assembly-*, thm-disconnects#proof-*.
MECHANICAL CHECKS PASSED: all 25 anchor nodes match anchor-table.md exactly (ID, file, decl, ABI hash, contract ID/version); DEPS equals the set of EDGE targets for every record; no cycles in the merged graph; every slice-A node reaches a root; all DEPS targets resolve; cross-slice IDs (thm-phases#assembly-sign-cases, thm-phases#assembly-c-zero, thm-disconnects#proof-a, thm-disconnects#proof-b) resolve and are consistent with the hypothesis packages of the roots; Prop 1.5 / (2.4) are consumed by no node (exclusion verified).
TALLY: nodes 42 PASS / 15 FAIL (of 57); coverage items 94 PASS / 1 FAIL (of 95); fixes F1-F21 (5 brand-new records: nodes step:loewner-global-uniqueness, step:flow-continuity, step:hull-closed, step:endpt-upcrossing-reduction, and item inv:L644:reverse-remark).

## 1. Node verdicts

PASS defn-loewner.solution
PASS defn-loewner.absorbing-time
PASS defn-hulls.left
FAIL defn-hulls.right: F1: f_t = g_t - U_t is only a function after defn-loewner.well-defined; DEPS omit it (Fix F1)
PASS def-disconnect
PASS eqn-cov-matrix
PASS defn-sle.gaussian-law
PASS defn-sle
PASS defn-phases.thin
PASS defn-phases.swallowing
PASS defn-phases.hitting
PASS defn-phases.dense
PASS eqn-nu-D.mu
PASS eqn-nu-D.nu
PASS eqn-nu-D.D
FAIL item-I: F18: SOURCE_HYPOTHESES adds "p admissible" to a definition that holds for any p; admissibility is the premise of Thm 1.8 (Fix F18)
FAIL item-II: F19: same as item-I (Fix F19)
FAIL step:loewner-local-solution: F2: EDGE to ext:picard-lindelof cites L674 (use site of step:endpt-liminf), not this step's use site L268; conclusion also bundles global uniqueness on a common interval, a separate bridge (Fix F2, F3)
FAIL step:loewner-glue-maximal: F4: patching solutions needs uniqueness on overlaps, i.e. the missing global-uniqueness step (Fix F4)
FAIL defn-loewner.well-defined: F5: the "any two solutions on [0,tau) agree" half needs the global-uniqueness step (Fix F5, F3)
PASS claim:hulls-monotone
PASS claim:gt-conformal
PASS eqn-scale.left
PASS eqn-scale
PASS eqn-reflect.left
PASS eqn-reflect
PASS eqn-conc
PASS step:driver-representation
FAIL eqn-def-ft: F13: f_t(z), t<T_z, exists only via defn-loewner.well-defined; missing dep (Fix F13)
PASS step:wlog-c-nonneg
FAIL defn-chordal-loewner: F17: hulls of chordal chains (L_t = {z in H: T_z<=t}, R_t, L606-L607) are used by Lemma 2.2 but are outside the node source range and conclusion (Fix F17)
FAIL lem-mult-by-i: F14: conclusion says "is the centered Loewner chain with driver iU"; identifying a solution with the chain needs defn-loewner.well-defined (Fix F14)
FAIL step:forward-real-driver: F15: statement is about left hulls L_t cup L_t* of the complex chain; missing dep on defn-hulls.left (Fix F15)
FAIL step:reverse-via-mult-by-i: F16: reverse chordal chain (defn-chordal-loewner) is a direct premise and is not in DEPS; the premises of Lemma 2.3 (reverse solution for every z in C, incl. the reflected half-plane) are not discharged and no SOURCE_GAP says so (Fix F16)
PASS lem-forward-reverse-ext
FAIL claim:hull-nonempty: F6: U_0 in L_t needs T_{U_0}=0, i.e. defn-loewner.absorbing-time and defn-loewner.solution (no solution of positive duration starts at U_0); only defn-hulls.left listed (Fix F6)
FAIL step:connected-loop-criterion: F9: reduction needs L_t closed (C\L_t open), an unstated premise never discharged; add SOURCE_GAP step (Fix F8, F9)
FAIL step:connected-homotopy: F10: joint continuity of (s,w) -> f_s(w) is asserted, not covered by well-defined (existence/uniqueness only); NOTE lacks SOURCE_GAP and no node exposes it (Fix F7, F10)
PASS step:connected-region-misses-hull
PASS lem-connected.left
PASS step:endpt-liminf
PASS step:endpt-upcrossing-bound
PASS step:endpt-finite-upcrossings
FAIL lem-endpt-cont: F12: the reduction "finitely many upcrossings of every [alpha,beta] and liminf=0 imply lim=0" (L675-677, "it suffices") is a quantifier-closure bridge with no node (Fix F11, F12)
PASS step:bm-scaling
PASS lem-scaling
PASS step:markov-driver
PASS lem-markov
PASS nonsource.exists-sle-driver
PASS thm-phases
PASS thm-phases.c-zero
PASS thm-disconnects.a
PASS thm-disconnects.b
PASS ext:picard-lindelof
PASS ext:lawler-4.5
PASS ext:strong-markov-bm
PASS ext:bm-existence

## 2. Coverage verdicts

PASS inv:heading:L225
PASS inv:heading:L228
PASS inv:cite:L230:lsw-lerw-ust
PASS inv:cite:L230:schramm0
PASS inv:cite:L230:smirnov-cardy
PASS inv:cite:L230:smirnov-ising
PASS inv:cite:L230:ss-contour
PASS inv:cite:L231:ss-contour
PASS inv:cite:L232:lawler-book
PASS inv:cite:L240:dg-supercritical-lfpp
PASS inv:cite:L240:huang-complex-insertion
PASS inv:cite:L240:rhodes-vargas-complex-gmt
PASS inv:heading:L244
PASS inv:defn-loewner
PASS inv:eqn-forward-loewner
PASS inv:defn:L271
PASS inv:cite:L283:lu-complex-loewner
PASS inv:cite:L286:lawler-book
PASS inv:cite:L292:rs-complex-sle
PASS inv:cite:L293:bcd-evolution-families1
PASS inv:cite:L293:tran-complex-loewner
PASS inv:remark-radial
PASS inv:defn-sle
PASS inv:eqn-cov-matrix
PASS inv:eqn-def-gt
PASS inv:eqn-def-ft
PASS inv:prop-duality
PASS inv:remark-duality
PASS inv:eqn-sle-kappa-def
PASS inv:eqn-cc
PASS inv:cite:L358:dg-supercritical-lfpp
PASS inv:heading:L403
PASS inv:cite:L406:schramm-sle
PASS inv:defn-phases
PASS inv:eqn-nu-D
PASS inv:eqn-p-ode
PASS inv:item-I.2
PASS inv:item-I
PASS inv:item-II
PASS inv:cite:L477:rs-complex-sle
PASS inv:def-disconnect
PASS inv:thm-disconnects
PASS inv:item-disconnect-z
PASS inv:item-disconnect-t
PASS inv:cite:L514:lu-complex-loewner
PASS inv:remark-curve
PASS inv:cite:L517:schramm-sle
PASS inv:cite:L521:schramm-sle
PASS inv:heading:L529
PASS inv:heading:L540
PASS inv:heading:L543
PASS inv:cite:L547:lu-complex-loewner
PASS inv:eqn-scale
PASS inv:eqn-reflect
PASS inv:eqn-conc
PASS inv:eqn-duality
PASS inv:heading:L582
PASS inv:defn-chordal-loewner
PASS inv:eqn-chordal-loewner
PASS inv:eqn-reverse-loewner
PASS inv:lem-forward-reverse-ext
PASS inv:lem-mult-by-i
PASS inv:proof:L640
PASS inv:proof:L647
PASS inv:cite:L648:lu-complex-loewner
PASS inv:heading:L654
PASS inv:lem-connected
PASS inv:proof:L661
PASS inv:lem-endpt-cont
PASS inv:proof:L673
PASS inv:eqn-endpt-cont-bd
PASS inv:heading:L696
PASS inv:lem-cut-glue
PASS inv:eqn-cut-glue
PASS inv:cite:L722:tran-complex-loewner
PASS inv:cite:L723:pom-book
PASS inv:proof:L730
PASS inv:eqn-simple-conc
PASS inv:eqn-simple-tip
PASS inv:eqn-simple-lim
PASS inv:eqn-simple-increment
PASS inv:heading:L768
PASS inv:lem-scaling
PASS inv:proof:L778
PASS inv:lem-markov
PASS inv:proof:L787
PASS inv:proof:L795
PASS inv:L268:endpt-limit
PASS inv:L284:hulls-monotone
PASS inv:L286:gt-conformal
PASS inv:L323:wlog-c-nonneg
PASS inv:L310:psd-equivalence
PASS inv:L459:c0-bdy-remark
PASS inv:L467:sigma-heuristic
FAIL inv:L604:loewner-theorem: F20: not background; L606-L607 define the chordal hulls L_t, R_t consumed by Lemma 2.2; map to defn-chordal-loewner (Fix F20, F17)

Missing from inventory (new item, Fix F21): the reversal sentence at L644 (forward chain for U gives reverse chain for iU) is a substantive unlabeled claim used by Lemma 2.2(b) and is not an inventory item.
## 3. Fixes

### F1 defn-hulls.right

```
DEPS: defn-hulls.left, defn-loewner.well-defined
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-hulls@L272-L275 | f_t is a map on the complement of L_t whose range complement is R_t
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-hulls@L272-L272 | f_t = g_t - U_t is a well-defined map only via existence and uniqueness of the Loewner IVP; R_t is the complement of its range
```

### F2 step:loewner-local-solution

Replace the existing EDGE line to `ext:picard-lindelof` (the locator moves to this step's own use site) and narrow the conclusion to the local statement.

```
SOURCE_CONCLUSION: near any time t0 with g(t0) != U_{t0} the ODE g-dot = 2/(g-U_t) has a solution, and two solutions that agree at a time t0 agree on a neighbourhood of t0 (local uniqueness only)
EDGE: ext:picard-lindelof | source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268 | "as in the case of a real driving function": right side is continuous in t and locally Lipschitz in g where g != U_t
```

### F3 new step:loewner-global-uniqueness

```
NODE: step:loewner-global-uniqueness
KIND: step
TITLE: Global uniqueness of Loewner solutions on a common interval
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268
CONTRACT_ID: paper.step:loewner-global-uniqueness
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U continuous; z in C; gamma1, gamma2 solutions of (1.1) on [0,tau)
SOURCE_QUANTIFIERS: U; z; tau; gamma1, gamma2
SOURCE_CONCLUSION: gamma1 = gamma2 on [0,tau) (the agreement set is nonempty, closed and open, by local uniqueness)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:loewner-local-solution, defn-loewner.solution
ROUTES: -
ROUTE_FOR: -
EDGE: step:loewner-local-solution | source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268 | local uniqueness is propagated along the interval
EDGE: defn-loewner.solution | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-loewner@L256-L256 | the solutions are solutions of (1.1)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: reviewer-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: the source (L268) asserts only that the solution is "defined up to some time T_z" as in the real-driver case; the passage from local to global uniqueness is not written.
```

### F4 step:loewner-glue-maximal

```
DEPS: step:loewner-local-solution, step:loewner-global-uniqueness, defn-loewner.absorbing-time
EDGE: step:loewner-local-solution | source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268 | solutions on shorter intervals are the pieces to be patched
EDGE: step:loewner-global-uniqueness | source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268 | uniqueness on overlaps lets the pieces patch into one solution on [0,T_z)
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268 | T_z is the supremum of existence times; the supremum must be attained as an open interval
```

### F5 defn-loewner.well-defined

```
DEPS: defn-loewner.solution, defn-loewner.absorbing-time, step:loewner-local-solution, step:loewner-global-uniqueness, step:loewner-glue-maximal
EDGE: defn-loewner.solution | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-loewner@L253-L256 | the statement concerns solutions of (1.1)
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268 | the solution interval is [0,T_z)
EDGE: step:loewner-local-solution | source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268 | local existence
EDGE: step:loewner-global-uniqueness | source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268 | any two solutions on a common interval agree
EDGE: step:loewner-glue-maximal | source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268 | existence on all of [0,T_z)
```

### F6 claim:hull-nonempty

```
DEPS: defn-hulls.left, defn-loewner.absorbing-time, defn-loewner.solution
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L659-L659 | U_0 in L_t means T_{U_0} <= t
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L659-L659 | T_{U_0} = 0 (no solution of positive duration starts at U_0)
EDGE: defn-loewner.solution | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L659-L659 | a solution must satisfy g_s != U_s, impossible at s = 0 when g_0 = U_0
```

### F7 new step:flow-continuity

```
NODE: step:flow-continuity
KIND: step
TITLE: Joint continuity of the Loewner flow in time and initial point
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662
CONTRACT_ID: paper.step:flow-continuity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U : [0,infinity) -> C continuous
SOURCE_QUANTIFIERS: U; (s,w) with s < T_w
SOURCE_CONCLUSION: (s,w) -> f_s(w) is continuous on {(s,w) : s < T_w}, and {w : T_w > t} is open for each t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-loewner.well-defined, defn-hulls.left
ROUTES: -
ROUTE_FOR: -
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662 | f_s(w) is defined for s < T_w; continuous dependence on w is a further property of the ODE flow
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662 | the domain {T_w > t} of f_t is the complement of L_t
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: reviewer-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: the source says "the function (r,s) -> f_s(L(r)) is continuous" without justification; continuous dependence of ODE solutions on the initial point is not in the existence/uniqueness statement of Def 1.1 and is not Picard-Lindelof as stated for ext:picard-lindelof (uncertain whether that external covers it).
```

### F8 new step:hull-closed

```
NODE: step:hull-closed
KIND: step
TITLE: L_t is closed
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662
CONTRACT_ID: paper.step:hull-closed
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U continuous
SOURCE_QUANTIFIERS: U; t >= 0
SOURCE_CONCLUSION: L_t is closed, i.e. the domain C \ L_t of f_t is open
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:flow-continuity, defn-hulls.left
ROUTES: -
ROUTE_FOR: -
EDGE: step:flow-continuity | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662 | {w : T_w > t} is open
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662 | L_t = {T_w <= t}
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: reviewer-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: the proof speaks of loops "that do not intersect L_t" and reduces connectedness to regions bounded by such loops, which silently uses that C \ L_t is open; this is not stated in the source.
```

### F9 step:connected-loop-criterion

```
DEPS: defn-hulls.left, step:hull-closed
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662 | L_t is the complement of the domain of f_t
EDGE: step:hull-closed | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662 | the planar reduction "it is enough to show" uses that L_t is closed
```

### F10 step:connected-homotopy

```
DEPS: defn-loewner.well-defined, defn-hulls.left, step:flow-continuity
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662 | f_s(w) is defined for w not in L_t, s <= t
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662 | w not in L_t means T_w > t, so f_s(w) != 0 for s <= t
EDGE: step:flow-continuity | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662 | "The function (r,s) -> f_s(L(r)) is continuous"
```

### F11 new step:endpt-upcrossing-reduction

```
NODE: step:endpt-upcrossing-reduction
KIND: step
TITLE: Finitely many upcrossings of every [alpha,beta] upgrades liminf = 0 to lim = 0
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L675-L677
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L675-L677
CONTRACT_ID: paper.step:endpt-upcrossing-reduction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: T_z < infinity; liminf_{t -> T_z^-} |f_t(z)| = 0; for all 0 < alpha < beta only finitely many upcrossings of [alpha,beta] before T_z
SOURCE_QUANTIFIERS: z; alpha, beta with 0 < alpha < beta
SOURCE_CONCLUSION: lim_{t -> T_z^-} |f_t(z)| = 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:endpt-liminf, step:endpt-finite-upcrossings
ROUTES: -
ROUTE_FOR: -
EDGE: step:endpt-liminf | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L675-L675 | "We need to replace the liminf by a limit"
EDGE: step:endpt-finite-upcrossings | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L677-L677 | "It suffices to show that there are at most finitely many upcrossings"
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: reviewer-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Quantifier closure over all pairs alpha < beta and the extraction of an upcrossing pair (intermediate value theorem) from limsup > 0 are implicit in "it suffices"; the source does not write them.
```

### F12 lem-endpt-cont

```
DEPS: defn-loewner.absorbing-time, step:endpt-upcrossing-reduction
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L668-L668 | T_z is the absorbing time
EDGE: step:endpt-upcrossing-reduction | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L675-L690 | liminf = 0 plus finitely many upcrossings of every [alpha,beta] gives the limit
```

### F13 eqn-def-ft

```
DEPS: defn-loewner.solution, defn-loewner.well-defined, defn-sle, step:driver-representation
EDGE: defn-loewner.solution | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-def-ft@L316-L316 | f_t = g_t - U_t with g_t from the Loewner ODE gives f_t = z + int 2/f ds - (U_t - U_0)
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-def-ft@L315-L315 | f_t(z) exists for t < T_z only through the well-defined chain
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-def-ft@L315-L315 | U is the SLE_Sigma driving BM
EDGE: step:driver-representation | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-def-ft@L317-L317 | U written as sqrt(a) B + i sqrt(b) B~
```

### F14 lem-mult-by-i

```
DEPS: defn-loewner.solution, defn-loewner.well-defined, defn-chordal-loewner
EDGE: defn-loewner.solution | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-mult-by-i@L641-L641 | "immediate consequence of Definition 1.1": the rotated map solves the forward ODE for iU
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-mult-by-i@L641-L641 | a solution of the ODE for iU is identified with the Loewner chain of iU by uniqueness
EDGE: defn-chordal-loewner | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-mult-by-i@L637-L637 | reverse ODE (2.6) is the hypothesis
```

### F15 step:forward-real-driver

```
DEPS: eqn-reflect, defn-chordal-loewner, defn-hulls.left, defn-hulls.right, defn-loewner.well-defined
EDGE: eqn-reflect | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L648-L648 | "first assertion is immediate from the reflection property under conjugation": U real so U* = U
EDGE: defn-chordal-loewner | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L626-L626 | forward chordal chain and its hulls
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L626-L626 | the left hulls of the complex chain are claimed to be L_t cup L_t*
EDGE: defn-hulls.right | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L626-L626 | right hulls are subsets of the real axis
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L648-L648 | complex chain coincides with chordal chain on H by uniqueness
```

### F16 step:reverse-via-mult-by-i

```
DEPS: lem-mult-by-i, step:forward-real-driver, defn-chordal-loewner
EDGE: lem-mult-by-i | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L648-L648 | "second assertion follows from ... Lemma 2.3"
EDGE: step:forward-real-driver | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L648-L648 | combined with the first assertion
EDGE: defn-chordal-loewner | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L628-L628 | the reverse chordal chain whose Schwarz extension feeds Lemma 2.3
NOTE: Includes the reversal remark at L644 (forward chain for U gives reverse chain for iU). SOURCE_GAP: Lemma 2.3 assumes a reverse solution g_t(z) for every z in C and a continuous complex driver; here the only available object is the reverse chordal chain on H, extended by Schwarz reflection (footnote at L623), and the discharge of that premise (existence of the reflected solution for the required times) is not written in the source.
```

### F17 defn-chordal-loewner

```
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#defn-chordal-loewner@L588-L607
SOURCE_CONCLUSION: forward chain g_t(z) solves g-dot = 2/(g-U_t), reverse chain solves g-dot = -2/(g-U_t), g_0(z) = z; centered chain f_t = g_t - U_t; forward chain: f_t maps H \ L_t onto H with L_t = {z in H : T_z <= t}; reverse chain: f_t maps H onto H \ R_t for some set R_t (hulls identified via Loewner's theorem, L603-L607)
NOTE: Definition 2.1 with (2.5), (2.6), plus the hull identification at L606-L607 that Lemma 2.2 consumes. SOURCE_GAP: Loewner's theorem (g_t the unique conformal map with g_t(z)-z -> 0) is recalled, not proved, and is not a node; Lemma 2.2 relies on it only through the hull identification.
```

### F18 item-I

```
SOURCE_HYPOTHESES: a, b, c real; p : R -> R an arbitrary function (the source introduces p before the theorem; admissibility of p is a premise of Thm 1.8, not of the integral)
```

### F19 item-II

```
SOURCE_HYPOTHESES: a, b, c real; p : R -> R an arbitrary function (the source introduces p before the theorem; admissibility of p is a premise of Thm 1.8, not of the integral)
```

### F20 inv:L604:loewner-theorem

```
ITEM: inv:L604:loewner-theorem
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L604:loewner-theorem@L603-L607
DISPOSITION: NODE defn-chordal-loewner
REASON: recollection of Loewner's theorem and the identification of the chordal hulls L_t, R_t (L606-L607); the hull identification is consumed by Lemma 2.2 and its step nodes; Loewner's theorem itself is recalled without proof (SOURCE_GAP in defn-chordal-loewner NOTE)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
```

### F21 new inv:L644:reverse-remark

```
ITEM: inv:L644:reverse-remark
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L644:reverse-remark@L644-L644
DISPOSITION: NODE step:reverse-via-mult-by-i
REASON: unlabeled claim after Lemma 2.3: if f_t is a centered Loewner chain with driver U then z -> i f_t(-iz) is a centered reverse chain with driver iU; used for Lemma 2.2(b)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: reviewer-A/sonnet
REVIEWER: -
```
