# Slice B topology review

Reviewer: reviewer-B/sonnet
Scope: slice B, records with EXTRACTOR extractor-B/sonnet: 65 nodes in DEPGRAPH.md and 64 items in DEPGRAPH_COVERAGE.md (paper.tex L805-L1249 and L2312-L2406).
Spans re-read in the raw source: L805-L830 (excluded section), L831-L1249 (Defs 2.9, 2.10, Lemmas 2.11, 2.13, 2.14, 2.16, Remarks 2.12, 2.15, and all proofs, skipping the `comment` blocks L999-1018, L1114-1131, L1140-1146, L1234-1248), L2312-L2406 (Appendix A). Also read: ERRATA.md, EXTRACTION_SPEC.md, INVENTORY.md and inventory.json (slice B rows), anchor-table.md, the statements of ComplexSLE/Frozen/Defs/IsAdmissibleDensity.lean and ComplexSLE/Frozen/Lemma_2_13_Exists.lean, and context records of slices A and C that slice B nodes cite or are cited by.
Mechanical checks done: all DEPS resolve to existing node ids; DEPS and EDGE lists agree for every slice B node; the whole graph has no dependency cycle; FROZEN_* fields and CONTRACT fields of lem-stationary.admissible and lem-p.exists match the anchor table.

Tally: nodes 49 PASS / 16 FAIL (of 65); coverage items 62 PASS / 2 FAIL (of 64); fixes F1-F18.

Notes: remark-sigma and lem-polar are mutually dependent only in the local sense described in the extractor's lem-polar note (remark-sigma depends on lem-polar, not the reverse), so no graph cycle arises. I left parent-lemma to child-step edges (for example lem-stationary to lem-polar, lem-kolmogorov to lem-hormander) as PASS because the parent's proof text cites them at its own locators; this is the extractor's consistent convention.

## 1. Node verdicts

PASS ext:ito-complex
PASS ext:levy-characterization
PASS ext:hormander-1d
PASS ext:scale-function
PASS ext:martingale-convergence
PASS ext:dct
FAIL defn-sigma: missing DEPS defn-loewner.well-defined (f_s(z) is the centered chain; slice A records that consumers of g_t, f_t depend on that theorem) (Fix F1)
FAIL step:arg-lift: missing DEPS defn-loewner.well-defined: existence, continuity and nonvanishing of f_t(z) for t<T_z; defn-sle is not what supplies them (Fix F2)
PASS def-arg
PASS lem-polar
PASS step:polar-ito-log
PASS step:polar-real-imag
PASS step:polar-time-change
FAIL step:polar-W-law: hypothesis "W,W~ as in step:polar-time-change" is not discharged (missing DEPS step:polar-time-change); covariance c t/sqrt(ab) of (B,B~) comes from step:driver-representation, not defn-sle (unnecessary edge) (Fix F3)
FAIL step:polar-derivative-sde: unnecessary edge to step:polar-real-imag (L928 uses only f^-2 = |f|^-2 e^{-2i theta}, i.e. def-arg, and never the SDEs for log|f|, theta); def-arg missing (Fix F4)
FAIL remark-sigma: missing DEPS defn-sigma: the remark is a claim about the domain and range of sigma_z (Fix F5)
PASS step:sigma-bounded-coefficients
PASS lem-stationary.admissible
PASS lem-stationary
PASS step:stat-martingale-qv
PASS step:stat-theta-bm-sde
PASS step:driver-negation-symmetry
FAIL step:stat-pi-reduction: listed premise "stationarity of e^{2i theta} (from Lemma A.1)" is not discharged: missing DEPS on step:stat-apply-kolmogorov-noncritical and -critical; -zz =_d zz uses pi-periodicity of p, so lem-stationary.admissible is also missing (Fix F6)
PASS step:stat-kolmogorov-normalization
PASS step:D-structure
PASS step:stat-apply-kolmogorov-noncritical
FAIL step:stat-apply-kolmogorov-critical: missing DEPS eqn-nu-D.mu: the value mu(u) beta'(u) = -+4 sqrt(ab/(a+b)) at zeros of beta is computed from the definition of mu (L993) (Fix F7)
PASS lem-p.exists
PASS lem-p
FAIL step:p-wlog-c-nonneg: missing DEPS lem-stationary.admissible: conclusion is "p admissible for (a,b,c) implies p~ admissible for (a,b,-c)" (L1026) (Fix F8)
FAIL step:p-case1-first-order-solutions: p_1(pi) > 0 (and p_1 >= 0 on [0,pi]) is consumed at L1054/L1065 by step:p-case1-periodic and step:p-case1-nonneg as a SOURCE_HYPOTHESES premise, but no node states or discharges it; record it in the conclusion with SOURCE_GAP (Fix F9)
PASS step:p-case1-periodic
PASS step:p-case1-mu-over-D-integral
PASS step:p-case1-nonneg
PASS step:p-case1-zero-set
FAIL step:p-case1: missing direct DEPS step:p-case1-first-order-solutions: smoothness of p_0, p_1 yields the claimed C^2 everywhere / D p in C^1 (L1041) (Fix F10)
PASS step:p-case2-welldefined
PASS step:p-case2-limits
FAIL step:p-case2-regularity: edge to step:p-case1-first-order-solutions consumes a node whose premise (|c|<sqrt(ab), D>0) is false in Case 2; the needed ODE (2.33) is already supplied by step:p-case2-welldefined (delete that edge) (Fix F11)
PASS step:p-case2
PASS step:p-positive-off-discrete
PASS step:p0-c0-r-star-zero
PASS remark-p0
FAIL lem-recurrence: EDGE locator for lem-stationary cites L1156-L1158, which mentions Lemma 2.13, not the stationarity use; the use site is L1187 (Fix F12)
PASS step:rec-reduction-to-x
FAIL step:rec-angle-hit-unif: edge to step:rec-hit-fixed-y is merely transitive: step:rec-monotone-in-y already consumes it and L1229 is the use site (Fix F15)
FAIL step:rec-renewal: missing DEPS step:stat-theta-bm-sde: L1182 applies the strong Markov property and pi-periodicity of the coefficients of SDE (2.30) (Fix F13)
FAIL step:rec-tau-finite: edge to lem-p wrong for R7/R15 (lem-recurrence is for every admissible p; lem-p gives only one constructed p); the density of the law of zz comes from lem-stationary.admissible. Also the tau_k^eps are defined in step:rec-renewal (missing DEPS) (Fix F14)
PASS step:rec-time-change-omega
PASS step:rec-scale-function-hit
PASS step:rec-hit-fixed-y
PASS step:rec-monotone-in-y
PASS lem-kolmogorov
PASS step:kol-shift-start
PASS step:kol-ito-expectation
PASS step:kol-derivative-at-zero
FAIL step:kol-integration-by-parts: unnecessary edge to step:kol-shift-start: L2384 uses periodicity hypotheses of the lemma, not the claim that the start law may be moved to [x,x+pi] (Fix F16)
PASS step:kol-semigroup-smooth
PASS step:kol-markov-semigroup
PASS step:kol-derivative-vanishes-all-times
PASS step:kol-process-stationarity
PASS lem-hormander
PASS step:horm-stratonovich
PASS step:horm-span-condition
PASS step:horm-apply-hairer

## 2. Coverage verdicts

PASS inv:heading:L805
PASS inv:cite:L808:kennedy-sle-sim
PASS inv:eqn-sim-map
PASS inv:eqn-sim-driving
PASS inv:eqn-sim-set
PASS inv:heading:L831
PASS inv:defn-sigma
PASS inv:eqn-defn-sigma
PASS inv:def-arg
PASS inv:lem-polar
PASS inv:eqn-def-mu
PASS inv:eqn-theta-t
PASS inv:eqn-abs-zt
FAIL inv:eqn-abs-zt-prime: ITEM id does not match the inventory id inv:eqn-abs-zt' (Fix F17)
PASS inv:remark-sigma
PASS inv:proof:L903
PASS inv:cite:L904:protter
PASS inv:eqn-abs-zt-op
PASS inv:eqn-theta-t-op
PASS inv:heading:L936
PASS inv:lem-p
PASS inv:eqn-def-D
PASS inv:eqn-p-ODE
PASS inv:lem-stationary
PASS inv:proof:L972
PASS inv:eqn-theta-t-bm
FAIL inv:eqn-theta-t-bm-prime: ITEM id does not match the inventory id inv:eqn-theta-t-bm' (Fix F18)
PASS inv:proof:L1024
PASS inv:eqn-defn-p0
PASS inv:eqn-defn-p1
PASS inv:eqn-p0-p1-ODE
PASS inv:eqn-critical-p
PASS inv:eqn-critical-p-ode
PASS inv:eqn-lhop-down
PASS inv:eqn-lhop-up
PASS inv:remark-p0
PASS inv:heading:L1149
PASS inv:lem-recurrence
PASS inv:proof:L1164
PASS inv:eqn-angle-hit-unif
PASS inv:eqn-omega-time
PASS inv:eqn-omega-sde
PASS inv:cite:L1210:lawler-book
PASS inv:cite:L1223:lawler-book
PASS inv:eqn-angle-hit-fixed
PASS inv:heading:L2314
PASS inv:lem-kolmogorov
PASS inv:eqn-kolmogorov-sde
PASS inv:eqn-hormander-cond
PASS inv:eqn-kolmogorov
PASS inv:lem-hormander
PASS inv:proof:L2345
PASS inv:eqn-stratanovich
PASS inv:cite:L2351:hairer-hormander
PASS inv:proof:L2360
PASS inv:eqn-periodic-deriv0
PASS inv:eqn-periodic-deriv
PASS inv:cite:L2396:ethier-semigroups
PASS inv:cite:L2396:gikhman-skorokhod
PASS inv:L847:sigma-range
PASS inv:L969:regularity-preview
PASS inv:L984:pi-reduction
PASS inv:L959:usage-remark
PASS inv:L2337:hormander-purpose

## 3. Fixes

All SOURCE_ROOT paths below are `source/arxiv-2203.07313v4/complex-sle-final.tex`; EDGE lines write it in full.

### F1 defn-sigma

```
DEPS: defn-sle, defn-loewner.absorbing-time, defn-loewner.well-defined
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-sigma@L838-L838 | centered SLE_Sigma maps f_t supply f_s(z)
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-sigma@L839-L839 | domain (0,T_z) of the time change uses the absorbing time
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-sigma@L842-L842 | the integrand |f_s(z)|^-2 uses the centered chain f_s(z) = g_s(z) - U_s, whose existence and uniqueness up to T_z is that theorem
```

### F2 step:arg-lift

```
DEPS: defn-loewner.absorbing-time, defn-sle, defn-loewner.well-defined
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#def-arg@L852-L852 | f_t(z) nonvanishing and continuous for t<T_z
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#def-arg@L852-L852 | f_t(z) is a continuous process built from the driver
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#def-arg@L852-L852 | f_t(z) is the (unique) solution, continuous in t and nonzero for t<T_z, so the lift to the covering R -> S^1 exists
```

### F3 step:polar-W-law

delete the EDGE line(s) to `defn-sle`

```
DEPS: ext:levy-characterization, defn-sigma, step:polar-time-change, step:driver-representation
EDGE: ext:levy-characterization | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L927-L927 | equality of law from equal quadratic (cross-)variations
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L927-L927 | <W>_t~ = int_0^sigma(t~) |f|^-2 ds = t~ by the definition of sigma
EDGE: step:polar-time-change | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L924-L927 | W and W~ are the stochastic integrals defined there
EDGE: step:driver-representation | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L927-L927 | (B,B~) are standard BMs with cross-variation c t/sqrt(ab)
```

### F4 step:polar-derivative-sde

delete the EDGE line(s) to `step:polar-real-imag`

```
DEPS: eqn-def-ft, defn-sigma, def-arg
EDGE: eqn-def-ft | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L928-L928 | differentiate the SDE for f_t(z) in z
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L928-L928 | time change
EDGE: def-arg | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L928-L928 | f_t^-2 = |f_t|^-2 e^{-2i theta_t}, real part -2cos(2 theta)/|f|^2
```

### F5 remark-sigma

```
DEPS: lem-polar, step:sigma-bounded-coefficients, lem-endpt-cont, defn-sigma
EDGE: lem-polar | source/arxiv-2203.07313v4/complex-sle-final.tex#remark-sigma@L893-L893 | SDEs with bounded coefficients on the sigma-time scale
EDGE: step:sigma-bounded-coefficients | source/arxiv-2203.07313v4/complex-sle-final.tex#remark-sigma@L894-L895 | |hat f| and |hat f'| bounded away from 0, infinity on compacts
EDGE: lem-endpt-cont | source/arxiv-2203.07313v4/complex-sle-final.tex#remark-sigma@L895-L895 | lim |f_t(z)| = 0 as t -> T_z- on {T_z<infinity}
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#remark-sigma@L894-L895 | the claim concerns the domain of sigma_z defined by t~ = int_0^sigma |f_s|^-2 ds
```

### F6 step:stat-pi-reduction

```
DEPS: eqn-reflect, step:driver-negation-symmetry, def-arg, step:stat-apply-kolmogorov-noncritical, step:stat-apply-kolmogorov-critical, lem-stationary.admissible
EDGE: eqn-reflect | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L984-L984 | (2.2): multiplying the driving function by -1 gives f_t -> -f_t(-.)
EDGE: step:driver-negation-symmetry | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L984-L984 | -U =_d U
EDGE: def-arg | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L984-L984 | carrier change theta <-> e^{2i theta}, e^{i theta}
EDGE: step:stat-apply-kolmogorov-noncritical | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L984-L984 | stationarity of e^{2i theta} (case |c| != sqrt(ab)) is the premise being upgraded
EDGE: step:stat-apply-kolmogorov-critical | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L984-L984 | stationarity of e^{2i theta} (case c = +-sqrt(ab)) is the premise being upgraded
EDGE: lem-stationary.admissible | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L984-L984 | p is pi-periodic, so -zz =_d zz
```

### F7 step:stat-apply-kolmogorov-critical

```
DEPS: lem-kolmogorov, step:stat-kolmogorov-normalization, step:D-structure, step:stat-theta-bm-sde, eqn-nu-D.mu
EDGE: lem-kolmogorov | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L993-L993 | Hormander-condition hypothesis (A.1) checked at zeros of beta
EDGE: step:stat-kolmogorov-normalization | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L993-L993 | 2p, alpha=mu, beta
EDGE: step:D-structure | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L988-L992 | 2D = beta^2 and zero set of beta
EDGE: step:stat-theta-bm-sde | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L989-L992 | rewrite with W'' and beta
EDGE: eqn-nu-D.mu | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L993-L993 | value of mu(u) beta'(u) at the zeros of beta
```

### F8 step:p-wlog-c-nonneg

```
DEPS: eqn-nu-D.mu, eqn-nu-D.D, lem-stationary.admissible
EDGE: eqn-nu-D.mu | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1026-L1026 | symmetry mu(c)(u) = -mu(-c)(-u)
EDGE: eqn-nu-D.D | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1026-L1026 | symmetry D(c)(u) = D(-c)(-u)
EDGE: lem-stationary.admissible | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1026-L1026 | "if p satisfies the hypotheses of Lemma 2.14 then p~ does"
```

### F9 step:p-case1-first-order-solutions

```
SOURCE_CONCLUSION: p_0(u) = exp(int_0^u (mu-D')/D) and p_1(u) = D(u)^-1 exp(int_0^u mu/D) int_0^u exp(-int_0^s mu/D) ds are smooth on R and satisfy -mu p_j + [D p_j]' = j; p_0(0)=1, p_1(0)=0; the source also asserts p_0, p_1 >= 0 (L1030) and uses p_1(pi) > 0 (L1054, L1065) without argument
NOTE: Covers eqn-defn-p0, eqn-defn-p1, eqn-p0-p1-ODE. Verification of the ODEs is direct differentiation. SOURCE_GAP: the source says p_0,p_1 : R -> [0,infty) and later 'p_1(pi) > 0' and 'p_0, p_1 clearly non-negative' with no argument; p_1(u) < 0 for u < 0, so nonnegativity holds only on [0,pi] where it is used. Downstream nodes step:p-case1-periodic and step:p-case1-nonneg consume 'p_1(pi) > 0' and 'p_1 >= 0 on [0,pi]' from this node.
```

### F10 step:p-case1

```
DEPS: step:p-case1-first-order-solutions, step:p-case1-periodic, step:p-case1-nonneg, step:p-case1-zero-set, lem-stationary.admissible
EDGE: step:p-case1-first-order-solutions | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1041-L1041 | p_0, p_1 smooth, so p is C^2 on R and D p is C^1 (x-condition vacuous)
EDGE: step:p-case1-periodic | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1058-L1063 | pi-periodicity and the ODE
EDGE: step:p-case1-nonneg | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1065-L1065 | nonnegativity
EDGE: step:p-case1-zero-set | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1088-L1088 | int_0^{2pi}(p_0+r_* p_1) > 0 so k exists
EDGE: lem-stationary.admissible | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1025-L1025 | admissibility target
```

### F11 step:p-case2-regularity

delete the EDGE line(s) to `step:p-case1-first-order-solutions`

```
DEPS: step:p-case2-limits, step:p-case2-welldefined
EDGE: step:p-case2-limits | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1110-L1110 | continuity at x+n pi and one-sided limits of [D p]'
EDGE: step:p-case2-welldefined | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1110-L1110 | ODE (2.33) i.e. [D p]' = 1 + mu p off the singular points (the source's "By (2.19)" is this same equation, valid in Case 2 only through (2.33))
```

### F12 lem-recurrence

```
DEPS: lem-stationary, step:wlog-c-nonneg, step:rec-reduction-to-x, step:rec-renewal, step:rec-tau-finite, step:rec-angle-hit-unif
EDGE: lem-stationary | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1187-L1187 | stationarity of e^{2i theta}
EDGE: step:wlog-c-nonneg | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1165-L1165 | c>=0 WLOG
EDGE: step:rec-reduction-to-x | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1165-L1165 | suffices to hit e^{2ix}
EDGE: step:rec-renewal | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1177-L1183 | infinitely many hits on {tau_k<infty for all k}
EDGE: step:rec-tau-finite | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1185-L1190 | a.s. some eps with all tau_k^eps finite
EDGE: step:rec-angle-hit-unif | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1167-L1171 | claim (2.45) fed to renewal argument
```

### F13 step:rec-renewal

```
DEPS: step:rec-angle-hit-unif, ext:strong-markov-bm, ext:martingale-convergence, step:stat-theta-bm-sde
EDGE: step:rec-angle-hit-unif | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1183-L1183 | conditional probability >= delta in each window
EDGE: ext:strong-markov-bm | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1182-L1182 | strong Markov property at tau_k
EDGE: ext:martingale-convergence | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1183-L1183 | conditional Borel-Cantelli to conclude infinitely many hits
EDGE: step:stat-theta-bm-sde | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1182-L1182 | pi-periodic coefficients of SDE (2.30) give the same conditional law from [theta_tau]
```

### F14 step:rec-tau-finite

delete the EDGE line(s) to `lem-p`

```
DEPS: lem-stationary, lem-stationary.admissible, step:rec-renewal
EDGE: lem-stationary | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1187-L1187 | stationary law of e^{2i theta}
EDGE: lem-stationary.admissible | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1187-L1187 | the admissible p is a density (angle law p 1_[0,2pi]), so the image law is non-atomic
EDGE: step:rec-renewal | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1177-L1180 | the stopping times tau_k^eps are defined there
```

### F15 step:rec-angle-hit-unif

delete the EDGE line(s) to `step:rec-hit-fixed-y`

```
DEPS: step:rec-monotone-in-y
EDGE: step:rec-monotone-in-y | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1229-L1229 | monotonicity in y reduces uniform bound to the worst y=x+pi-eps (itself built on the fixed-y bound)
```

### F16 step:kol-integration-by-parts

delete the EDGE line(s) to `step:kol-shift-start`

```
DEPS: step:kol-derivative-at-zero
EDGE: step:kol-derivative-at-zero | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2382-L2382 | integrand to be integrated by parts
```

### F17 inv:eqn-abs-zt-prime

```
ITEM: inv:eqn-abs-zt'
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-abs-zt'@L882-L882
DISPOSITION: NODE lem-polar, step:polar-derivative-sde
REASON: (2.27)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
```

### F18 inv:eqn-theta-t-bm-prime

```
ITEM: inv:eqn-theta-t-bm'
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-theta-t-bm'@L989-L989
DISPOSITION: NODE step:stat-apply-kolmogorov-critical
REASON: (2.31)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
```
