## Nodes

NODE: ext:birkhoff
KIND: external
TITLE: Birkhoff ergodic theorem
STATEMENT_SOURCE: external:standard#birkhoff-ergodic-theorem
PROOF_SOURCE: external:standard#proof
CONTRACT_ID: paper.ext:birkhoff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Birkhoff ergodic theorem
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: Canonical (spec E7). Cited at L1361 ('by the Birkhoff ergodic theorem').

NODE: ext:durrett-7.3.2
KIND: external
TITLE: Durrett Theorem 7.3.2 (recurrence of Z-valued stationary sequences)
STATEMENT_SOURCE: external:durrett#thm-7.3.2
PROOF_SOURCE: external:durrett#proof
CONTRACT_ID: paper.ext:durrett-7.3.2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Durrett Theorem 7.3.2 (recurrence of Z-valued stationary sequences)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: Canonical (spec). Cited at L1356 as 'essentially identical' proof for R-valued sequences with E(xi_1|I)=0: SOURCE_GAP (the real-valued adaptation is asserted, not proved).

NODE: ext:koebe-quarter
KIND: external
TITLE: Koebe quarter theorem (Lawler Corollary 3.18)
STATEMENT_SOURCE: external:lawler-book#cor-3.18
PROOF_SOURCE: external:lawler-book#proof
CONTRACT_ID: paper.ext:koebe-quarter
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Koebe quarter theorem (Lawler Corollary 3.18)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: Canonical (spec E10). Cited at L1463 and L1705. Premise recalled at L1702: phi : C\K1 -> C\K2 conformal, K1,K2 compact, giving |phi'(z)| dist(z,K1) asymp dist(phi(z),K2) with universal constants. Compactness of L_t, R_t is not established in the source (see step:hulls-compact).

NODE: ext:koebe-distortion
KIND: external
TITLE: Koebe distortion estimate (Lawler Corollary 3.23)
STATEMENT_SOURCE: external:lawler-book#cor-3.23
PROOF_SOURCE: external:lawler-book#proof
CONTRACT_ID: paper.ext:koebe-distortion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Koebe distortion estimate (Lawler Corollary 3.23)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: Canonical (spec E11). Cited at L1581 (and 'Koebe distortion theorem' at L1806).

NODE: ext:girsanov
KIND: external
TITLE: Girsanov theorem
STATEMENT_SOURCE: external:standard#girsanov
PROOF_SOURCE: external:standard#proof
CONTRACT_ID: paper.ext:girsanov
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Girsanov theorem
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: Canonical (spec E6). Cited at L1802 (for P(tau<infinity)>0 in Prop 3.2(b)); the application is not spelled out (see step:prop-ii-b-hit-lambda-prime).

NODE: ext:kolmogorov-zero-one
KIND: external
TITLE: Kolmogorov zero-one law (tail sigma-algebra of BM is trivial)
STATEMENT_SOURCE: external:standard#kolmogorov-zero-one-tail
PROOF_SOURCE: external:standard#proof
CONTRACT_ID: paper.ext:kolmogorov-zero-one
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Kolmogorov zero-one law (tail sigma-algebra of BM is trivial)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: NEW ext (not in spec table). Used implicitly at L1372 ('measurable w.r.t. the tail sigma-algebra of (B^1..B^m), so a.s. equal to a deterministic constant'). Named by the extractor, not by the source.

NODE: eqn-integral-nu
KIND: display
TITLE: Integrals (I),(II) as stationary expectations (3.1)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1257-L1260
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1257-L1257
CONTRACT_ID: paper.eqn-integral-nu
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time; law of e^{i theta^_t(zz)} is stationary; nu is pi-periodic (stated in source)
SOURCE_QUANTIFIERS: a,b,c; p; t >= 0
SOURCE_CONCLUSION: (I) = E(nu(theta^_t(zz))) and (II) = E(nu(theta^_t(zz)) + 2 cos(2 theta^_t(zz))) for all t >= 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: item-I, item-II, eqn-nu-D.nu, defn-sigma, def-arg, lem-stationary, lem-stationary.admissible
ROUTES: -
ROUTE_FOR: -
EDGE: item-I | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1259-L1259 | left side of the first identity
EDGE: item-II | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1260-L1260 | left side of the second identity
EDGE: eqn-nu-D.nu | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1257-L1260 | nu is pi-periodic and enters both integrands
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1255-L1255 | sigma-time change defining theta^_t
EDGE: def-arg | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1255-L1255 | argument process theta behind theta^
EDGE: lem-stationary | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1257-L1257 | stationarity of e^{i theta^_t(zz)} for every admissible p (R7/R15); the source cites only Lemma 2.13
EDGE: lem-stationary.admissible | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1255-L1257 | p ranges over admissible densities (R7/R15)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Display (3.1). The source only cites lem-p; under R7/R15 the stationarity is supplied by lem-stationary for every admissible p, so both edges are recorded. int_0^{2pi} nu p du = E nu(theta^) uses stationarity at each fixed t and pi-periodicity of nu (no separate step node).

NODE: prop-i.a
KIND: theorem
TITLE: Proposition 3.1(a): (I) >= 0 implies T_z = infinity
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1265-L1269
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1401-L1407
CONTRACT_ID: paper.prop3_1.a
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b > 0 (R5); c^2 <= ab; p admissible (Lemma 2.14 hypotheses, R7/R15); (Omega,P) any probability space with U an SLE_Sigma driver (R6, R9); z in C\{0} (R4); (I) >= 0
SOURCE_QUANTIFIERS: a,b,c; p; (Omega,P,U); z; a.s.
SOURCE_CONCLUSION: a.s. T_z = infinity
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Proposition_3_1_A.lean
FROZEN_DECL: ComplexSLE.proposition_3_1_a
FROZEN_ANCHOR_ID: thm.proposition_3_1_a.v1
FROZEN_ABI_SHA256: 98149ac34067ca49e2b3a5155685d35078ede80ef870a1e3917076c77a93a902
DEPS: item-I, defn-loewner.absorbing-time, step:prop-i-a-not-to-minus-infinity, lem-swallow-distance, step:all-z-apply-Tz, lem-all-z, step:section3-product-extension
ROUTES: -
ROUTE_FOR: -
EDGE: item-I | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1265-L1266 | sign hypothesis on (I)
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1268-L1268 | T_z in the conclusion
EDGE: step:prop-i-a-not-to-minus-infinity | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1406-L1406 | log∣f^_t(zz)∣ does not tend to -infinity when (I) >= 0
EDGE: lem-swallow-distance | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1407-L1407 | T_zz < infinity would force log∣f^_t(zz)∣ -> -infinity, so T_zz = infinity a.s.
EDGE: step:all-z-apply-Tz | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1407-L1407 | discharges the scale-invariance/future-dependence hypotheses of Lemma 3.3 for {T_z = infinity}
EDGE: lem-all-z | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1407-L1407 | extends a.s. T_zz = infinity to each fixed z != 0
EDGE: step:section3-product-extension | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1402-L1402 | the proof works with zz sampled from p independently of the driver, on the product extension of the given probability space
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Root. R4 (z in C\{0}), R5, R15/R7 (every admissible p), R17 (split from Prop 3.1). Hypothesis (I) >= 0 is the Lean hypothesis hI; (I) is item-I. Proof uses the Section-3 package (zz sampled from p); that package is not a hypothesis of the statement and is discharged in the steps (lem-p / lem-stationary). Source label prop-i.

NODE: prop-i.b
KIND: theorem
TITLE: Proposition 3.1(b): (I) < 0 implies T_z < infinity
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1265-L1270
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1401-L1416
CONTRACT_ID: paper.prop3_1.b
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b > 0 (R5); c^2 <= ab; p admissible (Lemma 2.14 hypotheses, R7/R15); (Omega,P) any probability space with U an SLE_Sigma driver (R6, R9); z in C\{0} (R4); (I) < 0
SOURCE_QUANTIFIERS: a,b,c; p; (Omega,P,U); z; a.s.
SOURCE_CONCLUSION: a.s. T_z < infinity
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Proposition_3_1_B.lean
FROZEN_DECL: ComplexSLE.proposition_3_1_b
FROZEN_ANCHOR_ID: thm.proposition_3_1_b.v1
FROZEN_ABI_SHA256: 80b1301f8349878a927cecf5bb3e25558a8e4f99a13edc51752231df161fa236
DEPS: item-I, defn-loewner.absorbing-time, eqn-neg-I1-bd, step:prop-i-b-ode-comparison, step:all-z-apply-Tz, lem-all-z, step:section3-product-extension
ROUTES: -
ROUTE_FOR: -
EDGE: item-I | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1265-L1270 | sign hypothesis on (I)
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1270-L1270 | T_z in the conclusion
EDGE: eqn-neg-I1-bd | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1409-L1412 | pathwise upper bound on log∣f_t(zz)∣ on (t_*,T_zz) in capacity time
EDGE: step:prop-i-b-ode-comparison | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1413-L1415 | F'(t) e^{-alpha F(t)} > 1 forces T_zz <= t_* + e^{-alpha F(t_*)}/alpha < infinity
EDGE: step:all-z-apply-Tz | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1416-L1416 | hypotheses of Lemma 3.3 for {T_z < infinity}
EDGE: lem-all-z | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1416-L1416 | extends a.s. T_zz < infinity to each fixed z != 0
EDGE: step:section3-product-extension | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1402-L1402 | the proof works with zz sampled from p independently of the driver, on the product extension of the given probability space
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Root. R4, R5, R15/R7, R17. The source writes (I) = -alpha < 0 inside the proof.

NODE: prop-ii.a
KIND: theorem
TITLE: Proposition 3.2(a): (II) < 0 implies dist(z,L_t) -> 0
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1276-L1281
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1458-L1469
CONTRACT_ID: paper.prop3_2.a
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b > 0 (R5); c^2 <= ab; p admissible (Lemma 2.14 hypotheses, R7/R15); (Omega,P) any probability space with U an SLE_Sigma driver (R6, R9); z in C\{0} (R4); (II) < 0
SOURCE_QUANTIFIERS: a,b,c; p; (Omega,P,U); z; a.s.
SOURCE_CONCLUSION: a.s. lim_{t->T_z^-} dist(z,L_t) = 0 (R14: for all eps > 0 there is t < T_z with dist(z,L_t) < eps)
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Proposition_3_2_A.lean
FROZEN_DECL: ComplexSLE.proposition_3_2_a
FROZEN_ANCHOR_ID: thm.proposition_3_2_a.v1
FROZEN_ABI_SHA256: 7bbf7b70ad8ac1714e12908c49ba28298a6e77844f927984651fff3b2fc3f161
DEPS: item-II, defn-hulls.left, defn-loewner.absorbing-time, step:prop-ii-a-koebe-limit, step:all-z-apply-dist, lem-all-z, step:section3-product-extension
ROUTES: -
ROUTE_FOR: -
EDGE: item-II | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1276-L1279 | sign hypothesis on (II)
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1279-L1279 | L_t in the conclusion
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1279-L1279 | T_z in the conclusion
EDGE: step:prop-ii-a-koebe-limit | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1459-L1468 | a.s. dist(zz,L_t) -> 0 as t -> T_zz
EDGE: step:all-z-apply-dist | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1468-L1468 | discharges the hypotheses of Lemma 3.3 for the event {lim dist(z,L_t)=0}
EDGE: lem-all-z | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1468-L1468 | extends to each fixed z != 0
EDGE: step:section3-product-extension | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1459-L1459 | the proof works with zz sampled from p independently of the driver, on the product extension of the given probability space
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Root. R4, R5, R14 (epsilon form; L_t increasing so the limit is the infimum), R15/R7, R17. The proof environment is labelled 'Proof of Proposition 3.2(a)' (typeset as item-ii-b at L1458, a hyperref glitch).

NODE: prop-ii.b
KIND: theorem
TITLE: Proposition 3.2(b): (II) > 0 implies lim dist(z,L_t) > 0
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1276-L1283
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1786-L1816
CONTRACT_ID: paper.prop3_2.b
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b > 0 (R5); c^2 <= ab; p admissible (Lemma 2.14 hypotheses, R7/R15); (Omega,P) any probability space with U an SLE_Sigma driver (R6, R9); z in C\{0} (R4); (II) > 0
SOURCE_QUANTIFIERS: a,b,c; p; (Omega,P,U); z; a.s.
SOURCE_CONCLUSION: a.s. lim_{t->T_z^-} dist(z,L_t) > 0 (R14: there is eps > 0 with eps <= dist(z,L_t) for all t < T_z)
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Proposition_3_2_B.lean
FROZEN_DECL: ComplexSLE.proposition_3_2_b
FROZEN_ANCHOR_ID: thm.proposition_3_2_b.v1
FROZEN_ABI_SHA256: 68e7f561920bc47ded181922aa3709800fd30024d385e40bf7734750bb063c67
DEPS: item-II, defn-hulls.left, defn-loewner.absorbing-time, step:prop-ii-b-martingale-zero-one, step:section3-product-extension, claim:hulls-monotone
ROUTES: -
ROUTE_FOR: -
EDGE: item-II | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1276-L1281 | sign hypothesis on (II)
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1281-L1281 | L_t in the conclusion
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1281-L1281 | T_z in the conclusion
EDGE: step:prop-ii-b-martingale-zero-one | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1815-L1815 | indicator of {lim dist > 0} is a.s. >= q_*, hence equals 1
EDGE: step:section3-product-extension | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1793-L1793 | Fubini over the independent pair (zz, U) requires the product extension of the given probability space
EDGE: claim:hulls-monotone | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1815-L1815 | L_t is increasing, so t -> dist(z,L_t) is non-increasing and the almost sure limit lim_{t->T_z-} dist(z,L_t) > 0 equals the infimum over t < T_z; this converts the proved limit statement into the frozen epsilon-form (R14) with epsilon := that infimum
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Root. R4, R5, R14, R15/R7, R17. The proof (L1786-1816) upgrades Lemma 3.8 (positive probability for zz) to an a.s. statement; Lemma 3.8 enters through step:prop-ii-b-lambda-positive-measure.

NODE: lem-all-z
KIND: lemma
TITLE: Lemma 3.3: from the stationary point zz to every z
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1294-L1301
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1305-L1319
CONTRACT_ID: paper.lem-all-z
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: {E(z)} events for the SLE_Sigma chain (f_t) with (i) a.s. for all r>0: E(z) iff E(rz) for the chain t -> r f_{t/r^2}(./r) (scale invariance); (ii) a.s. for all s>0: E(z) & {s<T_z} iff s<T_z and E(f_s(z)) for the chain f_{s,s+t} of (2.3) (future dependence); P(E(zz)) = 1; Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: events E; zz; z
SOURCE_CONCLUSION: P(E(z)) = 1 for every z in C\{0}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:all-z-lambda-conull, step:all-z-markov-transfer, step:all-z-stopping-time-choice
ROUTES: -
ROUTE_FOR: -
EDGE: step:all-z-lambda-conull | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1306-L1310 | Lambda is the whole unit circle up to a Lebesgue-null set
EDGE: step:all-z-markov-transfer | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1312-L1316 | P(E(z)) equals the average of P(E(.)) at e^{i theta_tau(z)} for a stopping time tau < T_z
EDGE: step:all-z-stopping-time-choice | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1318-L1318 | tau with P(e^{i theta_tau(z)} in Lambda) >= q for any q < 1, hence P(E(z)) = 1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Statement hypotheses are (i),(ii) and P(E(zz))=1; the Section-3 package supplies the law of zz. Section-3 text before L1294 introduces zz; the examples sentence L1303 is a separate unlabeled claim (step:all-z-apply-Tz, step:all-z-apply-dist). Typos: the statement's 'a.s. P(E)=1' is read as above.

NODE: step:all-z-null-set-density
KIND: step
TITLE: An admissible p vanishes only on a Lebesgue-null set
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1306-L1306
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1306-L1306
CONTRACT_ID: paper.step:all-z-null-set-density
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: p admissible (Lemma 2.14 hypotheses)
SOURCE_QUANTIFIERS: p
SOURCE_CONCLUSION: {u in [0,2pi] : p(u) = 0} is Lebesgue-null
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-stationary.admissible, lem-p
ROUTES: -
ROUTE_FOR: -
EDGE: lem-stationary.admissible | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1306-L1306 | p ranges over admissible densities (R7/R15)
EDGE: lem-p | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1306-L1306 | the source's justification: p of Lemma 2.13 is strictly positive off a discrete set
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: the source asserts 'non-zero on [0,2pi] except possibly on a discrete set' for p, which Lemma 2.13 proves only for the constructed p; admissibility (Lemma 2.14 hypotheses) does not state it (R7/R15). The hypothesis P(E(z))=1 transfers to Lambda a.e. only through this claim.

NODE: step:all-z-lambda-conull
KIND: step
TITLE: Lambda has full Lebesgue measure in the unit circle
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-nohit-set@L1306-L1310
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1306-L1310
CONTRACT_ID: paper.step:all-z-lambda-conull
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: P(E(zz)) = 1; zz independent of U with arg zz ~ p 1_[0,2pi]
SOURCE_QUANTIFIERS: Lambda := {|z| = 1 : P(E(z)) = 1}
SOURCE_CONCLUSION: the unit circle minus Lambda is Lebesgue-null
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:all-z-null-set-density
ROUTES: -
ROUTE_FOR: -
EDGE: step:all-z-null-set-density | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1306-L1310 | density p positive a.e. so a.s. event for zz forces P(E(z))=1 for a.e. z (Fubini over the independent zz)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Fubini over the independent pair (zz, U): 1 = P(E(zz)) = int P(E(e^{iu})) p(u) du. Display (eqn-nohit-set).

NODE: step:all-z-markov-transfer
KIND: step
TITLE: Conditioning at a stopping time tau < T_z
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1312-L1316
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1316-L1316
CONTRACT_ID: paper.step:all-z-markov-transfer
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z in C\{0}; tau stopping time for (f_t) with tau < T_z a.s.; (i),(ii) of Lemma 3.3
SOURCE_QUANTIFIERS: z; tau
SOURCE_CONCLUSION: P(E(z)) = E[ P(E(w))|_{w = e^{i theta_tau(z)}} ], i.e. conditional on (f_t)_{t<=tau} the rescaled future chain t -> |f_tau(z)|^{-1} f_{tau,tau+|f_tau(z)|^{-2}t}(|f_tau(z)| .) is an SLE_Sigma chain
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-scaling, lem-markov, eqn-conc, def-arg
ROUTES: -
ROUTE_FOR: -
EDGE: lem-scaling | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1316-L1316 | scale invariance applied with the F_tau-measurable factor ∣f_tau(z)∣^{-1}
EDGE: lem-markov | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1316-L1316 | strong Markov property at tau: the future chain is independent of F_tau
EDGE: eqn-conc | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1312-L1314 | the future chain f_{tau,tau+.} of (2.3)
EDGE: def-arg | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1312-L1312 | e^{i theta_tau(z)} = f_tau(z)/∣f_tau(z)∣
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Application of scaling and Markov at a stopping time with a random (F_tau-measurable) scale. The source writes 'P(E(z)) = P(E(z\'))' for the random point z\' = e^{i theta_tau(z)}; read as the conditional-expectation identity above (uncertain). Measurability of tau as a stopping time of the driver filtration is implicit.

NODE: step:all-z-stopping-time-choice
KIND: step
TITLE: Choice of tau with e^{i theta_tau(z)} in Lambda with probability >= q
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1318-L1318
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1318-L1318
CONTRACT_ID: paper.step:all-z-stopping-time-choice
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Lambda dense in the unit circle (from step:all-z-lambda-conull); theta_.(z) non-constant continuous on [0,T_z)
SOURCE_QUANTIFIERS: q < 1; z
SOURCE_CONCLUSION: there is a stopping time tau < T_z a.s. with P(e^{i theta_tau(z)} in Lambda) >= q; hence P(E(z)) >= q, and P(E(z)) = 1
CONSTANT_SCOPE: q in (0,1) is arbitrary; tau = tau(z,q) is a stopping time chosen after q; no dependence of Lambda on q
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:all-z-lambda-conull, lem-polar, defn-sigma, def-arg
ROUTES: -
ROUTE_FOR: -
EDGE: step:all-z-lambda-conull | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1318-L1318 | Lambda dense (full measure in the circle)
EDGE: lem-polar | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1318-L1318 | the SDE for theta^ shows theta is non-constant (non-degenerate noise)
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1312-L1312 | tau may be a sigma_z(t^)
EDGE: def-arg | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1318-L1318 | continuous argument process theta_t(z)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: asserted ('for any q > 0 we can find a stopping time tau ...') from 'non-constant, continuous, Lambda dense' without proof; no argument that theta_tau lands in the conull dense set Lambda with probability >= q is given (e.g. which tau, why q arbitrary).

NODE: step:all-z-apply-Tz
KIND: application
TITLE: Lemma 3.3 hypotheses hold for {T_z < infinity} (and its complement)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1303-L1303
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1303-L1303
CONTRACT_ID: paper.step:all-z-apply-Tz
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E(z) = {T_z < infinity} (equivalently {T_z = infinity})
SOURCE_QUANTIFIERS: z; r > 0; s > 0
SOURCE_CONCLUSION: scale invariance and future dependence hold for E(z) = {T_z < infinity}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-scale, eqn-conc, defn-loewner.absorbing-time
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-scale | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1303-L1303 | T_{rz} for the chain r f_{t/r^2}(./r) equals r^2 T_z, absorption time scales
EDGE: eqn-conc | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1303-L1303 | future dependence: T_z = s + T_{f_s(z)}(chain f_{s,s+.}) on {s < T_z}
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1303-L1303 | T_z
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: asserted only ('Examples of events for which the hypotheses apply are {T_z<infinity} ...', L1303), not verified. Used for {T_z=infinity} in Prop 3.1(a) as well (complement of the same event; closure under complement is implicit).

NODE: step:all-z-apply-dist
KIND: application
TITLE: Lemma 3.3 hypotheses hold for {lim_{t->T_z} dist(z,L_t) = 0}
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1303-L1303
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1303-L1303
CONTRACT_ID: paper.step:all-z-apply-dist
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E(z) = {lim_{t->T_z^-} dist(z,L_t) = 0} (equivalently its complement {lim > 0})
SOURCE_QUANTIFIERS: z; r > 0; s > 0
SOURCE_CONCLUSION: scale invariance and future dependence hold for E(z) = {lim_{t->T_z^-} dist(z,L_t) = 0}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-scale, eqn-conc, defn-hulls.left, defn-loewner.absorbing-time
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-scale | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1303-L1303 | left hulls of the rescaled chain are r L_{t/r^2}, so distances scale
EDGE: eqn-conc | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1303-L1303 | future dependence: relation of L_{s+t} and L_{s,s+t}
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1303-L1303 | L_t
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1303-L1303 | T_z
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: asserted only (L1303). Future dependence for the distance event ('dist(z,L_t) -> 0 iff dist(f_s(z), L_{s,s+t}) -> 0') is not obvious and not argued in the source (conformal distortion between L_{s+t} and f_s^{-1}(L_{s,s+t}) would be needed). R14: the event is read in epsilon-form.

NODE: lem-stationary-sde
KIND: lemma
TITLE: Lemma 3.4: law of large numbers and recurrence for stationary SDE functionals
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1327-L1343
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1360-L1379
CONTRACT_ID: paper.lem-stationary-sde
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m in N; (B^1..B^m) m-dim BM (arbitrary covariance); X : [0,inf) -> C adapted to the filtration of B, law stationary in time, dX = g^0(X)dt + sum g^j(X) dB^j with measurable g^j; deterministic xbar with a.s. arbitrarily large t with X_t = xbar; measurable f^0..f^m : C -> R with E int_0^1 (f^j(X_s))^2 ds < infinity; Y : [0,inf) -> R with dY = f^0(X)dt + sum f^j(X) dB^j
SOURCE_QUANTIFIERS: m; B; X; xbar; f^j; Y
SOURCE_CONCLUSION: a.s. Y_t/t -> E f^0(X_0) (source typo T2: X_0^0 read as X_0); if E f^0(X_0) = 0 then a.s. for each eps > 0 there are arbitrarily large t with |Y_t| < eps
CONSTANT_SCOPE: xbar is a deterministic point of C (independent of omega, chosen before X); m, f^j, g^j are deterministic
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:sde-birkhoff-limit, step:sde-limit-deterministic, step:sde-mean-zero, step:sde-recurrence-zero
ROUTES: -
ROUTE_FOR: -
EDGE: step:sde-birkhoff-limit | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1361-L1363 | Y_t/t converges a.s. to E(Y_1-Y_0 ∣ I)
EDGE: step:sde-limit-deterministic | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1366-L1372 | the limit is a.s. a deterministic constant
EDGE: step:sde-mean-zero | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1374-L1375 | E(Y_1-Y_0) = E f^0(X_0), identifying the constant
EDGE: step:sde-recurrence-zero | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1377-L1378 | second assertion when E f^0(X_0) = 0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: General stochastic lemma (no SLE input). Y_0 is not assumed 0; the second assertion needs sum_{k<=n} xi_k = Y_n - Y_0 so Y_0 = 0 (true in all applications: Y_0 = log|zz| = 0 and log(|f_0'|/|f_0|) = 0) -- implicit hypothesis, uncertain. Filtration of the SDE solution X relative to B and uniqueness in law of its SDE are not stated.

NODE: step:sde-stationary-increments
KIND: step
TITLE: Y has stationary increments
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1361-L1361
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1361-L1361
CONTRACT_ID: paper.step:sde-stationary-increments
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: X stationary in law, adapted to filtration of B; SDEs of X, Y
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: the increment sequence (Y_n - Y_{n-1})_{n>=1} is a stationary sequence
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: asserted ('The process Y has stationary increments'). Stationarity of the law of X alone does not give stationarity of the pair (X, B-increments); the joint stationarity of (X_{t+.}, B_{t+.}-B_t) is not stated in the hypotheses.

NODE: step:sde-continuity-noninteger
KIND: step
TITLE: Continuity argument for non-integer times
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1361-L1363
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1361-L1363
CONTRACT_ID: paper.step:sde-continuity-noninteger
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E int_0^1 (f^j(X_s))^2 ds < infinity; stationary increments
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Y_t/t and Y_{floor(t)}/floor(t) have the same limit a.s. (sup_{t in [n,n+1]} |Y_t - Y_n| / n -> 0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:sde-stationary-increments
ROUTES: -
ROUTE_FOR: -
EDGE: step:sde-stationary-increments | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1361-L1363 | stationarity of the increments of Y is used to compare Y_t/t with Y_{floor(t)}/floor(t)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: the source says only 'a standard continuity argument'; the details (Doob, Chebyshev, Borel-Cantelli) appear only in a %-commented block (L1364), which is not part of the paper.

NODE: step:sde-birkhoff-limit
KIND: step
TITLE: Birkhoff: Y_t/t -> E(Y_1-Y_0 | I)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1361-L1363
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1361-L1363
CONTRACT_ID: paper.step:sde-birkhoff-limit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (Y_n - Y_{n-1}) stationary; I invariant sigma-algebra of the increment sequence
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: a.s. Y_t/t -> E(Y_1 - Y_0 | I) as t -> infinity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: ext:birkhoff, step:sde-stationary-increments, step:sde-continuity-noninteger
ROUTES: -
ROUTE_FOR: -
EDGE: ext:birkhoff | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1361-L1361 | Birkhoff ergodic theorem for the stationary increment sequence
EDGE: step:sde-stationary-increments | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1361-L1361 | Y has stationary increments
EDGE: step:sde-continuity-noninteger | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1361-L1361 | passes from integer to real times
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Carrier change: sequence Y_n/n to process Y_t/t.

NODE: step:sde-regeneration
KIND: step
TITLE: Post-tau_k increments of Y are independent of B up to tau_k
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1366-L1367
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1366-L1367
CONTRACT_ID: paper.step:sde-regeneration
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: xbar as in the lemma; tau_1 = first t with X_t = xbar; tau_k = first t >= tau_{k-1}+1 with X_t = xbar; a.s. tau_k < infinity
SOURCE_QUANTIFIERS: k >= 1
SOURCE_CONCLUSION: {Y_{t+tau_k} - Y_{tau_k}}_{t>=0} is independent of (B^1..B^m)|_{[0,tau_k]}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: ext:strong-markov-bm
ROUTES: -
ROUTE_FOR: -
EDGE: ext:strong-markov-bm | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1367-L1367 | strong Markov property of BM at the stopping time tau_k
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP (partial): the conditional law of the post-tau_k increments depends only on X_{tau_k} = xbar only if the SDE for X has uniqueness in law (or X is a functional of the post-tau_k noise and xbar); the source says 'by the strong Markov property and the SDEs for X and Y' without stating this.

NODE: step:sde-limit-deterministic
KIND: step
TITLE: lim Y_t/t is a.s. a deterministic constant
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1366-L1372
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1366-L1372
CONTRACT_ID: paper.step:sde-limit-deterministic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: tau_k as in step:sde-regeneration; tau_k >= k
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: lim_{t->infty} Y_t/t is a.s. equal to a deterministic constant
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:sde-birkhoff-limit, step:sde-regeneration, ext:kolmogorov-zero-one
ROUTES: -
ROUTE_FOR: -
EDGE: step:sde-birkhoff-limit | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1366-L1370 | the limit exists a.s.
EDGE: step:sde-regeneration | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1367-L1372 | limit equals lim (Y_{t+tau_k}-Y_{tau_k})/t, independent of B∣[0,tau_k]
EDGE: ext:kolmogorov-zero-one | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1372-L1372 | tail sigma-algebra of B is trivial
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Tail-measurability from independence of every B|[0,tau_k] and tau_k >= k.

NODE: step:sde-mean-zero
KIND: step
TITLE: Mean-zero stochastic integrals and E(Y_1-Y_0) = E f^0(X_0)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1374-L1375
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1374-L1375
CONTRACT_ID: paper.step:sde-mean-zero
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E int_0^1 (f^j(X_t))^2 dt < infinity for j >= 1; X stationary
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: E int_0^1 f^j(X_t) dB^j_t = 0 for j >= 1 and E(Y_1 - Y_0) = E f^0(X_0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Standard L^2 Ito-integral property plus stationarity of X and Fubini. The citation [Revuz-Yor, Thm IV.2.2] appears only in a %-comment at L1374 (not part of the paper), so no ext node is created; the orchestrator may add one. Reused in step:integral-ii-expectation.

NODE: step:sde-recurrence-zero
KIND: step
TITLE: Recurrence of Y near 0 when E f^0(X_0) = 0
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1377-L1378
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1377-L1378
CONTRACT_ID: paper.step:sde-recurrence-zero
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E f^0(X_0) = 0; xi_n = Y_n - Y_{n-1}
SOURCE_QUANTIFIERS: eps > 0
SOURCE_CONCLUSION: a.s. for each eps > 0 there are arbitrarily large t with |Y_t| < eps
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-recurrent, step:sde-stationary-increments, step:sde-birkhoff-limit, step:sde-limit-deterministic, step:sde-mean-zero
ROUTES: -
ROUTE_FOR: -
EDGE: lem-recurrent | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1378-L1378 | applied to the stationary sequence xi_n
EDGE: step:sde-birkhoff-limit | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1378-L1378 | E(xi_1 ∣ I) is the a.s. limit of Y_n/n
EDGE: step:sde-limit-deterministic | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1378-L1378 | the limit is deterministic
EDGE: step:sde-mean-zero | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1378-L1378 | that constant equals E f^0(X_0) = 0, hence E(xi_1 ∣ I) = 0
EDGE: step:sde-stationary-increments | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1378-L1378 | discharges the premise 'stationary sequence' of Lemma 3.5 for xi_n = Y_n - Y_{n-1}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The source applies Lemma 3.5 directly; the hypothesis E(xi_1 | I) = 0 of Lemma 3.5 is discharged only implicitly via the first part (limit = E(Y_1-Y_0|I) = const = 0). Also uses Y_0 = 0 (see lem-stationary-sde NOTE).

NODE: lem-recurrent
KIND: lemma
TITLE: Lemma 3.5: recurrence for stationary sequences with E(xi_1|I) = 0
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrent@L1349-L1352
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrent@L1355-L1357
CONTRACT_ID: paper.lem-recurrent
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (xi_n) stationary sequence in R; I the invariant sigma-algebra; E(xi_1 | I) = 0
SOURCE_QUANTIFIERS: (xi_n); eps > 0
SOURCE_CONCLUSION: a.s. for each eps > 0 there are infinitely many n with |sum_{k<=n} xi_k| < eps
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:recurrent-durrett-adaptation
ROUTES: -
ROUTE_FOR: -
EDGE: step:recurrent-durrett-adaptation | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrent@L1356-L1356 | 'essentially identical' to Durrett Thm 7.3.2
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Alternative reference in %-comment (Dekking, L1353) is not part of the paper.

NODE: step:recurrent-durrett-adaptation
KIND: step
TITLE: Adaptation of Durrett Thm 7.3.2 to real-valued sequences with E(xi_1|I)=0
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrent@L1356-L1356
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrent@L1356-L1356
CONTRACT_ID: paper.step:recurrent-durrett-adaptation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: xi stationary R-valued, E(xi_1 | I) = 0
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: recurrence of partial sums (Durrett Thm 7.3.2 statement for Z-valued sequences extended to R-valued)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: ext:durrett-7.3.2
ROUTES: -
ROUTE_FOR: -
EDGE: ext:durrett-7.3.2 | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrent@L1356-L1356 | template theorem
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: proof delegated to 'essentially identical' to [Durrett 7.3.2] (which is for Z-valued random variables); the real-valued and non-ergodic (conditional on I) version is not proved.

NODE: lem-swallow-distance
KIND: lemma
TITLE: Lemma 3.6: log|f^_t(z)| -> -infinity when T_z < infinity
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-swallow-distance@L1389-L1392
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-swallow-distance@L1394-L1397
CONTRACT_ID: paper.lem-swallow-distance
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z in C; sigma = sigma_z; hats denote sigma-time
SOURCE_QUANTIFIERS: z
SOURCE_CONCLUSION: a.s. on {T_z < infinity}, log|f^_t(z)| -> -infinity as t -> infinity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-sigma, step:swallow-time-change
ROUTES: -
ROUTE_FOR: -
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-swallow-distance@L1391-L1391 | sigma_z and hats
EDGE: step:swallow-time-change | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-swallow-distance@L1395-L1396 | passes the capacity-time limit to sigma-time
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Statement is for every z in C, not only zz. For z = 0, T_0 = 0 and sigma_0 is degenerate (R4); the application is to zz and z != 0.

NODE: step:swallow-time-change
KIND: step
TITLE: Capacity-time limit to sigma-time limit
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-swallow-distance@L1395-L1396
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-swallow-distance@L1395-L1396
CONTRACT_ID: paper.step:swallow-time-change
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: T_z < infinity
SOURCE_QUANTIFIERS: z
SOURCE_CONCLUSION: lim_{t->T_z^-} log|f_t(z)| = -infinity and sigma(infinity) = T_z give lim_{t^ -> infinity} log|f^_t(z)| = -infinity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-endpt-cont, remark-sigma
ROUTES: -
ROUTE_FOR: -
EDGE: lem-endpt-cont | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-swallow-distance@L1395-L1395 | on {T_z < infinity}, lim_{t->T_z^-} log∣f_t(z)∣ = -infinity
EDGE: remark-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-swallow-distance@L1396-L1396 | sigma(infinity) = T_z, so t^ -> infinity corresponds to t -> T_z^-
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Carrier change capacity time to sigma-time.

NODE: step:stationary-sde-X-form
KIND: step
TITLE: The SDEs for X = e^{2 i theta^(zz)} and Y have the form required by Lemma 3.4
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1402-L1403
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1402-L1403
CONTRACT_ID: paper.step:stationary-sde-X-form
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time; coefficients of the SDEs of Lemma 2.11 are pi-periodic
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: X_t = e^{2 i theta^_t(zz)} satisfies dX = g^0(X)dt + sum_j g^j(X)dB^j with measurable g^j (m = 2), and log|f^_t(zz)|, log(|f^_t'(zz)|/|f^_t(zz)|) satisfy dY = f^0(X)dt + sum f^j(X)dB^j with measurable f^j and E int_0^1 (f^j(X_s))^2 ds < infinity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-polar
ROUTES: -
ROUTE_FOR: -
EDGE: lem-polar | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1403-L1403 | SDEs for theta^, log∣f^∣ and log∣f^'∣ (drifts mu, nu, -2cos 2theta^ are pi-periodic, hence functions of X)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: the source asserts 'the needed SDEs for X and Y come from Lemma 2.11 and the fact that the coefficients are pi-periodic' (also L1345). The drift coefficients are pi-periodic, but the diffusion coefficients -sqrt(a) sin(theta^), sqrt(b) cos(theta^), sqrt(a) cos(theta^), sqrt(b) sin(theta^) are only 2pi-periodic (sign flips under theta -> theta + pi), so they are not functions of X = e^{2 i theta^} without a sign-absorbing change of Brownian motion; also an Ito computation for e^{2 i theta^} is needed. Integrability (bounded coefficients) is implicit. Not stated in the source.

NODE: step:prop-i-apply-stationary-sde
KIND: application
TITLE: Apply Lemma 3.4 with Y = log|f^(zz)|, m = 2, X = e^{2 i theta^(zz)}
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1402-L1403
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1402-L1403
CONTRACT_ID: paper.step:prop-i-apply-stationary-sde
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: a.s. log|f^_t(zz)|/t -> (I); if (I) = 0 then a.s. for each eps > 0 there are arbitrarily large t with |log|f^_t(zz)|| < eps
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-stationary-sde, step:stationary-sde-X-form, lem-polar, lem-recurrence, lem-stationary, eqn-integral-nu
ROUTES: -
ROUTE_FOR: -
EDGE: lem-stationary-sde | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1402-L1402 | conclusion of Lemma 3.4 for Y = log∣f^(zz)∣
EDGE: step:stationary-sde-X-form | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1403-L1403 | SDEs for X and Y in the form required
EDGE: lem-polar | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1402-L1403 | SDE (eqn-abs-zt) for log∣f^_t(zz)∣ with drift nu(theta^)
EDGE: lem-recurrence | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1403-L1403 | recurrence of X (hits a fixed xbar at arbitrarily large times)
EDGE: lem-stationary | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1403-L1403 | stationarity of the law of X_t = e^{2 i theta^_t(zz)} for every admissible p
EDGE: eqn-integral-nu | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1402-L1402 | E f^0(X_0) = E nu(theta^_0(zz)) = (I)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Premise discharge: m=2, X adapted to the (enlarged) filtration of the driver (zz is independent of U, so enlarge by sigma(zz)), Y_0 = log|zz| = 0, f^0 = nu, f^1 = sqrt(a) cos, f^2 = sqrt(b) sin; (I) = E nu(theta^_t(zz)) = E log|f^_t(zz)|/t from eqn-integral-nu. Lemma 2.16 is used under a, b > 0 and c^2 <= ab (R5); its case c = sqrt(ab) hits a single point, |c| < sqrt(ab) hits any point. Local hypothesis package supplied by lem-p/lem-stationary.

NODE: step:prop-i-a-not-to-minus-infinity
KIND: step
TITLE: (I) >= 0 implies log|f^_t(zz)| does not tend to -infinity
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1406-L1406
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1406-L1406
CONTRACT_ID: paper.step:prop-i-a-not-to-minus-infinity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (I) >= 0; Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: a.s. log|f^_t(zz)| does not converge to -infinity as t -> infinity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:prop-i-apply-stationary-sde
ROUTES: -
ROUTE_FOR: -
EDGE: step:prop-i-apply-stationary-sde | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1406-L1406 | case (I) > 0: log∣f^_t∣/t -> (I) > 0; case (I) = 0: arbitrarily large t with ∣log∣f^_t∣∣ < eps
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Case split (I) > 0 / (I) = 0 (the source only writes 'by Lemma 3.4').

NODE: eqn-neg-I1-bd
KIND: display
TITLE: Pathwise bound (3.2): log|f_t(zz)| < -(alpha/2) int_0^t |f_s(zz)|^{-2} ds
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-neg-I1-bd@L1409-L1412
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1409-L1410
CONTRACT_ID: paper.eqn-neg-I1-bd
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (I) = -alpha < 0; Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: alpha > 0
SOURCE_CONCLUSION: a.s. there is t_* < T_zz such that for all t in (t_*, T_zz): log|f_t(zz)| < -(alpha/2) int_0^t |f_s(zz)|^{-2} ds
CONSTANT_SCOPE: alpha = -(I) > 0 is deterministic (depends on Sigma, p); t_* < T_zz is random (depends on omega), a.s. finite
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:prop-i-apply-stationary-sde, defn-sigma, remark-sigma
ROUTES: -
ROUTE_FOR: -
EDGE: step:prop-i-apply-stationary-sde | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1409-L1409 | log∣f^_t(zz)∣/t -> -alpha
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1409-L1410 | t^ = int_0^{sigma(t^)} ∣f_s(zz)∣^{-2} ds converts t^ to capacity time
EDGE: remark-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1409-L1409 | sigma maps (0,infinity) onto (0,T_zz): 'going back to the original parametrization' covers (t_*,T_zz)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Carrier change sigma-time to capacity time. The exact constant alpha/2 comes from log|f^_t| < -(alpha/2) t^ for t^ large.

NODE: step:prop-i-b-ode-comparison
KIND: step
TITLE: ODE comparison: F'(t) e^{-alpha F(t)} > 1 forces T_zz < infinity
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1413-L1415
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1413-L1415
CONTRACT_ID: paper.step:prop-i-b-ode-comparison
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: eqn-neg-I1-bd; F(t) = int_0^t |f_s(zz)|^{-2} ds, F' = |f_t(zz)|^{-2}
SOURCE_QUANTIFIERS: alpha > 0
SOURCE_CONCLUSION: a.s. T_zz <= t_* + (1/alpha) e^{-alpha F(t_*)} < infinity
CONSTANT_SCOPE: alpha > 0 deterministic; t_* is the random time of (3.2); the bound t_* + e^{-alpha F(t_*)}/alpha is random
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-neg-I1-bd
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-neg-I1-bd | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1413-L1414 | rearranged to F'(t) e^{-alpha F(t)} > 1 on (t_*,T_zz)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Elementary calculus; kept as a step because it contains a contradiction argument for t > t_* + e^{-alpha F(t_*)}/alpha (quantifier closure, including the case T_zz = infinity).

NODE: eqn-sde-ratio
KIND: display
TITLE: SDE (3.4) for log(|f^_t'|/|f^_t|)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-sde-ratio@L1441-L1446
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-integral-ii@L1441-L1446
CONTRACT_ID: paper.eqn-sde-ratio
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z in C; sigma = sigma_z; W, W~ standard BMs correlated as (B,B~)
SOURCE_QUANTIFIERS: z; t^ >= 0
SOURCE_CONCLUSION: d log(|f^_t'(z)|/|f^_t(z)|) = -(nu(theta^_t) + 2 cos 2theta^_t) dt^ - sqrt(a) cos(theta^_t) dW_t^ - sqrt(b) sin(theta^_t) dW~_t^
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-polar
ROUTES: -
ROUTE_FOR: -
EDGE: lem-polar | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-sde-ratio@L1441-L1441 | subtract the SDE (eqn-abs-zt) for d log∣f^∣ from (eqn-abs-zt') for d log∣f^'∣
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Derived by subtracting two SDEs of Lemma 2.11 (routine, no step). Written for fixed z; reused for zz in Lemma 3.7 and Lemma 3.8, and for fixed z in Lemma 3.12. The BMs in the source are called W, W~ and are the same pair as in Lemma 2.11 (the sign of the dW terms is as in the source).

NODE: lem-integral-ii
KIND: lemma
TITLE: Lemma 3.7: E log(|f^'|/|f^|)(zz) = -t^ (II), and divergence when (II) < 0
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-integral-ii@L1430-L1437
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-integral-ii@L1440-L1452
CONTRACT_ID: paper.lem-integral-ii
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time; second part: (II) < 0
SOURCE_QUANTIFIERS: t^ >= 0
SOURCE_CONCLUSION: E log(|f^_t'(zz)|/|f^_t(zz)|) = -t^ (II) for all t^ >= 0; if (II) < 0 then a.s. lim_{t^->infinity} |f^_t'(zz)|/|f^_t(zz)| = +infinity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: item-II, defn-sigma, eqn-sde-ratio, step:integral-ii-expectation, step:integral-ii-apply-stationary-sde
ROUTES: -
ROUTE_FOR: -
EDGE: item-II | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-integral-ii@L1433-L1435 | the constant (II)
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-integral-ii@L1433-L1433 | sigma-time parametrization
EDGE: eqn-sde-ratio | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-integral-ii@L1441-L1444 | SDE for log(∣f^'∣/∣f^∣)
EDGE: step:integral-ii-expectation | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-integral-ii@L1447-L1450 | expectation identity from stationarity
EDGE: step:integral-ii-apply-stationary-sde | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-integral-ii@L1451-L1451 | second part by Lemma 3.4
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The source writes z for zz in the display (eqn-sde-ratio) and 'stationary in zz' where 'stationary in t' is meant. Section-3 package applies.

NODE: step:integral-ii-expectation
KIND: step
TITLE: E log(|f^'|/|f^|)(zz) = -t^ (II)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-integral-ii@L1447-L1450
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-integral-ii@L1447-L1450
CONTRACT_ID: paper.step:integral-ii-expectation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: t^ >= 0
SOURCE_CONCLUSION: E log(|f^_t'(zz)|/|f^_t(zz)|) = -t^ E(nu(theta^) + 2 cos 2theta^) = -t^ (II)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-sde-ratio, step:sde-mean-zero, eqn-integral-nu
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-sde-ratio | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-integral-ii@L1447-L1447 | the SDE integrated from 0 to t^ with log(∣f_0'∣/∣f_0∣) = 0
EDGE: step:sde-mean-zero | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-integral-ii@L1447-L1450 | the stochastic-integral terms have mean zero (bounded integrands)
EDGE: eqn-integral-nu | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-integral-ii@L1447-L1450 | E(nu(theta^) + 2cos 2theta^) = (II) by stationarity
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Fubini plus stationarity at each time t.

NODE: step:integral-ii-apply-stationary-sde
KIND: application
TITLE: Apply Lemma 3.4 with Y = log(|f^'|/|f^|)(zz)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-integral-ii@L1451-L1451
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-integral-ii@L1451-L1451
CONTRACT_ID: paper.step:integral-ii-apply-stationary-sde
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (II) < 0; Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: (II) < 0 implies a.s. log(|f^_t'(zz)|/|f^_t(zz)|)/t^ -> -(II) > 0, so the ratio tends to +infinity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-stationary-sde, eqn-sde-ratio, step:stationary-sde-X-form, lem-recurrence, lem-stationary, eqn-integral-nu
ROUTES: -
ROUTE_FOR: -
EDGE: lem-stationary-sde | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-integral-ii@L1451-L1451 | conclusion for Y = log(∣f^'∣/∣f^∣)
EDGE: eqn-sde-ratio | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-integral-ii@L1451-L1451 | SDE giving f^0 = -(nu + 2 cos 2theta^), f^1 = -sqrt(a) cos, f^2 = -sqrt(b) sin
EDGE: step:stationary-sde-X-form | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-integral-ii@L1451-L1451 | SDE form for X and Y
EDGE: lem-recurrence | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-integral-ii@L1451-L1451 | recurrence of X
EDGE: lem-stationary | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-integral-ii@L1451-L1451 | stationarity of X
EDGE: eqn-integral-nu | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-integral-ii@L1451-L1451 | E f^0(X_0) = -(II)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The source says only 'the second part follows from applying Lemma 3.4'; the premise discharge parallels step:prop-i-apply-stationary-sde. Y_0 = log(|f_0'(zz)|/|f_0(zz)|) = log(1/|zz|) = 0.

NODE: step:zero-in-left-hull
KIND: step
TITLE: 0 belongs to every left hull
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1558-L1558
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1558-L1558
CONTRACT_ID: paper.step:zero-in-left-hull
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U_0 = 0 (R4)
SOURCE_QUANTIFIERS: t >= 0
SOURCE_CONCLUSION: 0 in L_t, hence dist(zz, L_t) <= |zz| = 1 and log(1/dist(zz,L_{sigma(t^)})) >= 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-hulls.left, defn-loewner.absorbing-time, defn-sle
ROUTES: -
ROUTE_FOR: -
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1558-L1558 | L_t = {z : T_z <= t}
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1558-L1558 | T_0 = 0 because the driver starts at the singular point 0
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1558-L1558 | U_0 = 0 almost surely is part of the SLE_Sigma driver (R6); this supplies the premise U_0 = 0 (T_0 = 0, so 0 in L_t) that is otherwise only a hypothesis of this node
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: R4: U_0 = 0, so T_0 = 0 and 0 in L_t for all t. Used at L1558. The shifted-driver statement for L_{t,s+t} used at L1768 is step:zero-in-future-left-hull. Premise U_0 = 0 is supplied by defn-sle (a.s. U_0 = 0, R6); for a general continuous driver the correct statement is U_0 in L_t (claim:hull-nonempty).

NODE: step:zero-in-right-hull
KIND: step
TITLE: 0 belongs to every right hull R_t
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-hit-koebe@L1463-L1463
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-hit-koebe@L1463-L1463
CONTRACT_ID: paper.step:zero-in-right-hull
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: t >= 0
SOURCE_CONCLUSION: 0 in R_t, hence dist(f_t(zz), R_t) <= |f_t(zz)|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-hulls.right
ROUTES: -
ROUTE_FOR: -
EDGE: defn-hulls.right | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-hit-koebe@L1463-L1463 | R_t = C minus the range of f_t
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: used as 'the fact that 0 in R_t' (L1463, L1586) without statement or proof; the source does not argue why 0 is not in the range of f_t = g_t - U_t.

NODE: step:hulls-compact
KIND: step
TITLE: L_t and R_t are compact (premise of the Koebe theorems)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1702-L1705
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1702-L1705
CONTRACT_ID: paper.step:hulls-compact
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: t >= 0
SOURCE_CONCLUSION: L_t, R_t (and L_{t,s+t}, R_{t,s+t}, L_t u R_t, L_{t,s+t} u R_t) are compact subsets of C
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: claim:gt-conformal, defn-hulls.left, defn-hulls.right, step:hull-closed
ROUTES: -
ROUTE_FOR: -
EDGE: claim:gt-conformal | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1702-L1705 | f_t : C\L_t -> C\R_t conformal
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1702-L1702 | L_t
EDGE: defn-hulls.right | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1702-L1702 | R_t
EDGE: step:hull-closed | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1702-L1705 | L_t closed (domain of f_t open); R_t closed because f_t is an open map on an open domain
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: Koebe (L1702) is stated for compact K1, K2 but the source never states or proves compactness of L_t, R_t (or of their unions) before applying it at L1463, L1583, L1708-L1780.

NODE: eqn-hit-koebe
KIND: display
TITLE: Koebe estimate (3.5): |f_t'(zz)| asymp dist(f_t(zz),R_t)/dist(zz,L_t) <= |f_t(zz)|/dist(zz,L_t)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-hit-koebe@L1464-L1467
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1463-L1463
CONTRACT_ID: paper.eqn-hit-koebe
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: t < T_zz; Section-3 package (L1255-1257): zz is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); the display is deterministic given t < T_zz
SOURCE_QUANTIFIERS: t < T_zz
SOURCE_CONCLUSION: |f_t'(zz)| asymp dist(f_t(zz),R_t)/dist(zz,L_t) <= |f_t(zz)|/dist(zz,L_t) with universal constants
CONSTANT_SCOPE: implicit constants in the asymp / lesssim relations are universal: independent of Sigma, p, t^, s^, zz and omega; the relation holds for every t < T_zz
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: ext:koebe-quarter, step:hulls-compact, claim:gt-conformal, defn-hulls.right, step:zero-in-right-hull
ROUTES: -
ROUTE_FOR: -
EDGE: ext:koebe-quarter | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-hit-koebe@L1463-L1463 | Koebe quarter theorem for the conformal map f_t : C\L_t -> C\R_t
EDGE: step:hulls-compact | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-hit-koebe@L1463-L1463 | compactness premise of Koebe
EDGE: claim:gt-conformal | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-hit-koebe@L1463-L1463 | f_t is a conformal bijection C\L_t -> C\R_t
EDGE: defn-hulls.right | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-hit-koebe@L1465-L1465 | R_t
EDGE: step:zero-in-right-hull | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-hit-koebe@L1463-L1465 | dist(f_t(zz),R_t) <= ∣f_t(zz)∣ because 0 in R_t
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Display (3.5) (eqn-hit-koebe), stated for zz but a deterministic inequality for every z with t < T_z (reused for fixed z in Lemma 3.12). Constants universal.

NODE: step:prop-ii-a-capacity-time
KIND: step
TITLE: lim_{t->T_zz^-} |f_t'(zz)|/|f_t(zz)| = infinity
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1459-L1462
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1459-L1462
CONTRACT_ID: paper.step:prop-ii-a-capacity-time
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (II) < 0; Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: a.s. lim_{t->T_zz^-} |f_t'(zz)|/|f_t(zz)| = infinity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-integral-ii, remark-sigma, defn-sigma
ROUTES: -
ROUTE_FOR: -
EDGE: lem-integral-ii | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1459-L1459 | sigma-time limit +infinity when (II) < 0
EDGE: remark-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1460-L1462 | sigma(infinity) = T_zz, so t^ -> infinity iff t -> T_zz^-
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1460-L1460 | hats denote sigma-time
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Carrier change sigma-time to capacity time ('i.e.').

NODE: step:prop-ii-a-koebe-limit
KIND: step
TITLE: dist(zz,L_t) -> 0 as t -> T_zz
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1463-L1468
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1468-L1468
CONTRACT_ID: paper.step:prop-ii-a-koebe-limit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (II) < 0; Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: a.s. dist(zz,L_t) -> 0 as t -> T_zz^- (R14 epsilon form)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:prop-ii-a-capacity-time, eqn-hit-koebe, claim:hulls-monotone
ROUTES: -
ROUTE_FOR: -
EDGE: step:prop-ii-a-capacity-time | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1468-L1468 | ∣f_t'∣/∣f_t∣ -> infinity
EDGE: eqn-hit-koebe | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1463-L1468 | dist(zz,L_t) <= C ∣f_t(zz)∣/∣f_t'(zz)∣
EDGE: claim:hulls-monotone | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1468-L1468 | t -> dist(zz,L_t) non-increasing so limit exists and equals infimum (R14)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Combination of the divergence of |f_t'|/|f_t| with (3.5). R14 ensures lim means infimum.

NODE: lem-converse-w-o-upgrade
KIND: lemma
TITLE: Lemma 3.8: (II) > 0 implies P(lim dist(zz,L_t) = 0) < 1
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1475-L1478
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1638-L1781
CONTRACT_ID: paper.lem-converse-w-o-upgrade
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (II) > 0; Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: P(lim_{t->T_zz^-} dist(zz,L_t) = 0) < 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: item-II, step:converse-conclude
ROUTES: -
ROUTE_FOR: -
EDGE: item-II | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1476-L1476 | sign hypothesis on (II)
EDGE: step:converse-conclude | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1639-L1642 | contrapositive: lim = 0 a.s. forces (II) <= 0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The proof is by contrapositive (eqn-converse-show0). Setup (Step 1, L1660-1674) defines t = sigma(t^), s = sigma(s^+t^) - sigma(t^) and claims the existence of E_s^ with (3.x) = eqn-dist-3; Steps 2-4 are the nodes listed in DEPS of step:converse-conclude and eqn-dist-3. Outline displays (eqn-dist-3-outline, eqn-stationary-outline) are excluded as restatements.

NODE: step:future-point-outside-hulls
KIND: step
TITLE: zz not in L_{s+t}; f_t(zz) not in R_t u L_{t,s+t}
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1707-L1707
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1707-L1707
CONTRACT_ID: paper.step:future-point-outside-hulls
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time; t = sigma(t^), s = sigma(s^+t^) - sigma(t^)
SOURCE_QUANTIFIERS: t^, s^ > 0
SOURCE_CONCLUSION: s + t = sigma(s^+t^) < T_zz, so zz not in L_{s+t} and f_t(zz) is not in R_t u L_{t,s+t}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-sigma, remark-sigma, defn-hulls.left, eqn-conc, defn-hulls.right
ROUTES: -
ROUTE_FOR: -
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1707-L1707 | s + t = sigma(s^ + t^)
EDGE: remark-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1707-L1707 | sigma(s^+t^) < T_zz (sigma maps (0,infinity) onto (0,T_zz))
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1707-L1707 | L_{s+t} = {T <= s+t}
EDGE: eqn-conc | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1707-L1707 | f_t(L_{s+t} \ L_t) = L_{t,s+t} and f_t maps C\L_t into C\R_t
EDGE: defn-hulls.right | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1707-L1707 | R_t
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Short membership argument asserted with 'so ... and hence'.

NODE: eqn-two-formulas
KIND: display
TITLE: Koebe for f_{t,s+t} on C\L_{t,s+t} (3.7)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-two-formulas@L1708-L1714
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1708-L1714
CONTRACT_ID: paper.eqn-two-formulas
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time; t, s as in Step 1
SOURCE_QUANTIFIERS: t^, s^
SOURCE_CONCLUSION: |f_{t,s+t}'(f_t(zz))| asymp dist(f_{s+t}(zz), R_{t,s+t})/dist(f_t(zz), L_{t,s+t}) with universal constants
CONSTANT_SCOPE: implicit constants in the asymp / lesssim relations are universal: independent of Sigma, p, t^, s^, zz and omega
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: ext:koebe-quarter, step:hulls-compact, claim:gt-conformal, eqn-conc, step:future-point-outside-hulls
ROUTES: -
ROUTE_FOR: -
EDGE: ext:koebe-quarter | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-two-formulas@L1708-L1712 | Koebe quarter theorem for f_{t,s+t} : C\L_{t,s+t} -> C\R_{t,s+t}
EDGE: step:hulls-compact | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-two-formulas@L1708-L1708 | compactness premise
EDGE: claim:gt-conformal | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-two-formulas@L1708-L1708 | conformality of the future map f_{t,s+t}
EDGE: eqn-conc | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-two-formulas@L1708-L1712 | f_{t,s+t}(f_t(zz)) = f_{s+t}(zz)
EDGE: step:future-point-outside-hulls | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-two-formulas@L1708-L1712 | f_t(zz) not in L_{t,s+t}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Display (3.7).

NODE: eqn-two-formulas-b
KIND: display
TITLE: Koebe for f_{t,s+t} on C\(L_{t,s+t} u R_t) (3.8)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-two-formulas'@L1716-L1721
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1708-L1721
CONTRACT_ID: paper.eqn-two-formulas-b
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time; t, s as in Step 1
SOURCE_QUANTIFIERS: t^, s^
SOURCE_CONCLUSION: |f_{t,s+t}'(f_t(zz))| asymp dist(f_{s+t}(zz), R_{s+t})/dist(f_t(zz), L_{t,s+t} u R_t) with universal constants
CONSTANT_SCOPE: implicit constants in the asymp / lesssim relations are universal: independent of Sigma, p, t^, s^, zz and omega
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: ext:koebe-quarter, step:hulls-compact, claim:gt-conformal, eqn-conc, step:future-point-outside-hulls
ROUTES: -
ROUTE_FOR: -
EDGE: ext:koebe-quarter | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-two-formulas'@L1716-L1719 | Koebe quarter theorem on the smaller domain C\(L_{t,s+t} u R_t)
EDGE: step:hulls-compact | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-two-formulas'@L1716-L1716 | compactness of L_{t,s+t} u R_t
EDGE: claim:gt-conformal | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-two-formulas'@L1716-L1716 | conformality
EDGE: eqn-conc | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-two-formulas'@L1716-L1719 | f_{s+t}(zz) = f_{t,s+t}(f_t(zz)) and R_{s+t} = R_{t,s+t} u f_{t,s+t}(R_t \ L_{t,s+t}) (image of the complement of the union)
EDGE: step:future-point-outside-hulls | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-two-formulas'@L1716-L1716 | f_t(zz) not in L_{t,s+t} u R_t
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Display (3.8) (inventory eqn-two-formulas'); ID uses suffix -b. Identification of the complement of the image of C\(L_{t,s+t} u R_t) with R_{s+t} is implicit in the source (uses eqn-conc).

NODE: eqn-two-dist-ratio
KIND: display
TITLE: Comparison (3.9) of the two Koebe formulas
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-two-dist-ratio@L1722-L1725
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1722-L1722
CONTRACT_ID: paper.eqn-two-dist-ratio
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: t^, s^
SOURCE_CONCLUSION: dist(f_{s+t}(zz),R_{t,s+t})/dist(f_t(zz),L_{t,s+t}) asymp dist(f_{s+t}(zz),R_{s+t})/dist(f_t(zz),L_{t,s+t} u R_t)
CONSTANT_SCOPE: implicit constants in the asymp / lesssim relations are universal: independent of Sigma, p, t^, s^, zz and omega
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-two-formulas, eqn-two-formulas-b
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-two-formulas | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-two-dist-ratio@L1722-L1722 | first expression for ∣f_{t,s+t}'(f_t(zz))∣
EDGE: eqn-two-formulas-b | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-two-dist-ratio@L1722-L1722 | second expression for the same derivative
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Display (3.9); equate two expressions of the same derivative.

NODE: eqn-koebe-t
KIND: display
TITLE: Koebe for f_t on C\L_{s+t} (3.10)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-koebe-t@L1727-L1733
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1727-L1728
CONTRACT_ID: paper.eqn-koebe-t
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: t^, s^
SOURCE_CONCLUSION: |f_t'(zz)| dist(zz,L_{s+t}) asymp dist(f_t(zz), L_{t,s+t} u R_t) asymp [dist(f_t(zz),L_{t,s+t})/dist(f_{s+t}(zz),R_{t,s+t})] dist(f_{s+t}(zz),R_{s+t})
CONSTANT_SCOPE: implicit constants in the asymp / lesssim relations are universal: independent of Sigma, p, t^, s^, zz and omega
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: ext:koebe-quarter, step:hulls-compact, claim:gt-conformal, eqn-conc, eqn-two-dist-ratio, step:future-point-outside-hulls
ROUTES: -
ROUTE_FOR: -
EDGE: ext:koebe-quarter | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-koebe-t@L1727-L1728 | Koebe quarter theorem for f_t : C\L_{s+t} -> C\(L_{t,s+t} u R_t)
EDGE: step:hulls-compact | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-koebe-t@L1727-L1727 | compactness
EDGE: eqn-conc | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-koebe-t@L1727-L1727 | f_t maps C\L_{s+t} onto C\(L_{t,s+t} u R_t)
EDGE: eqn-two-dist-ratio | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-koebe-t@L1728-L1728 | second asymp via (3.9)
EDGE: step:future-point-outside-hulls | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-koebe-t@L1727-L1727 | zz not in L_{s+t}
EDGE: claim:gt-conformal | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-koebe-t@L1727-L1728 | f_t is conformal (injective holomorphic) on C\L_t, hence on C\L_{s+t}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Display (3.10).

NODE: eqn-dist-1
KIND: display
TITLE: Rearrangement (3.11)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-1@L1734-L1738
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1734-L1734
CONTRACT_ID: paper.eqn-dist-1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: t^, s^
SOURCE_CONCLUSION: dist(f_t(zz),L_{t,s+t})/(|f_t(zz)| dist(zz,L_{s+t})) asymp (|f_t'(zz)|/|f_t(zz)|) dist(f_{s+t}(zz),R_{t,s+t})/dist(f_{s+t}(zz),R_{s+t})
CONSTANT_SCOPE: implicit constants in the asymp / lesssim relations are universal: independent of Sigma, p, t^, s^, zz and omega
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-koebe-t
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-koebe-t | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-1@L1734-L1734 | re-arranging (3.10)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Display (3.11). Routine algebra of asymp relations.

NODE: eqn-dist-event
KIND: display
TITLE: Definition of the event E_s^ (3.12)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-event@L1744-L1747
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-event@L1744-L1747
CONTRACT_ID: paper.eqn-dist-event
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: t^, s^
SOURCE_CONCLUSION: E_s^ := {dist(f_t(zz), L_{t,s+t}) <= dist(f_t(zz), R_t)}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Definition (3.12). The event depends on t^ and s^ through t = sigma(t^), s = sigma(s^+t^) - sigma(t^).

NODE: step:converse-event-converges
KIND: step
TITLE: 1_{E_s^} -> 1 as s^ -> infinity (under the contrapositive hypothesis)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-event@L1748-L1748
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-event@L1748-L1748
CONTRACT_ID: paper.step:converse-event-converges
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: lim_{u->T_zz^-} dist(zz,L_u) = 0 a.s.; t = sigma(t^) fixed; Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: t^
SOURCE_CONCLUSION: a.s. 1_{E_s^} -> 1 as s^ -> infinity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-dist-event, remark-sigma, eqn-conc, claim:hulls-monotone
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-dist-event | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-event@L1748-L1748 | the event
EDGE: remark-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-event@L1748-L1748 | s + t -> T_zz as s^ -> infinity
EDGE: eqn-conc | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-event@L1748-L1748 | relates L_{s+t} and L_{t,s+t} (f_t(L_{s+t}\L_t) = L_{t,s+t})
EDGE: claim:hulls-monotone | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-event@L1748-L1748 | L_{s+t} increasing in s
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: asserted ('the assumption implies 1_E -> 1'). Needs (i) dist(f_t(zz),L_{t,s+t}) -> 0 from dist(zz,L_{s+t}) -> 0 (transfer through the conformal map f_t at the interior point zz, with dist(zz,L_t) > 0 fixed) and (ii) dist(f_t(zz),R_t) > 0 fixed; neither is argued.

NODE: eqn-dist-cases
KIND: display
TITLE: Case formula (3.13)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-cases@L1750-L1754
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1750-L1750
CONTRACT_ID: paper.eqn-dist-cases
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: t^, s^
SOURCE_CONCLUSION: dist(f_t(zz), L_{t,s+t} u R_t) = dist(f_t(zz),L_{t,s+t}) 1_E + dist(f_t(zz),R_t) 1_{E^c}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-dist-event
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-dist-event | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-cases@L1750-L1750 | definition of E_s^ as the case where the L_{t,s+t}-distance is the smaller
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Display (3.13); minimum of two distances.

NODE: eqn-koebe-union
KIND: display
TITLE: Koebe on E_s^ (3.14)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-koebe-union@L1756-L1761
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1756-L1756
CONTRACT_ID: paper.eqn-koebe-union
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time; on E_s^
SOURCE_QUANTIFIERS: t^, s^
SOURCE_CONCLUSION: on E_s^: |f_t'(zz)| asymp dist(f_t(zz),L_{t,s+t} u R_t)/dist(zz,L_{s+t}) = dist(f_t(zz),L_{t,s+t})/dist(zz,L_{s+t})
CONSTANT_SCOPE: implicit constants in the asymp / lesssim relations are universal: independent of Sigma, p, t^, s^, zz and omega
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: ext:koebe-quarter, eqn-koebe-t, eqn-dist-cases
ROUTES: -
ROUTE_FOR: -
EDGE: ext:koebe-quarter | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-koebe-union@L1756-L1756 | Koebe applied to f_t as in (3.10)
EDGE: eqn-koebe-t | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-koebe-union@L1756-L1756 | first asymp (3.10)
EDGE: eqn-dist-cases | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-koebe-union@L1756-L1760 | on E the union-distance equals the L_{t,s+t}-distance
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Display (3.14).

NODE: eqn-dist-es
KIND: display
TITLE: Bound on E_s^ (3.15)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-es@L1762-L1766
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1762-L1762
CONTRACT_ID: paper.eqn-dist-es
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time; on E_s^
SOURCE_QUANTIFIERS: t^, s^
SOURCE_CONCLUSION: on E_s^: dist(f_t(zz),L_{t,s+t})/(|f_t(zz)| dist(zz,L_{s+t})) asymp |f_t'(zz)|/|f_t(zz)|
CONSTANT_SCOPE: implicit constants in the asymp / lesssim relations are universal: independent of Sigma, p, t^, s^, zz and omega
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-koebe-union
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-koebe-union | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-es@L1762-L1762 | divide (3.14) by ∣f_t(zz)∣
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Display (3.15).

NODE: eqn-dist-2
KIND: display
TITLE: Bound on E_s^c, first part (3.16)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-2@L1768-L1772
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1768-L1768
CONTRACT_ID: paper.eqn-dist-2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time; on E_s^c
SOURCE_QUANTIFIERS: t^, s^
SOURCE_CONCLUSION: on E_s^c: dist(f_{s+t}(zz),R_{t,s+t})/dist(f_{s+t}(zz),R_{s+t}) asymp dist(f_t(zz),L_{t,s+t})/dist(f_t(zz),L_{t,s+t} u R_t) <= |f_t(zz)|/dist(f_t(zz),R_t)
CONSTANT_SCOPE: implicit constants in the asymp / lesssim relations are universal: independent of Sigma, p, t^, s^, zz and omega
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-two-dist-ratio, step:zero-in-future-left-hull, eqn-dist-cases
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-two-dist-ratio | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-2@L1768-L1768 | the asymp via (3.9)
EDGE: eqn-dist-cases | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-2@L1768-L1768 | on E^c the union distance equals dist(f_t(zz),R_t)
EDGE: step:zero-in-future-left-hull | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-2@L1768-L1768 | 0 in L_{t,s+t}, so dist(f_t(zz),L_{t,s+t}) <= ∣f_t(zz)∣
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Display (3.16).

NODE: eqn-dist-esc
KIND: display
TITLE: Bound on E_s^c (3.17)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-esc@L1773-L1777
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1773-L1778
CONTRACT_ID: paper.eqn-dist-esc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time; on E_s^c
SOURCE_QUANTIFIERS: t^, s^
SOURCE_CONCLUSION: on E_s^c: dist(f_t(zz),L_{t,s+t})/(|f_t(zz)| dist(zz,L_{s+t})) <~ |f_t'(zz)|/dist(f_t(zz),R_t) asymp 1/dist(zz,L_t)
CONSTANT_SCOPE: implicit constants in the asymp / lesssim relations are universal: independent of Sigma, p, t^, s^, zz and omega
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-dist-1, eqn-dist-2, ext:koebe-quarter, step:hulls-compact, claim:gt-conformal
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-dist-1 | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-esc@L1773-L1773 | left side of (3.11)
EDGE: eqn-dist-2 | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-esc@L1773-L1773 | upper bound for the ratio of R-distances on E^c
EDGE: ext:koebe-quarter | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-esc@L1778-L1778 | Koebe quarter for f_t : C\L_t -> C\R_t gives the last asymp
EDGE: step:hulls-compact | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-esc@L1778-L1778 | compactness
EDGE: claim:gt-conformal | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-esc@L1778-L1778 | f_t conformal C\L_t -> C\R_t
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Display (3.17).

NODE: eqn-dist-3
KIND: display
TITLE: Main distance inequality (3.6)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-3@L1669-L1674
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1780-L1780
CONTRACT_ID: paper.eqn-dist-3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: lim_{u->T_zz^-} dist(zz,L_u) = 0 a.s. (hypothesis of the contrapositive); Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time; t = sigma(t^), s = sigma(s^+t^) - sigma(t^)
SOURCE_QUANTIFIERS: t^, s^ > 0
SOURCE_CONCLUSION: log[dist(f_t(zz),L_{t,s+t})/|f_t(zz)|] - log dist(zz,L_{s+t}) <= log(|f_t'(zz)|/|f_t(zz)|) 1_{E_s^} + log(1/dist(zz,L_t)) 1_{E_s^c} + C, with a universal constant C
CONSTANT_SCOPE: C is universal: independent of Sigma, p, t^, s^, zz and omega (the implicit asymp constants of (3.15), (3.17) are absorbed into C)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-dist-event, eqn-dist-es, eqn-dist-esc
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-dist-event | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-3@L1669-L1672 | event E_s^ in the right-hand side
EDGE: eqn-dist-es | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-3@L1780-L1780 | bound on E_s^
EDGE: eqn-dist-esc | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-3@L1780-L1780 | bound on E_s^c
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Display (3.6). 'Combining (3.15) and (3.17) yields (3.6)': take logarithms on each event and absorb the universal constants into C. The relation 1_E -> 1 is a separate node (step:converse-event-converges). Statement as claim at L1669-1674 (Step 1), proved in Steps 3-4.

NODE: step:converse-rhs-limit
KIND: step
TITLE: Limit of E[right side of (3.6)] as s^ -> infinity
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1678-L1691
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1678-L1691
CONTRACT_ID: paper.step:converse-rhs-limit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: eqn-dist-3; 1_{E_s^} -> 1 a.s.; Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: t^ fixed; s^ -> infinity
SOURCE_CONCLUSION: lim_{s^->infinity} E[RHS of (3.6)] = E log(|f_t'(zz)|/|f_t(zz)|) + C, with E|log(|f_t'(zz)|/|f_t(zz)|)| < infinity
CONSTANT_SCOPE: C is the universal constant of (3.6); independent of t^, s^, Sigma, omega; the limit s^ -> infinity is taken with t^ fixed
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-dist-3, eqn-sde-ratio, step:converse-event-converges, ext:dct, lem-log-finite-exp
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-dist-3 | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1678-L1678 | the right side
EDGE: eqn-sde-ratio | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1679-L1681 | integrability E∣log(∣f_t'∣/∣f_t∣)∣ < infinity from the SDE
EDGE: step:converse-event-converges | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1683-L1683 | 1_E -> 1
EDGE: ext:dct | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1683-L1691 | dominated convergence for both terms
EDGE: lem-log-finite-exp | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1687-L1689 | log(1/dist(zz,L_t)) is integrable, dominating the E^c term
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Application of DCT; the source dominates the positive part of the second term (log(1/dist) >= 0 by 0 in L_t).

NODE: step:converse-lhs-nonneg
KIND: step
TITLE: E[left side of (3.6)] >= 0
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1693-L1698
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1693-L1698
CONTRACT_ID: paper.step:converse-lhs-nonneg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: eqn-dist-3 left side; Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: t^, s^ > 0
SOURCE_CONCLUSION: E[log(dist(f_t(zz),L_{t,s+t})/|f_t(zz)|) - log dist(zz,L_{s+t})] >= 0 for every s^ > 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-computation, claim:hulls-monotone, lem-log-finite-exp
ROUTES: -
ROUTE_FOR: -
EDGE: lem-computation | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1693-L1695 | dist(f_t(zz),L_{t,s+t})/∣f_t(zz)∣ has the law of dist(zz,L_s)
EDGE: claim:hulls-monotone | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1697-L1697 | dist(zz,L_{s+t}) <= dist(zz,L_s) (L_s subset L_{s+t})
EDGE: lem-log-finite-exp | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1697-L1697 | log(1/dist(zz,L_{s+t})) has finite expectation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Uses equality in law (the projection of Lemma 3.9 to the first coordinate of the second component) and the monotone coupling dist(zz,L_{s+t}) <= dist(zz,L_s) between different random variables on the same space.

NODE: step:converse-conclude
KIND: step
TITLE: Contrapositive: lim dist = 0 a.s. implies (II) <= 0
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-converse-show0@L1639-L1642
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1697-L1698
CONTRACT_ID: paper.step:converse-conclude
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: lim dist(zz,L_u) = 0 a.s.; Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: t^ > 0
SOURCE_CONCLUSION: E log(|f_t'(zz)|/|f_t(zz)|) + C >= 0, i.e. C - t^ (II) >= 0 for all t^, hence (II) <= 0
CONSTANT_SCOPE: C is the universal constant of (3.6), independent of t^ (this is what allows t^ -> infinity); t^ is arbitrary
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:converse-rhs-limit, step:converse-lhs-nonneg, lem-integral-ii
ROUTES: -
ROUTE_FOR: -
EDGE: step:converse-rhs-limit | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1697-L1697 | limit of the right side, combined with the left side at L1697
EDGE: step:converse-lhs-nonneg | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1697-L1698 | left side has nonnegative expectation
EDGE: lem-integral-ii | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1697-L1698 | E log(∣f_t'∣/∣f_t∣) = -t^ (II)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Display (eqn-converse-show0). C is universal (independent of t^), so t^ -> infinity gives (II) <= 0.

NODE: eqn-computation-tilde-f
KIND: display
TITLE: Rescaled future chain f~_u (3.3)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-computation-tilde-f@L1517-L1520
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-computation-tilde-f@L1517-L1520
CONTRACT_ID: paper.eqn-computation-tilde-f
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: t^ >= 0; u >= 0
SOURCE_CONCLUSION: f~_u(w) := |f_{sigma(t^)}(zz)|^{-1} f_{sigma(t^), |f_{sigma(t^)}(zz)|^2 u + sigma(t^)}(|f_{sigma(t^)}(zz)| w)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Definition (3.3) of the rescaled shifted chain; the shift and scale are F_{sigma(t^)}-measurable.

NODE: step:computation-scaling-markov
KIND: application
TITLE: f~ has the law of f and is independent of the evolution up to sigma(t^)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-computation@L1521-L1524
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-computation@L1521-L1524
CONTRACT_ID: paper.step:computation-scaling-markov
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: t^ >= 0
SOURCE_CONCLUSION: (f~_u)_{u>=0} =_D (f_u)_{u>=0}, independent of the Loewner evolution up to sigma(t^); its left hull is L~_u = |f_{sigma(t^)}(zz)|^{-1} L_{sigma(t^), |f_{sigma(t^)}(zz)|^2 u + sigma(t^)}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-scaling, lem-markov, eqn-computation-tilde-f, eqn-scale, defn-sigma
ROUTES: -
ROUTE_FOR: -
EDGE: lem-scaling | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-computation@L1521-L1521 | scaling by the F_{sigma(t^)}-measurable factor ∣f_{sigma(t^)}(zz)∣
EDGE: lem-markov | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-computation@L1521-L1521 | strong Markov property at the stopping time sigma(t^)
EDGE: eqn-computation-tilde-f | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-computation@L1521-L1523 | definition of f~
EDGE: eqn-scale | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-computation@L1523-L1524 | left hull of the rescaled chain is the rescaled left hull
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-computation@L1521-L1521 | sigma(t^) is the stopping time
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Application with random scale; the stopping-time property of sigma(t^) with respect to the driver filtration and the independence of zz are implicit.

NODE: eqn-wt-L-dist
KIND: display
TITLE: Joint law identity (3.4)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-wt-L-dist@L1526-L1533
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-computation@L1526-L1533
CONTRACT_ID: paper.eqn-wt-L-dist
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: t^, s^ >= 0
SOURCE_CONCLUSION: (f_{sigma(t^)}(zz)/|f_{sigma(t^)}(zz)|, L~_{sigma~(s^)})_{s^>=0} =_D (zz, L_{sigma(s^)})_{s^>=0}, with sigma~ the sigma-time of f~ at f_{sigma(t^)}(zz)/|f_{sigma(t^)}(zz)|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:computation-scaling-markov, lem-stationary
ROUTES: -
ROUTE_FOR: -
EDGE: step:computation-scaling-markov | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-computation@L1526-L1526 | f~ =_D f and independent of the past
EDGE: lem-stationary | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-computation@L1526-L1526 | stationarity: f_{sigma(t^)}(zz)/∣f_{sigma(t^)}(zz)∣ =_D zz
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Display (3.4) (eqn-wt-L-dist). The independence of f_{sigma(t^)}(zz)/|.| from f~ uses the Markov property (F_{sigma(t^)}-measurability), and the first component is a function of the pre-sigma(t^) past.

NODE: step:computation-time-change-identity
KIND: step
TITLE: sigma~(s^) = |f_{sigma(t^)}(zz)|^{-2}(sigma(s^+t^) - sigma(t^))
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-computation@L1534-L1542
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-computation@L1534-L1542
CONTRACT_ID: paper.step:computation-time-change-identity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: t^, s^ >= 0
SOURCE_CONCLUSION: |f_{sigma(t^)}(zz)|^2 sigma~(s^) + sigma(t^) = sigma(s^+t^); hence L~_{sigma~(s^)} = |f_{sigma(t^)}(zz)|^{-1} L_{sigma(t^),sigma(s^+t^)}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-conc, defn-sigma, eqn-computation-tilde-f
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-conc | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-computation@L1538-L1538 | 'concatenation property': f_{sigma(t^),sigma(t^)+v}(f_{sigma(t^)}(zz)) = f_{sigma(t^)+v}(zz)
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-computation@L1540-L1542 | definition of sigma(s^+t^) via int_0^{.} ∣f_v(zz)∣^{-2} dv
EDGE: eqn-computation-tilde-f | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-computation@L1537-L1537 | unfold f~
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The 'elementary but somewhat tedious scaling calculation' chain of equalities (substitution v = |f|^2 u + sigma(t^)). Carrier change: sigma~-time of f~ to sigma-time of f.

NODE: lem-computation
KIND: lemma
TITLE: Lemma 3.9: stationarity of the pair (point, future hull)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-computation@L1506-L1513
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-computation@L1515-L1543
CONTRACT_ID: paper.lem-computation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: t^, s^ >= 0 fixed
SOURCE_CONCLUSION: (f_{sigma(t^)}(zz)/|f_{sigma(t^)}(zz)|, L_{sigma(t^),sigma(s^+t^)}/|f_{sigma(t^)}(zz)|) =_D (zz, L_{sigma(s^)})
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-wt-L-dist, step:computation-time-change-identity
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-wt-L-dist | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-computation@L1531-L1533 | joint law identity in sigma~-time
EDGE: step:computation-time-change-identity | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-computation@L1542-L1542 | converts L~_{sigma~(s^)} to the future hull L_{sigma(t^),sigma(s^+t^)}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Section-3 package. The paper's normalization of L_{t,s+t} is as in (2.3) (eqn-conc).

NODE: lem-log-finite-exp
KIND: lemma
TITLE: Lemma 3.10: E log(1/dist(zz,L_{sigma(t^)})) < infinity
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1550-L1556
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1572-L1631
CONTRACT_ID: paper.lem-log-finite-exp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: t^ > 0
SOURCE_CONCLUSION: E log(1/dist(zz,L_{sigma(t^)})) < infinity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-sigma, step:log-finite-tail-to-expectation
ROUTES: -
ROUTE_FOR: -
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1553-L1553 | sigma-time parametrization
EDGE: step:log-finite-tail-to-expectation | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1577-L1577 | tail bound implies finiteness
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Note at L1558: |zz| = 1 and 0 in L_{sigma(t^)} so the integrand is >= 0 (step:zero-in-left-hull).

NODE: step:log-finite-distortion
KIND: step
TITLE: Distortion estimate: f_{tau_k}(B_{16^{-k-1}}(zz))/|f_{tau_k}(zz)| in B_{1/2}
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-finite-exp-1@L1580-L1590
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1580-L1590
CONTRACT_ID: paper.step:log-finite-distortion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time; tau_k = first time L_t hits the ball of radius 16^{-k} centred at zz
SOURCE_QUANTIFIERS: k in N
SOURCE_CONCLUSION: |f_{tau_k}(w) - f_{tau_k}(zz)| <= 8|w - zz| dist(f_{tau_k}(zz),R_{tau_k})/dist(zz,L_{tau_k}) for w in B_{16^{-k-1}}(zz); consequently f_{tau_k}(B_{16^{-k-1}}(zz))/|f_{tau_k}(zz)| subset B_{1/2}(f_{tau_k}(zz)/|f_{tau_k}(zz)|)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: ext:koebe-distortion, step:hulls-compact, claim:gt-conformal, step:zero-in-right-hull, defn-hulls.left
ROUTES: -
ROUTE_FOR: -
EDGE: ext:koebe-distortion | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-finite-exp-1@L1581-L1583 | standard distortion estimate for f_{tau_k}
EDGE: step:hulls-compact | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-finite-exp-1@L1581-L1581 | compactness premise
EDGE: claim:gt-conformal | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-finite-exp-1@L1581-L1581 | f_{tau_k} conformal C\L_{tau_k} -> C\R_{tau_k}
EDGE: step:zero-in-right-hull | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-finite-exp-2@L1586-L1586 | dist(f_{tau_k}(zz),R_{tau_k}) <= ∣f_{tau_k}(zz)∣
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-finite-exp-1@L1580-L1580 | tau_k defined through L_t
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Combines displays (eqn-finite-exp-1) and (eqn-finite-exp-2); dist(zz,L_{tau_k}) >= 16^{-k} by definition of tau_k. The construction of tau_k (a stopping time for the hull filtration) is included here.

NODE: step:log-finite-exit-times
KIND: step
TITLE: T_k <= tau_{k+1}
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1592-L1597
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1592-L1594
CONTRACT_ID: paper.step:log-finite-exit-times
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time; T_k = first t after tau_k with L_{tau_k,t}/|f_{tau_k}(zz)| not contained in B_{1/2}(0)
SOURCE_QUANTIFIERS: k in N
SOURCE_CONCLUSION: a.s. T_k <= tau_{k+1}; (T_k - tau_k)/|f_{tau_k}(zz)|^2 is the first exit time from B_{1/2}(0) of the left hulls of the chain f~_t(w) = f_{tau_k, |f_{tau_k}(zz)|^2 t + tau_k}(|f_{tau_k}(zz)| w)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:log-finite-distortion, eqn-conc
ROUTES: -
ROUTE_FOR: -
EDGE: step:log-finite-distortion | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1592-L1592 | ball inclusion (eqn-finite-exp-2)
EDGE: eqn-conc | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1592-L1597 | f_{tau_k}(L_t \ L_{tau_k}) = L_{tau_k,t}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Includes display (eqn-finite-exp-3), the rescaled chain at tau_k.

NODE: step:log-finite-iid
KIND: application
TITLE: The integral int_{tau_k}^{T_k} |f_v(zz)|^{-2} dv is independent of F_{tau_k} with k-free law
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-finite-exp-4@L1599-L1612
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1599-L1612
CONTRACT_ID: paper.step:log-finite-iid
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: k in N
SOURCE_CONCLUSION: int_{tau_k}^{T_k} |f_v(zz)|^{-2} dv is independent of F_{tau_k} and its law does not depend on k
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-scaling, lem-markov, step:computation-scaling-markov, step:log-finite-exit-times, eqn-conc, defn-sigma
ROUTES: -
ROUTE_FOR: -
EDGE: lem-scaling | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1599-L1599 | scale invariance with factor ∣f_{tau_k}(zz)∣
EDGE: lem-markov | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1599-L1599 | strong Markov property at tau_k
EDGE: step:computation-scaling-markov | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1599-L1599 | 'applied as in the beginning of the proof of Lemma 3.9'
EDGE: step:log-finite-exit-times | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1594-L1603 | T_k as a first exit time of the rescaled chain
EDGE: eqn-conc | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1608-L1608 | concatenation property in the simplification chain
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1601-L1609 | int ∣f_.∣^{-2} is the sigma-time clock
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP (partial): display (eqn-finite-exp-4) and the substitution chain v = |f_{tau_k}(zz)|^2 u + tau_k are carried out, but the claim 'independent from F_{tau_k} and its law does not depend on k' is not justified: the integral is evaluated along the F_{tau_k}-measurable starting point f_{tau_k}(zz)/|f_{tau_k}(zz)| of the rescaled chain f~ (which is independent of F_{tau_k} and =_D f), so the integral is a function of f~ and of a point on the unit circle; independence of F_{tau_k} and k-independence of the law require an extra argument (e.g. a bound uniform over starting points, or stationarity of e^{i theta^}). tau_k is a stopping time of the driver filtration (implicit).

NODE: step:log-finite-q-choice
KIND: step
TITLE: Choice of the constant q = q(Sigma)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1612-L1615
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1612-L1615
CONTRACT_ID: paper.step:log-finite-q-choice
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: law of int_{tau_k}^{T_k} |f_v(zz)|^{-2} dv independent of k
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: there is q = q(Sigma) > 0 with P(int_{tau_k}^{T_k} |f_v(zz)|^{-2} dv >= q) >= 1/2 for all k
CONSTANT_SCOPE: q = q(Sigma) > 0 depends only on Sigma (and p); independent of k and omega
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:log-finite-iid
ROUTES: -
ROUTE_FOR: -
EDGE: step:log-finite-iid | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1612-L1615 | k-independence of the law
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Witness choice. Positivity of the integral with probability > 1/2 (T_k > tau_k a.s.) is implicit.

NODE: step:log-finite-binomial
KIND: step
TITLE: Binomial tail bound on the number of successful scales
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1616-L1622
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1616-L1622
CONTRACT_ID: paper.step:log-finite-binomial
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: events A_k = {int_{tau_k}^{T_k} |f_v(zz)|^{-2} dv >= q}, P(A_k) >= 1/2
SOURCE_QUANTIFIERS: N in N; k in N
SOURCE_CONCLUSION: events A_k independent; P(#{j <= k : A_j} <= N) <= C_N 2^{-k} with C_N depending only on N; hence P(int_0^{tau_k} |f_v(zz)|^{-2} dv <= q N) <= C_N 2^{-k}
CONSTANT_SCOPE: C_N depends only on N (combinatorial); independent of k, Sigma and omega; N is fixed before k
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:log-finite-q-choice, step:log-finite-iid, step:log-finite-exit-times
ROUTES: -
ROUTE_FOR: -
EDGE: step:log-finite-q-choice | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1614-L1617 | P(A_k) >= 1/2
EDGE: step:log-finite-iid | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1616-L1616 | independence of A_k from F_{tau_k} gives independence of A_1,...,A_k
EDGE: step:log-finite-exit-times | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1621-L1622 | the intervals [tau_j,T_j] are disjoint (T_j <= tau_{j+1}) so int_0^{tau_k} >= sum_{j<=k} int_{tau_j}^{T_j}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Combinatorial estimate (binomial tail) and a comparison of integrals. Domination of a stochastic dominance by independent Bernoulli(1/2) variables is implicit.

NODE: eqn-log-finite-end
KIND: display
TITLE: (3.2'): P(tau_k <= sigma(qN)) <= C_N 2^{-k}
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-log-finite-end@L1625-L1628
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1625-L1625
CONTRACT_ID: paper.eqn-log-finite-end
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: N in N; k in N
SOURCE_CONCLUSION: P(tau_k <= sigma(q N)) <= C_N 2^{-k} for all k in N
CONSTANT_SCOPE: C_N depends only on N, as in the binomial bound; independent of k; N in N arbitrary
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:log-finite-binomial, defn-sigma
ROUTES: -
ROUTE_FOR: -
EDGE: step:log-finite-binomial | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1621-L1625 | P(int_0^{tau_k} <= qN) <= C_N 2^{-k}
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1625-L1625 | tau_k <= sigma(qN) iff int_0^{tau_k} ∣f_v∣^{-2} dv <= qN
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Display (eqn-log-finite-end) (labelled (3.x) in print).

NODE: eqn-log-finite-show
KIND: display
TITLE: Tail bound (3.18): P(dist(zz,L_{sigma(t^)}) <= 16^{-k}) <= C_{t^} 2^{-k+1}
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-log-finite-show@L1573-L1576
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1629-L1630
CONTRACT_ID: paper.eqn-log-finite-show
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: t^ > 0; k in N
SOURCE_CONCLUSION: there is C_{t^} = C(t^,Sigma) with P(dist(zz,L_{sigma(t^)}) <= 16^{-k}) <= C_{t^} 2^{-k+1} for all k in N
CONSTANT_SCOPE: C_t^ depends only on t^ and Sigma (and p), not on k or omega; chosen before k; N = N(t^,Sigma) with qN >= t^
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-log-finite-end, defn-sigma
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-log-finite-end | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1629-L1630 | choose N with qN >= t^; {dist <= 16^{-k}} subset {tau_k <= sigma(t^)} subset {tau_k <= sigma(qN)}
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1629-L1630 | sigma increasing
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Witness N = N(t^,Sigma) with qN >= t^. Display (eqn-log-finite-show).

NODE: step:log-finite-tail-to-expectation
KIND: step
TITLE: Tail bound implies E log(1/dist) < infinity
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1577-L1577
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1577-L1577
CONTRACT_ID: paper.step:log-finite-tail-to-expectation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: eqn-log-finite-show; log(1/dist(zz,L_{sigma(t^)})) >= 0
SOURCE_QUANTIFIERS: t^ > 0
SOURCE_CONCLUSION: E log(1/dist(zz,L_{sigma(t^)})) < infinity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-log-finite-show, step:zero-in-left-hull
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-log-finite-show | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1577-L1577 | geometric tail P(log(1/dist) >= k log 16) <= C 2^{-k+1}
EDGE: step:zero-in-left-hull | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1577-L1577 | log(1/dist(zz,L_{sigma(t^)})) >= 0 so the tail integral formula applies
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: 'immediately implies': summation of a geometric tail.

NODE: step:prop-ii-b-scale-reduction
KIND: step
TITLE: q(z) = q(z/|z|)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1787-L1791
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1791-L1791
CONTRACT_ID: paper.step:prop-ii-b-scale-reduction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: q(z) := P(lim_{t->T_z^-} dist(z,L_t) > 0), z in C\{0}
SOURCE_QUANTIFIERS: z
SOURCE_CONCLUSION: q(z) = q(z/|z|)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-scaling, eqn-scale
ROUTES: -
ROUTE_FOR: -
EDGE: lem-scaling | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1791-L1791 | scale invariance of the chain
EDGE: eqn-scale | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1791-L1791 | left hulls of the rescaled chain are rescaled; limit of distance scales by 1/∣z∣
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Positivity of the limit is invariant under scaling by 1/|z| (the limit gets multiplied by 1/|z|).

NODE: step:prop-ii-b-lambda-positive-measure
KIND: step
TITLE: Lambda = {|z|=1 : q(z) > 0} has positive Lebesgue measure
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1793-L1799
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1793-L1798
CONTRACT_ID: paper.step:prop-ii-b-lambda-positive-measure
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (II) > 0; Section-3 package (L1252-1255): zz (bold z) is a random point of the unit circle with arg zz ~ p(u)1_[0,2pi](u)du, independent of the driver U, p admissible (R7/R15); sigma = sigma_zz; hats denote sigma-time
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: E[q(zz)] > 0 and Lambda := {|z| = 1 : q(z) > 0} has positive one-dimensional Lebesgue measure
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-converse-w-o-upgrade, claim:hulls-monotone, lem-stationary.admissible
ROUTES: -
ROUTE_FOR: -
EDGE: lem-converse-w-o-upgrade | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1793-L1793 | P(lim dist(zz,L_t) = 0) < 1
EDGE: claim:hulls-monotone | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1793-L1793 | dist(zz,L_t) non-increasing so the limit exists in [0,infinity) and 'not = 0' means '> 0' (R14)
EDGE: lem-stationary.admissible | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1794-L1794 | the law of arg zz has a density p 1_[0,2pi] w.r.t. Lebesgue measure
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Fubini over the independent pair (zz, U): E q(zz) = int q(e^{iu}) p(u) du > 0 forces Lambda to have positive measure (using the density, absolute continuity).

NODE: step:prop-ii-b-hit-lambda-prime
KIND: step
TITLE: P(tau < infinity) > 0 for the first entry time tau into a closed positive-measure subset Lambda'
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1801-L1802
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1801-L1802
CONTRACT_ID: paper.step:prop-ii-b-hit-lambda-prime
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Lambda' closed subset of Lambda with positive Lebesgue measure; z with |z| = 1; theta^_t^(z) = arg f_{sigma_z(t^)}(z); tau = smallest t^ > 0 with e^{i theta^_t^(z)} in Lambda'
SOURCE_QUANTIFIERS: z
SOURCE_CONCLUSION: P(tau < infinity) > 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-polar, ext:girsanov, step:prop-ii-b-lambda-positive-measure
ROUTES: -
ROUTE_FOR: -
EDGE: lem-polar | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1802-L1802 | SDE (eqn-theta-t) for theta^_t^(z)
EDGE: ext:girsanov | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1802-L1802 | 'Girsanov's theorem'
EDGE: step:prop-ii-b-lambda-positive-measure | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1801-L1801 | positive measure of Lambda gives a positive-measure closed Lambda'
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: 'From the SDE and Girsanov's theorem, we infer P(tau < infinity) > 0' is asserted; the comparison with a driftless diffusion/Brownian motion, absolute continuity of its hitting law w.r.t. Lebesgue measure and the transfer through Girsanov are not given.

NODE: step:prop-ii-b-markov-transfer
KIND: step
TITLE: Conditional probability at sigma_z(tau) equals q(e^{i theta^_tau(z)})
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1804-L1805
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1804-L1805
CONTRACT_ID: paper.step:prop-ii-b-markov-transfer
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: tau as above; on {tau < infinity}
SOURCE_QUANTIFIERS: z; |z| = 1
SOURCE_CONCLUSION: on {tau < infinity}, P(lim_{t->T_z^-} dist(z,L_t) > 0 | f up to sigma_z(tau)) = q(e^{i theta^_tau(z)})
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-scaling, lem-markov, eqn-conc, step:prop-ii-b-scale-reduction, step:all-z-apply-dist, defn-sigma
ROUTES: -
ROUTE_FOR: -
EDGE: lem-scaling | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1804-L1804 | scale invariance at the F-measurable scale ∣f_{sigma_z(tau)}(z)∣
EDGE: lem-markov | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1804-L1804 | domain Markov property at the stopping time sigma_z(tau)
EDGE: eqn-conc | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1804-L1805 | future chain f_{sigma_z(tau),sigma_z(tau)+.}
EDGE: step:prop-ii-b-scale-reduction | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1805-L1805 | q(w) = q(w/∣w∣) after rescaling to the unit circle
EDGE: step:all-z-apply-dist | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1804-L1805 | future dependence of the event {lim dist > 0} (same as hypothesis (ii) of Lemma 3.3)
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1802-L1802 | sigma_z
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Application of scaling + Markov at a stopping time; the event is determined by the future chain only through future dependence (SOURCE_GAP at step:all-z-apply-dist).

NODE: step:prop-ii-b-lambda-full
KIND: step
TITLE: Lambda is the whole unit circle
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1799-L1805
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1801-L1805
CONTRACT_ID: paper.step:prop-ii-b-lambda-full
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Lambda' closed, positive measure, subset of Lambda
SOURCE_QUANTIFIERS: z with |z| = 1
SOURCE_CONCLUSION: q(z) > 0 for every z with |z| = 1 (hence for every z in C\{0} by scale invariance)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:prop-ii-b-hit-lambda-prime, step:prop-ii-b-markov-transfer, step:prop-ii-b-scale-reduction
ROUTES: -
ROUTE_FOR: -
EDGE: step:prop-ii-b-hit-lambda-prime | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1802-L1803 | P(tau < infinity) > 0
EDGE: step:prop-ii-b-markov-transfer | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1804-L1805 | q(z) >= E[q(e^{i theta^_tau}) ; tau < infinity] > 0 since e^{i theta^_tau} in Lambda' subset Lambda
EDGE: step:prop-ii-b-scale-reduction | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1799-L1799 | q(z) > 0 on the unit circle gives q(z) > 0 on C\{0}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Conclusion: q(z) > 0 on the circle, hence on C\{0}.

NODE: step:prop-ii-b-koebe-ball
KIND: step
TITLE: Koebe distortion: lim dist(z,L_t) >= r implies the ball B_{r/16}(z) is absorbed at T_z
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1806-L1806
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1806-L1807
CONTRACT_ID: paper.step:prop-ii-b-koebe-ball
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: lim_{t->T_z^-} dist(z,L_t) >= r > 0
SOURCE_QUANTIFIERS: z; r > 0
SOURCE_CONCLUSION: for each w in B_{r/16}(z): lim_{t->T_z^-} dist(f_t(w),R_t) = 0 and lim_{t->T_w^-} dist(w,L_t) >= 15r/16 > 0 (L_t absorbs B_{r/16}(z) at time T_z)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: ext:koebe-distortion, step:hulls-compact, claim:gt-conformal, defn-hulls.right, step:zero-in-right-hull
ROUTES: -
ROUTE_FOR: -
EDGE: ext:koebe-distortion | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1806-L1806 | Koebe distortion theorem for f_t
EDGE: step:hulls-compact | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1806-L1806 | compactness premise
EDGE: claim:gt-conformal | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1806-L1806 | f_t conformal C\L_t -> C\R_t
EDGE: defn-hulls.right | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1806-L1806 | R_t
EDGE: step:zero-in-right-hull | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1806-L1806 | dist(f_t(z),R_t) <= ∣f_t(z)∣
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: the chain 'Koebe distortion, so lim dist(f_t(w),R_t)=0 for w in B_{r/16}(z); therefore (L_t) absorbs B_{r/16}(z) at time T_z' is asserted. In particular dist(f_t(z),R_t) -> 0 (the commented-out argument at L1807 is not part of the paper) and T_w = T_z for w in the ball are not derived. The case T_z = infinity is not discussed.

NODE: step:prop-ii-b-compactness
KIND: step
TITLE: Uniform lower bound q >= q_* > 0 on the unit circle and on C\{0}
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1808-L1809
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1808-L1809
CONTRACT_ID: paper.step:prop-ii-b-compactness
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: q(z) > 0 for all z (step:prop-ii-b-lambda-full)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: there exists q_* > 0 with q(z) >= q_* for all z in C\{0}
CONSTANT_SCOPE: epsilon = epsilon(z) depends on z; q_* > 0 depends only on Sigma (and p), uniform in z in C\{0} and independent of omega
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:prop-ii-b-lambda-full, step:prop-ii-b-koebe-ball, step:prop-ii-b-scale-reduction
ROUTES: -
ROUTE_FOR: -
EDGE: step:prop-ii-b-lambda-full | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1808-L1808 | q(z) > 0 for every z
EDGE: step:prop-ii-b-koebe-ball | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1808-L1808 | q(w) >= q(z)/2 for w in B_eps(z) (eps from r with P(lim dist >= r) >= q(z)/2)
EDGE: step:prop-ii-b-scale-reduction | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1809-L1809 | extend from the unit circle to C\{0}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Witness epsilon = epsilon(z) from continuity of probability in r, then finite subcover of the circle (compactness) and scaling. The step 'q(w) >= q(z)/2' is the 'Consequently' of L1808.

NODE: step:prop-ii-b-conditional-lower-bound
KIND: step
TITLE: P(lim dist > 0 | F_{sigma_z(t^)}) >= q_* for all t^
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1811-L1814
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1811-L1814
CONTRACT_ID: paper.step:prop-ii-b-conditional-lower-bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z in C\{0}
SOURCE_QUANTIFIERS: z; t^ >= 0
SOURCE_CONCLUSION: P(lim_{t->T_z^-} dist(z,L_t) > 0 | F_{sigma_z(t^)}) >= q_* for all t^ >= 0
CONSTANT_SCOPE: q_* is the deterministic constant of step:prop-ii-b-compactness, depending only on Sigma (and p), independent of z and t^
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-markov, lem-scaling, eqn-conc, step:all-z-apply-dist, step:prop-ii-b-compactness
ROUTES: -
ROUTE_FOR: -
EDGE: lem-markov | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1811-L1811 | strong Markov property at sigma_z(t^)
EDGE: lem-scaling | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1811-L1811 | rescaling to the unit circle
EDGE: eqn-conc | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1811-L1811 | future chain after sigma_z(t^)
EDGE: step:all-z-apply-dist | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1811-L1811 | future dependence of the event {lim dist > 0}
EDGE: step:prop-ii-b-compactness | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1811-L1814 | q >= q_* everywhere
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Application of the Markov property to the event; measurability of the event and of sigma_z(t^) as stopping times implicit.

NODE: step:prop-ii-b-martingale-zero-one
KIND: step
TITLE: Martingale convergence upgrades to a.s. lim dist(z,L_t) > 0
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1815-L1815
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1815-L1815
CONTRACT_ID: paper.step:prop-ii-b-martingale-zero-one
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z in C\{0}; P(A | F_{sigma_z(t^)}) >= q_* for all t^; A = {lim dist(z,L_t) > 0}
SOURCE_QUANTIFIERS: z
SOURCE_CONCLUSION: a.s. lim_{t->T_z^-} dist(z,L_t) > 0
CONSTANT_SCOPE: q_* is the deterministic constant of step:prop-ii-b-compactness, depending only on Sigma (and p), independent of z and t^
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: ext:martingale-convergence, step:prop-ii-b-conditional-lower-bound, remark-sigma
ROUTES: -
ROUTE_FOR: -
EDGE: ext:martingale-convergence | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1815-L1815 | P(A ∣ F_{sigma_z(t^)}) -> 1_A a.s.
EDGE: step:prop-ii-b-conditional-lower-bound | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1813-L1815 | the conditional probabilities are >= q_* so 1_A >= q_* a.s., hence 1_A = 1 a.s.
EDGE: remark-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1815-L1815 | sigma_z(t^) -> T_z so the filtration F_{sigma_z(t^)} exhausts the information determining A
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Levy upward theorem; A must be measurable w.r.t. the sigma-algebra generated by the F_{sigma_z(t^)} (implicit; uses sigma_z(t^) -> T_z).

NODE: step:c0-explicit-density
KIND: step
TITLE: Explicit stationary density p for c = 0 (3.19)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-c0-p@L1829-L1836
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-phases@L1829-L1836
CONTRACT_ID: paper.step:c0-explicit-density
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b > 0; c = 0; p = the density constructed in the proof of Lemma 2.13 (case 1, c = 0), equal to k p_0 by Remark 2.15
SOURCE_QUANTIFIERS: a,b > 0
SOURCE_CONCLUSION: this p is admissible (lem-p.exists, case 1) and p(u) = Z^{-1}(a+b+(b-a)cos 2u)^{4/(b-a)} for a != b, p(u) = Z^{-1} exp((4/a)cos^2 u) for a = b, with Z = Z(a,b) > 0 the normalizing constant for int_0^{2pi} p = 1
CONSTANT_SCOPE: Z = Z(a,b) > 0 depends only on a and b (c = 0)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-stationary.admissible, eqn-nu-D.mu, eqn-nu-D.D, lem-p, remark-p0
ROUTES: -
ROUTE_FOR: -
EDGE: lem-stationary.admissible | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-phases@L1829-L1829 | p is an admissible density solving the ODE (2.24)
EDGE: eqn-nu-D.mu | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-phases@L1829-L1829 | mu simplifies for c = 0 in the ODE
EDGE: eqn-nu-D.D | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-phases@L1829-L1829 | D simplifies for c = 0 in the ODE
EDGE: lem-p | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-phases@L1829-L1836 | p of Lemma 2.13, with r_* = 0 so p = p_0 when c = 0
EDGE: remark-p0 | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-phases@L1836-L1836 | for c = 0 the periodic solution is a constant times p_0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: the explicit integration of (mu - D')/D for c = 0 (the Mathematica check sits in a %-comment, L1140-L1146) and the check of normalization/regularity at a = b are not written. The identification is for the constructed p (Remark 2.15); the source never claims it for every admissible p and uniqueness of the normalized pi-periodic solution is not argued, but the c = 0 root does not need it: the later Lemmas 3.11/3.12 are applied to this p only. Consumers that cite 'p admissible' in this section (step:c0-bdy-finite-time, lem-c0-phases) are read with p := this density.

NODE: eqn-c0-integrals
KIND: display
TITLE: Integrals (I),(II) for c = 0 (3.20)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-c0-integrals@L1838-L1842
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-phases@L1838-L1838
CONTRACT_ID: paper.eqn-c0-integrals
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c = 0; p as in (3.19)
SOURCE_QUANTIFIERS: a,b > 0
SOURCE_CONCLUSION: nu(u) = (2 - a/2 + b/2) cos 2u; (I) = (2 - a/2 + b/2) int_0^{2pi} cos(2u) p(u) du; (II) = (4 - a/2 + b/2) int_0^{2pi} cos(2u) p(u) du
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-nu-D.nu, item-I, item-II
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-nu-D.nu | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-c0-integrals@L1838-L1838 | formula for nu when c = 0
EDGE: item-I | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-c0-integrals@L1840-L1840 | (I) = int nu p
EDGE: item-II | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-c0-integrals@L1841-L1841 | (II) = int (nu + 2cos 2u) p
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Display (3.20).

NODE: step:c0-positivity-reduction
KIND: step
TITLE: Reduction of positivity of int cos(2u)p(u) du to [0,pi/2]
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-c0-phase-show'@L1849-L1853
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-phases@L1849-L1853
CONTRACT_ID: paper.step:c0-positivity-reduction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: p as in (3.19), a,b > 0
SOURCE_QUANTIFIERS: a,b > 0
SOURCE_CONCLUSION: p pi-periodic and cos(2(pi-u))p(pi-u) = cos(2u)p(u), so (3.21) follows from int_0^{pi/2} cos(2u) p(u) du > 0 ((3.22))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:c0-explicit-density
ROUTES: -
ROUTE_FOR: -
EDGE: step:c0-explicit-density | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-phases@L1849-L1850 | explicit pi-periodic and even (in 2u -> cos 2u) form of p
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Symmetry reductions from the explicit formula (cos 2u even under u -> pi - u).

NODE: step:c0-positivity-reflection
KIND: step
TITLE: Reflection across pi/4: |cos(2(pi/2-u))p(pi/2-u)| < cos(2u)p(u) on [0,pi/4)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-cos-reflect@L1855-L1872
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-phases@L1855-L1874
CONTRACT_ID: paper.step:c0-positivity-reflection
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: p as in (3.19), a,b > 0
SOURCE_QUANTIFIERS: a,b > 0; u in [0,pi/4)
SOURCE_CONCLUSION: |cos(2(pi/2-u))p(pi/2-u)| < cos(2u)p(u) for u in [0,pi/4), hence int_0^{pi/2} cos(2u)p(u) du > 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:c0-explicit-density, step:c0-positivity-reduction
ROUTES: -
ROUTE_FOR: -
EDGE: step:c0-explicit-density | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-cos-reflect@L1856-L1861 | explicit reflected formula (3.23)
EDGE: step:c0-positivity-reduction | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-phases@L1855-L1855 | reduction to [0,pi/2]
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Includes display (eqn-cos-reflect) and the case split a < b, a > b, a = b (the source says 'by considering separately'; the inequalities are written only in a %-comment).

NODE: eqn-c0-phase-show
KIND: display
TITLE: Positivity (3.21): int_0^{2pi} cos(2u)p(u) du > 0
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-c0-phase-show@L1843-L1847
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-phases@L1849-L1874
CONTRACT_ID: paper.eqn-c0-phase-show
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c = 0; a,b > 0; p as in (3.19)
SOURCE_QUANTIFIERS: a,b > 0
SOURCE_CONCLUSION: int_0^{2pi} cos(2u) p(u) du > 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:c0-positivity-reduction, step:c0-positivity-reflection
ROUTES: -
ROUTE_FOR: -
EDGE: step:c0-positivity-reduction | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-phases@L1849-L1853 | reduction to [0,pi/2]
EDGE: step:c0-positivity-reflection | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-phases@L1855-L1874 | the [0,pi/2] integral is positive
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Display (eqn-c0-phase-show); used also in Lemma 3.12.

NODE: step:c0-sign-analysis
KIND: step
TITLE: Signs of (I),(II) for c = 0
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-phases@L1847-L1847
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-phases@L1847-L1847
CONTRACT_ID: paper.step:c0-sign-analysis
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c = 0; a,b > 0
SOURCE_QUANTIFIERS: a,b > 0
SOURCE_CONCLUSION: (I) >= 0 iff a - b <= 4 (with (I) = 0 iff a - b = 4) and (I) < 0 iff a - b > 4; (II) >= 0 iff a - b <= 8, (II) > 0 iff a - b < 8, (II) < 0 iff a - b > 8; so the sign pairs are ((I)>=0,(II)>0) for a-b<=4, ((I)<0,(II)>0) for 4<a-b<8, ((I)<0,(II)<0) for a-b>8
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-c0-integrals, eqn-c0-phase-show
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-c0-integrals | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-phases@L1847-L1847 | (I),(II) as multiples of int cos(2u)p(u)du
EDGE: eqn-c0-phase-show | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-phases@L1847-L1847 | the common integral is > 0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Case analysis on the sign of 2 - a/2 + b/2 and 4 - a/2 + b/2. The source states only 'I >= 0 iff a-b <= 4 and II >= 0 iff a-b <= 8'; the strict inequalities needed by Props 3.1/3.2 follow from the same formulas.

NODE: lem-c0-phases
KIND: lemma
TITLE: Lemma 3.11: phases for c = 0 away from the swallowing/hitting boundary
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-phases@L1824-L1827
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-phases@L1828-L1875
CONTRACT_ID: paper.lem-c0-phases
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b > 0 (R5; the source says 'a, b > 0' at L1845-1847); c = 0
SOURCE_QUANTIFIERS: a,b
SOURCE_CONCLUSION: SLE_Sigma is in the thin phase if a - b <= 4, the swallowing phase if 4 < a - b < 8, and the hitting phase if a - b > 8
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:c0-explicit-density, step:c0-sign-analysis, thm-phases#assembly-sign-cases
ROUTES: -
ROUTE_FOR: -
EDGE: step:c0-explicit-density | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-phases@L1829-L1836 | explicit p (and its admissibility) for c = 0
EDGE: step:c0-sign-analysis | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-phases@L1846-L1847 | signs of (I),(II) in terms of a - b
EDGE: thm-phases#assembly-sign-cases | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-phases@L1847-L1847 | 'our description of the phases in terms of (I),(II) (Propositions 3.1 and 3.2)' converts the signs to phases
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Source states 'Assume c = 0' only; R5 (a,b > 0) is used at L1845-1847 ('for any choice of a, b > 0'). The step 'description of the phases in terms of (I),(II)' is the Props-3.1/3.2 assembly (thm-phases#assembly-sign-cases), not the root thm-phases (which would be circular for a root consuming this lemma).

NODE: step:c0-bdy-drift-vanishes
KIND: step
TITLE: nu(.) + 2cos(2.) = 0 when c = 0 and a - b = 8
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1916-L1916
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1916-L1916
CONTRACT_ID: paper.step:c0-bdy-drift-vanishes
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c = 0; a - b = 8
SOURCE_QUANTIFIERS: u in R
SOURCE_CONCLUSION: nu(u) + 2 cos(2u) = 0 for all u
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-nu-D.nu
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-nu-D.nu | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1916-L1916 | nu(u) = (2 - a/2 + b/2) cos 2u = -2 cos 2u when a - b = 8
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Algebra on the definition of nu.

NODE: step:c0-bdy-martingale-bm
KIND: step
TITLE: log(|f^'|/|f^|)(z) is a time-changed BM with limsup +infinity
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1917-L1925
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1917-L1925
CONTRACT_ID: paper.step:c0-bdy-martingale-bm
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c = 0; a - b = 8; a,b > 0; z in C\{0}; sigma = sigma_z
SOURCE_QUANTIFIERS: z
SOURCE_CONCLUSION: log(|f^_t'(z)|/|f^_t(z)|) is a continuous martingale with quadratic variation int_0^t (a cos^2 theta^_s + b sin^2 theta^_s) ds -> infinity, hence a time-changed Brownian motion; a.s. limsup_{t^->infinity} log(|f^_t'(z)|/|f^_t(z)|) = +infinity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:c0-bdy-drift-vanishes, eqn-sde-ratio, lem-polar, ext:levy-characterization
ROUTES: -
ROUTE_FOR: -
EDGE: step:c0-bdy-drift-vanishes | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1916-L1917 | drift of the SDE vanishes
EDGE: eqn-sde-ratio | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1917-L1917 | SDE for the ratio (or Lemma 2.11 directly)
EDGE: lem-polar | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1917-L1917 | (W,W~) =_D (B,B~) independent standard BMs since c = 0
EDGE: ext:levy-characterization | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1922-L1923 | continuous martingale with QV -> infinity is a time-changed BM (Dambis-Dubins-Schwarz)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: QV -> infinity follows from a cos^2 + b sin^2 >= min(a,b) > 0 (needs a,b > 0, R5); the source states it without justification. The source's 'the SDE (3.4) (or just Lemma 2.11)' refers to eqn-sde-ratio for fixed z.

NODE: step:c0-bdy-capacity-time
KIND: step
TITLE: limsup_{t->T_z^-} |f_t'(z)|/|f_t(z)| = infinity
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1923-L1925
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1923-L1925
CONTRACT_ID: paper.step:c0-bdy-capacity-time
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c = 0; a - b = 8
SOURCE_QUANTIFIERS: z
SOURCE_CONCLUSION: a.s. limsup_{t->T_z^-} |f_t'(z)|/|f_t(z)| = infinity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:c0-bdy-martingale-bm, remark-sigma, defn-sigma
ROUTES: -
ROUTE_FOR: -
EDGE: step:c0-bdy-martingale-bm | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1923-L1923 | limsup in sigma-time
EDGE: remark-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1924-L1924 | sigma(infinity) = T_z so t^ -> infinity iff t -> T_z^-
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1915-L1915 | sigma_z
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Carrier change sigma-time to capacity time ('i.e.').

NODE: step:c0-bdy-hitting-from-limsup
KIND: step
TITLE: limsup |f_t'|/|f_t| = infinity implies dist(z,L_t) -> 0
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1926-L1926
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1926-L1926
CONTRACT_ID: paper.step:c0-bdy-hitting-from-limsup
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c = 0; a - b = 8; z in C\{0}
SOURCE_QUANTIFIERS: z
SOURCE_CONCLUSION: a.s. lim_{t->T_z^-} dist(z,L_t) = 0, i.e. z in the closure of union_{t<T_z} L_t (R14)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:c0-bdy-capacity-time, eqn-hit-koebe, claim:hulls-monotone
ROUTES: -
ROUTE_FOR: -
EDGE: step:c0-bdy-capacity-time | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1926-L1926 | limsup ∣f_t'∣/∣f_t∣ = infinity
EDGE: eqn-hit-koebe | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1926-L1926 | 'see in particular (3.5)': dist(z,L_t) <= C ∣f_t(z)∣/∣f_t'(z)∣
EDGE: claim:hulls-monotone | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1926-L1926 | t -> dist(z,L_t) is non-increasing so liminf = 0 gives lim = 0 (R14)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The source says 'The proof of Proposition 3.2(a) ... then implies'; here limsup (not lim) is used, so monotonicity of dist(z,L_t) is needed; (3.5) is applied to a fixed z (it was stated for zz).

NODE: step:c0-bdy-finite-time
KIND: step
TITLE: T_z < infinity when c = 0 and a - b = 8
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1926-L1926
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1926-L1926
CONTRACT_ID: paper.step:c0-bdy-finite-time
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c = 0; a - b = 8; a,b > 0; p admissible
SOURCE_QUANTIFIERS: z in C\{0}
SOURCE_CONCLUSION: a.s. T_z < infinity for each z != 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: prop-i.b, eqn-c0-integrals, eqn-c0-phase-show, step:c0-explicit-density
ROUTES: -
ROUTE_FOR: -
EDGE: prop-i.b | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1926-L1926 | (I) < 0 gives T_z < infinity
EDGE: eqn-c0-integrals | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1926-L1926 | (I) = (2 - a/2 + b/2) int cos(2u) p du = -2 int cos(2u)p du
EDGE: eqn-c0-phase-show | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1926-L1926 | int cos(2u) p du > 0 so (I) < 0
EDGE: step:c0-explicit-density | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1926-L1926 | p is the explicit admissible density used in (3.20)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: the hitting phase requires T_z < infinity, but the proof of Lemma 3.12 shows only dist(z,L_t) -> 0; finiteness of T_z (from (I) = -2 int cos(2u)p du < 0 and Prop 3.1(b)) is not stated.

NODE: lem-c0-bdy
KIND: lemma
TITLE: Lemma 3.12: c = 0, a - b = 8 is in the hitting phase
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1910-L1913
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1914-L1927
CONTRACT_ID: paper.lem-c0-bdy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b > 0 (R5); c = 0; a - b = 8
SOURCE_QUANTIFIERS: a,b
SOURCE_CONCLUSION: SLE_Sigma is in the hitting phase
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-phases.hitting, step:c0-bdy-hitting-from-limsup, step:c0-bdy-finite-time
ROUTES: -
ROUTE_FOR: -
EDGE: defn-phases.hitting | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1912-L1926 | conclusion: for each z != 0, a.s. T_z < infinity and z in closure of union_{t<T_z} L_t
EDGE: step:c0-bdy-hitting-from-limsup | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1926-L1926 | z in the closure of union_{t<T_z} L_t
EDGE: step:c0-bdy-finite-time | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1926-L1926 | T_z < infinity
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: R5/P8: the case (II) = 0 (a - b = 8) is hitting. The statement in the source reads 'hitting phase' without the finiteness of T_z in the proof; see step:c0-bdy-finite-time.

NODE: thm-phases#assembly-sign-cases
KIND: step
TITLE: Thm 1.8 proof: Props 3.1/3.2 give the four sign-case phases
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L437-L449
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L1930-L1932
CONTRACT_ID: paper.thm-phases#assembly-sign-cases
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b > 0; c^2 <= ab; p admissible (R5, R7/R15); probability space and SLE_Sigma driver (R9); z in C\{0} (R4)
SOURCE_QUANTIFIERS: z; sign pattern of ((I),(II))
SOURCE_CONCLUSION: ((I) >= 0, (II) > 0) => thin; ((I) < 0, (II) > 0) => swallowing; ((I) < 0, (II) < 0) => hitting; ((I) >= 0, (II) < 0) => dense
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: prop-i.a, prop-i.b, prop-ii.a, prop-ii.b, defn-phases.thin, defn-phases.swallowing, defn-phases.hitting, defn-phases.dense, claim:hulls-monotone, defn-hulls.left
ROUTES: -
ROUTE_FOR: -
EDGE: prop-i.a | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L1930-L1931 | (I) >= 0 gives T_z = infinity (thin, dense)
EDGE: prop-i.b | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L1930-L1931 | (I) < 0 gives T_z < infinity (swallowing, hitting)
EDGE: prop-ii.a | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L1930-L1931 | (II) < 0 gives dist(z,L_t) -> 0 (hitting, dense)
EDGE: prop-ii.b | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L1930-L1931 | (II) > 0 gives lim dist(z,L_t) > 0 (thin, swallowing)
EDGE: defn-phases.thin | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L1930-L1931 | target property of case 1
EDGE: defn-phases.swallowing | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L1930-L1931 | target property of case 2
EDGE: defn-phases.hitting | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L1930-L1931 | target property of case 3
EDGE: defn-phases.dense | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L1930-L1931 | target property of case 4
EDGE: claim:hulls-monotone | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L1930-L1931 | L_t increasing, so inf_{t<T_z} dist(z,L_t) is the limit (R14) and 'not in the closure' translates to a positive infimum
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L1930-L1931 | L_t = {T_z <= t}, so T_z = infinity gives z not in union_t L_t
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: 'Combine Propositions 3.1 and 3.2' is the entire proof. The translation from (T_z, lim dist(z,L_t)) to the closure statements of Def 1.7 is not written (e.g. thin: T_z = infinity and inf_t dist(z,L_t) > 0 gives z not in closure; dense: T_z = infinity gives z not in union_t L_t while dist -> 0 gives z in the closure; R14 epsilon form). Slice A's thm-phases currently depends directly on prop-i.a/b and prop-ii.a/b; recommend it depends on this node instead (or in addition).

NODE: thm-phases#assembly-c-zero
KIND: step
TITLE: Thm 1.8 proof: c = 0 phases from Lemmas 3.11 and 3.12
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L450-L450
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L1930-L1932
CONTRACT_ID: paper.thm-phases#assembly-c-zero
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b > 0 (R5); c = 0
SOURCE_QUANTIFIERS: a,b
SOURCE_CONCLUSION: thin if a - b <= 4; swallowing if 4 < a - b < 8; hitting if a - b >= 8
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-c0-phases, lem-c0-bdy
ROUTES: -
ROUTE_FOR: -
EDGE: lem-c0-phases | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L1931-L1932 | thin for a-b<=4, swallowing for 4<a-b<8, hitting for a-b>8
EDGE: lem-c0-bdy | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L1931-L1932 | hitting for a-b = 8
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Union of the cases of Lemma 3.11 and Lemma 3.12 (a-b>8 and a-b=8 give a-b>=8, P8). Trivial assembly; included because the source states it as part of the proof of Thm 1.8 (L1930-1932). Slice A's thm-phases.c-zero depends on lem-c0-phases, lem-c0-bdy directly; recommend it depends on this node (and no longer needs prop-i.a/b, prop-ii.a/b directly since Lemma 3.11 consumes the sign-case assembly).

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
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: reviewer-C/sonnet
REVIEWER: global-reviewer/sonnet
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The source writes 'the fact that 0 in L_{t,s+t}' at L1768 without argument (read as the shifted-driver version of L1558; not a SOURCE_GAP beyond what L1558 already assumes). Split out of step:zero-in-left-hull so each EDGE locator cites its own use site.


## Coverage

ITEM: inv:heading:L1250
KIND: heading
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#heading:L1250@L1250-L1250
DISPOSITION: EXCLUDED
REASON: structural heading (section title), no mathematical content
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-integral-nu
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1258-L1258
DISPOSITION: NODE eqn-integral-nu
REASON: display (3.1)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:prop-i
KIND: proposition
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1265-L1271
DISPOSITION: NODE prop-i.a, prop-i.b
REASON: Proposition 3.1, split into roots (a),(b) (R17)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:prop-ii
KIND: proposition
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1276-L1284
DISPOSITION: NODE prop-ii.a, prop-ii.b
REASON: Proposition 3.2, split into roots (a),(b) (R17)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:item-ii-a
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#item-ii-a@L1279-L1279
DISPOSITION: NODE prop-ii.a
REASON: label of item (a) of Prop 3.2
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:item-ii-b
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#item-ii-b@L1281-L1281
DISPOSITION: NODE prop-ii.b
REASON: label of item (b) of Prop 3.2
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:heading:L1290
KIND: heading
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#heading:L1290@L1290-L1290
DISPOSITION: EXCLUDED
REASON: structural heading
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:lem-all-z
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-all-z@L1294-L1301
DISPOSITION: NODE lem-all-z
REASON: Lemma 3.3
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:proof:L1305
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L1305@L1305-L1319
DISPOSITION: NODE lem-all-z, step:all-z-null-set-density, step:all-z-lambda-conull, step:all-z-markov-transfer, step:all-z-stopping-time-choice
REASON: proof of Lemma 3.3
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-nohit-set
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-nohit-set@L1307-L1307
DISPOSITION: NODE step:all-z-lambda-conull
REASON: display defining Lambda
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:lem-stationary-sde
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-sde@L1327-L1343
DISPOSITION: NODE lem-stationary-sde
REASON: Lemma 3.4
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:lem-recurrent
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrent@L1349-L1352
DISPOSITION: NODE lem-recurrent
REASON: Lemma 3.5
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:proof:L1355
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L1355@L1355-L1357
DISPOSITION: NODE lem-recurrent, step:recurrent-durrett-adaptation
REASON: proof of Lemma 3.5 (delegated to Durrett)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:cite:L1356:durrett
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L1356:durrett@L1356-L1356
DISPOSITION: NODE ext:durrett-7.3.2
REASON: citation Durrett Thm 7.3.2
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:proof:L1360
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L1360@L1360-L1379
DISPOSITION: NODE lem-stationary-sde, step:sde-stationary-increments, step:sde-continuity-noninteger, step:sde-birkhoff-limit, step:sde-regeneration, step:sde-limit-deterministic, step:sde-mean-zero, step:sde-recurrence-zero, ext:birkhoff, ext:kolmogorov-zero-one, ext:strong-markov-bm
REASON: proof of Lemma 3.4
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:cite:L1374:revuz-yor
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L1374:revuz-yor@L1374-L1374
DISPOSITION: EXCLUDED
REASON: citation occurs only inside a %-comment tail on line 1374 (not part of the paper); the mean-zero fact it supports is step:sde-mean-zero
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:heading:L1383
KIND: heading
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#heading:L1383@L1383-L1383
DISPOSITION: EXCLUDED
REASON: structural heading
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:lem-swallow-distance
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-swallow-distance@L1389-L1392
DISPOSITION: NODE lem-swallow-distance
REASON: Lemma 3.6
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:proof:L1394
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L1394@L1394-L1397
DISPOSITION: NODE lem-swallow-distance, step:swallow-time-change
REASON: proof of Lemma 3.6
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:proof:L1401
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L1401@L1401-L1418
DISPOSITION: NODE prop-i.a, prop-i.b, step:prop-i-apply-stationary-sde, step:prop-i-a-not-to-minus-infinity, eqn-neg-I1-bd, step:prop-i-b-ode-comparison, step:stationary-sde-X-form
REASON: proof of Prop 3.1
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-neg-I1-bd
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-neg-I1-bd@L1410-L1410
DISPOSITION: NODE eqn-neg-I1-bd
REASON: display (3.2)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:heading:L1421
KIND: heading
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#heading:L1421@L1421-L1421
DISPOSITION: EXCLUDED
REASON: structural heading
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:lem-integral-ii
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-integral-ii@L1430-L1437
DISPOSITION: NODE lem-integral-ii
REASON: Lemma 3.7
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:proof:L1440
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L1440@L1440-L1452
DISPOSITION: NODE lem-integral-ii, eqn-sde-ratio, step:integral-ii-expectation, step:integral-ii-apply-stationary-sde
REASON: proof of Lemma 3.7
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-sde-ratio
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-sde-ratio@L1444-L1444
DISPOSITION: NODE eqn-sde-ratio
REASON: display (3.4)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:proof:L1458
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L1458@L1458-L1469
DISPOSITION: NODE prop-ii.a, step:prop-ii-a-capacity-time, step:prop-ii-a-koebe-limit, eqn-hit-koebe, step:zero-in-right-hull, step:hulls-compact
REASON: proof of Prop 3.2(a)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:cite:L1463:lawler-book
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L1463:lawler-book@L1463-L1463
DISPOSITION: NODE ext:koebe-quarter
REASON: citation Lawler Cor 3.18 (Koebe quarter)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-hit-koebe
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-hit-koebe@L1464-L1464
DISPOSITION: NODE eqn-hit-koebe
REASON: display (3.5)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:lem-converse-w-o-upgrade
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1475-L1478
DISPOSITION: NODE lem-converse-w-o-upgrade
REASON: Lemma 3.8
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-dist-3-outline
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-3-outline@L1488-L1488
DISPOSITION: EXCLUDED
REASON: outline restatement of eqn-dist-3 in the proof outline (L1481-1498); content captured by eqn-dist-3
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-stationary-outline
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-stationary-outline@L1494-L1494
DISPOSITION: EXCLUDED
REASON: outline restatement of Lemma 3.9 (equality in law); content captured by lem-computation
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:lem-computation
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-computation@L1506-L1513
DISPOSITION: NODE lem-computation
REASON: Lemma 3.9
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:proof:L1515
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L1515@L1515-L1543
DISPOSITION: NODE lem-computation, eqn-computation-tilde-f, step:computation-scaling-markov, eqn-wt-L-dist, step:computation-time-change-identity
REASON: proof of Lemma 3.9
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-computation-tilde-f
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-computation-tilde-f@L1518-L1518
DISPOSITION: NODE eqn-computation-tilde-f
REASON: display (3.3)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-wt-L-dist
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-wt-L-dist@L1532-L1532
DISPOSITION: NODE eqn-wt-L-dist
REASON: display (3.4)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:lem-log-finite-exp
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1550-L1556
DISPOSITION: NODE lem-log-finite-exp
REASON: Lemma 3.10
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:proof:L1572
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L1572@L1572-L1631
DISPOSITION: NODE lem-log-finite-exp, step:log-finite-distortion, step:log-finite-exit-times, step:log-finite-iid, step:log-finite-q-choice, step:log-finite-binomial, eqn-log-finite-end, eqn-log-finite-show, step:log-finite-tail-to-expectation
REASON: proof of Lemma 3.10
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-log-finite-show
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-log-finite-show@L1574-L1574
DISPOSITION: NODE eqn-log-finite-show
REASON: display (3.18)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:cite:L1581:lawler-book
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L1581:lawler-book@L1581-L1581
DISPOSITION: NODE ext:koebe-distortion
REASON: citation Lawler Cor 3.23 (Koebe distortion)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-finite-exp-1
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-finite-exp-1@L1584-L1584
DISPOSITION: NODE step:log-finite-distortion
REASON: display inside the distortion step
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-finite-exp-2
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-finite-exp-2@L1589-L1589
DISPOSITION: NODE step:log-finite-distortion
REASON: display inside the distortion step
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-finite-exp-3
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-finite-exp-3@L1595-L1595
DISPOSITION: NODE step:log-finite-exit-times
REASON: display (rescaled chain at tau_k)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-finite-exp-4
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-finite-exp-4@L1602-L1602
DISPOSITION: NODE step:log-finite-iid
REASON: display (integral independent of F_{tau_k})
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-log-finite-end
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-log-finite-end@L1626-L1626
DISPOSITION: NODE eqn-log-finite-end
REASON: display
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:proof:L1638
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L1638@L1638-L1781
DISPOSITION: NODE lem-converse-w-o-upgrade, step:converse-rhs-limit, step:converse-lhs-nonneg, step:converse-conclude, step:converse-event-converges, step:future-point-outside-hulls, eqn-dist-3
REASON: proof of Lemma 3.8 (Steps 1-4)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-converse-show0
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-converse-show0@L1640-L1640
DISPOSITION: NODE step:converse-conclude
REASON: display (contrapositive form)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-dist-3
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-3@L1672-L1672
DISPOSITION: NODE eqn-dist-3
REASON: display (3.6)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:cite:L1705:lawler-book
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L1705:lawler-book@L1705-L1705
DISPOSITION: NODE ext:koebe-quarter, step:hulls-compact
REASON: citation Lawler Cor 3.18; premise recalled at L1702
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-two-formulas
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-two-formulas@L1713-L1713
DISPOSITION: NODE eqn-two-formulas
REASON: display (3.7)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-two-formulas-prime
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-two-formulas'@L1720-L1720
DISPOSITION: NODE eqn-two-formulas-b
REASON: display (3.8)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-two-dist-ratio
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-two-dist-ratio@L1723-L1723
DISPOSITION: NODE eqn-two-dist-ratio
REASON: display (3.9)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-koebe-t
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-koebe-t@L1729-L1729
DISPOSITION: NODE eqn-koebe-t
REASON: display (3.10)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-dist-1
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-1@L1737-L1737
DISPOSITION: NODE eqn-dist-1
REASON: display (3.11)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-dist-event
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-event@L1745-L1745
DISPOSITION: NODE eqn-dist-event, step:converse-event-converges
REASON: display (3.12) and the convergence claim of L1748
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-dist-cases
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-cases@L1751-L1751
DISPOSITION: NODE eqn-dist-cases
REASON: display (3.13)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-koebe-union
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-koebe-union@L1757-L1757
DISPOSITION: NODE eqn-koebe-union
REASON: display (3.14)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-dist-es
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-es@L1765-L1765
DISPOSITION: NODE eqn-dist-es
REASON: display (3.15)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-dist-2
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-2@L1771-L1771
DISPOSITION: NODE eqn-dist-2
REASON: display (3.16)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-dist-esc
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-dist-esc@L1776-L1776
DISPOSITION: NODE eqn-dist-esc
REASON: display (3.17)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:proof:L1786
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L1786@L1786-L1816
DISPOSITION: NODE prop-ii.b, step:prop-ii-b-scale-reduction, step:prop-ii-b-lambda-positive-measure, step:prop-ii-b-hit-lambda-prime, step:prop-ii-b-markov-transfer, step:prop-ii-b-lambda-full, step:prop-ii-b-koebe-ball, step:prop-ii-b-compactness, step:prop-ii-b-conditional-lower-bound, step:prop-ii-b-martingale-zero-one, ext:girsanov, ext:koebe-distortion, ext:martingale-convergence
REASON: proof of Prop 3.2(b)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:heading:L1819
KIND: heading
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#heading:L1819@L1819-L1819
DISPOSITION: EXCLUDED
REASON: structural heading
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:lem-c0-phases
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-phases@L1824-L1827
DISPOSITION: NODE lem-c0-phases
REASON: Lemma 3.11
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:proof:L1828
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L1828@L1828-L1875
DISPOSITION: NODE lem-c0-phases, step:c0-explicit-density, step:c0-positivity-reduction, step:c0-positivity-reflection, step:c0-sign-analysis
REASON: proof of Lemma 3.11
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-c0-p
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-c0-p@L1830-L1830
DISPOSITION: NODE step:c0-explicit-density
REASON: display (3.19)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-c0-integrals
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-c0-integrals@L1839-L1839
DISPOSITION: NODE eqn-c0-integrals
REASON: display (3.20)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-c0-phase-show
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-c0-phase-show@L1844-L1844
DISPOSITION: NODE eqn-c0-phase-show
REASON: display (3.21)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-c0-phase-show-prime
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-c0-phase-show'@L1851-L1851
DISPOSITION: NODE step:c0-positivity-reduction
REASON: display (3.22)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:eqn-cos-reflect
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-cos-reflect@L1856-L1856
DISPOSITION: NODE step:c0-positivity-reflection
REASON: display (3.23)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:lem-c0-bdy
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c0-bdy@L1910-L1913
DISPOSITION: NODE lem-c0-bdy
REASON: Lemma 3.12
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:proof:L1914
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L1914@L1914-L1927
DISPOSITION: NODE lem-c0-bdy, step:c0-bdy-drift-vanishes, step:c0-bdy-martingale-bm, step:c0-bdy-capacity-time, step:c0-bdy-hitting-from-limsup, step:c0-bdy-finite-time
REASON: proof of Lemma 3.12
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:proof:L1930
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L1930@L1930-L1932
DISPOSITION: NODE thm-phases#assembly-sign-cases, thm-phases#assembly-c-zero
REASON: proof of Thm 1.8 (statement-level roots thm-phases, thm-phases.c-zero are slice A)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:L1303:all-z-examples
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L1303:all-z-examples@L1303-L1303
DISPOSITION: NODE step:all-z-apply-Tz, step:all-z-apply-dist
REASON: unlabeled claim: the hypotheses of Lemma 3.3 hold for {T_z<infinity} and the dist-event (SOURCE_GAP)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:L1345:recurrence-premise
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L1345:recurrence-premise@L1345-L1345
DISPOSITION: NODE step:prop-i-apply-stationary-sde, step:integral-ii-apply-stationary-sde
REASON: unlabeled claim: X = e^{2 i theta^} satisfies the premises of Lemma 3.4 (recurrence from Lemma 2.16)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:L1403:sde-premises
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L1403:sde-premises@L1402-L1403
DISPOSITION: NODE step:stationary-sde-X-form
REASON: unlabeled claim: SDEs for X and Y come from Lemma 2.11 with pi-periodic coefficients (SOURCE_GAP)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:L1463:zero-in-right-hull
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L1463:zero-in-right-hull@L1463-L1463
DISPOSITION: NODE step:zero-in-right-hull
REASON: unlabeled claim 'the fact that 0 in R_t' (SOURCE_GAP)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:L1558:zero-in-left-hull
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L1558:zero-in-left-hull@L1558-L1558
DISPOSITION: NODE step:zero-in-left-hull, step:zero-in-future-left-hull
REASON: unlabeled claim |zz| = 1 and 0 in L_{sigma(t^)}; also used at L1768 for L_{t,s+t}
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:L1702:koebe-premise
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L1702:koebe-premise@L1702-L1705
DISPOSITION: NODE step:hulls-compact, ext:koebe-quarter
REASON: Koebe quarter statement recalled with compact K1,K2; compactness of L_t,R_t is never established (SOURCE_GAP)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:L1707:future-point-outside
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L1707:future-point-outside@L1707-L1707
DISPOSITION: NODE step:future-point-outside-hulls
REASON: unlabeled claim zz not in L_{s+t}, f_t(zz) not in R_t u L_{t,s+t}
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:L1806:koebe-ball
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L1806:koebe-ball@L1806-L1807
DISPOSITION: NODE step:prop-ii-b-koebe-ball
REASON: unlabeled Koebe-distortion absorption claim (SOURCE_GAP); the %-commented sketch at L1807 is not part of the paper
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:L1471:prop-ii-b-commentary
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L1471:prop-ii-b-commentary@L1471-L1473
DISPOSITION: EXCLUDED
REASON: commentary on the difficulty of Prop 3.2(b); no claim beyond Lemma 3.8
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:L1481:outline
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L1481:outline@L1481-L1498
DISPOSITION: EXCLUDED
REASON: proof outline of Lemma 3.8; every claim recurs in the full proof (eqn-dist-3, lem-computation, lem-log-finite-exp)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:L1426:asymp-notation
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L1426:asymp-notation@L1426-L1426
DISPOSITION: EXCLUDED
REASON: notation for asymp and <~ (no mathematical claim)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

ITEM: inv:L1504:stationarity-intro
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L1504:stationarity-intro@L1504-L1504
DISPOSITION: EXCLUDED
REASON: restates stationarity of e^{i theta^(zz)} (Lemma 2.13), recorded as edges from lem-computation's proof nodes
COVERAGE_STATUS: REVIEWED
EXTRACTOR: extractor-C/sonnet
REVIEWER: reviewer-C/sonnet

## Report

- Source ranges read: paper.tex L1250-L1946 in full (slice C); read-only L437-L450 (Thm 1.8 statement), L834-L1000 and L1130-L1165 (Defs 2.9/2.10, Lemmas 2.11/2.13/2.14 statements, Remark 2.12/2.15, Lemma 2.16 statement) to read the statements slice C consumes; L556-L575 ((2.3)); the full slice-A packet graph/packets/slice-A.md (read-only, canonical IDs and the thm-phases/item-I/item-II/phase-definition nodes); ERRATA.md; graph/EXTRACTION_SPEC.md; graph/INVENTORY.md (slice C); graph/anchor-table.md; the statement part of the four frozen declaration files I own (Proposition_3_1_A/B, Proposition_3_2_A/B; each shows `by sorry`, which I did not use).
- Counts: 104 nodes, 292 EDGE lines. Nodes: 4 frozen roots (prop-i.a, prop-i.b, prop-ii.a, prop-ii.b), 10 lemmas, 22 displays, 53 steps, 6 applications, 9 externals. Coverage: 83 ITEM records (71 inventory items plus 12 added): 71 mapped to nodes (63 inventory + 8 added), 12 excluded (8 inventory: 5 headings, the Revuz-Yor citation inside a %-comment, eqn-dist-3-outline, eqn-stationary-outline; 4 added: L1426 notation, L1471 commentary, L1481 outline, L1504 stationarity restatement).
- Slice C canonical IDs created, as in the spec: eqn-integral-nu, lem-all-z, lem-stationary-sde, lem-recurrent, lem-swallow-distance, lem-integral-ii, lem-converse-w-o-upgrade, lem-computation, lem-log-finite-exp, lem-c0-phases, lem-c0-bdy, eqn-hit-koebe, plus roots prop-i.a/.b, prop-ii.a/.b. Extra non-spec IDs: eqn-neg-I1-bd, eqn-sde-ratio, eqn-computation-tilde-f, eqn-wt-L-dist, eqn-two-formulas, eqn-two-formulas-b (the inventory's eqn-two-formulas'), eqn-two-dist-ratio, eqn-koebe-t, eqn-dist-1, eqn-dist-event, eqn-dist-cases, eqn-koebe-union, eqn-dist-es, eqn-dist-2, eqn-dist-esc, eqn-dist-3, eqn-log-finite-show, eqn-log-finite-end, eqn-c0-integrals, eqn-c0-phase-show, and `step:` nodes. Proof of Thm 1.8 (L1930-1932): nodes `thm-phases#assembly-sign-cases` and `thm-phases#assembly-c-zero`.
- Slice-A nodes consumed: defn-hulls.left, defn-hulls.right, defn-loewner.absorbing-time, item-I, item-II, eqn-nu-D.nu, eqn-nu-D.mu, eqn-nu-D.D, defn-phases.thin, defn-phases.swallowing, defn-phases.hitting, defn-phases.dense, eqn-conc, eqn-scale, lem-scaling, lem-markov, lem-endpt-cont, claim:hulls-monotone, claim:gt-conformal, ext:strong-markov-bm. Not used: eqn-reflect, step:wlog-c-nonneg (L1949 is in slice D), step:driver-representation (slice C never uses U = sqrt(a)B + i sqrt(b)B~ directly; it appears only inside lem-polar).
- Slice-B nodes consumed (canonical IDs only, not seen): defn-sigma, def-arg, lem-polar, remark-sigma, lem-p, lem-stationary, remark-p0, lem-recurrence, lem-stationary.admissible. Not used: lem-kolmogorov, lem-hormander.
- Cross-slice edges (to canonical IDs I do not own): 29 distinct targets, 131 edge lines. To A: claim:gt-conformal, claim:hulls-monotone, defn-hulls.left, defn-hulls.right, defn-loewner.absorbing-time, defn-phases.*, eqn-conc, eqn-nu-D.D/.mu/.nu, eqn-scale, ext:strong-markov-bm, item-I, item-II, lem-endpt-cont, lem-markov, lem-scaling. To B: def-arg, defn-sigma, lem-p, lem-polar, lem-recurrence, lem-stationary, lem-stationary.admissible, remark-p0, remark-sigma. Edges from A into slice C: thm-phases -> prop-i.a/.b, prop-ii.a/.b (already present); thm-phases.c-zero -> lem-c0-phases, lem-c0-bdy, prop-i.a/.b, prop-ii.a/.b (already present).
- Orchestrator action items for slice A: `thm-phases#assembly-sign-cases` feeds only slice A's thm-phases (Props -> phase translation, SOURCE_GAP) and slice C's lem-c0-phases; `thm-phases#assembly-c-zero` is the trivial union for thm-phases.c-zero. Slice A should add `thm-phases#assembly-sign-cases` to thm-phases and `thm-phases#assembly-c-zero` to thm-phases.c-zero (replacing or adding to their direct prop-i/prop-ii edges), otherwise the two assembly nodes are not reachable from slice-A roots (thm-phases#assembly-sign-cases is reached from lem-c0-phases, which slice A's thm-phases.c-zero consumes; thm-phases#assembly-c-zero is otherwise unreached). lem-c0-phases and lem-c0-bdy are reachable from slice A's thm-phases.c-zero.
- Alternate routes: none (no route nodes). The source gives no alternative proofs; the Dekking reference at L1353 is %-commented.
- SOURCE_GAP nodes (18 ordinary nodes, plus the external ext:durrett-7.3.2): step:all-z-null-set-density (R7: admissible p vanishes only on a null set), step:all-z-stopping-time-choice, step:all-z-apply-Tz, step:all-z-apply-dist, step:sde-stationary-increments, step:sde-continuity-noninteger (details only in %-comment), step:sde-regeneration (partial: uniqueness in law of the SDE for X not stated), step:recurrent-durrett-adaptation, step:stationary-sde-X-form (diffusion coefficients are 2pi- not pi-periodic, so not functions of X = e^{2 i theta^}), step:zero-in-right-hull, step:hulls-compact (compactness premise of Koebe never established), step:converse-event-converges, step:log-finite-iid (partial: independence of F_{tau_k} and k-independence of the law), step:prop-ii-b-hit-lambda-prime (Girsanov inference), step:prop-ii-b-koebe-ball, step:c0-explicit-density (identification of every admissible p with the explicit formula, R7), step:c0-bdy-finite-time (T_z < infinity not shown in Lemma 3.12), thm-phases#assembly-sign-cases (Props -> phases translation).
- New ext: IDs: `ext:kolmogorov-zero-one` (external:standard#kolmogorov-zero-one-tail, tail triviality used implicitly at L1372). Externals first cited here using canonical spec IDs: ext:birkhoff, ext:durrett-7.3.2, ext:koebe-quarter, ext:koebe-distortion, ext:girsanov, ext:martingale-convergence, ext:dct, ext:levy-characterization. ext:martingale-convergence, ext:dct and ext:levy-characterization are also defined in graph/packets/slice-B.md (seen after writing, by name only); the orchestrator should deduplicate (keep one definition, my edges use the canonical IDs). ext:strong-markov-bm is owned by slice A and only referenced.
- Uncertainty list: (1) the Section-3 package ("zz sampled from p") is recorded in SOURCE_HYPOTHESES of each consuming node and its supply is via lem-p / lem-stationary (R7/R15), per spec Section 4; the source cites only Lemma 2.13, so both edges exist wherever stationarity is used. (2) Y_0 = 0 is an implicit hypothesis of Lemma 3.4's second assertion (noted on lem-stationary-sde). (3) step:sde-mean-zero has no ext node because its Revuz-Yor citation is only in a %-comment (inventory item excluded). (4) Lemma 3.8's step 2 uses E log(1/dist(zz, L_{s+t})) < infinity, while Lemma 3.10 is stated for L_{sigma(t^)}; applied at index s^ + t^. (5) The Koebe applications (eqn-hit-koebe, eqn-two-formulas, ..., step:prop-ii-b-koebe-ball) consume step:hulls-compact and claim:gt-conformal: whether the orchestrator wants to keep that explicit gap node is a judgment call. (6) eqn-hit-koebe is stated for zz but reused for fixed z in Lemma 3.12. (7) step:zero-in-left-hull covers 0 in L_{t,s+t} through eqn-conc/shifted driver. (8) lem-c0-phases consumes thm-phases#assembly-sign-cases rather than the root thm-phases to avoid depending on a root. (9) The Prop 3.2(a) proof environment is labelled item-ii-b by a hyperref glitch at L1458. (10) The step splits of Lemma 3.8 (Steps 1-4) follow the source's step labels; the Koebe-chain displays follow the spec's list "(3.18)-(3.28)" (print numbering differs from the labels I used in titles, which are my reading). (11) Frozen CONTRACT_ID values follow the anchor table (paper.prop3_1.a etc.).
- Confirmations: no Lean evidence was sought (only the statement parts of the four anchor files I own were read, to copy identity fields and check hypotheses; ABI hashes copied from graph/EXTRACTION_SPEC.md section 8), no anchor ABI was edited or inferred, no Lean was run, and no file other than graph/packets/slice-C.md was written (generator scripts live in the session scratchpad).
