## Nodes

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
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1165-L1165 | sigma-time is unchanged by conjugation (∣f_s∣ is unchanged)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: global-reviewer/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: the source writes only 'Assume without loss of generality that c >= 0' for a statement about the argument process. Distinct from step:wlog-c-nonneg (hull level, used at L323/L1951) and from step:p-wlog-c-nonneg (admissibility of p~ only).

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


## Coverage

ITEM: inv:L554:reflect-map-identity
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L554:reflect-map-identity@L553-L558
DISPOSITION: NODE step:reflect-map-identity
REASON: map-level form of the reflection property (2.2), used at L984 and L1165 but stated in the source for hulls only; SOURCE_GAP
COVERAGE_STATUS: PROPOSED
EXTRACTOR: global-reviewer/sonnet
REVIEWER: -

ITEM: inv:L1165:wlog-arg
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L1165:wlog-arg@L1165-L1165
DISPOSITION: NODE step:wlog-c-nonneg-arg
REASON: 'Assume without loss of generality that c >= 0' in the proof of Lemma 2.16, a reduction for the argument process under conjugation (not the hull-level reduction of L323)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: global-reviewer/sonnet
REVIEWER: -

ITEM: inv:L1255:product-extension
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L1255:product-extension@L1255-L1255
DISPOSITION: NODE step:section3-product-extension
REASON: 'independent from the driving Brownian motion' (also L939): carrier change from the given probability space to the product with the circle, not stated in the source; SOURCE_GAP
COVERAGE_STATUS: PROPOSED
EXTRACTOR: global-reviewer/sonnet
REVIEWER: -

