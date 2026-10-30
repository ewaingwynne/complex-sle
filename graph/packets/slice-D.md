## Nodes

NODE: ext:loewner-convergence
KIND: external
TITLE: Lawler Prop 4.43: locally uniform convergence of driving functions gives locally uniform convergence of Loewner maps away from the hull
STATEMENT_SOURCE: external:lawler-book#prop-4.43
PROOF_SOURCE: external:standard#proof
CONTRACT_ID: paper.ext:loewner-convergence
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Lawler Prop 4.43: locally uniform convergence of driving functions gives locally uniform convergence of Loewner maps away from the hull
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: First cited at L2011. Stated for real driving functions on H; extension to C asserted by replacing H by C (T6): SOURCE_GAP, recorded on step:haus-maps-converge.

NODE: ext:bm-support
KIND: external
TITLE: Support theorem: a Brownian motion stays uniformly within delta of a given admissible continuous path on [0,T] with positive probability
STATEMENT_SOURCE: external:standard#brownian-support
PROOF_SOURCE: external:standard#proof
CONTRACT_ID: paper.ext:bm-support
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Support theorem: a Brownian motion stays uniformly within delta of a given admissible continuous path on [0,T] with positive probability
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: First cited (implicitly) at L2023 ('positive chance to be arbitrarily close to 0') and L2106-2107 ('positive probability as long as C is large'). Slice C may also cite it; orchestrator deduplicates. For the planar covariance Sigma the target path must lie in the Cameron-Martin support of Sigma (degenerate when c^2=ab).

NODE: ext:blumenthal
KIND: external
TITLE: Blumenthal zero-one law: germ sigma-field of Brownian motion is trivial
STATEMENT_SOURCE: external:standard#blumenthal-zero-one
PROOF_SOURCE: external:standard#proof
CONTRACT_ID: paper.ext:blumenthal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Blumenthal zero-one law: germ sigma-field of Brownian motion is trivial
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: First cited at L2223.

NODE: lem-haus
KIND: lemma
TITLE: Continuity of Loewner maps and of left/right hulls in the driving function
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L1998-L2009
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2010-L2020
CONTRACT_ID: paper.lem-haus
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U^n, U : [0,infinity) -> C continuous; g^n_t, g_t the corresponding forward Loewner maps; L^n_t, L_t the left hulls; U^n -> U uniformly on compact sub-intervals of [0,infinity)
SOURCE_QUANTIFIERS: for each T>0 and eps>0: (i) uniform convergence of g^n_t(z) to g_t(z) on [0,T] x {dist(z,K_T)>=eps}; (ii) for each t there is n_0 such that for n>=n_0: L^n_t subset B_eps(L_t) and every point disconnected from infinity by L_t is disconnected from infinity by B_eps(L^n_t); same for reverse maps, and for right hulls instead of left hulls
SOURCE_CONCLUSION: g^n_t(z) -> g_t(z) uniformly on [0,T] x {z : dist(z,K_T)>=eps}; for each t, for n large: L^n_t subset B_eps(L_t) and B_eps(L^n_t) disconnects from infinity every point that L_t disconnects
CONSTANT_SCOPE: n_0 depends on t, T, eps, and the sequences
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:haus-maps-converge, step:haus-subsequence-limit-contained, step:haus-limit-conformal-extension, step:haus-contradiction-L-t, step:haus-subsubsequence-closure, step:haus-right-hull-reduction
ROUTES: -
ROUTE_FOR: -
EDGE: step:haus-maps-converge | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2011-L2011 | first bullet (convergence of the maps) is the cited convergence result
EDGE: step:haus-subsequence-limit-contained | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2014-L2017 | L' subset L_t for a Hausdorff-subsequential limit L'
EDGE: step:haus-limit-conformal-extension | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2018-L2019 | if L' disconnects fewer points than L_t, g_t extends conformally to V
EDGE: step:haus-contradiction-L-t | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2019-L2019 | extension of g_t to V is impossible since V meets L_t
EDGE: step:haus-subsubsequence-closure | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2015-L2015 | subsequence-of-subsequence argument yields the quantitative statement for all large n
EDGE: step:haus-right-hull-reduction | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2013-L2013 | right hulls and reverse maps reduce to left hulls of reverse maps
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: K_T is undefined in the source; read as the time-T left hull L_T. The footnote definition of 'disconnected from infinity by a bounded set' agrees with def-disconnect. Statement-level dependence on definitions is carried through the steps.

NODE: step:haus-maps-converge
KIND: step
TITLE: Convergence of forward (and reverse) Loewner maps from convergence of drivers
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2011-L2011
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2011-L2011
CONTRACT_ID: paper.step:haus-maps-converge
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U^n -> U locally uniformly, continuous complex drivers
SOURCE_QUANTIFIERS: T>0, eps>0
SOURCE_CONCLUSION: g^n_t -> g_t uniformly on [0,T] x {dist(z,K_T)>=eps}; same for reverse Loewner maps
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: ext:loewner-convergence, defn-loewner.well-defined
ROUTES: -
ROUTE_FOR: -
EDGE: ext:loewner-convergence | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2011-L2011 | cited Prop 4.43
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2011-L2011 | g_t, g^n_t are the maps whose existence and uniqueness is asserted for continuous complex drivers
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: Prop 4.43 of Lawler is stated for real drivers on H; the source asserts that the proof extends by replacing H by C (T6). The reverse-map version is asserted by 'the same proof applies'.

NODE: step:haus-subsequence-limit-contained
KIND: step
TITLE: Hausdorff-subsequential limit L' of L^n_t lies in L_t
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2014-L2017
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2014-L2017
CONTRACT_ID: paper.step:haus-subsequence-limit-contained
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: t>0 fixed; maps converge as in step:haus-maps-converge
SOURCE_QUANTIFIERS: subsequence of N
SOURCE_CONCLUSION: for every subsequence there is a further subsequence along which L^n_t -> L' in Hausdorff distance and L' subset L_t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:haus-maps-converge, defn-hulls.left, step:hull-closed, step:hulls-compact
ROUTES: -
ROUTE_FOR: -
EDGE: step:haus-maps-converge | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2017-L2017 | g^n_t -> g_t on C minus B_eps(L_t) gives L' subset B_eps(L_t) for each eps
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2017-L2017 | L_t = {T_z <= t}
EDGE: step:hull-closed | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2017-L2017 | L_t closed, so the intersection over eps of B_eps(L_t) is L_t and L' subset L_t
EDGE: step:hulls-compact | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2015-L2015 | "By compactness": the L^n_t and L_t are compact and uniformly bounded, so Hausdorff-convergent subsequences exist
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Existence of a Hausdorff-convergent subsequence uses compactness/uniform boundedness of L^n_t (step:hulls-compact, itself a SOURCE_GAP of slice C) and closedness of L_t (step:hull-closed, SOURCE_GAP of slice A); neither is cited at L2015-L2017.

NODE: step:haus-limit-conformal-extension
KIND: step
TITLE: Normal-family argument: g^n_t converges on V to a conformal limit extending g_t
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2018-L2019
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2018-L2019
CONTRACT_ID: paper.step:haus-limit-conformal-extension
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: V bounded open, meets boundary of unbounded component of C minus L_t, V disjoint from L', and L' does not disconnect V from infinity (negation of the claim)
SOURCE_QUANTIFIERS: subsequence from the previous step
SOURCE_CONCLUSION: g_t extends conformally to V
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:haus-subsequence-limit-contained, step:haus-maps-converge, claim:gt-conformal
ROUTES: -
ROUTE_FOR: -
EDGE: step:haus-subsequence-limit-contained | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2018-L2018 | L' is the Hausdorff limit; choice of V relative to L' and L_t
EDGE: step:haus-maps-converge | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2019-L2019 | uniform boundedness of g^n_t on V from convergence on a set separating V from infinity, and identification of the limit with g_t on the complement of L_t
EDGE: claim:gt-conformal | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2019-L2019 | g^n_t is conformal on V for large n
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Uses Cauchy integral formula, Montel-type compactness, analytic continuation (standard, not cited as external). Source states 'conformal or constant' limit (Hurwitz).

NODE: step:haus-contradiction-L-t
KIND: step
TITLE: g_t cannot extend conformally to a set V meeting L_t
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2019-L2019
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2019-L2019
CONTRACT_ID: paper.step:haus-contradiction-L-t
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: V meets the boundary of the unbounded component of C minus L_t, so V meets L_t; g_t extends conformally to V
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: contradiction
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:haus-limit-conformal-extension, claim:gt-conformal, defn-hulls.left
ROUTES: -
ROUTE_FOR: -
EDGE: step:haus-limit-conformal-extension | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2019-L2019 | supplies the conformal extension of g_t to V
EDGE: claim:gt-conformal | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2019-L2019 | g_t conformal from C minus L_t onto its image
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2019-L2019 | L_t is the set of absorbed points T_z<=t
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: the non-extendability of g_t across L_t ('which cannot hold since V intersects L_t') is asserted without argument.

NODE: step:haus-subsubsequence-closure
KIND: step
TITLE: Subsequence principle: from limit identification to the quantitative statement for all large n
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2015-L2015
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2015-L2019
CONTRACT_ID: paper.step:haus-subsubsequence-closure
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: t>0, eps>0; every subsequence has a further subsequence with Hausdorff limit L' subset L_t disconnecting the same points as L_t
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: for n large: L^n_t subset B_eps(L_t) and B_eps(L^n_t) disconnects every point that L_t disconnects
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:haus-subsequence-limit-contained, step:haus-contradiction-L-t, def-disconnect
ROUTES: -
ROUTE_FOR: -
EDGE: step:haus-subsequence-limit-contained | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2015-L2015 | L' subset L_t along subsubsequences gives the inclusion
EDGE: step:haus-contradiction-L-t | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2018-L2019 | no point set V witnessing a difference between L' and L_t, so L' and L_t disconnect the same points
EDGE: def-disconnect | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2015-L2015 | 'disconnect the same set of points from infinity'
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The passage from Hausdorff convergence L^n_t -> L' with L' disconnecting x to 'B_eps(L^n_t) disconnects x for large n' is not spelled out.

NODE: step:haus-right-hull-reduction
KIND: step
TITLE: Right-hull and reverse-map versions via left hulls of reverse chains
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2013-L2013
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2013-L2013
CONTRACT_ID: paper.step:haus-right-hull-reduction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: complex continuous drivers
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: the right-hull statement follows from the left-hull statement applied to the reverse Loewner maps
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-forward-reverse-ext, lem-mult-by-i
ROUTES: -
ROUTE_FOR: -
EDGE: lem-forward-reverse-ext | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2013-L2013 | cited as the link between forward/reverse chains and hulls
EDGE: lem-mult-by-i | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L2013-L2013 | reverse chain with driver U is obtained from the forward chain with iU by conjugation by multiplication by i (Lemma 2.3)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: Lemma 2.2 is stated for real drivers; for complex drivers the identification of right hulls with left hulls of the reverse chain is not stated (duality (2.4) is not a node, see slice A). Lemma 2.3 is added as the natural complex-driver ingredient (extractor reading).

NODE: lem-line-approx
KIND: lemma
TITLE: Hulls and map of an SLE_Sigma chain are close to the zero-driver chain
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-line-approx@L1991-L1993
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-line-approx@L2022-L2025
CONTRACT_ID: paper.lem-line-approx
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b>0 (R5), c in [-sqrt(ab),sqrt(ab)] (Sigma PSD), c>=0 after the WLOG of L1951; (f_t),(L_t),(R_t) the centered chain, left and right hulls of an SLE_Sigma driver
SOURCE_QUANTIFIERS: T>0, eps>0 deterministic; positive probability
SOURCE_CONCLUSION: with positive probability: Hausdorff distance of L_T to [-2T^{1/2} i, 2T^{1/2} i] is <= eps; Hausdorff distance of R_T to [-2T^{1/2}, 2T^{1/2}] is <= eps; sup distance of f_T to z -> sqrt(z^2+4T) is <= eps off the eps-neighborhood of the segment [-2T^{1/2} i, 2T^{1/2} i]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:line-zero-driver-chain, step:line-small-driver-positive, step:line-apply-haus
ROUTES: -
ROUTE_FOR: -
EDGE: step:line-zero-driver-chain | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-line-approx@L2023-L2023 | explicit zero-driver chain, hulls and map
EDGE: step:line-small-driver-positive | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-line-approx@L2023-L2023 | driver is within delta of 0 on [0,T] with positive probability
EDGE: step:line-apply-haus | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-line-approx@L2024-L2024 | Lemma 4.3 transfers closeness of drivers to closeness of hulls and maps
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Typo: the statement writes [-2T^{-1/2} i, ...]; read as [-2T^{1/2} i, 2T^{1/2} i] (as in the proof, L2023-2024). The statement has no a,b>0 hypothesis of its own; the section package is recorded.

NODE: step:line-zero-driver-chain
KIND: step
TITLE: Zero driver: g_t = sqrt(z^2+4t), L_t=[-2 t^{1/2} i,2 t^{1/2} i], R_t=[-2 t^{1/2},2 t^{1/2}]
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-line-approx@L2023-L2023
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-line-approx@L2023-L2023
CONTRACT_ID: paper.step:line-zero-driver-chain
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: driving function U = 0
SOURCE_QUANTIFIERS: t>=0
SOURCE_CONCLUSION: the Loewner chain is z -> sqrt(z^2+4t), left hulls the vertical segment, right hulls the horizontal segment
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-loewner.well-defined, defn-hulls.left, defn-hulls.right
ROUTES: -
ROUTE_FOR: -
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-line-approx@L2023-L2023 | identifies the chain driven by 0 as the unique solution of the Loewner ODE
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-line-approx@L2023-L2023 | left hull is {z: T_z<=t}
EDGE: defn-hulls.right | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-line-approx@L2023-L2023 | right hull is the complement of the range of f_t
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Explicit computation stated without verification (solving g' = 2/g); reused in step:disc-setup (z -> sqrt(z^2+4T)).

NODE: step:line-small-driver-positive
KIND: step
TITLE: The planar driver stays uniformly near 0 on [0,T] with positive probability
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-line-approx@L2023-L2023
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-line-approx@L2023-L2023
CONTRACT_ID: paper.step:line-small-driver-positive
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U planar BM with covariance Sigma
SOURCE_QUANTIFIERS: T>0, delta>0
SOURCE_CONCLUSION: P(sup_{t in [0,T]} |U_t| < delta) > 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: ext:bm-support, defn-sle
ROUTES: -
ROUTE_FOR: -
EDGE: ext:bm-support | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-line-approx@L2023-L2023 | 'positive chance to be arbitrarily close to 0 on [0,T]'
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-line-approx@L2023-L2023 | U is a planar BM with covariance Sigma
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Support theorem for a possibly degenerate planar BM (c^2=ab). Not named as a citation in the source.

NODE: step:line-apply-haus
KIND: application
TITLE: Apply Lemma 4.3 with U = 0 to deduce the Hausdorff and map bounds
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-line-approx@L2024-L2024
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-line-approx@L2024-L2024
CONTRACT_ID: paper.step:line-apply-haus
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U small on [0,T] with positive probability; U^n -> 0 comparison
SOURCE_QUANTIFIERS: T>0, eps>0
SOURCE_CONCLUSION: L_T subset B_eps(segment), every point of the segment disconnected from infinity by B_eps(L_T), analogous for right hulls, hence Hausdorff bounds; f_T uniformly close to the zero-driver map
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-haus, step:line-zero-driver-chain, step:line-small-driver-positive
ROUTES: -
ROUTE_FOR: -
EDGE: lem-haus | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-line-approx@L2024-L2024 | applied with U equiv 0 (sequential statement used as continuity at the zero driver)
EDGE: step:line-zero-driver-chain | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-line-approx@L2024-L2024 | limit chain explicit
EDGE: step:line-small-driver-positive | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-line-approx@L2024-L2024 | event of positive probability on which the driver is small
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: (i) 'every point of the segment is disconnected from infinity by B_eps(L_T)' does not by itself give the other half of the Hausdorff distance (points of the segment within eps of L_T); (ii) the uniform bound for f_T is not mentioned in the proof (it follows from the first bullet of Lemma 4.3); (iii) passage from the sequential statement of Lemma 4.3 to a statement for small drivers is not spelled out.

NODE: lem:re-im-bounds
KIND: lemma
TITLE: Pathwise bounds on increments of Re f_t(z), Im f_t(z) while |f_t(z)|>1
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem:re-im-bounds@L2043-L2067
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem:re-im-bounds@L2069-L2077
CONTRACT_ID: paper.lem:re-im-bounds
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b>0 (R5); (B,B~) the correlated standard BMs of (1.6) with U = sqrt(a)B + i sqrt(b)B~; z in C; rho_z = inf{t : |f_t(z)|<=1}
SOURCE_QUANTIFIERS: z in C; s,t in [0,rho_z]
SOURCE_CONCLUSION: h^-(s,t;a) <= Re f_t(z)-Re f_s(z) <= h^+(s,t;a) and h^-(s,t;b) <= Im f_t(z)-Im f_s(z) <= h^+(s,t;b), where h^{+-}(s,t;a)=+-2(t-s)-sqrt(a)(B_t-B_s) and h^{+-}(s,t;b)=+-2(t-s)-sqrt(b)(B~_t-B~_s)
CONSTANT_SCOPE: pathwise, all s<=t in [0,rho_z] simultaneously
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:re-im-ft-sde, step:re-im-drift-bound
ROUTES: -
ROUTE_FOR: -
EDGE: step:re-im-ft-sde | source/arxiv-2203.07313v4/complex-sle-final.tex#lem:re-im-bounds@L2070-L2075 | real and imaginary SDEs from (1.6)
EDGE: step:re-im-drift-bound | source/arxiv-2203.07313v4/complex-sle-final.tex#lem:re-im-bounds@L2076-L2076 | drift terms bounded by 2 on [s,t]
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabeled lemma (inventory eqn-re-ft.2) with displays (eqn-re-ft) and (eqn-im-ft) folded into it. The source writes the h^{+-} terms as -sqrt(a)(B_t-B_s) so the bounds hold for every pair s<t pathwise (the martingale part cancels exactly).

NODE: step:re-im-ft-sde
KIND: step
TITLE: Real and imaginary parts of f_t(z) satisfy a pair of SDEs
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-re-im-ft@L2070-L2075
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-re-im-ft@L2070-L2075
CONTRACT_ID: paper.step:re-im-ft-sde
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b>0; z in C; f_t(z) solves (1.6)
SOURCE_QUANTIFIERS: t < T_z
SOURCE_CONCLUSION: dRe f_t = 2Re f_t/|f_t|^2 dt - sqrt(a) dB_t; dIm f_t = -2 Im f_t/|f_t|^2 dt - sqrt(b) dB~_t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-def-ft, step:driver-representation
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-def-ft | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-re-im-ft@L2070-L2070 | taking real and imaginary parts of df_t = 2/f_t dt - sqrt(a)dB - i sqrt(b)dB~ (2/f = 2 conj(f)/∣f∣^2)
EDGE: step:driver-representation | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-re-im-ft@L2073-L2074 | identifies the noise terms with sqrt(a)B and sqrt(b)B~
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Display (eqn-re-im-ft). Pure algebra over (1.6), but kept as a step because it fixes the sign conventions of the later bounds.

NODE: step:re-im-drift-bound
KIND: step
TITLE: Drift of Re/Im f_t(z) is bounded by 2 in absolute value while |f_t(z)|>=1
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem:re-im-bounds@L2076-L2076
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem:re-im-bounds@L2076-L2076
CONTRACT_ID: paper.step:re-im-drift-bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: |f_r(z)|>=1 for r in [s,t]
SOURCE_QUANTIFIERS: s<=t
SOURCE_CONCLUSION: |2 Re f_r/|f_r|^2|<=2 and |2 Im f_r/|f_r|^2|<=2 so integrating the SDEs on [s,t] gives the stated bounds
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:re-im-ft-sde, lem-endpt-cont
ROUTES: -
ROUTE_FOR: -
EDGE: step:re-im-ft-sde | source/arxiv-2203.07313v4/complex-sle-final.tex#lem:re-im-bounds@L2076-L2076 | SDEs applied on the interval [s,t]
EDGE: lem-endpt-cont | source/arxiv-2203.07313v4/complex-sle-final.tex#lem:re-im-bounds@L2049-L2049 | s,t in [0,rho_z] with rho_z < T_z so that f_t(z) exists at the endpoint; ∣f_t(z)∣ -> 0 at T_z < infinity forces rho_z < T_z
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The source uses |f_r|>=1 on [s,t] where the definition of rho gives |f_r|>1 on [0,rho). SOURCE_GAP: existence of f_rho(z) (rho < T_z; also the case T_z = infinity with |f_t|>1 for all t, where [0,rho] is not an interval of definition) is not addressed in L2043-L2077; lem-endpt-cont is the ingredient the proof of Lemma 4.4 later cites (L2134) for the same inference.

NODE: lem-c-event
KIND: lemma
TITLE: Positive-probability event on the increments of the driving BMs
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c-event@L2082-L2103
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c-event@L2105-L2108
CONTRACT_ID: paper.lem-c-event
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b>0 (R5); c>=0 (WLOG of L1951), so the correlation c/sqrt(ab) of B and B~ is non-negative; h^{+-} as in lem:re-im-bounds
SOURCE_QUANTIFIERS: exists C_0 such that for every C>=C_0 (deterministic)
SOURCE_CONCLUSION: with positive probability: (cond-2) -C<=h^-(0,t;a)<=h^+(0,t;a)<=C for t in [0,1]; (cond-3) -5C<=h^-(1,2;a)<=h^+(1,2;a)<=-4C; (cond-1) h^+(0,1;b)<=-2; (cond-4) h^+(1,t;b)<=1 for all t in [1,2]
CONSTANT_SCOPE: C_0 depends only on a,b,c
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:c-event-E1, step:c-event-E2, step:c-event-combine
ROUTES: -
ROUTE_FOR: -
EDGE: step:c-event-E1 | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c-event@L2106-L2106 | conditions (cond-1) and (cond-2) on [0,1]
EDGE: step:c-event-E2 | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c-event@L2107-L2107 | conditions (cond-3) and (cond-4) on [1,2]
EDGE: step:c-event-combine | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c-event@L2107-L2107 | independence of the two events gives simultaneous positive probability
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Displays cond-1..cond-4 are folded into this lemma. The label lem-c-event appears at L2102 inside the statement. 'for all sufficiently large C' read as there exists C_0(a,b,c).

NODE: step:c-event-E1
KIND: step
TITLE: Event E_1: sqrt(b)B~_1>=4 and sqrt(a)|B_t|<=C-2t on [0,1] has positive probability for large C
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c-event@L2106-L2106
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c-event@L2106-L2106
CONTRACT_ID: paper.step:c-event-E1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b>0; (B,B~) correlated standard BMs; correlation c/sqrt(ab)>=0
SOURCE_QUANTIFIERS: C large
SOURCE_CONCLUSION: P(E_1)>0
CONSTANT_SCOPE: C_0 depends on a,b,c
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:driver-representation, ext:bm-support
ROUTES: -
ROUTE_FOR: -
EDGE: step:driver-representation | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c-event@L2106-L2106 | B and B~ are the standard BMs in U = sqrt(a)B + i sqrt(b)B~
EDGE: ext:bm-support | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c-event@L2106-L2106 | positivity of the probability of this event on [0,1]
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Rewrites cond-1 as sqrt(b)B~_1>=4 and cond-2 as sqrt(a)|B_t|<=C-2t. Positivity is asserted ('as long as C is large') without citing a support theorem; ext:bm-support is the assumed ingredient. When c^2=ab (B~=B) positivity needs C large relative to b/a.

NODE: step:c-event-E2
KIND: step
TITLE: Event E_2: 2+4C<=sqrt(a)(B_2-B_1)<=5C-2 and sqrt(b)(B~_t-B~_1)>=2t-3 on [1,2] has positive probability for large C
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c-event@L2107-L2107
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c-event@L2107-L2107
CONTRACT_ID: paper.step:c-event-E2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b>0; correlation c/sqrt(ab)>=0
SOURCE_QUANTIFIERS: C large
SOURCE_CONCLUSION: P(E_2)>0
CONSTANT_SCOPE: C_0 depends on a,b,c
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:driver-representation, step:wlog-c-nonneg, ext:bm-support
ROUTES: -
ROUTE_FOR: -
EDGE: step:driver-representation | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c-event@L2107-L2107 | B and B~ standard BMs with correlation c/sqrt(ab)
EDGE: step:wlog-c-nonneg | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c-event@L2107-L2107 | non-negativity of the correlation is the WLOG assumption of L1951
EDGE: ext:bm-support | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c-event@L2107-L2107 | positivity of the probability of this event
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Rewrites cond-3 and cond-4. The assumption c>=0 is used here: a large positive increment of B is compatible with a large positive increment of B~.

NODE: step:c-event-combine
KIND: step
TITLE: E_1 and E_2 are independent and positive, so all four conditions hold with positive probability
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c-event@L2107-L2107
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c-event@L2107-L2107
CONTRACT_ID: paper.step:c-event-combine
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E_1 depends on increments on [0,1], E_2 on [1,2]
SOURCE_QUANTIFIERS: C large
SOURCE_CONCLUSION: P(E_1 cap E_2)=P(E_1)P(E_2)>0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:c-event-E1, step:c-event-E2, defn-sle
ROUTES: -
ROUTE_FOR: -
EDGE: step:c-event-E1 | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c-event@L2107-L2107 | P(E_1)>0
EDGE: step:c-event-E2 | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c-event@L2107-L2107 | P(E_2)>0
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-c-event@L2107-L2107 | independent increments of the planar BM U give independence of E_1,E_2
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Quantifier closure: the same C works for both events.

NODE: lem-pos-hits-before-neg
KIND: lemma
TITLE: Re f_2 changes sign across a segment [x,y] disjoint from L_2 with positive probability
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2036-L2039
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2120-L2139
CONTRACT_ID: paper.lem-pos-hits-before-neg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b>0 (parameters of (1.3)); (c>=0 through lem-c-event, WLOG of L1951)
SOURCE_QUANTIFIERS: exists deterministic 0<x<y; then positive probability event
SOURCE_CONCLUSION: exists 0<x<y such that with positive probability L_2 cap [x,y] = empty and Re f_2(x)<0<Re f_2(y)
CONSTANT_SCOPE: x=2C and y=7C where C depends only on a,b,c
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:pos-choose-C-x-y, step:pos-segment-disjoint-L2, step:pos-real-part-sign-change
ROUTES: -
ROUTE_FOR: -
EDGE: step:pos-choose-C-x-y | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2121-L2124 | choice of C, x, y and the event
EDGE: step:pos-segment-disjoint-L2 | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2134-L2134 | disjointness of [x,y] from L_2
EDGE: step:pos-real-part-sign-change | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2136-L2138 | sign change of Re f_2
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The statement hypothesises only a,b>0, but its proof (via lem-c-event) needs c>=0; the section WLOG supplies this at the consumers. Typo: the last line of the proof writes f_1(x), f_1(y); read f_2.

NODE: step:pos-choose-C-x-y
KIND: step
TITLE: Choice of C>=1 on the event of Lemma 4.6 and of x=2C, y=7C
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2121-L2124
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2121-L2124
CONTRACT_ID: paper.step:pos-choose-C-x-y
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b>0; c>=0
SOURCE_QUANTIFIERS: C>=1 with the event of lem-c-event of positive probability
SOURCE_CONCLUSION: work on this event; x=2C, y=7C, z in [x,y]
CONSTANT_SCOPE: C deterministic depending on a,b,c
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-c-event
ROUTES: -
ROUTE_FOR: -
EDGE: lem-c-event | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2121-L2121 | supplies C and the positive-probability event
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Witness/parameter choice.

NODE: step:pos-real-part-lower-bound
KIND: step
TITLE: Re f_t(z)>=C on [0,1] for z in [x,y] and hence rho_z>=1
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2125-L2129
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2125-L2129
CONTRACT_ID: paper.step:pos-real-part-lower-bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: event of lem-c-event holds; z in [x,y]; C>=1
SOURCE_QUANTIFIERS: t in [0,1 wedge rho_z]
SOURCE_CONCLUSION: Re f_t(z) - Re z >= -C so Re f_t(z) >= C>=1, hence rho_z>=1 and Re f_t(z)>=C on [0,1]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem:re-im-bounds, lem-c-event, step:pos-choose-C-x-y
ROUTES: -
ROUTE_FOR: -
EDGE: lem:re-im-bounds | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2125-L2125 | eqn-re-ft with s=0
EDGE: lem-c-event | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2125-L2125 | (cond-2) bounds h^-(0,t;a)>=-C
EDGE: step:pos-choose-C-x-y | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2124-L2124 | x=2C, y=7C so Re z>=2C
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Bootstrapping argument (a bound valid up to rho_z implies rho_z>=1).

NODE: step:pos-imag-part-bound
KIND: step
TITLE: Im f_t(z)<=-1 on [1,2] and hence rho_z>=2 for z in [x,y]
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2130-L2132
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2130-L2132
CONTRACT_ID: paper.step:pos-imag-part-bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: event of lem-c-event holds; rho_z>=1 and Re f_t(z)>=C on [0,1]
SOURCE_QUANTIFIERS: z in [x,y]
SOURCE_CONCLUSION: Im f_1(z)<=-2, Im f_t(z)-Im f_1(z)<=1 on [1,2], so Im f_t(z)<=-1 on [1,2] and rho_z>=2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem:re-im-bounds, lem-c-event, step:pos-real-part-lower-bound
ROUTES: -
ROUTE_FOR: -
EDGE: lem:re-im-bounds | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2130-L2131 | eqn-im-ft with (s,t)=(0,1) and (1,t)
EDGE: lem-c-event | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2130-L2131 | (cond-1) and (cond-4)
EDGE: step:pos-real-part-lower-bound | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2130-L2130 | ∣f_t∣>=1 on [0,1] justifies the Im bound on [0,1]
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Source writes Im f_1(z) = Im f_1(z) - Im z, using Im z = 0 for z in [x,y].

NODE: step:pos-segment-disjoint-L2
KIND: step
TITLE: [x,y] is disjoint from L_2
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2134-L2134
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2134-L2134
CONTRACT_ID: paper.step:pos-segment-disjoint-L2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: rho_z>=2 for each z in [x,y]
SOURCE_QUANTIFIERS: z in [x,y]
SOURCE_CONCLUSION: T_z>2 for each z in [x,y], so [x,y] cap L_2 = empty
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-endpt-cont, step:pos-imag-part-bound, defn-hulls.left
ROUTES: -
ROUTE_FOR: -
EDGE: lem-endpt-cont | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2134-L2134 | ∣f_t(z)∣->0 as t->T_z, so rho_z<T_z
EDGE: step:pos-imag-part-bound | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2134-L2134 | rho_z>=2
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2134-L2134 | L_2 = {z : T_z<=2}
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The outline at L2041 cites Remark 2.12 (remark-sigma) for the same inference; the proof itself cites Lemma 2.5. Alternate citation recorded here, no route node created (both give the same implication).

NODE: step:pos-real-part-sign-change
KIND: step
TITLE: -6C<=Re f_2(z)-Re z<=-3C so Re f_2(x)<=-C<0<C<=Re f_2(y)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2136-L2138
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2136-L2138
CONTRACT_ID: paper.step:pos-real-part-sign-change
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: rho_z>=2 for z in [x,y]; event of lem-c-event holds
SOURCE_QUANTIFIERS: z in [x,y]
SOURCE_CONCLUSION: Re f_2(x)<=2C-3C=-C and Re f_2(y)>=7C-6C=C
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem:re-im-bounds, lem-c-event, step:pos-imag-part-bound, step:pos-choose-C-x-y
ROUTES: -
ROUTE_FOR: -
EDGE: lem:re-im-bounds | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2136-L2137 | eqn-re-ft with (s,t)=(1,2) and (0,1)
EDGE: lem-c-event | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2136-L2137 | (cond-3) and (cond-2)
EDGE: step:pos-imag-part-bound | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2136-L2136 | rho_z>=2 so the bounds are valid on [0,2]
EDGE: step:pos-choose-C-x-y | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2138-L2138 | Re f_2(x) <= 2C-3C and Re f_2(y) >= 7C-6C use x=2C, y=7C
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Typo T-lem4.4: source concludes about f_1(x), f_1(y) but means f_2.

NODE: lem-disconnect-2
KIND: lemma
TITLE: Left hulls disconnect a fixed open set with positive probability
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L1960-L1963
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2160-L2195
CONTRACT_ID: paper.lem-disconnect-2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b>0 (R5), c in [-sqrt(ab),sqrt(ab)] (Sigma PSD), c>=0 after the WLOG of L1951; (f_t),(L_t),(R_t) the centered chain, left and right hulls of an SLE_Sigma driver
SOURCE_QUANTIFIERS: exists deterministic bounded open U subset C and exists t>0 (both deterministic)
SOURCE_CONCLUSION: with positive probability: U cap L_t = empty and L_t disconnects U from infinity
CONSTANT_SCOPE: U and t depend only on Sigma (a,b,c), not on the driver
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:disc-choose-U
ROUTES: -
ROUTE_FOR: -
EDGE: step:disc-choose-U | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | "this gives the lemma statement for t = T+2+K": choice of the deterministic U among U^-, U^+ with positive probability (the former edges to step:disc-independence-product and step:disc-pullback-conclusion are now consumed by step:disc-choose-U)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: as stated the lemma is trivial for U = empty (the empty set is open, bounded, disjoint from L_t and disconnected from infinity). Non-emptiness of U (U = U^- or U^+ of the proof) is implicit and is read as part of the statement; consumers (proof-a, proof-b) need it. The hypothesis c>=0 is supplied at consumers by step:wlog-c-nonneg. AUTHOR_BLOCKED (ERRATA P10): the proof as written goes through step:disc-setup, whose construction of U^+- is refuted; the statement itself is not claimed false.

NODE: step:disc-setup
KIND: step
TITLE: Choice of parameters T, eps, K, the sets U^{+-} and the four events E_1..E_4
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2161-L2177
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2161-L2177
CONTRACT_ID: paper.step:disc-setup
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: x<y from lem-pos-hits-before-neg; T>y^2/2; eps,K>0; 'left-right crossing' of an axis-parallel rectangle R is a connected S subset R meeting both vertical sides
SOURCE_QUANTIFIERS: T, eps, K, then U^- and U^+
SOURCE_CONCLUSION: U^+- deterministic open sets at distance >=2eps from the imaginary axis mapped by z -> sqrt(z^2+4T) into B_{eps/2}(x -+ 2 i eps); events E_1 (L_T within eps of imaginary axis, R_T within eps of real axis, f_T(U^+-) subset B_eps(x +- 2i eps), R_T contains a left-right crossing of [x,y]x[-eps,eps]), E_2 (L_{T,T+2} disjoint from [x,y]x[-eps,eps] and f_{T,T+2} maps any left-right crossing of it to a set containing a left-right crossing of [-eps,eps]x[-2K^{1/2}+eps,2K^{1/2}-eps]), E_3 (f_{T,T+2}(B_{3eps}(x)) at distance >eps from the imaginary axis), E_4 (L_{T+2,T+2+K} within eps of the imaginary axis and hitting every left-right crossing of [-eps,eps]x[-2K^{1/2}+eps,2K^{1/2}-eps])
CONSTANT_SCOPE: T,eps,K are fixed deterministic parameters; E_2,E_3 are only claimed for suitable eps,K
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-pos-hits-before-neg, step:line-zero-driver-chain
ROUTES: -
ROUTE_FOR: -
EDGE: lem-pos-hits-before-neg | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2161-L2161 | supplies x<y with 0<x<y<2T^{1/2} (via T>y^2/2)
EDGE: step:line-zero-driver-chain | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2165-L2165 | time-T zero-driver Loewner map z -> sqrt(z^2+4T) used to define U^+-
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: AUTHOR_BLOCKED (ERRATA P10): the construction at L2165 is refuted for x = 2C, y = 7C, not merely unstated. SOURCE_GAP: existence of non-empty open U^+- satisfying both requirements (distance >= 2 eps from the imaginary axis; mapped by z -> sqrt(z^2+4T) into B_{eps/2}(x -+ 2 i eps)) is asserted at L2165, not shown. Reviewer computation (to be confirmed by the orchestrator): the preimage of w = x -+ 2 i eps is z with z^2 = w^2-4T, |Re z| ~ 2 x eps / sqrt(4T-x^2), and the preimage of B_{eps/2}(w) has |Re z| <= ~ 2.5 x eps / sqrt(4T-x^2) as eps -> 0. A point at distance >= 2 eps from the imaginary axis therefore needs x / sqrt(4T-x^2) >~ 0.8. For the choice made in the proof of Lemma 4.4 (x = 2C, y = 7C, so x/y = 2/7) and any T > y^2/2 one has x / sqrt(4T-x^2) < 0.21 (numerically max |Re z|/eps = 0.72 at C = 1, T = 13, eps = 0.01), so U^+- would be empty. Lemma 4.4 is stated existentially ('we can choose 0<x<y'), so the proof of Lemma 4.1 may not re-pick x, y. The text also writes (B_t) for measurability; the hulls depend on U = (B, B~). Global review: confirmed. For any T with y < 2T^{1/2} the exact linearization gives max |Re z|/eps over the preimage of B_{eps/2}(x -+ 2 i eps) of about 2.5 x/sqrt(4T-x^2) < 0.7, below the required 2; the required 2 would need T <= 0.64 x^2, incompatible with y < 2T^{1/2} unless y < 1.6 x, while Lemma 4.4 forces y/x > 2 (Re f_2(z) - Re z lies in [-6C,-3C]); the preimage lies within eps of the segment [-2T^{1/2} i, 2T^{1/2} i], where L_T may lie and where the uniform closeness of f_T to z -> sqrt(z^2+4T) is not available. Dependents modeled as if the construction held: step:disc-E1-positive, step:disc-concatenation-transfer, step:disc-topological-separation, step:disc-pullback-conclusion, step:disc-choose-U, lem-disconnect-2 and everything downstream.

NODE: step:disc-E1-positive
KIND: step
TITLE: P(E_1)>0 for every T, eps>0
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2169-L2169
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2180-L2180
CONTRACT_ID: paper.step:disc-E1-positive
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: T,eps>0; parameters of step:disc-setup
SOURCE_QUANTIFIERS: T,eps>0
SOURCE_CONCLUSION: P(E_1)>0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-haus, lem-line-approx, step:disc-setup, step:right-hull-connected
ROUTES: -
ROUTE_FOR: -
EDGE: lem-haus | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2180-L2180 | cited as the source of P(E_1)>0
EDGE: lem-line-approx | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2180-L2180 | the Hausdorff/uniform closeness statements that give containment in eps-neighborhoods and f_T(U^+-) subset B_eps(x +- 2i eps) are those of Lemma 4.2
EDGE: step:disc-setup | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2169-L2169 | definition of E_1 and of U^+-
EDGE: step:right-hull-connected | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2169-L2169 | "R_T contains a left-right crossing of [x,y]x[-eps,eps]": a connected R_T Hausdorff-close to [-2T^{1/2},2T^{1/2}] supplies the crossing
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: (i) the source cites Lemma 4.3 directly; the closeness statements it needs are those of Lemma 4.2, recorded as an additional dependency; (ii) the crossing needs connectedness of R_T, now carried by step:right-hull-connected (itself a SOURCE_GAP); (iii) 'for each T, eps > 0' cannot hold for eps large compared with 2T^{1/2} - y, and the existence of U^+- is in doubt (see step:disc-setup, F6).

NODE: step:disc-E4-positive
KIND: step
TITLE: P(E_4)>0 for every K, eps>0 (by Markov property and Lemma 4.3)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2175-L2175
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2180-L2180
CONTRACT_ID: paper.step:disc-E4-positive
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K,eps>0; L_{T+2,T+2+K} is the left hull of the chain restarted at time T+2
SOURCE_QUANTIFIERS: K,eps>0 and the restart time T+2
SOURCE_CONCLUSION: P(E_4)>0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-haus, lem-line-approx, lem-connected.left, lem-markov, step:disc-setup
ROUTES: -
ROUTE_FOR: -
EDGE: lem-haus | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2180-L2180 | cited 'applied ... with K in place of T'
EDGE: lem-line-approx | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2180-L2180 | closeness of L_K to the vertical segment [-2K^{1/2} i,2K^{1/2} i]
EDGE: lem-connected.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2175-L2175 | a connected hull close to the vertical segment hits every left-right crossing of the rectangle (extractor reading: connectedness of the left hull is needed)
EDGE: lem-markov | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2179-L2179 | the restarted chain (f_{T+2,T+2+s}) has the law of a centered SLE_Sigma chain
EDGE: step:disc-setup | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2175-L2175 | definition of E_4
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The connectedness dependency is the extractor's reading; the source does not name it.

NODE: step:disc-E2E3-positive
KIND: step
TITLE: P(E_2 cap E_3)>0 for some eps,K and any T (Lemma 4.4 applied to the restarted chain)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2171-L2173
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2181-L2181
CONTRACT_ID: paper.step:disc-E2E3-positive
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: x<y from lem-pos-hits-before-neg; any T>0
SOURCE_QUANTIFIERS: exists eps,K>0 (then any T>0)
SOURCE_CONCLUSION: P(E_2 cap E_3)>0
CONSTANT_SCOPE: eps,K chosen depending only on a,b,c, x,y; independent of T
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-pos-hits-before-neg, lem-markov, step:disc-setup
ROUTES: -
ROUTE_FOR: -
EDGE: lem-pos-hits-before-neg | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2181-L2181 | applied to (f_{T,T+t}) instead of (f_t): L_{T,T+2} cap [x,y]=empty and Re f_{T,T+2}(x)<0<Re f_{T,T+2}(y)
EDGE: lem-markov | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2181-L2181 | restarted chain f_{T,T+t} has the law of a centered SLE_Sigma chain, so Lemma 4.4 applies for every T
EDGE: step:disc-setup | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2171-L2171 | definition of E_2,E_3
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: Lemma 4.4 gives disjointness of the segment [x,y] from L_2 and a sign change of Re f_2 on the endpoints. E_2 requires (a) disjointness from the thickened rectangle [x,y]x[-eps,eps], (b) that the image of every left-right crossing of this rectangle contains a left-right crossing of [-eps,eps]x[-2K^{1/2}+eps,2K^{1/2}-eps] (needs continuity/compactness and a choice of eps,K, and eps small compared with |Re f_2(x)|, |Re f_2(y)|, which Lemma 4.4's statement does not quantify). E_3 needs B_{3eps}(x) cap L_{T,T+2} = empty (domain of f_{T,T+2}) and a continuity estimate near x. This bridge, including the choice 'for some eps,K', is not argued.

NODE: step:disc-independence-product
KIND: step
TITLE: E_1, E_2 cap E_3, E_4 are independent, hence P(E_1 cap E_2 cap E_3 cap E_4)>0
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2179-L2181
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2179-L2181
CONTRACT_ID: paper.step:disc-independence-product
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E_1 measurable w.r.t. U on [0,T]; E_2 cap E_3 w.r.t. U_t-U_T on [T,T+2]; E_4 w.r.t. U_t-U_{T+2} on [T+2,T+2+K]
SOURCE_QUANTIFIERS: one choice of eps,K,T
SOURCE_CONCLUSION: P(E_1 cap E_2 cap E_3 cap E_4)>0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:disc-E1-positive, step:disc-E4-positive, step:disc-E2E3-positive, defn-sle, eqn-conc
ROUTES: -
ROUTE_FOR: -
EDGE: step:disc-E1-positive | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2180-L2180 | P(E_1)>0
EDGE: step:disc-E4-positive | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2180-L2180 | P(E_4)>0
EDGE: step:disc-E2E3-positive | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2181-L2181 | P(E_2 cap E_3)>0
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2179-L2179 | independent increments of the driver on disjoint time intervals
EDGE: eqn-conc | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2179-L2179 | f_{t,s+t} is the chain driven by U(.+t)-U(t), a function of the increments after t
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Quantifier closure: eps,K are chosen first (for E_2 cap E_3), then T is arbitrary for the others. The source writes (B_t) for measurability; the chain depends on both B and B~.

NODE: step:disc-concatenation-transfer
KIND: step
TITLE: On E_1..E_4, L_{T,T+2+K} meets S but not B_{3eps}(x)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2183-L2194
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2183-L2194
CONTRACT_ID: paper.step:disc-concatenation-transfer
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E_1..E_4 hold for some eps,K,T
SOURCE_QUANTIFIERS: outcome of the events
SOURCE_CONCLUSION: choose connected S subset R_T avoiding f_T(U^+-) crossing [x,y]x[-eps,eps]; f_{T,T+2}(S) crosses the second rectangle; L_{T+2,T+2+K} meets f_{T,T+2}(S) but not f_{T,T+2}(B_{3eps}(x)); hence L_{T,T+2+K} meets S but not B_{3eps}(x)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-conc, step:disc-setup
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-conc | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | concatenation at time 2 for the chain (f_{T,T+s}) transfers hits of L_{T+2,T+2+K} through f_{T,T+2}
EDGE: step:disc-setup | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2183-L2193 | definitions of E_1..E_4
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Typo: the third bullet writes f_{T+2}(B_{3eps}(x)); read f_{T,T+2}. SOURCE_GAP: (i) 'L_{T,T+2+K} does not intersect B_{3eps}(x)' needs L_{T,T+2} cap B_{3eps}(x) = empty (this is also the domain condition for f_{T,T+2}(B_{3eps}(x)) in E_3), but E_2 only gives L_{T,T+2} disjoint from the thin rectangle [x,y]x[-eps,eps], which does not contain B_{3eps}(x). (ii) The transfer via (2.3) also involves the term R_{T,T+2} in L_{T,T+2+K} = L_{T,T+2} cup f_{T,T+2}^{-1}(L_{T+2,T+2+K}\R_{T,T+2}); this is not discussed. (iii) 'S avoids f_T(U^+-)' is automatic only because f_T(U^+-) lies in the range of f_T, i.e. needs U^+- cap L_T = empty.

NODE: step:disc-topological-separation
KIND: step
TITLE: L_{T,T+2+K} cup R_T disconnects one of f_T(U^+-) from infinity without hitting it
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194
CONTRACT_ID: paper.step:disc-topological-separation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: L_{T,T+2+K} meets S and misses B_{3eps}(x); R_T within eps of the real axis; f_T(U^+-) subset B_eps(x +- 2i eps) subset B_{3eps}(x) minus R_T
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: one of f_T(U^-), f_T(U^+) is disconnected from infinity by L_{T,T+2+K} cup R_T and disjoint from it
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:disc-concatenation-transfer, def-disconnect, defn-hulls.right, step:disc-setup
ROUTES: -
ROUTE_FOR: -
EDGE: step:disc-concatenation-transfer | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | L_{T,T+2+K} meets S but not B_{3eps}(x)
EDGE: def-disconnect | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | notion of disconnection from infinity
EDGE: defn-hulls.right | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | R_T contained in the eps-neighborhood of the real axis and contains the crossing S
EDGE: step:disc-setup | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | E_1: R_T within eps of the real axis and f_T(U^+-) subset B_eps(x +- 2i eps) subset B_{3eps}(x) minus R_T
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: 'By topological considerations' (planar topology: the crossing S of R_T joined with the hull L_{T,T+2+K} crossing it, together with the confinement of R_T, separates one of the two sets above/below the real axis from infinity) is asserted without proof.

NODE: step:disc-pullback-conclusion
KIND: step
TITLE: Pull back the disconnection through f_T by concatenation: L_{T+2+K} disconnects U^+- avoiding it
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194
CONTRACT_ID: paper.step:disc-pullback-conclusion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: L_{T,T+2+K} cup R_T disconnects f_T(U^+-) from infinity and avoids it; U^+- cap L_T = empty (from E_1)
SOURCE_QUANTIFIERS: t = T+2+K
SOURCE_CONCLUSION: U cap L_t = empty and L_t disconnects U from infinity for t=T+2+K and U=U^- or U^+
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:disc-topological-separation, step:disc-concat-disconnect-general, step:disc-setup
ROUTES: -
ROUTE_FOR: -
EDGE: step:disc-topological-separation | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | disconnection of f_T(U^+-) by L_{T,T+2+K} cup R_T
EDGE: step:disc-concat-disconnect-general | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | "By the concatenation property": instance s=T, t=2+K, point in U^+-
EDGE: step:disc-setup | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | E_1 and the choice of U^+-: U^+- cap L_T = empty, so f_T is defined on U^+-
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Carrier change z <-> f_T(z); an instance of step:disc-concat-disconnect-general. Which of U^-, U^+ occurs is random; the deterministic choice is made in step:disc-choose-U (the earlier reading 'U is the deterministic union' is withdrawn).

NODE: step:disc-a-q-scale-invariance
KIND: step
TITLE: q(z)=q(z/|z|) by scale invariance
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2201-L2205
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2205-L2205
CONTRACT_ID: paper.step:disc-a-q-scale-invariance
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z in C minus {0}; q(z)=P((L_t) disconnects z from infinity before T_z)
SOURCE_QUANTIFIERS: z in C minus {0}
SOURCE_CONCLUSION: q(z)=q(z/|z|)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-scaling, eqn-scale, defn-hulls.left, def-disconnect
ROUTES: -
ROUTE_FOR: -
EDGE: lem-scaling | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2205-L2205 | law of the chain is invariant under r^{-1} f_{r^2 t}(r.)
EDGE: eqn-scale | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2205-L2205 | hulls and absorbing times scale: L_t^{rU(./r^2)} = r L_{t/r^2}
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2203-L2203 | event defined through left hulls and T_z
EDGE: def-disconnect | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2205-L2205 | disconnection from infinity is preserved by the scaling z -> z/∣z∣
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The event 'disconnects z from infinity before time T_z' is read as: exists t<T_z (equivalently z not in L_t) with L_t disconnecting z; z not in L_t iff T_z>t.

NODE: step:disc-a-positive-measure-set
KIND: step
TITLE: The set of unit z with q(z)>0 has positive 1-d Lebesgue measure
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2206-L2206
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2206-L2206
CONTRACT_ID: paper.step:disc-a-positive-measure-set
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U, t from lem-disconnect-2 (U nonempty, bounded, open)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: {|z|=1 : q(z)>0} has positive Lebesgue measure
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-disconnect-2, step:disc-a-q-scale-invariance, def-disconnect, defn-hulls.left, step:zero-in-left-hull
ROUTES: -
ROUTE_FOR: -
EDGE: lem-disconnect-2 | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2206-L2206 | positive probability that L_t disconnects U from infinity avoiding it
EDGE: step:disc-a-q-scale-invariance | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2206-L2206 | q(w)>0 for w in U transfers to z/∣z∣; the radial projection of a non-empty open set is a non-empty open arc set
EDGE: def-disconnect | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2206-L2206 | w in U with U cap L_t = empty is disconnected before T_w
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2206-L2206 | w not in L_t iff T_w>t
EDGE: step:zero-in-left-hull | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2206-L2206 | 0 in L_t for all t, so U cap L_t = empty gives 0 not in U and z/∣z∣ is defined on U
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: needs U non-empty (see lem-disconnect-2) and 0 not in U (0 in L_t for all t, so U cap L_t = empty excludes 0). The inference from Lemma 4.1 to positive measure of the set is a one-line assertion.

NODE: step:disc-a-hit-Lambda
KIND: step
TITLE: A closed positive-measure set Lambda' is hit by e^{i theta^_tz(z)} with positive probability
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207
CONTRACT_ID: paper.step:disc-a-hit-Lambda
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z with |z|=1; Lambda' closed subset of Lambda={|z|=1: q(z)>0} of positive measure; tau = first t~ with e^{i theta^_t~(z)} in Lambda'
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: P(tau<infinity)>0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-polar, defn-sigma, def-arg, ext:girsanov, step:disc-a-positive-measure-set
ROUTES: -
ROUTE_FOR: -
EDGE: lem-polar | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207 | the SDE (2.25) for theta^_t~ in sigma-time (re-use of Prop 3.2(b) L1801-1802)
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207 | sigma-time parametrization
EDGE: def-arg | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207 | argument process theta^
EDGE: ext:girsanov | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207 | Girsanov (as in Prop 3.2(b) L1802) reduces to a diffusion hitting positive-measure sets
EDGE: step:disc-a-positive-measure-set | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207 | Lambda has positive measure so such Lambda' exists
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Models the reused first half of the proof of Prop 3.2(b) (L1799-1802), as the source says 'exactly as in'. The slice C counterpart steps are not named here; slice C owns ext:girsanov. SOURCE_GAP inherited from Prop 3.2(b): the Girsanov hitting argument is only sketched.

NODE: step:disc-a-markov-restart
KIND: step
TITLE: Conditional probability given F at sigma_z(tau) is at least q(e^{i theta^_tau(z)})
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207
CONTRACT_ID: paper.step:disc-a-markov-restart
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: tau as above; event tau<infinity
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: on {tau<infinity}, P(disconnect z before T_z | F_{sigma_z(tau)}) >= q(e^{i theta^_tau(z)})
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-scaling, lem-markov, defn-sigma, remark-sigma, step:disc-a-q-scale-invariance, step:disc-concat-disconnect-general
ROUTES: -
ROUTE_FOR: -
EDGE: lem-scaling | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207 | rescale the restarted chain to unit-circle start (Prop 3.2(b) L1804)
EDGE: lem-markov | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207 | domain Markov property at the stopping time sigma_z(tau)
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207 | sigma_z(tau) is a stopping time for the driver filtration
EDGE: remark-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207 | sigma_z maps (0,infinity) into (0,T_z): z is not in L_{sigma_z(tau)} so f_{sigma_z(tau)}(z) exists
EDGE: step:disc-a-q-scale-invariance | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207 | q(f_s(z)) = q(f_s(z)/∣f_s(z)∣) = q(e^{i theta^_tau(z)}) for the restarted point
EDGE: step:disc-concat-disconnect-general | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207 | disconnection of f_s(z) by the restarted left hull (together with R_s) pulls back to disconnection of z by the original hull
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: In Prop 3.2(b) the event lim dist(z,L_t)>0 is determined by the restarted chain. The disconnection event is not (disconnection may occur earlier, and the transfer needs concatenation (2.3)), so 'exactly as in Prop 3.2(b)' glosses a change from equality to inequality. The pullback step is the extractor's modeling of that bridge.

NODE: step:disc-a-q-positive-all-z
KIND: step
TITLE: q(z)>0 for every z in C minus {0}
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207
CONTRACT_ID: paper.step:disc-a-q-positive-all-z
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: q(z)>0 on a set of positive measure of the unit circle
SOURCE_QUANTIFIERS: z in C minus {0}
SOURCE_CONCLUSION: q(z)>0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:disc-a-hit-Lambda, step:disc-a-markov-restart, step:disc-a-q-scale-invariance
ROUTES: -
ROUTE_FOR: -
EDGE: step:disc-a-hit-Lambda | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207 | P(tau<infinity)>0
EDGE: step:disc-a-markov-restart | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207 | q(z)>= E[1_{tau<inf} q(e^{i theta^_tau})]>0 since e^{i theta^_tau} in Lambda'
EDGE: step:disc-a-q-scale-invariance | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2207 | reduction from C minus {0} to the unit circle
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Mirrors the Lambda-claim of Prop 3.2(b) (L1799-1804).

NODE: step:disc-a-open-condition
KIND: step
TITLE: Disconnection before T_z is stable under small perturbation of the point
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2209-L2209
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2209-L2209
CONTRACT_ID: paper.step:disc-a-open-condition
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z in C minus {0}; on the event that (L_t) disconnects z from infinity before T_z
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: exists random r>0 such that for each w in B_r(z), (L_t) disconnects w before T_w
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: def-disconnect, defn-hulls.left, step:hull-closed
ROUTES: -
ROUTE_FOR: -
EDGE: def-disconnect | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2209-L2209 | z lies in a bounded component of the open set C minus L_t, so do nearby points
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2209-L2209 | w not in L_t iff T_w>t
EDGE: step:hull-closed | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2209-L2209 | C minus L_t is open, so a ball around z stays inside the same bounded component and outside L_t
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Asserted without proof; follows from elementary topology if L_t is closed (closedness of L_t is not cited: uncertain). This replaces the Koebe-distortion openness argument of Prop 3.2(b).

NODE: step:disc-a-uniform-lower-bound
KIND: step
TITLE: There is q_*>0 with q(z)>=q_* for every z in C minus {0}
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2209-L2210
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2209-L2210
CONTRACT_ID: paper.step:disc-a-uniform-lower-bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: q(z)>0 for all z; random r>0 from step:disc-a-open-condition
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: exists q_*>0: q(z)>=q_* for all z in C minus {0}
CONSTANT_SCOPE: q_* depends only on Sigma
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:disc-a-q-positive-all-z, step:disc-a-open-condition, step:disc-a-q-scale-invariance
ROUTES: -
ROUTE_FOR: -
EDGE: step:disc-a-q-positive-all-z | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2207-L2210 | positivity of q at every point of the circle
EDGE: step:disc-a-open-condition | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2209-L2209 | gives a deterministic eps with q(w)>=q(z)/2 on B_eps(z) (continuity of probability)
EDGE: step:disc-a-q-scale-invariance | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2210-L2210 | extend the bound from the unit circle to C minus {0}
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Compactness argument: cover the unit circle by finitely many balls B_eps(z_i). Step also contains the passage from random r to deterministic eps (not spelled out).

NODE: eqn-disconnect-mart
KIND: display
TITLE: Conditional lower bound P(disconnect z before T_z | F_{sigma_z(t~)}) >= q_*
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-disconnect-mart@L2212-L2216
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-disconnect-mart@L2212-L2216
CONTRACT_ID: paper.eqn-disconnect-mart
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: q_*>0 uniform; sigma_z the time change of Definition 2.9; z in C minus {0}
SOURCE_QUANTIFIERS: z in C minus {0}; t~>=0
SOURCE_CONCLUSION: P((L_t) disconnects z from infinity before T_z | F_{sigma_z(t~)}) >= q_* for all t~>=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-scaling, lem-markov, defn-sigma, remark-sigma, step:disc-a-uniform-lower-bound, step:disc-concat-disconnect-general
ROUTES: -
ROUTE_FOR: -
EDGE: lem-scaling | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2212-L2212 | scale invariance of the restarted chain
EDGE: lem-markov | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2212-L2212 | strong Markov property at sigma_z(t~)
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2216-L2216 | sigma_z as in Definition 2.9
EDGE: step:disc-a-uniform-lower-bound | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2212-L2212 | the uniform bound q_*
EDGE: remark-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2212-L2212 | sigma_z(t~) < T_z, so the restart point f_{sigma_z(t~)}(z) exists
EDGE: step:disc-concat-disconnect-general | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2212-L2212 | disconnection by the restarted left hull pulls back to disconnection of z (inequality, not equality)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: KIND display: (eqn-disconnect-mart). The source writes 'for each z in C'; read z in C minus {0} (R4: sigma_0 undefined). Same SOURCE_GAP note on the restart as in step:disc-a-markov-restart.

NODE: step:disc-a-martingale-limit-one
KIND: step
TITLE: The indicator of the disconnection event is a.s. 1 by martingale convergence
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2217-L2217
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2217-L2217
CONTRACT_ID: paper.step:disc-a-martingale-limit-one
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: conditional bound >= q_* for all t~
SOURCE_QUANTIFIERS: z in C minus {0}
SOURCE_CONCLUSION: a.s. 1_{disconnect z before T_z} = 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: ext:martingale-convergence, remark-sigma, eqn-disconnect-mart
ROUTES: -
ROUTE_FOR: -
EDGE: ext:martingale-convergence | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2217-L2217 | Levy upward convergence of the conditional probabilities
EDGE: remark-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2217-L2217 | sigma_z(t~) increases to T_z so the filtration F_{sigma_z(t~)} exhausts the information needed for the event
EDGE: eqn-disconnect-mart | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2214-L2217 | lower bound q_* passes to the limit
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Same 'martingale convergence plus 0-1' step as in Prop 3.2(b) L1815-1816; measurability of the event with respect to the union of the sigma_z-time filtrations is implicit.

NODE: thm-disconnects#proof-a
KIND: step
TITLE: Proof assembly of Theorem 1.10(a) from Lemma 4.1
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2199-L2217
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2199-L2217
CONTRACT_ID: paper.thm-disconnects#proof-a
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b>0 (R5), c in [-sqrt(ab),sqrt(ab)]; z in C minus {0} (R4)
SOURCE_QUANTIFIERS: z in C minus {0}
SOURCE_CONCLUSION: a.s. exists t>0 with z not in L_t and L_t disconnects z from infinity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:wlog-c-nonneg, step:disc-a-martingale-limit-one, defn-hulls.left
ROUTES: -
ROUTE_FOR: -
EDGE: step:wlog-c-nonneg | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2206-L2206 | Lemma 4.1 (and through it Lemma 4.6) is only proved for c>=0, so the Lemma 4.1 invocation presupposes the section's WLOG reduction
EDGE: step:disc-a-martingale-limit-one | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2217-L2217 | final 0-1 argument gives almost sure disconnection before T_z
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2201-L2203 | 'disconnects z from infinity before T_z' means exists t<T_z with z not in L_t
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Step node consumed by root thm-disconnects.a. The source says the proof is 'very similar to' Prop 3.2(b); the reused steps are modeled explicitly by step:disc-a-* (no dependence on slice C step IDs). The source states (a) for each z in C; R4 restricts to z != 0.

NODE: step:disc-b-scale-invariance
KIND: step
TITLE: P(set disconnected by L_t has non-empty interior) is independent of t
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2221-L2221
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2221-L2221
CONTRACT_ID: paper.step:disc-b-scale-invariance
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: t>0
SOURCE_QUANTIFIERS: t>0
SOURCE_CONCLUSION: P(interior of {points disconnected from infinity by L_t} non-empty) does not depend on t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-scaling, eqn-scale, def-disconnect, defn-hulls.left
ROUTES: -
ROUTE_FOR: -
EDGE: lem-scaling | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2221-L2221 | law invariance under r^{-1} f_{r^2 t}(r.)
EDGE: eqn-scale | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2221-L2221 | L_t^{rU(./r^2)} = r L_{t/r^2}
EDGE: def-disconnect | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2221-L2221 | disconnected set scales with the hull
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2221-L2221 | left hull L_t
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Scaling maps disconnected sets to scaled sets, preserving non-empty interior.

NODE: step:disc-b-positive-for-all-t
KIND: step
TITLE: That probability is positive for every t>0
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2222-L2222
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2222-L2222
CONTRACT_ID: paper.step:disc-b-positive-for-all-t
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U,t_0 from lem-disconnect-2
SOURCE_QUANTIFIERS: t>0
SOURCE_CONCLUSION: P(set disconnected by L_t has non-empty interior)>0 for every t>0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-disconnect-2, step:disc-b-scale-invariance, def-disconnect
ROUTES: -
ROUTE_FOR: -
EDGE: lem-disconnect-2 | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2222-L2222 | positive probability that L_{t_0} disconnects the non-empty open set U
EDGE: step:disc-b-scale-invariance | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2222-L2222 | transfers positivity from t_0 to every t>0
EDGE: def-disconnect | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2222-L2222 | U subset set disconnected by L_{t_0}, U open and non-empty
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Lemma 4.1 provides one t_0; the passage to every t>0 uses the scale invariance step (source compresses both). Needs U non-empty (see lem-disconnect-2).

NODE: step:disc-b-blumenthal
KIND: step
TITLE: Almost surely there are arbitrarily small times t with non-empty interior of the disconnected set
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2223-L2223
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2223-L2223
CONTRACT_ID: paper.step:disc-b-blumenthal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: P(A_t)=p>0 for all t, A_t = {interior of set disconnected by L_t non-empty}
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: a.s. for every n there is t<1/n with A_t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:disc-b-positive-for-all-t, ext:blumenthal, defn-sle
ROUTES: -
ROUTE_FOR: -
EDGE: step:disc-b-positive-for-all-t | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2222-L2223 | P(A_{t_n})>=p for t_n->0, so P(limsup A_{t_n})>=p>0
EDGE: ext:blumenthal | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2223-L2223 | the limsup event is in the germ sigma-field, hence has probability 0 or 1
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2223-L2223 | filtration of the driving Brownian motion
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Source typo: 'for the set' read 'such that the set'. Measurability of the event in the germ sigma-field (L_t is F_t-measurable) is implicit.

NODE: step:disc-b-monotone-extension
KIND: step
TITLE: Monotonicity extends the property from small times to all times
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2224-L2224
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2224-L2224
CONTRACT_ID: paper.step:disc-b-monotone-extension
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: arbitrarily small t with A_t; left hulls non-decreasing
SOURCE_QUANTIFIERS: t>0
SOURCE_CONCLUSION: A_s holds for every s>0 a.s.
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:disc-b-blumenthal, claim:hulls-monotone, def-disconnect
ROUTES: -
ROUTE_FOR: -
EDGE: step:disc-b-blumenthal | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2224-L2224 | small times t_n with A_{t_n}
EDGE: claim:hulls-monotone | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2224-L2224 | 'the left hulls are non-decreasing'
EDGE: def-disconnect | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2224-L2224 | enlarging the hull enlarges the disconnected set; subsets of L_t count as disconnected
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Quantifier closure: a.s. simultaneously for all t>0 (not for each fixed t).

NODE: thm-disconnects#proof-b
KIND: step
TITLE: Proof assembly of Theorem 1.10(b) from Lemma 4.1
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2220-L2224
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2220-L2224
CONTRACT_ID: paper.thm-disconnects#proof-b
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b>0 (R5), c in [-sqrt(ab),sqrt(ab)]
SOURCE_QUANTIFIERS: a.s.; for all t>0
SOURCE_CONCLUSION: the set of points disconnected from infinity by L_t has non-empty interior
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:wlog-c-nonneg, step:disc-b-monotone-extension
ROUTES: -
ROUTE_FOR: -
EDGE: step:wlog-c-nonneg | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2222-L2222 | Lemma 4.1 is only proved for c>=0, so the Lemma 4.1 invocation presupposes the section's WLOG reduction
EDGE: step:disc-b-monotone-extension | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2224-L2224 | conclusion for every t>0 simultaneously
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Step node consumed by root thm-disconnects.b. Independent of proof-a (R17).

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
EDGE: step:disc-independence-product | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | P(E_1 cap ... cap E_4) > 0 is what lets one of the two sets be chosen
EDGE: step:disc-pullback-conclusion | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | on the four events one of U^-, U^+ is avoided and disconnected by L_{T+2+K}
EDGE: step:disc-setup | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | U^+- are deterministic, bounded, open (and needed non-empty)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: reviewer-D/sonnet (proposed by reviewer; orchestrator to adopt)
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Quantifier closure / witness choice. SOURCE_GAP: the source says only 'this gives the lemma statement for t = T+2+K'. The disconnected set is random (U^- or U^+ depending on omega), and the lemma needs one deterministic U; P(A^-) + P(A^+) >= P(E_1 cap ... cap E_4) > 0 selects a sign. The extractor's reading 'U is the deterministic union' (NOTE of step:disc-pullback-conclusion) is not valid: on the event only one of the two sets is disconnected, so the union is not. Non-emptiness of U^+- depends on step:disc-setup (see F6).

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
DEPS: eqn-conc, def-disconnect, defn-hulls.left, defn-hulls.right, claim:gt-conformal, step:hulls-compact
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-conc | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | L_{s+t} = L_s cup f_s^{-1}(L_{s,s+t}\R_s); f_s maps C\L_s into C\R_s
EDGE: def-disconnect | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | disconnection from infinity and disjointness
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | L_{s+t}, L_s, z not in L_{s+t} iff T_z > s+t
EDGE: defn-hulls.right | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | R_s is the complement of the range of f_s, so f_s(z) not in R_s
EDGE: claim:gt-conformal | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | f_s: C\L_s -> C\R_s is a conformal bijection with f_s(w) - w bounded near infinity, so the bounded components of C\L_{s+t} correspond to the bounded components of C\(L_{s,s+t} u R_s)
EDGE: step:hulls-compact | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L2194-L2194 | L_s, R_s, L_{s,s+t} compact, so a component of the complement is unbounded iff its image is
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: reviewer-D/sonnet (proposed by reviewer; orchestrator to adopt)
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: the source states this transfer only inside the proof of Lemma 4.1 ('By the concatenation property (2.3)', instance s = T, point in U^+-) and again, tacitly, as 'exactly as in the proof of Proposition 3.2(b)' at L2207/L2212 with s = sigma_z(tau) or sigma_z(t~) and an arbitrary z. The general form is the reused claim; it is the inequality (not the equality of Prop 3.2(b)) because disconnection may already occur before s.


## Coverage

ITEM: inv:heading:L1947
KIND: heading
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#heading:L1947@L1947-L1947
DISPOSITION: EXCLUDED
REASON: structural heading (section title); its theorem is carried by nodes below
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:lem-disconnect-2
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-disconnect-2@L1960-L1963
DISPOSITION: NODE lem-disconnect-2
REASON: Lemma 4.1 statement
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:item-behavior-a
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#item-behavior-a@L1971-L1971
DISPOSITION: EXCLUDED
REASON: heuristic outline of the strategy (property (a)); formalized in the proof by events E_1..E_4 (steps step:disc-setup, step:disc-E1-positive); not an independent claim
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:item-behavior-b
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#item-behavior-b@L1974-L1974
DISPOSITION: EXCLUDED
REASON: heuristic outline of the strategy (property (b)); formalized by E_2..E_4 (steps step:disc-E2E3-positive, step:disc-E4-positive); not an independent claim
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:lem-line-approx
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-line-approx@L1991-L1993
DISPOSITION: NODE lem-line-approx
REASON: Lemma 4.2 statement
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:lem-haus
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-haus@L1998-L2009
DISPOSITION: NODE lem-haus
REASON: Lemma 4.3 statement
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:proof:L2010
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L2010@L2010-L2020
DISPOSITION: NODE step:haus-maps-converge, step:haus-subsequence-limit-contained, step:haus-limit-conformal-extension, step:haus-contradiction-L-t, step:haus-subsubsequence-closure, step:haus-right-hull-reduction, lem-haus
REASON: proof of Lemma 4.3 split into the cited convergence, the subsequence/containment step, the normal-family extension, the contradiction, the subsubsequence closure and the right-hull reduction
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:cite:L2011:lawler-book
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L2011:lawler-book@L2011-L2011
DISPOSITION: NODE ext:loewner-convergence
REASON: Lawler Prop 4.43 invoked by the proof of Lemma 4.3
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:proof:L2022
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L2022@L2022-L2025
DISPOSITION: NODE step:line-zero-driver-chain, step:line-small-driver-positive, step:line-apply-haus, lem-line-approx
REASON: proof of Lemma 4.2
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:lem-pos-hits-before-neg
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-pos-hits-before-neg@L2036-L2039
DISPOSITION: NODE lem-pos-hits-before-neg
REASON: Lemma 4.4 statement
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:eqn-re-ft.2
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-re-ft.2@L2043-L2067
DISPOSITION: NODE lem:re-im-bounds
REASON: unlabeled Lemma 4.5 (spec ID lem:re-im-bounds)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:eqn-re-ft
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-re-ft@L2055-L2055
DISPOSITION: NODE lem:re-im-bounds
REASON: display (eqn-re-ft) is part of the statement of Lemma 4.5
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:eqn-im-ft
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-im-ft@L2060-L2060
DISPOSITION: NODE lem:re-im-bounds
REASON: display (eqn-im-ft) is part of the statement of Lemma 4.5
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:proof:L2069
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L2069@L2069-L2077
DISPOSITION: NODE step:re-im-ft-sde, step:re-im-drift-bound, lem:re-im-bounds
REASON: proof of Lemma 4.5
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:eqn-re-im-ft
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-re-im-ft@L2072-L2072
DISPOSITION: NODE step:re-im-ft-sde
REASON: SDEs for real and imaginary parts
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:cond-2.2
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cond-2.2@L2082-L2103
DISPOSITION: NODE lem-c-event
REASON: Lemma 4.6 statement (spec ID lem-c-event)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:cond-2
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cond-2@L2085-L2085
DISPOSITION: NODE lem-c-event
REASON: display condition inside the statement of Lemma 4.6
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:cond-3
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cond-3@L2090-L2090
DISPOSITION: NODE lem-c-event
REASON: display condition inside the statement of Lemma 4.6
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:cond-1
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cond-1@L2094-L2094
DISPOSITION: NODE lem-c-event
REASON: display condition inside the statement of Lemma 4.6
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:cond-4
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cond-4@L2099-L2099
DISPOSITION: NODE lem-c-event
REASON: display condition inside the statement of Lemma 4.6
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:proof:L2105
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L2105@L2105-L2108
DISPOSITION: NODE step:c-event-E1, step:c-event-E2, step:c-event-combine, lem-c-event
REASON: proof of Lemma 4.6
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:proof:L2120
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L2120@L2120-L2139
DISPOSITION: NODE step:pos-choose-C-x-y, step:pos-real-part-lower-bound, step:pos-imag-part-bound, step:pos-segment-disjoint-L2, step:pos-real-part-sign-change, lem-pos-hits-before-neg
REASON: proof of Lemma 4.4
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:proof:L2160
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L2160@L2160-L2195
DISPOSITION: NODE step:disc-setup, step:disc-E1-positive, step:right-hull-connected, step:disc-E4-positive, step:disc-E2E3-positive, step:disc-independence-product, step:disc-concatenation-transfer, step:disc-topological-separation, step:disc-pullback-conclusion, step:disc-concat-disconnect-general, step:disc-choose-U, lem-disconnect-2
REASON: proof of Lemma 4.1
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:proof:L2199
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L2199@L2199-L2225
DISPOSITION: NODE thm-disconnects#proof-a, thm-disconnects#proof-b, step:disc-a-q-scale-invariance, step:disc-a-positive-measure-set, step:disc-a-hit-Lambda, step:disc-a-markov-restart, step:disc-a-q-positive-all-z, step:disc-a-open-condition, step:disc-a-uniform-lower-bound, eqn-disconnect-mart, step:disc-a-martingale-limit-one, step:disc-concat-disconnect-general, step:disc-b-scale-invariance, step:disc-b-positive-for-all-t, step:disc-b-blumenthal, step:disc-b-monotone-extension
REASON: proof of Theorem 1.10: assembly nodes proof-a and proof-b with their step nodes
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:eqn-disconnect-mart
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-disconnect-mart@L2213-L2213
DISPOSITION: NODE eqn-disconnect-mart
REASON: display (eqn-disconnect-mart)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:heading:L2230
KIND: heading
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#heading:L2230@L2230-L2230
DISPOSITION: EXCLUDED
REASON: Section 5 open problems: excluded (R2, spec section 7); feeds no root
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:ques:L2237
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#ques:L2237@L2237-L2239
DISPOSITION: EXCLUDED
REASON: Section 5 open problems: excluded (R2, spec section 7); feeds no root
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:cite:L2242:bp-lqg-notes
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L2242:bp-lqg-notes@L2242-L2242
DISPOSITION: EXCLUDED
REASON: Section 5 open problems: excluded (R2, spec section 7); feeds no root (bibliographic citation)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:cite:L2242:shef-zipper
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L2242:shef-zipper@L2242-L2242
DISPOSITION: EXCLUDED
REASON: Section 5 open problems: excluded (R2, spec section 7); feeds no root (bibliographic citation)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:cite:L2242:ss-contour
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L2242:ss-contour@L2242-L2242
DISPOSITION: EXCLUDED
REASON: Section 5 open problems: excluded (R2, spec section 7); feeds no root (bibliographic citation)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:ques:L2246
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#ques:L2246@L2246-L2248
DISPOSITION: EXCLUDED
REASON: Section 5 open problems: excluded (R2, spec section 7); feeds no root
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:cite:L2252:wang-ld-survey
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L2252:wang-ld-survey@L2252-L2252
DISPOSITION: EXCLUDED
REASON: Section 5 open problems: excluded (R2, spec section 7); feeds no root (bibliographic citation)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:ques:L2254
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#ques:L2254@L2254-L2263
DISPOSITION: EXCLUDED
REASON: Section 5 open problems: excluded (R2, spec section 7); feeds no root
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:cite:L2269:zhan-duality1
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L2269:zhan-duality1@L2269-L2269
DISPOSITION: EXCLUDED
REASON: Section 5 open problems: excluded (R2, spec section 7); feeds no root (bibliographic citation)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:ques:L2271
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#ques:L2271@L2271-L2273
DISPOSITION: EXCLUDED
REASON: Section 5 open problems: excluded (R2, spec section 7); feeds no root
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:cite:L2275:lawler-werness-multipoint
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L2275:lawler-werness-multipoint@L2275-L2275
DISPOSITION: EXCLUDED
REASON: Section 5 open problems: excluded (R2, spec section 7); feeds no root (bibliographic citation)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:ques-transient
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#ques-transient@L2277-L2279
DISPOSITION: EXCLUDED
REASON: Section 5 open problems: excluded (R2, spec section 7); feeds no root
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:cite:L2283:beffara-dim
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L2283:beffara-dim@L2283-L2283
DISPOSITION: EXCLUDED
REASON: Section 5 open problems: excluded (R2, spec section 7); feeds no root (bibliographic citation)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:ques:L2285
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#ques:L2285@L2285-L2293
DISPOSITION: EXCLUDED
REASON: Section 5 open problems: excluded (R2, spec section 7); feeds no root
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:ques:L2299
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#ques:L2299@L2299-L2301
DISPOSITION: EXCLUDED
REASON: Section 5 open problems: excluded (R2, spec section 7); feeds no root
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:L1950:wlog
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L1950:wlog@L1950-L1951
DISPOSITION: NODE step:wlog-c-nonneg
REASON: WLOG c>=0 sentence: represented by the slice-A node step:wlog-c-nonneg (cross-slice); consumed by thm-disconnects#proof-a, #proof-b and step:c-event-E2
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:L1953:notation
KIND: definition
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L1953:notation@L1953-L1956
DISPOSITION: EXCLUDED
REASON: notation for rectangles [x,y]x[x',y'] only; no mathematical claim
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:L1966:outline
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L1966:outline@L1966-L1977
DISPOSITION: EXCLUDED
REASON: informal proof strategy for Lemma 4.1 (properties (a),(b), 'Properties (a) and (b) together imply ...'); the rigorous content is in the proof of Lemma 4.1 (L2160-2195)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:L2027:outline-b
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L2027:outline-b@L2027-L2034
DISPOSITION: EXCLUDED
REASON: informal outline of how property (b) is obtained (two forcing conditions); formalized by events E_2..E_4 in the proof of Lemma 4.1
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:L2041:reduction
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L2041:reduction@L2041-L2041
DISPOSITION: NODE step:pos-segment-disjoint-L2
REASON: outline remark that |f_t(z)|>1 on [0,2] implies [x,y] disjoint from L_2 by Remark 2.12: captured as step:pos-segment-disjoint-L2 (alternate citation of remark-sigma in its NOTE)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:L2162:def-crossing
KIND: definition
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L2162:def-crossing@L2162-L2162
DISPOSITION: NODE step:disc-setup
REASON: definition of left-right crossing, used in events E_1..E_4
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-D/sonnet
REVIEWER: -

ITEM: inv:L2023:bm-support
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L2023:bm-support@L2023-L2023
DISPOSITION: NODE ext:bm-support
REASON: 'The driving Brownian motion has a positive chance to be arbitrarily close to 0 on [0,T]' is an uncited standard (support) theorem used by Lemma 4.2; first citation point of ext:bm-support (also used at L2106-2107)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: reviewer-D/sonnet (proposed by reviewer; orchestrator to adopt)
REVIEWER: -

ITEM: inv:cite:L2223:blumenthal
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L2223:blumenthal@L2223-L2223
DISPOSITION: NODE ext:blumenthal
REASON: Blumenthal's zero-one law invoked by name in the proof of Theorem 1.10(b)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: reviewer-D/sonnet (proposed by reviewer; orchestrator to adopt)
REVIEWER: -


## Report

- Source ranges read: paper.tex L1947-L2311 in full (slice D); read-only L495-L511 (Thm 1.10 and Def 1.9 statements), L301-L323 and L555-L570, L590-L650 (Defs 1.4, (2.1)-(2.4), Lemmas 2.2/2.3 statements), L1786-L1816 (proof of Prop 3.2(b), the text reused by the proof of Thm 1.10(a)), plus greps. Also ERRATA.md, graph/EXTRACTION_SPEC.md, graph/INVENTORY.md (slice D), graph/EXTRACTOR_BRIEF.md and the skill packet/template docs; canonical node blocks in graph/packets/slice-A.md and slice-B.md (read-only). No frozen declaration files were needed (slice D owns no anchors).
- Counts: 51 nodes, 143 EDGE lines. Nodes: 6 lemmas (lem-disconnect-2, lem-line-approx, lem-haus, lem-pos-hits-before-neg, lem:re-im-bounds, lem-c-event), 1 display (eqn-disconnect-mart), 1 application (step:line-apply-haus), 40 steps (including thm-disconnects#proof-a and thm-disconnects#proof-b), 3 externals. No frozen anchors, no route nodes. All nodes are reachable from the two proof-assembly nodes; no cycles within the slice.
- Coverage: 46 ITEM records (40 inventory items plus 6 added: inv:L1950:wlog, inv:L1953:notation, inv:L1966:outline, inv:L2027:outline-b, inv:L2041:reduction, inv:L2162:def-crossing): 25 mapped to nodes, 21 excluded (headings, informal outline paragraphs and notation, all of section 5 with its citations and questions).
- Cross-slice edges (canonical IDs not owned by D): A: defn-loewner.well-defined, defn-hulls.left, defn-hulls.right, def-disconnect, defn-sle, eqn-conc, eqn-scale, eqn-def-ft, lem-scaling, lem-markov, lem-endpt-cont, lem-forward-reverse-ext, lem-mult-by-i, lem-connected.left, claim:gt-conformal, claim:hulls-monotone, step:wlog-c-nonneg, step:driver-representation. B: remark-sigma, defn-sigma, def-arg, lem-polar. C (ext owner): ext:girsanov. A (ext): ext:martingale-convergence. Slice C step IDs are not used: the steps reused from the proof of Prop 3.2(b) are modeled as my own nodes step:disc-a-* (hit Lambda' via Girsanov, restart/Markov, q positive everywhere, uniform q_*, conditional bound, martingale limit), so the orchestrator may later merge them with C's analogous steps. Inbound: thm-disconnects.a depends on thm-disconnects#proof-a and thm-disconnects.b on thm-disconnects#proof-b (as in slice A).
- Alternate routes: none created. The two citations of the same fact "[x,y] disjoint from L_2" (Remark 2.12 at L2041 versus Lemma 2.5 at L2134) are recorded in the NOTE of step:pos-segment-disjoint-L2; only lem-endpt-cont is a dependency.
- SOURCE_GAP nodes: lem-disconnect-2 (statement trivial for U = empty, so non-emptiness is read in); step:haus-maps-converge (Lawler Prop 4.43 extended from H to C, T6); step:haus-contradiction-L-t (non-extendability of g_t across L_t); step:haus-right-hull-reduction (Lemma 2.2 is for real drivers; duality (2.4) is not a node); step:line-apply-haus (Hausdorff lower half, the f_T bound and sequential-to-uniform passage unargued); step:disc-setup (existence of U^+- with both required properties; my rough check suggests the distance-2eps-from-the-imaginary-axis requirement may fail); step:disc-E1-positive (needs connectedness of R_T, the right-hull part of Lemma 2.4, which is not a graph node, and cites Lemma 4.3 where Lemma 4.2 is what gives the statements); step:disc-E2E3-positive (bridge from Lemma 4.4 to thin-rectangle crossings and the choice of eps,K); step:disc-topological-separation ("topological considerations"); step:disc-a-positive-measure-set; step:disc-a-hit-Lambda and step:disc-a-markov-restart (inherited Girsanov sketch; "exactly as in Prop 3.2(b)" glosses a change from equality to inequality and a concatenation transfer); step:disc-a-open-condition (assumes L_t closed).
- New ext: IDs: none. Externals first cited here, with canonical IDs: ext:loewner-convergence, ext:bm-support, ext:blumenthal. ext:bm-support may also be cited by slice C (the orchestrator should deduplicate); ext:girsanov is referenced but defined by C.
- Uncertainty list: (1) Whether lem-connected.left is a legitimate dependency of step:disc-E4-positive (extractor reading: connected hull close to a segment hits every crossing). (2) step:pos-* ID conventions: the displays cond-1..4, eqn-re-ft and eqn-im-ft are folded into lem-c-event and lem:re-im-bounds, not separate nodes. (3) Typos read as corrected: [-2T^{-1/2} i, ...] to T^{1/2} in Lemma 4.2; K_T in Lemma 4.3 read as L_T; f_1(x), f_1(y) at the end of the proof of Lemma 4.4 read as f_2; f_{T+2}(B_{3eps}(x)) read as f_{T,T+2}; (B_t) for measurability read as U=(B,B~); "for each z in C" in (eqn-disconnect-mart) read as z != 0 (R4); "for the set" at L2223 read as "such that the set". (4) The a,b>0 hypothesis and c>=0 WLOG are recorded as local hypothesis packages; lem-pos-hits-before-neg and lem-line-approx state only a,b>0 or nothing, but their proofs rely on the section package, supplied at consumers by step:wlog-c-nonneg. (5) step:disc-pullback-conclusion is reused by proof-a as the bridge between the restarted chain and the original event, which is my modeling, not source text. (6) step:disc-concatenation-transfer may hide an unaddressed R_{T,T+2} term in (2.3). (7) Slice A's contract IDs for several anchors contain a stray backtick (e.g. paper.thm1_10.a`); not my slice, flagged for the merger.
- Confirmations: no Lean evidence was sought, no declaration of ComplexSLE/ was read (slice D owns no anchors), no anchor ABI was edited or inferred, no Lean was run, and no file other than graph/packets/slice-D.md was written (the generator script and a scratch body file live in the session scratchpad).
