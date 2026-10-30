# Proof dependency database — arXiv:2203.07313v4 (Loewner evolution driven by complex Brownian motion)

GRAPH_VERSION: 4
ROOTS: defn-loewner.well-defined, lem-p.exists, nonsource.exists-sle-driver, thm-phases, thm-phases.c-zero, thm-disconnects.a, thm-disconnects.b, prop-i.a, prop-i.b, prop-ii.a, prop-ii.b, lem-connected.left, eqn-scale.left, eqn-reflect.left
CORPUS: source/arxiv-2203.07313v4/complex-sle-final.tex sha256:6f182d3af83b14781ad6c96c634a6d211230b0a54490453aca70cb52f77db252
CONVENTIONS: see graph/EXTRACTION_SPEC.md §3 (rulings R4-R17: z ≠ 0; a, b > 0 from Lemma 2.13 on; planar-BM driver; every admissible p; ε-form limits; left-hull splits; typos T1-T7)
STANDING_ASSUMPTIONS: -
EXTERNAL_POLICY: cited literature results and named standard theorems explicitly invoked by a proof are KIND external leaves (graph/EXTRACTION_SPEC.md §5); routine facts below the step threshold are not nodes
FROZEN_ANCHORS: defn-loewner.solution, defn-loewner.absorbing-time, defn-hulls.left, def-disconnect, eqn-cov-matrix, defn-sle.gaussian-law, defn-sle, defn-phases.thin, defn-phases.swallowing, defn-phases.hitting, defn-phases.dense, eqn-nu-D.mu, eqn-nu-D.nu, eqn-nu-D.D, lem-stationary.admissible, item-I, item-II, defn-loewner.well-defined, lem-p.exists, nonsource.exists-sle-driver, thm-phases, thm-phases.c-zero, thm-disconnects.a, thm-disconnects.b, prop-i.a, prop-i.b, prop-ii.a, prop-ii.b, lem-connected.left, eqn-scale.left, eqn-reflect.left
FROZEN_MANIFEST: frozen-anchor-manifest.json | sha256:2828acc43590018a4ecb51212013762c7de09abea5cb78e81aea33e0e52ef3ed
WRITER: orchestrator/opus-5.5/session-a85056b9
GLOBAL_REVIEWER: -
GLOBAL_REVIEW_REF: -

The dependency direction is `NODE -> prerequisite`. `DEPS` is conjunctive. `ROUTES` lists
alternative `KIND: route` nodes; one route is sufficient. Lean fields are initialized planning
metadata and are not evaluated here. Node schema: see
`~/.claude/skills/build-proof-dependency-graph/assets/DEPGRAPH.template.md`.

## Nodes
NODE: defn-loewner.solution
KIND: definition
TITLE: Loewner initial value problem (solution predicate)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#defn-loewner@L251-L263
PROOF_SOURCE: -
CONTRACT_ID: paper.def.IsLoewnerSolution
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U : [0,infinity) -> C continuous (Def 1.1 setting; the frozen predicate itself is stated for arbitrary U)
SOURCE_QUANTIFIERS: U; z in C; solution interval; t >= 0
SOURCE_CONCLUSION: for each z in C, g_t(z) solves g_t(z)-dot = 2/(g_t(z)-U_t), g_0(z) = z; centered chain f_t(z) = g_t(z) - U_t
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Defs/IsLoewnerSolution.lean
FROZEN_DECL: ComplexSLE.IsLoewnerSolution
FROZEN_ANCHOR_ID: def.IsLoewnerSolution.v1
FROZEN_ABI_SHA256: bbe2299b871e2374841a91b93b4f6762ad46fdaed6a82c43893c005089db4d29
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Frozen predicate IsLoewnerSolution (U z tau gamma). The centered chain f_t = g_t - U_t is a notational consequence, not a separate node; g_t, f_t are meaningful only after defn-loewner.well-defined (consumers depend on that theorem).

NODE: defn-loewner.absorbing-time
KIND: definition
TITLE: Absorbing time T_z
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268
PROOF_SOURCE: -
CONTRACT_ID: paper.def.absorbingTime
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (U continuous in the surrounding Def 1.1)
SOURCE_QUANTIFIERS: U; z in C
SOURCE_CONCLUSION: T_z in [0,infinity] is the time up to which the solution of (1.1) started at z exists
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Defs/AbsorbingTime.lean
FROZEN_DECL: ComplexSLE.absorbingTime
FROZEN_ANCHOR_ID: def.absorbingTime.v1
FROZEN_ABI_SHA256: f831e140c92a7542b39fb4f416dbd3ffaf931cb64e30ff1cd9362379efa590f1
DEPS: defn-loewner.solution
ROUTES: -
ROUTE_FOR: -
EDGE: defn-loewner.solution | source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268 | T_z is defined as the maximal time of existence of a solution of the initial value problem
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Frozen definition absorbingTime U z = sSup of tau with a solution on [0,tau).

NODE: defn-hulls.left
KIND: definition
TITLE: Left hull L_t
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#defn-hulls@L271-L277
PROOF_SOURCE: -
CONTRACT_ID: paper.def.leftHull
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U continuous
SOURCE_QUANTIFIERS: U; t >= 0
SOURCE_CONCLUSION: L_t = {z in C : T_z <= t} is the complement of the domain of f_t
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Defs/LeftHull.lean
FROZEN_DECL: ComplexSLE.leftHull
FROZEN_ANCHOR_ID: def.leftHull.v1
FROZEN_ABI_SHA256: c203d2a3a6eb3db7f822226cccc6b9ad6add6cd583a36c32bc8619bd900e809e
DEPS: defn-loewner.absorbing-time
ROUTES: -
ROUTE_FOR: -
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-hulls@L272-L272 | L_t is defined as {z : T_z <= t}
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Frozen leftHull. The right-hull half of Def 1.2 is node defn-hulls.right.

NODE: defn-hulls.right
KIND: definition
TITLE: Right hull R_t
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#defn-hulls@L272-L277
PROOF_SOURCE: -
CONTRACT_ID: paper.defn-hulls.right
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U continuous
SOURCE_QUANTIFIERS: U; t >= 0
SOURCE_CONCLUSION: R_t = C minus the range of f_t, so f_t : C\L_t -> C\R_t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-hulls.left, defn-loewner.well-defined
ROUTES: -
ROUTE_FOR: -
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-hulls@L272-L275 | f_t is a map on the complement of L_t whose range complement is R_t
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-hulls@L272-L272 | f_t = g_t - U_t is a well-defined map only via existence and uniqueness of the Loewner IVP; R_t is the complement of its range
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Non-anchored definition, needed by the full (2.1)-(2.3) statements, Lemma 2.2, and slice D uses of R_T. Not frozen (R16: right-hull parts are ordinary nodes). Whether a root consumes it is decided by the orchestrator via slice D edges.

NODE: def-disconnect
KIND: definition
TITLE: S disconnects S' from infinity
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#def-disconnect@L497-L499
PROOF_SOURCE: -
CONTRACT_ID: paper.def.DisconnectsFromInfinity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: S, S' subsets of C
SOURCE_QUANTIFIERS: S, S'
SOURCE_CONCLUSION: S' is disjoint from every unbounded connected component of C \ S; S' cap S = empty not required
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Defs/DisconnectsFromInfinity.lean
FROZEN_DECL: ComplexSLE.DisconnectsFromInfinity
FROZEN_ANCHOR_ID: def.DisconnectsFromInfinity.v1
FROZEN_ABI_SHA256: 396f675756de6faa68b7c805e29e8d726cae4320d590f5a714e96ee80ee540c2
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Frozen DisconnectsFromInfinity. Source reads "unbounded connected component C \ S" with a missing "of".

NODE: eqn-cov-matrix
KIND: definition
TITLE: Covariance matrix Sigma
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-cov-matrix@L304-L306
PROOF_SOURCE: -
CONTRACT_ID: paper.def.covMatrix
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Sigma symmetric positive semidefinite (equivalently a,b >= 0, |c| <= sqrt(ab) per L310)
SOURCE_QUANTIFIERS: a, b, c real
SOURCE_CONCLUSION: Sigma = [[a,c],[c,b]]
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Defs/CovMatrix.lean
FROZEN_DECL: ComplexSLE.covMatrix
FROZEN_ANCHOR_ID: def.covMatrix.v1
FROZEN_ABI_SHA256: 9c7db20131aa7365837343dbfe0137f267d6d9583f10c6217364b322317c9dc2
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Frozen covMatrix. PSD is a standing assumption of theorems (R6), not a field of the definition. The equivalence "PSD iff a,b>=0, |c|<=sqrt(ab)" at L310 is below the step threshold (2x2 linear algebra).

NODE: defn-sle.gaussian-law
KIND: definition
TITLE: Centered Gaussian law on C = R^2
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#defn-sle@L301-L308
PROOF_SOURCE: -
CONTRACT_ID: paper.def.complexGaussian
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: covariance matrix S
SOURCE_QUANTIFIERS: S
SOURCE_CONCLUSION: centered Gaussian law on C identified with R^2 with covariance S (the law of an increment of the driver, ruling R6)
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Defs/ComplexGaussian.lean
FROZEN_DECL: ComplexSLE.complexGaussian
FROZEN_ANCHOR_ID: def.complexGaussian.v1
FROZEN_ABI_SHA256: 35770535322d991e762fad0a8fe630fa74e550a8a476439b08129e00de75c486
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Frozen complexGaussian; added by ruling R6 to make "Brownian motion in C with infinitesimal covariance Sigma" precise (Def 1.4 itself only says Brownian motion).

NODE: defn-sle
KIND: definition
TITLE: SLE_Sigma driving process (planar BM with covariance Sigma)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#defn-sle@L301-L308
PROOF_SOURCE: -
CONTRACT_ID: paper.def.IsSLEDriver
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Sigma = [[a,c],[c,b]] symmetric PSD (standing assumption in theorems)
SOURCE_QUANTIFIERS: a, b, c; probability space (Omega,P); U : [0,infinity) x Omega -> C
SOURCE_CONCLUSION: U has a.s. continuous paths, U_0 = 0, independent increments, U_t - U_s ~ N(0,(t-s)Sigma); SLE_Sigma is the Loewner chain driven by U
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Defs/IsSLEDriver.lean
FROZEN_DECL: ComplexSLE.IsSLEDriver
FROZEN_ANCHOR_ID: def.IsSLEDriver.v1
FROZEN_ABI_SHA256: a3e7b316bc3a0ef59101d633fadad41bf1cf76893aaccc318657527c33d60af5
DEPS: eqn-cov-matrix, defn-sle.gaussian-law
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-cov-matrix | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-sle@L304-L307 | the covariance of the driver is Sigma
EDGE: defn-sle.gaussian-law | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-sle@L307-L307 | increments of U have Gaussian law with covariance (t-s)Sigma
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: R6/P3: source says U = sqrt(a) B + i sqrt(b) B~ with Cov(B_t,B~_t) = ct/sqrt(ab), which does not make (B,B~) jointly Gaussian and is 0/0 for ab = 0; read as planar BM with covariance Sigma. The representation is node step:driver-representation. Frozen IsSLEDriver.

NODE: defn-phases.thin
KIND: definition
TITLE: Thin phase
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#defn-phases@L409-L417
PROOF_SOURCE: -
CONTRACT_ID: paper.def.IsThinPhase
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Sigma symmetric PSD (standing assumption)
SOURCE_QUANTIFIERS: a, b, c; every probability space and SLE_Sigma driver; z in C\{0}; a.s.
SOURCE_CONCLUSION: for each z != 0, a.s. z not in closure of union_t L_t
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Defs/IsThinPhase.lean
FROZEN_DECL: ComplexSLE.IsThinPhase
FROZEN_ANCHOR_ID: def.IsThinPhase.v1
FROZEN_ABI_SHA256: 7727fa4e3bd47573921bd91b01e159429ee6bf9918604c734f8eae2575c8142c
DEPS: defn-sle, defn-hulls.left
ROUTES: -
ROUTE_FOR: -
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-phases@L410-L410 | the phase is a property of an SLE_Sigma driven chain (all probability spaces / drivers)
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-phases@L412-L412 | the condition is stated in terms of the left hulls L_t
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Frozen IsThinPhase (item L412). R4: z != 0 (z = 0 gives T_0 = 0, 0 in L_0, and the literal statement is false); R12: probabilities over all spaces in Type.

NODE: defn-phases.swallowing
KIND: definition
TITLE: Swallowing phase
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#defn-phases@L409-L417
PROOF_SOURCE: -
CONTRACT_ID: paper.def.IsSwallowingPhase
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Sigma symmetric PSD (standing assumption)
SOURCE_QUANTIFIERS: a, b, c; every probability space and SLE_Sigma driver; z in C\{0}; a.s.
SOURCE_CONCLUSION: for each z != 0, a.s. T_z < infinity and z not in closure of union_{t<T_z} L_t
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Defs/IsSwallowingPhase.lean
FROZEN_DECL: ComplexSLE.IsSwallowingPhase
FROZEN_ANCHOR_ID: def.IsSwallowingPhase.v1
FROZEN_ABI_SHA256: da5f6acbe728f180308ef886460f4e1cb38a7ac67b56a6fa0a79da36708ee72f
DEPS: defn-sle, defn-hulls.left, defn-loewner.absorbing-time
ROUTES: -
ROUTE_FOR: -
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-phases@L410-L410 | the phase is a property of an SLE_Sigma driven chain (all probability spaces / drivers)
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-phases@L413-L413 | the condition is stated in terms of the left hulls L_t
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-phases@L413-L413 | the condition uses T_z (finite and the time union)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Frozen IsSwallowingPhase (item L413). R4: z != 0 (z = 0 gives T_0 = 0, 0 in L_0, and the literal statement is false); R12: probabilities over all spaces in Type.

NODE: defn-phases.hitting
KIND: definition
TITLE: Hitting phase
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#defn-phases@L409-L417
PROOF_SOURCE: -
CONTRACT_ID: paper.def.IsHittingPhase
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Sigma symmetric PSD (standing assumption)
SOURCE_QUANTIFIERS: a, b, c; every probability space and SLE_Sigma driver; z in C\{0}; a.s.
SOURCE_CONCLUSION: for each z != 0, a.s. T_z < infinity and z in closure of union_{t<T_z} L_t
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Defs/IsHittingPhase.lean
FROZEN_DECL: ComplexSLE.IsHittingPhase
FROZEN_ANCHOR_ID: def.IsHittingPhase.v1
FROZEN_ABI_SHA256: f226bef104f2e8332fb32fce332025566773b0e16564ff8d199410f001b307d0
DEPS: defn-sle, defn-hulls.left, defn-loewner.absorbing-time
ROUTES: -
ROUTE_FOR: -
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-phases@L410-L410 | the phase is a property of an SLE_Sigma driven chain (all probability spaces / drivers)
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-phases@L414-L414 | the condition is stated in terms of the left hulls L_t
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-phases@L414-L414 | the condition uses T_z (finite and the time union)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Frozen IsHittingPhase (item L414). R4: z != 0 (z = 0 gives T_0 = 0, 0 in L_0, and the literal statement is false); R12: probabilities over all spaces in Type.

NODE: defn-phases.dense
KIND: definition
TITLE: Dense phase
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#defn-phases@L409-L417
PROOF_SOURCE: -
CONTRACT_ID: paper.def.IsDensePhase
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Sigma symmetric PSD (standing assumption)
SOURCE_QUANTIFIERS: a, b, c; every probability space and SLE_Sigma driver; z in C\{0}; a.s.
SOURCE_CONCLUSION: for each z != 0, a.s. z in closure of union_t L_t minus union_t L_t
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Defs/IsDensePhase.lean
FROZEN_DECL: ComplexSLE.IsDensePhase
FROZEN_ANCHOR_ID: def.IsDensePhase.v1
FROZEN_ABI_SHA256: 1ee346e80cf2a6167b73f56641824ee302db6becb222740bf3701d7971e7e5df
DEPS: defn-sle, defn-hulls.left
ROUTES: -
ROUTE_FOR: -
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-phases@L410-L410 | the phase is a property of an SLE_Sigma driven chain (all probability spaces / drivers)
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-phases@L415-L415 | the condition is stated in terms of the left hulls L_t
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Frozen IsDensePhase (item L415). R4: z != 0 (z = 0 gives T_0 = 0, 0 in L_0, and the literal statement is false); R12: probabilities over all spaces in Type.

NODE: eqn-nu-D.mu
KIND: definition
TITLE: Drift mu(u)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-nu-D@L424-L424
PROOF_SOURCE: -
CONTRACT_ID: paper.def.mu
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b,c real
SOURCE_QUANTIFIERS: a,b,c; u real
SOURCE_CONCLUSION: mu(u) = -(2 - a/2 + b/2) sin 2u - c cos 2u
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Defs/Mu.lean
FROZEN_DECL: ComplexSLE.mu
FROZEN_ANCHOR_ID: def.mu.v1
FROZEN_ABI_SHA256: cd3369a3cc72d9850889657ec3f058716a2c7cbc084efbddfcc84738b784297b
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Frozen mu.

NODE: eqn-nu-D.nu
KIND: definition
TITLE: Log-drift nu(u)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-nu-D@L425-L425
PROOF_SOURCE: -
CONTRACT_ID: paper.def.nu
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b,c real
SOURCE_QUANTIFIERS: a,b,c; u real
SOURCE_CONCLUSION: nu(u) = (2 - a/2 + b/2) cos 2u - c sin 2u
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Defs/Nu.lean
FROZEN_DECL: ComplexSLE.nu
FROZEN_ANCHOR_ID: def.nu.v1
FROZEN_ABI_SHA256: f9ff6a5f33ed2c7350371531fdb5f1700586fdc010eb37a4a4c11857b1ce23e3
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Frozen nu.

NODE: eqn-nu-D.D
KIND: definition
TITLE: Diffusion coefficient D(u)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-nu-D@L426-L426
PROOF_SOURCE: -
CONTRACT_ID: paper.def.diffusionD
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b,c real
SOURCE_QUANTIFIERS: a,b,c; u real
SOURCE_CONCLUSION: D(u) = (a/2) sin^2 u + (b/2) cos^2 u - c cos u sin u
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Defs/DiffusionD.lean
FROZEN_DECL: ComplexSLE.diffusionD
FROZEN_ANCHOR_ID: def.diffusionD.v1
FROZEN_ABI_SHA256: ae71cf207fc738d3a8f3b0629a9e5bc1c4b8e6c767665016cbbb6630db368cc2
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Frozen diffusionD.

NODE: item-I
KIND: definition
TITLE: Integral (I)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#item-I@L440-L440
PROOF_SOURCE: -
CONTRACT_ID: paper.def.integralI
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a, b, c real; p : R -> R an arbitrary function (the source introduces p before the theorem; admissibility of p is a premise of Thm 1.8, not of the integral)
SOURCE_QUANTIFIERS: a,b,c; p
SOURCE_CONCLUSION: (I) = integral_0^{2pi} nu(u) p(u) du
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Defs/IntegralI.lean
FROZEN_DECL: ComplexSLE.integralI
FROZEN_ANCHOR_ID: def.integralI.v1
FROZEN_ABI_SHA256: 5971ead00dfc488c751540f8e58da9f1b4f95e192413d7e6f2712586ba7823ad
DEPS: eqn-nu-D.nu
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-nu-D.nu | source/arxiv-2203.07313v4/complex-sle-final.tex#item-I@L440-L440 | the integrand is nu(u)p(u)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Frozen integralI.

NODE: item-II
KIND: definition
TITLE: Integral (II)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#item-II@L441-L441
PROOF_SOURCE: -
CONTRACT_ID: paper.def.integralII
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a, b, c real; p : R -> R an arbitrary function (the source introduces p before the theorem; admissibility of p is a premise of Thm 1.8, not of the integral)
SOURCE_QUANTIFIERS: a,b,c; p
SOURCE_CONCLUSION: (II) = integral_0^{2pi} (nu(u) + 2 cos 2u) p(u) du
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Defs/IntegralII.lean
FROZEN_DECL: ComplexSLE.integralII
FROZEN_ANCHOR_ID: def.integralII.v1
FROZEN_ABI_SHA256: f79d30902daa10ab3c6b8002e63af5af5c565a7558faa9d8067507619f09211c
DEPS: eqn-nu-D.nu
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-nu-D.nu | source/arxiv-2203.07313v4/complex-sle-final.tex#item-II@L441-L441 | the integrand contains nu(u)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Frozen integralII.

NODE: step:loewner-local-solution
KIND: step
TITLE: Local existence and uniqueness for the Loewner ODE away from U_t
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268
CONTRACT_ID: paper.step:loewner-local-solution
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U continuous; z in C, z != U_0
SOURCE_QUANTIFIERS: U; z; initial time
SOURCE_CONCLUSION: near any time t0 with g(t0) != U_{t0} the ODE g-dot = 2/(g-U_t) has a solution, and two solutions that agree at a time t0 agree on a neighbourhood of t0 (local uniqueness only)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: ext:picard-lindelof, defn-loewner.solution
ROUTES: -
ROUTE_FOR: -
EDGE: ext:picard-lindelof | source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268 | "as in the case of a real driving function": right side is continuous in t and locally Lipschitz in g where g != U_t
EDGE: defn-loewner.solution | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-loewner@L256-L256 | the ODE is (1.1)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: the source asserts existence/uniqueness of the solution of (1.1) "as in the case of a real driving function" (L268) without proof. This step exposes the Picard-Lindelof application (RHS jointly continuous, locally Lipschitz in g on {g != U_t}); case z = U_0 gives T_z = 0.

NODE: step:loewner-glue-maximal
KIND: step
TITLE: Gluing: a solution exists on all of [0,T_z)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268
CONTRACT_ID: paper.step:loewner-glue-maximal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U continuous
SOURCE_QUANTIFIERS: U; z
SOURCE_CONCLUSION: using uniqueness, solutions on [0,tau) with increasing tau patch together to a solution on [0,T_z), where T_z = sup of such tau
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:loewner-local-solution, step:loewner-global-uniqueness, defn-loewner.absorbing-time
ROUTES: -
ROUTE_FOR: -
EDGE: step:loewner-local-solution | source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268 | solutions on shorter intervals are the pieces to be patched
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268 | T_z is the supremum of existence times; the supremum must be attained as an open interval
EDGE: step:loewner-global-uniqueness | source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268 | uniqueness on overlaps lets the pieces patch into one solution on [0,T_z)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: not written in the source (L268 says only that the solution is defined up to T_z). Quantifier closure: sup of existence intervals is itself an existence interval.

NODE: defn-loewner.well-defined
KIND: theorem
TITLE: Well-definedness of the Loewner chain
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#defn-loewner@L251-L268
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268
CONTRACT_ID: paper.def1_1.wellDefined
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U : [0,infinity) -> C continuous
SOURCE_QUANTIFIERS: U; z in C; solutions gamma1, gamma2 on [0,tau)
SOURCE_CONCLUSION: the IVP (1.1) started at z has a solution on [0,T_z), and any two solutions on a common interval [0,tau) agree
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/LoewnerWellDefined.lean
FROZEN_DECL: ComplexSLE.loewner_wellDefined
FROZEN_ANCHOR_ID: thm.loewner_wellDefined.v1
FROZEN_ABI_SHA256: 627a9c24bc589b835afd7829fa4c0ca50499a5167908b24c5ac70bd838f0257f
DEPS: defn-loewner.solution, defn-loewner.absorbing-time, step:loewner-local-solution, step:loewner-global-uniqueness, step:loewner-glue-maximal
ROUTES: -
ROUTE_FOR: -
EDGE: defn-loewner.solution | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-loewner@L253-L256 | the statement concerns solutions of (1.1)
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268 | the solution interval is [0,T_z)
EDGE: step:loewner-local-solution | source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268 | local existence
EDGE: step:loewner-glue-maximal | source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268 | existence on all of [0,T_z)
EDGE: step:loewner-global-uniqueness | source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268 | any two solutions on a common interval agree
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Root. Source only states "the solution is defined up to some time T_z" (L268); proof not given, so both step nodes carry SOURCE_GAP. The limit |f_t(z)| -> 0 stated at L268 is lem-endpt-cont and is not part of the frozen statement.

NODE: claim:hulls-monotone
KIND: claim
TITLE: Left hulls are increasing
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#hulls-monotone@L284-L284
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#hulls-monotone@L284-L284
CONTRACT_ID: paper.claim:hulls-monotone
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U continuous
SOURCE_QUANTIFIERS: U; s < t
SOURCE_CONCLUSION: L_s subset L_t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-hulls.left
ROUTES: -
ROUTE_FOR: -
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#hulls-monotone@L272-L272 | "By definition": L_t = {T_z <= t} is increasing in t
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabeled sentence at L284 ("By definition ... increasing"); immediate from the definition; kept as a node because Thm 1.10(b) proof (slice D) and others reuse it. Right-hull non-monotonicity is excluded.

NODE: claim:gt-conformal
KIND: claim
TITLE: g_t is conformal from C\L_t onto C\(R_t+U_t); z(g_t(z)-z) -> 2t
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#gt-conformal@L286-L286
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#gt-conformal@L286-L286
CONTRACT_ID: paper.claim:gt-conformal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U continuous
SOURCE_QUANTIFIERS: U; t >= 0; z in C
SOURCE_CONCLUSION: g_t : C\L_t -> C\(R_t+U_t) is holomorphic and bijective, and lim z(g_t(z)-z) = 2t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-hulls.left, defn-hulls.right, defn-loewner.well-defined, ext:lawler-4.5
ROUTES: -
ROUTE_FOR: -
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#gt-conformal@L286-L286 | domain of g_t is the complement of L_t
EDGE: defn-hulls.right | source/arxiv-2203.07313v4/complex-sle-final.tex#gt-conformal@L286-L286 | range of g_t is the complement of R_t + U_t
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#gt-conformal@L286-L286 | g_t is the time-t flow map defined by the well-defined IVP
EDGE: ext:lawler-4.5 | source/arxiv-2203.07313v4/complex-sle-final.tex#gt-conformal@L286-L286 | "exactly the same arguments as ... [Lawler, Theorem 4.5]"
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: asserted by analogy, not proved (L286 "one can check"). The limit is written t -> infinity in the source; read as z -> infinity (typo, the quantity z(g_t(z)-z) at fixed t) -- uncertain, not covered by any ERRATA entry.

NODE: eqn-scale.left
KIND: theorem
TITLE: Scaling property for left hulls
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-scale@L549-L552
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-scale@L547-L547
CONTRACT_ID: paper.prop2_1_scaling.leftHull
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U continuous
SOURCE_QUANTIFIERS: U; r > 0; t >= 0
SOURCE_CONCLUSION: L_t^{rU(./r^2)} = r L_{t/r^2}
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Scaling_LeftHull.lean
FROZEN_DECL: ComplexSLE.scaling_leftHull
FROZEN_ANCHOR_ID: thm.scaling_leftHull.v1
FROZEN_ABI_SHA256: 0b072ed0d86d49729df12aafd3234c5371ca05e7bd4e7563aca829a4ad0259f5
DEPS: defn-loewner.solution, defn-loewner.absorbing-time, defn-hulls.left, defn-loewner.well-defined
ROUTES: -
ROUTE_FOR: -
EDGE: defn-loewner.solution | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-scale@L547-L547 | identification of solutions of the ODE
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-scale@L547-L547 | hulls are sublevel sets of T_z
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-scale@L547-L547 | statement is about L_t
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-scale@L547-L547 | uniqueness of the ODE solution identifies the transformed solution with the chain of the transformed driver
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Root (left-hull part of (2.1), R16). Source proof: "easily consequences of Definition 1.1; see [Lu, Section 2]" (no proof in source). Typo T7: U : [0,infinity) -> R at L545 should be -> C.

NODE: eqn-scale
KIND: display
TITLE: Scaling property (2.1), full
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-scale@L549-L552
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-scale@L547-L547
CONTRACT_ID: paper.eqn-scale
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U : [0,infinity) -> C continuous
SOURCE_QUANTIFIERS: U; r > 0; t >= 0; z in C
SOURCE_CONCLUSION: f_t^{rU(./r^2)}(z) = r f_{t/r^2}(z/r), L_t^{rU(./r^2)} = r L_{t/r^2}, R_t^{rU(./r^2)} = r R_{t/r^2}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-scale.left, defn-hulls.right, defn-loewner.well-defined, defn-loewner.solution
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-scale.left | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-scale@L552-L552 | the left-hull identity is one conjunct
EDGE: defn-hulls.right | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-scale@L552-L552 | right-hull identity
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-scale@L547-L547 | f_t identity by uniqueness of solutions
EDGE: defn-loewner.solution | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-scale@L547-L547 | the ODE is rescaled
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Canonical full (2.1). Proof not in source (cited to Lu Sect. 2).

NODE: eqn-reflect.left
KIND: theorem
TITLE: Reflection property for left hulls
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-reflect@L553-L557
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-reflect@L547-L547
CONTRACT_ID: paper.prop2_2_reflection.leftHull
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U continuous
SOURCE_QUANTIFIERS: U; t >= 0
SOURCE_CONCLUSION: L_t^{U*} = (L_t^U)* and L_t^{-U} = -L_t^U
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Reflection_LeftHull.lean
FROZEN_DECL: ComplexSLE.reflection_leftHull
FROZEN_ANCHOR_ID: thm.reflection_leftHull.v1
FROZEN_ABI_SHA256: a622f14fdc883f8e0806d2d8df7ef10f345eba58d229d3bea9f50da620fc7cb7
DEPS: defn-loewner.solution, defn-loewner.absorbing-time, defn-hulls.left, defn-loewner.well-defined
ROUTES: -
ROUTE_FOR: -
EDGE: defn-loewner.solution | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-reflect@L547-L547 | identification of solutions of the ODE
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-reflect@L547-L547 | hulls are sublevel sets of T_z
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-reflect@L547-L547 | statement is about L_t
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-reflect@L547-L547 | uniqueness of the ODE solution identifies the transformed solution with the chain of the transformed driver
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Root (left-hull part of (2.2), R16). Proof not in source (cited to Lu Sect. 2).

NODE: eqn-reflect
KIND: display
TITLE: Reflection property (2.2), full
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-reflect@L553-L558
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-reflect@L547-L547
CONTRACT_ID: paper.eqn-reflect
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U continuous
SOURCE_QUANTIFIERS: U; t >= 0
SOURCE_CONCLUSION: L_t^{U*} = (L_t^U)*, L_t^{-U} = -L_t^U, and the same for right hulls
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-reflect.left, defn-hulls.right, defn-loewner.well-defined
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-reflect.left | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-reflect@L556-L556 | left-hull statement is a conjunct
EDGE: defn-hulls.right | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-reflect@L558-L558 | "The same is true with right hulls"
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-reflect@L547-L547 | uniqueness of ODE solutions
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Canonical full (2.2). Proof not in source.

NODE: eqn-conc
KIND: display
TITLE: Concatenation property (2.3)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-conc@L559-L565
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-conc@L547-L547
CONTRACT_ID: paper.eqn-conc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U continuous
SOURCE_QUANTIFIERS: U; s,t >= 0
SOURCE_CONCLUSION: f_{s+t} = f_{t,s+t} o f_t on C\L_{s+t}; L_{s+t} = L_t cup f_t^{-1}(L_{t,s+t}\R_t); f_t(L_{s+t}\L_t) = L_{t,s+t}; R_{s+t} = R_{t,s+t} cup f_{t,s+t}(R_t\L_{t,s+t})
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-loewner.well-defined, defn-loewner.solution, defn-hulls.left, defn-hulls.right, claim:hulls-monotone
ROUTES: -
ROUTE_FOR: -
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-conc@L547-L547 | flow composition via uniqueness of the ODE solution
EDGE: defn-loewner.solution | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-conc@L547-L547 | time-shifted driver U(.+t)-U(t)
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-conc@L562-L562 | hull identities
EDGE: defn-hulls.right | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-conc@L564-L564 | hull identities
EDGE: claim:hulls-monotone | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-conc@L562-L562 | L_t subset L_{s+t} is used in the union decomposition
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Canonical (2.3). Proof not in source (cited to Lu Sect. 2). Used by Lemma 2.8 and slices C, D. The source writes f_{t,s+t} with a time-shifted chain, defined in the item itself (no separate node).

NODE: step:driver-representation
KIND: step
TITLE: Representation U = sqrt(a) B + i sqrt(b) B~ for a planar BM with covariance Sigma
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#defn-sle@L307-L308
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#defn-sle@L307-L308
CONTRACT_ID: paper.step:driver-representation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a, b > 0; U planar BM with covariance Sigma (R6, R5)
SOURCE_QUANTIFIERS: a,b,c; U; B := Re U / sqrt(a), B~ := Im U / sqrt(b)
SOURCE_CONCLUSION: B, B~ are standard linear BMs with Cov(B_t,B~_t) = ct/sqrt(ab) and U = sqrt(a) B + i sqrt(b) B~
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-sle
ROUTES: -
ROUTE_FOR: -
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-sle@L307-L307 | from increments N(0,(t-s)Sigma) one reads off the marginals and the cross-covariance of the coordinates
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: R6: in the source the representation is the definition; here it becomes a consequence. Only for a, b > 0 (division by sqrt a, sqrt b; R5). Also restates (1.2) display eqn-def-gt.

NODE: eqn-def-ft
KIND: display
TITLE: SDE (1.6) for the centered SLE_Sigma maps f_t
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-def-ft@L315-L319
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-def-ft@L315-L319
CONTRACT_ID: paper.eqn-def-ft
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b>0 (R5), Sigma PSD
SOURCE_QUANTIFIERS: z in C; t < T_z
SOURCE_CONCLUSION: df_t(z) = (2/f_t(z)) dt - sqrt(a) dB_t - i sqrt(b) dB~_t, f_0(z) = z
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-loewner.solution, defn-loewner.well-defined, defn-sle, step:driver-representation
ROUTES: -
ROUTE_FOR: -
EDGE: defn-loewner.solution | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-def-ft@L316-L316 | f_t = g_t - U_t with g_t from the Loewner ODE gives f_t = z + int 2/f ds - (U_t - U_0)
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-def-ft@L315-L315 | U is the SLE_Sigma driving BM
EDGE: step:driver-representation | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-def-ft@L317-L317 | U written as sqrt(a) B + i sqrt(b) B~
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-def-ft@L315-L315 | f_t(z) exists for t < T_z only through the well-defined chain
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabeled "Equivalently ... SDE" (L315-319, spec Section 6). Pathwise this is the integral form of the ODE; no Ito calculus needed here (U is the integrator). Valid up to T_z.

NODE: step:wlog-c-nonneg
KIND: step
TITLE: WLOG c >= 0 by conjugation
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#wlog-c-nonneg@L323-L323
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#wlog-c-nonneg@L323-L323
CONTRACT_ID: paper.step:wlog-c-nonneg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Sigma = [[a,c],[c,b]] PSD
SOURCE_QUANTIFIERS: a,b,c; U
SOURCE_CONCLUSION: replacing c by -c replaces U by its conjugate, so left hulls are conjugated; properties invariant under conjugation may be proved for c >= 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-reflect.left, defn-sle, eqn-cov-matrix
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-reflect.left | source/arxiv-2203.07313v4/complex-sle-final.tex#wlog-c-nonneg@L323-L323 | conjugating the driver conjugates the left hulls (reflection property)
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#wlog-c-nonneg@L323-L323 | conjugate of an SLE_{Sigma} driver is an SLE_{Sigma with -c} driver
EDGE: eqn-cov-matrix | source/arxiv-2203.07313v4/complex-sle-final.tex#wlog-c-nonneg@L323-L323 | covariance matrix with c replaced by -c
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Spec Section 4: a WLOG step consuming the reflection property. The source justifies it by the Loewner ODE (eqn-forward-loewner) at L323; the extractor routes it through the reflection property (2.2). Also used at L1949 (slice D).

NODE: defn-chordal-loewner
KIND: definition
TITLE: Chordal Loewner chains (forward and reverse)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#defn-chordal-loewner@L588-L607
PROOF_SOURCE: -
CONTRACT_ID: paper.defn-chordal-loewner
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U : [0,infinity) -> R continuous
SOURCE_QUANTIFIERS: U; z in H
SOURCE_CONCLUSION: forward chain g_t(z) solves g-dot = 2/(g-U_t), reverse chain solves g-dot = -2/(g-U_t), g_0(z) = z; centered chain f_t = g_t - U_t; forward chain: f_t maps H \ L_t onto H with L_t = {z in H : T_z <= t}; reverse chain: f_t maps H onto H \ R_t for some set R_t (hulls identified via Loewner's theorem, L603-L607)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Definition 2.1 with (2.5), (2.6), plus the hull identification at L606-L607 that Lemma 2.2 consumes. SOURCE_GAP: Loewner's theorem (g_t the unique conformal map with g_t(z)-z -> 0) is recalled, not proved, and is not a node; Lemma 2.2 relies on it only through the hull identification.

NODE: lem-mult-by-i
KIND: lemma
TITLE: Multiplying by i converts reverse to forward chains
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-mult-by-i@L635-L639
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-mult-by-i@L640-L642
CONTRACT_ID: paper.lem-mult-by-i
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U : [0,infinity) -> C continuous; g_t(z) the solution of the reverse IVP (2.6) for each z in C; f_t = g_t - U_t
SOURCE_QUANTIFIERS: U; z; t
SOURCE_CONCLUSION: z -> i f_t(-iz) is the centered Loewner chain with driver iU
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-loewner.solution, defn-loewner.well-defined, defn-chordal-loewner
ROUTES: -
ROUTE_FOR: -
EDGE: defn-loewner.solution | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-mult-by-i@L641-L641 | "immediate consequence of Definition 1.1": the rotated map solves the forward ODE for iU
EDGE: defn-chordal-loewner | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-mult-by-i@L637-L637 | reverse ODE (2.6) is the hypothesis
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-mult-by-i@L641-L641 | a solution of the ODE for iU is identified with the Loewner chain of iU by uniqueness
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Statement formulated for complex U with the reverse equation; solution is assumed to exist for the given times (source treats the solution as given). The reversal remark at L644 is a separate unlabeled claim, folded into step:reverse-via-mult-by-i.

NODE: step:forward-real-driver
KIND: step
TITLE: Real driver: complex chain extends the forward chordal chain by Schwarz reflection
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L623-L626
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L648-L648
CONTRACT_ID: paper.step:forward-real-driver
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U : [0,infinity) -> R continuous
SOURCE_QUANTIFIERS: U; t
SOURCE_CONCLUSION: the Schwarz reflection of the forward chordal chain f_t is the complex centered chain with driver U, with left hulls L_t cup L_t*, right hulls in R
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-reflect, defn-chordal-loewner, defn-hulls.left, defn-hulls.right, defn-loewner.well-defined
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-reflect | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L648-L648 | "first assertion is immediate from the reflection property under conjugation": U real so U* = U
EDGE: defn-chordal-loewner | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L626-L626 | forward chordal chain and its hulls
EDGE: defn-hulls.right | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L626-L626 | right hulls are subsets of the real axis
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L648-L648 | complex chain coincides with chordal chain on H by uniqueness
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L626-L626 | the left hulls of the complex chain are claimed to be L_t cup L_t*
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Part (a). SOURCE_GAP: the identification of the Schwarz-reflected map and of the hulls is delegated to [Lu, Section 2]; only the conjugation-symmetry argument is given.

NODE: step:reverse-via-mult-by-i
KIND: step
TITLE: Part (b): reverse chain by combining part (a) with rotation
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L627-L629
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L648-L648
CONTRACT_ID: paper.step:reverse-via-mult-by-i
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U : [0,infinity) -> R continuous
SOURCE_QUANTIFIERS: U; t
SOURCE_CONCLUSION: (i f^_t(-i .)) is the centered complex chain with driver iU, left hulls in the imaginary axis, right hulls iR_t cup iR_t*
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-mult-by-i, step:forward-real-driver, defn-chordal-loewner
ROUTES: -
ROUTE_FOR: -
EDGE: lem-mult-by-i | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L648-L648 | "second assertion follows from ... Lemma 2.3"
EDGE: step:forward-real-driver | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L648-L648 | combined with the first assertion
EDGE: defn-chordal-loewner | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L628-L628 | the reverse chordal chain whose Schwarz extension feeds Lemma 2.3
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Includes the reversal remark at L644 (forward chain for U gives reverse chain for iU). SOURCE_GAP: Lemma 2.3 assumes a reverse solution g_t(z) for every z in C and a continuous complex driver; here the only available object is the reverse chordal chain on H, extended by Schwarz reflection (footnote at L623), and the discharge of that premise (existence of the reflected solution for the required times) is not written in the source.

NODE: lem-forward-reverse-ext
KIND: lemma
TITLE: Real and imaginary drivers recover forward and reverse chordal chains
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L620-L630
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L647-L649
CONTRACT_ID: paper.lem-forward-reverse-ext
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U : [0,infinity) -> R continuous; f_t centered forward (a) / reverse (b) chordal chain; f^ Schwarz reflection
SOURCE_QUANTIFIERS: U; t
SOURCE_CONCLUSION: (a) f^_t is the centered complex chain driven by U, left hulls L_t cup L_t*, right hulls in R; (b) i f^_t(-i.) is the centered complex chain driven by iU, left hulls in iR, right hulls iR_t cup iR_t*
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-chordal-loewner, step:forward-real-driver, step:reverse-via-mult-by-i
ROUTES: -
ROUTE_FOR: -
EDGE: defn-chordal-loewner | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L624-L628 | forward/reverse chordal chains are in the hypotheses
EDGE: step:forward-real-driver | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L648-L648 | proof of (a)
EDGE: step:reverse-via-mult-by-i | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L648-L648 | proof of (b)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Consumed at L2013 (Lemma 4.3, slice D) for the right-hull reduction. The statement mentions hulls only via defn-chordal-loewner and step nodes.

NODE: claim:hull-nonempty
KIND: claim
TITLE: L_t contains the starting point U_0
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L658-L660
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L658-L660
CONTRACT_ID: paper.claim:hull-nonempty
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U continuous
SOURCE_QUANTIFIERS: U; t >= 0
SOURCE_CONCLUSION: U_0 in L_t, so L_t is nonempty
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-hulls.left, defn-loewner.absorbing-time, defn-loewner.solution
ROUTES: -
ROUTE_FOR: -
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L659-L659 | U_0 in L_t means T_{U_0} <= t
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L659-L659 | T_{U_0} = 0 (no solution of positive duration starts at U_0)
EDGE: defn-loewner.solution | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L659-L659 | a solution must satisfy g_s != U_s, impossible at s = 0 when g_0 = U_0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: nonemptiness (needed because the frozen anchor states IsConnected = nonempty and connected) is not stated in the source; follows from f_0(U_0) = 0. For U_0 = 0 this is the R4 convention 0 in L_t.

NODE: step:connected-loop-criterion
KIND: step
TITLE: Connectedness of L_t from loops not surrounding the origin
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L663
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L663
CONTRACT_ID: paper.step:connected-loop-criterion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: L_t closed set (complement of the domain of f_t)
SOURCE_QUANTIFIERS: t; loops mcl L in C\L_t
SOURCE_CONCLUSION: it suffices that the region bounded by every loop mcl L in C\L_t not surrounding the origin does not meet L_t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-hulls.left, step:hull-closed
ROUTES: -
ROUTE_FOR: -
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662 | L_t is the complement of the domain of f_t
EDGE: step:hull-closed | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662 | the planar reduction "it is enough to show" uses that L_t is closed
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Planar topology reduction asserted without proof ("it is enough to show"). Note: the source says loop that "does not surround the origin"; uncertain whether this should read the starting point U_0 (T5-adjacent).

NODE: step:connected-homotopy
KIND: step
TITLE: Loop images stay in C\{0}: f_t o loop homotopic to loop
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662
CONTRACT_ID: paper.step:connected-homotopy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: loop mcl L in C\L_t
SOURCE_QUANTIFIERS: t
SOURCE_CONCLUSION: (r,s) -> f_s(mcl L(r)) is continuous on [0,1]x[0,t] with values in C\{0}, hence f_t o mcl L is homotopic to mcl L in C\{0}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-loewner.well-defined, defn-hulls.left, step:flow-continuity
ROUTES: -
ROUTE_FOR: -
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662 | f_s(w) is defined for w not in L_t, s <= t
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662 | w not in L_t means T_w > t, so f_s(w) != 0 for s <= t
EDGE: step:flow-continuity | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662 | "The function (r,s) -> f_s(L(r)) is continuous"
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Continuity of the flow in (r,s) is asserted. T5: "a.s." in a deterministic lemma (L662 "Hence, a.s."): ignored.

NODE: step:connected-region-misses-hull
KIND: step
TITLE: Winding number argument: bounded region misses L_t
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L663
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L663
CONTRACT_ID: paper.step:connected-region-misses-hull
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: loop mcl L in C\L_t not surrounding 0; f_t o mcl L homotopic to mcl L in C\{0}
SOURCE_QUANTIFIERS: t
SOURCE_CONCLUSION: f_t o mcl L does not surround the origin, hence the region bounded by mcl L does not intersect L_t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:connected-homotopy, claim:gt-conformal
ROUTES: -
ROUTE_FOR: -
EDGE: step:connected-homotopy | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662 | homotopy of f_t o mcl L to mcl L in C\{0}
EDGE: claim:gt-conformal | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662 | f_t is conformal (injective, holomorphic) on C\L_t so the winding number around its zero set transfers
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP (T5): "f_t o L homotopic to L, hence the region bounded by L misses L_t" is a sketch; the transfer of winding numbers through the conformal map f_t is not written. DEPS on claim:gt-conformal is the extractor reading of what the sketch needs (uncertain).

NODE: lem-connected.left
KIND: theorem
TITLE: Left hulls are connected
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L658-L666
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L661-L663
CONTRACT_ID: paper.lem2_4.leftHull
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U : [0,infinity) -> C continuous
SOURCE_QUANTIFIERS: U; t >= 0
SOURCE_CONCLUSION: L_t is connected (and nonempty)
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Lemma_2_4_LeftHull.lean
FROZEN_DECL: ComplexSLE.lemma_2_4_leftHull
FROZEN_ANCHOR_ID: thm.lemma_2_4_leftHull.v1
FROZEN_ABI_SHA256: 346e1871675ffbff3149f1eba8ce7064deda3bae36480f3631f217663d08e7ab
DEPS: defn-hulls.left, claim:hull-nonempty, step:connected-loop-criterion, step:connected-homotopy, step:connected-region-misses-hull
ROUTES: -
ROUTE_FOR: -
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L659-L659 | statement is about L_t
EDGE: claim:hull-nonempty | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L659-L659 | nonemptiness part of the frozen IsConnected
EDGE: step:connected-loop-criterion | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662 | "enough to show" reduction
EDGE: step:connected-homotopy | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662 | homotopy argument
EDGE: step:connected-region-misses-hull | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662 | conclusion of the argument
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Root (left hull only, R16; the right hull follows from duality (2.4), excluded: feeds no root). Typo T5.

NODE: step:endpt-liminf
KIND: step
TITLE: liminf |f_t(z)| = 0 at a finite absorbing time
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L674-L675
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L674-L674
CONTRACT_ID: paper.step:endpt-liminf
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U continuous; T_z < infinity
SOURCE_QUANTIFIERS: U; z
SOURCE_CONCLUSION: liminf_{t -> T_z^-} |f_t(z)| = 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: ext:picard-lindelof, defn-loewner.absorbing-time, defn-loewner.well-defined
ROUTES: -
ROUTE_FOR: -
EDGE: ext:picard-lindelof | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L674-L674 | "standard existence results for solutions to ODEs": maximal solution exists until the liminf of ∣g-U∣ vanishes
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L674-L674 | T_z is the maximal existence time
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L674-L674 | solution on [0,T_z)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Characterization of the maximal existence time stated without proof.

NODE: step:endpt-upcrossing-bound
KIND: step
TITLE: Upcrossings of [alpha,beta] have duration at least epsilon
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L677-L689
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L679-L689
CONTRACT_ID: paper.step:endpt-upcrossing-bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U continuous; T_z < infinity; 0 < alpha < beta
SOURCE_QUANTIFIERS: U; z; alpha, beta
SOURCE_CONCLUSION: beta - alpha <= 2 alpha^{-1}(t2-t1) + rho(t2-t1) hence t2 - t1 >= eps(T_z,alpha,beta) for each upcrossing
CONSTANT_SCOPE: eps depends on T_z, alpha, beta (and the modulus of continuity of U on [0,T_z])
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-loewner.solution, defn-loewner.well-defined
ROUTES: -
ROUTE_FOR: -
EDGE: defn-loewner.solution | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L680-L687 | integral form of the ODE gives (2.7) ∣f_{t2}-f_{t1}∣ <= int 2/∣f∣ ds + ∣U_{t1}-U_{t2}∣
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L680-L680 | f_t(z) defined on [0,T_z)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Includes the uniform continuity / modulus rho of U on the compact [0,T_z] (Heine-Cantor, below threshold).

NODE: step:endpt-finite-upcrossings
KIND: step
TITLE: Finitely many upcrossings before T_z
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L690-L690
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L690-L690
CONTRACT_ID: paper.step:endpt-finite-upcrossings
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: T_z < infinity; each upcrossing has length >= eps
SOURCE_QUANTIFIERS: U; z; alpha < beta
SOURCE_CONCLUSION: the number of upcrossings of [alpha,beta] is at most T_z/eps
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:endpt-upcrossing-bound
ROUTES: -
ROUTE_FOR: -
EDGE: step:endpt-upcrossing-bound | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L689-L690 | the lower bound eps on upcrossing durations plus disjointness of intervals
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Disjoint-interval counting.

NODE: lem-endpt-cont
KIND: lemma
TITLE: |f_t(z)| tends to 0 at the absorbing time
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L667-L672
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L673-L691
CONTRACT_ID: paper.lem-endpt-cont
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U : [0,infinity) -> C continuous; z in C; T_z < infinity
SOURCE_QUANTIFIERS: U; z
SOURCE_CONCLUSION: lim_{t -> T_z^-} |f_t(z)| = 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-loewner.absorbing-time, step:endpt-upcrossing-reduction
ROUTES: -
ROUTE_FOR: -
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L668-L668 | T_z is the absorbing time
EDGE: step:endpt-upcrossing-reduction | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L675-L690 | liminf = 0 plus finitely many upcrossings of every [alpha,beta] gives the limit
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Also the claim at L268. Quantifier closure over rational alpha<beta from the finite-upcrossing statement is implicit in "it suffices" (not a separate node). Consumed throughout (L824, L1395, L2134).

NODE: step:bm-scaling
KIND: step
TITLE: Brownian scaling for the planar driver
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-scaling@L779-L779
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-scaling@L779-L779
CONTRACT_ID: paper.step:bm-scaling
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U planar BM with covariance Sigma (R6)
SOURCE_QUANTIFIERS: r > 0
SOURCE_CONCLUSION: s -> r^{-1} U_{r^2 s} is again a planar BM with covariance Sigma
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-sle
ROUTES: -
ROUTE_FOR: -
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-scaling@L779-L779 | "Brownian scaling": continuity, independent increments and Gaussian increments are preserved
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Standard; kept as a step because the SLE_Sigma driver structure (R6) is a concrete property to verify.

NODE: lem-scaling
KIND: lemma
TITLE: Scale invariance of SLE_Sigma
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-scaling@L774-L776
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-scaling@L778-L780
CONTRACT_ID: paper.lem-scaling
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f_t centered Loewner chain for an SLE_Sigma; r > 0
SOURCE_QUANTIFIERS: r
SOURCE_CONCLUSION: (r^{-1} f_{r^2 t}(r.))_{t >= 0} has the law of a centered SLE_Sigma chain
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-scale, step:bm-scaling, defn-sle
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-scale | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-scaling@L779-L779 | "scaling property (2.1)" identifies the rescaled chain as the chain driven by r^{-1}U(r^2 .)
EDGE: step:bm-scaling | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-scaling@L779-L779 | "Brownian scaling" gives the law of the rescaled driver
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-scaling@L775-L775 | SLE_Sigma chain
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The full (2.1) (with f_t) is needed because the statement concerns f_t. Consumed in slices C, D.

NODE: step:markov-driver
KIND: step
TITLE: Strong Markov property for the planar driver
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-markov@L788-L788
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-markov@L788-L788
CONTRACT_ID: paper.step:markov-driver
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: T stopping time for the filtration of the driving BM; U planar BM with covariance Sigma
SOURCE_QUANTIFIERS: T
SOURCE_CONCLUSION: s -> U_{T+s} - U_T is independent of F_T and distributed as U
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: ext:strong-markov-bm, defn-sle
ROUTES: -
ROUTE_FOR: -
EDGE: ext:strong-markov-bm | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-markov@L788-L788 | "immediate from the strong Markov property of Brownian motion"
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-markov@L783-L783 | driver is a planar BM with covariance Sigma
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: T finite a.s. (or on {T < infinity}) is implicit in the source. The filtration is written as that of the "driving Brownian motion B_t"; read as the natural filtration of U (uncertain).

NODE: lem-markov
KIND: lemma
TITLE: Markov property of SLE_Sigma
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-markov@L782-L785
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-markov@L787-L789
CONTRACT_ID: paper.lem-markov
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f_t centered SLE_Sigma; T stopping time w.r.t. the filtration of the driving BM
SOURCE_QUANTIFIERS: T
SOURCE_CONCLUSION: the chain (f_{T,s+T})_{s >= 0} from (2.3) is independent of F_T and has the law of a centered SLE_Sigma chain
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-conc, step:markov-driver, defn-sle
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-conc | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-markov@L783-L783 | f_{T,s+T} is the Loewner chain of the shifted driver U(.+T)-U(T) defined in (2.3)
EDGE: step:markov-driver | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-markov@L788-L788 | independence and law of the shifted driver
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-markov@L783-L783 | SLE_Sigma chain
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Measurability of the map from driver path to chain is implicit.

NODE: nonsource.exists-sle-driver
KIND: theorem
TITLE: Existence of an SLE_Sigma driver
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#defn-sle@L301-L308
PROOF_SOURCE: external:standard#brownian-motion-existence
CONTRACT_ID: paper.nonsource.existsSLEDriver
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a, b > 0; c^2 <= ab (R5, R13)
SOURCE_QUANTIFIERS: a,b,c
SOURCE_CONCLUSION: there is a probability space carrying a planar BM U with covariance Sigma (SLE_Sigma driver)
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/ExistsSLEDriver.lean
FROZEN_DECL: ComplexSLE.exists_sleDriver
FROZEN_ANCHOR_ID: thm.exists_sleDriver.v1
FROZEN_ABI_SHA256: cb6850fe26b9549e5e5795f68670c65beb5f354084bfe7c0b086b6192ca62fdc
DEPS: defn-sle, ext:bm-existence
ROUTES: -
ROUTE_FOR: -
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-sle@L307-L307 | the statement asserts existence of an object satisfying the driver definition
EDGE: ext:bm-existence | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-sle@L307-L307 | existence of planar BM with covariance Sigma
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Non-source root (R13): the paper takes the existence for granted at Def 1.4.

NODE: thm-phases
KIND: theorem
TITLE: Phases of SLE_Sigma
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L437-L449
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L1930-L1932
CONTRACT_ID: paper.thm1_8.phases
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a, b > 0; c^2 <= ab (R5); p admissible in the sense of Lemma 2.14 (R7/R15)
SOURCE_QUANTIFIERS: a,b,c; p; four sign implications
SOURCE_CONCLUSION: (I)>=0 and (II)>0 => thin; (I)<0 and (II)>0 => swallowing; (I)<0 and (II)<0 => hitting; (I)>=0 and (II)<0 => dense
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Theorem_1_8.lean
FROZEN_DECL: ComplexSLE.theorem_1_8
FROZEN_ANCHOR_ID: thm.theorem_1_8.v1
FROZEN_ABI_SHA256: a6e1ebdf58aaf0db8d9b0eecfdd5cb139c91a84c01bda7b0b4de6db3e4f5475b
DEPS: defn-phases.thin, defn-phases.swallowing, defn-phases.hitting, defn-phases.dense, item-I, item-II, lem-stationary.admissible, thm-phases#assembly-sign-cases
ROUTES: -
ROUTE_FOR: -
EDGE: defn-phases.thin | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L445-L445 | thin conclusion
EDGE: defn-phases.swallowing | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L446-L446 | swallowing conclusion
EDGE: defn-phases.hitting | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L447-L447 | hitting conclusion
EDGE: defn-phases.dense | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L448-L448 | dense conclusion
EDGE: item-I | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L440-L440 | sign condition on (I)
EDGE: item-II | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L441-L441 | sign condition on (II)
EDGE: lem-stationary.admissible | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L428-L432 | p is a non-negative periodic solution of (1.11) with regularity (admissibility)
EDGE: thm-phases#assembly-sign-cases | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L1930-L1932 | "Combine Propositions 3.1 and 3.2": the four sign cases are assembled from Props 3.1/3.2 (merge adjudication, see slice C NOTE)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Root; R4 (z != 0), R5, R7, R17 (c = 0 part split off). Proof is the single sentence at L1930-1932; slice C owns the Props; per spec Section 9 this node depends on canonical C IDs directly. Footnote 1 and (1.11) say 2pi-periodic; Lemma 2.14 admissibility says pi-periodic (P4). mu and D enter only through admissibility (slice B).

NODE: thm-phases.c-zero
KIND: theorem
TITLE: Phases of SLE_Sigma when c = 0
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L450-L450
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L1930-L1932
CONTRACT_ID: paper.thm1_8.cZero
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a, b > 0 (R5); c = 0
SOURCE_QUANTIFIERS: a, b
SOURCE_CONCLUSION: thin if a-b <= 4; swallowing if 4 < a-b < 8; hitting if a-b >= 8
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Theorem_1_8_CZero.lean
FROZEN_DECL: ComplexSLE.theorem_1_8_c_zero
FROZEN_ANCHOR_ID: thm.theorem_1_8_c_zero.v1
FROZEN_ABI_SHA256: 2ac1a2c03ab122e2d2b04cd9d4f8d9ceaa4f35e452106838a9322f0c47d08bcd
DEPS: defn-phases.thin, defn-phases.swallowing, defn-phases.hitting, thm-phases#assembly-c-zero
ROUTES: -
ROUTE_FOR: -
EDGE: defn-phases.thin | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L450-L450 | thin conclusion
EDGE: defn-phases.swallowing | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L450-L450 | swallowing conclusion
EDGE: defn-phases.hitting | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L450-L450 | hitting conclusion
EDGE: thm-phases#assembly-c-zero | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-phases@L1930-L1932 | "Combine ... with Lemmas 3.11 and 3.12": the c = 0 description is the union of Lemmas 3.11 and 3.12
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Root; R8/P8: a-b = 8 lies in the hitting phase through Lemma 3.12. The statement is "if c = 0" at L450 and does not mention p; frozen with three conclusions.

NODE: thm-disconnects.a
KIND: theorem
TITLE: SLE_Sigma disconnects points: (a)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L502-L507
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2199-L2225
CONTRACT_ID: paper.thm1_10.a
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a, b > 0 (the source a,b != 0 with PSD; R5 audit); c in [-sqrt(ab), sqrt(ab)]
SOURCE_QUANTIFIERS: z in C\{0} (R4); a.s.
SOURCE_CONCLUSION: exists t > 0 with z not in L_t and L_t disconnects z from infinity
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Theorem_1_10_A.lean
FROZEN_DECL: ComplexSLE.theorem_1_10_a
FROZEN_ANCHOR_ID: thm.theorem_1_10_a.v1
FROZEN_ABI_SHA256: 4075bd36d6a8503eb38319a978b1826157dc31f0b0800820be15fde67340548a
DEPS: def-disconnect, defn-sle, defn-hulls.left, thm-disconnects#proof-a
ROUTES: -
ROUTE_FOR: -
EDGE: def-disconnect | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L502-L502 | "L_t disconnects ... from infinity"
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L504-L504 | driver is an SLE_Sigma BM
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L504-L504 | statement is about left hulls L_t
EDGE: thm-disconnects#proof-a | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2199-L2225 | proof assembly of assertion (a) in Section 4
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Root. The source says "for each z in C"; R4 excludes z = 0 (0 in L_t for all t).

NODE: thm-disconnects.b
KIND: theorem
TITLE: SLE_Sigma disconnects points: (b)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L502-L509
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2199-L2225
CONTRACT_ID: paper.thm1_10.b
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a, b > 0 and c in [-sqrt(ab), sqrt(ab)]
SOURCE_QUANTIFIERS: a.s.; for all t > 0
SOURCE_CONCLUSION: the set of points disconnected from infinity by L_t has nonempty interior
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Theorem_1_10_B.lean
FROZEN_DECL: ComplexSLE.theorem_1_10_b
FROZEN_ANCHOR_ID: thm.theorem_1_10_b.v1
FROZEN_ABI_SHA256: a4e294f2aeaf5af14560b8ff75ed1e705bf450412093f7d1877c04ce72501f47
DEPS: def-disconnect, defn-sle, defn-hulls.left, thm-disconnects#proof-b
ROUTES: -
ROUTE_FOR: -
EDGE: def-disconnect | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L502-L502 | "L_t disconnects ... from infinity"
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L504-L504 | driver is an SLE_Sigma BM
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L504-L504 | statement is about left hulls L_t
EDGE: thm-disconnects#proof-b | source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L2199-L2225 | proof assembly of assertion (b) in Section 4
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Root. P7: uniform in t: a.s., for every t > 0. By Definition 1.9 points of L_t count as disconnected, so (b) does not itself say that C\L_t is disconnected.

NODE: ext:picard-lindelof
KIND: external
TITLE: Picard-Lindelof ODE existence and uniqueness
STATEMENT_SOURCE: external:standard#picard-lindelof
PROOF_SOURCE: external:standard#proof
CONTRACT_ID: paper.ext:picard-lindelof
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Picard-Lindelof ODE existence and uniqueness
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: In Mathlib; first cited at L674 ("standard existence results for solutions to ODEs").

NODE: ext:lawler-4.5
KIND: external
TITLE: Lawler Theorem 4.5: g_t is conformal onto H minus hull; z(g_t-z) -> 2t
STATEMENT_SOURCE: external:lawler-book#thm-4.5
PROOF_SOURCE: external:lawler-book#proof
CONTRACT_ID: paper.ext:lawler-4.5
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Lawler Theorem 4.5: g_t is conformal onto H minus hull; z(g_t-z) -> 2t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: Cited by analogy at L286; extension to complex driving function and C is asserted: SOURCE_GAP.

NODE: ext:strong-markov-bm
KIND: external
TITLE: Strong Markov property of Brownian motion
STATEMENT_SOURCE: external:standard#strong-markov-brownian-motion
PROOF_SOURCE: external:standard#proof
CONTRACT_ID: paper.ext:strong-markov-bm
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Strong Markov property of Brownian motion
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: Canonical ID per spec; cited at L788.

NODE: ext:bm-existence
KIND: external
TITLE: Existence of planar Brownian motion with covariance Sigma
STATEMENT_SOURCE: external:standard#brownian-motion-existence
PROOF_SOURCE: external:standard#proof
CONTRACT_ID: paper.ext:bm-existence
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Existence of planar Brownian motion with covariance Sigma
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: Canonical ID per spec; used only by the non-source root.

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

NODE: ext:ito-complex
KIND: external
TITLE: Ito formula for complex semimartingales
STATEMENT_SOURCE: external:protter#II.35
PROOF_SOURCE: -
CONTRACT_ID: paper.ext:ito-complex
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Ito's formula for (complex) continuous semimartingales (Protter, Ch. II, Thm 35); used in slice B also for real C^2 functions of a real diffusion (Lemma A.1).
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: External input (policy EXTERNAL_POLICY); canonical ID from EXTRACTION_SPEC section 5. First cited in slice B; orchestrator deduplicates.

NODE: ext:levy-characterization
KIND: external
TITLE: Levy characterization / Dambis-Dubins-Schwarz
STATEMENT_SOURCE: external:standard#levy-characterization
PROOF_SOURCE: -
CONTRACT_ID: paper.ext:levy-characterization
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Continuous (local) martingales with prescribed quadratic (cross-)variations are Brownian motions (equal in law), including time-change/representation form dM = sqrt(h) dW'.
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: External input (policy EXTERNAL_POLICY); canonical ID from EXTRACTION_SPEC section 5. First cited in slice B; orchestrator deduplicates.

NODE: ext:hormander-1d
KIND: external
TITLE: Hormander criterion, one-dimensional case
STATEMENT_SOURCE: external:hairer-hormander#thm-1.3
PROOF_SOURCE: -
CONTRACT_ID: paper.ext:hormander-1d
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: One-dimensional Hormander criterion of Hairer (Thm 1.3): if beta(u) and beta'(u)gamma(u)-gamma'(u)beta(u) span R at every u, the Stratonovich SDE dX=gamma dt+beta o dB has smooth transition densities and smooth semigroup.
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: External input (policy EXTERNAL_POLICY); canonical ID from EXTRACTION_SPEC section 5. First cited in slice B; orchestrator deduplicates.

NODE: ext:scale-function
KIND: external
TITLE: Scale-function hitting lemma
STATEMENT_SOURCE: external:lawler-book#lemma-1.24
PROOF_SOURCE: -
CONTRACT_ID: paper.ext:scale-function
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Lawler [Lemma 1.24]: positive probability that a one-dimensional diffusion with scale function psi exits an interval at the endpoint where psi is bounded below.
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: External input (policy EXTERNAL_POLICY); canonical ID from EXTRACTION_SPEC section 5. First cited in slice B; orchestrator deduplicates.

NODE: ext:martingale-convergence
KIND: external
TITLE: Levy upward martingale convergence (conditional Borel-Cantelli)
STATEMENT_SOURCE: external:standard#levy-upward-martingale-convergence
PROOF_SOURCE: -
CONTRACT_ID: paper.ext:martingale-convergence
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Levy's upward theorem, from which the conditional second Borel-Cantelli lemma follows (in Mathlib).
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: External input (policy EXTERNAL_POLICY); canonical ID from EXTRACTION_SPEC section 5. First cited in slice B; orchestrator deduplicates.

NODE: ext:dct
KIND: external
TITLE: Dominated convergence
STATEMENT_SOURCE: external:standard#dominated-convergence
PROOF_SOURCE: -
CONTRACT_ID: paper.ext:dct
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Dominated convergence theorem (in Mathlib).
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: External input (policy EXTERNAL_POLICY); canonical ID from EXTRACTION_SPEC section 5. First cited in slice B; orchestrator deduplicates.

NODE: defn-sigma
KIND: definition
TITLE: sigma-time parametrization of a centered SLE_Sigma at a fixed point
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#defn-sigma@L836-L844
PROOF_SOURCE: -
CONTRACT_ID: paper.defn-sigma
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (f_t) a centered SLE_Sigma; z in C
SOURCE_QUANTIFIERS: forall (f_t); forall z
SOURCE_CONCLUSION: sigma=sigma_z is defined by t~ = int_0^{sigma(t~)} |f_s(z)|^-2 ds (eqn-defn-sigma), parametrizing (f_t)_{t in (0,T_z)}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-sle, defn-loewner.absorbing-time, defn-loewner.well-defined
ROUTES: -
ROUTE_FOR: -
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-sigma@L838-L838 | centered SLE_Sigma maps f_t supply f_s(z)
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-sigma@L839-L839 | domain (0,T_z) of the time change uses the absorbing time
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-sigma@L842-L842 | the integrand ∣f_s(z)∣^-2 uses the centered chain f_s(z) = g_s(z) - U_s, whose existence and uniqueness up to T_z is that theorem
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Covers eqn-defn-sigma. Range claim (sigma onto (0,T_z)) is deferred to remark-sigma. z=0 degenerate (T_0=0, R4): the source says 'for z in C' without exclusion; use only for z != 0 downstream. Time-change stated for t in (0,T_z) (source writes domain loosely).

NODE: step:arg-lift
KIND: step
TITLE: Existence and uniqueness of the continuous argument lift
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#def-arg@L851-L853
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#def-arg@L851-L853
CONTRACT_ID: paper.step:arg-lift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (f_t) centered SLE_Sigma; z in C; t in [0,T_z); f_t(z) != 0 for t<T_z
SOURCE_QUANTIFIERS: forall z; exists unique continuous theta_.(z)
SOURCE_CONCLUSION: there is a unique continuous t -> theta_t(z) on [0,T_z) with f_t(z)/|f_t(z)| = e^{i theta_t(z)} and theta_0(z) in [0,2pi)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-loewner.absorbing-time, defn-sle, defn-loewner.well-defined
ROUTES: -
ROUTE_FOR: -
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#def-arg@L852-L852 | f_t(z) nonvanishing and continuous for t<T_z
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#def-arg@L852-L852 | f_t(z) is a continuous process built from the driver
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#def-arg@L852-L852 | f_t(z) is the (unique) solution, continuous in t and nonzero for t<T_z, so the lift to the covering R -> S^1 exists
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Well-definedness of Def 2.10 (path-lifting for the covering R->S^1). SOURCE_GAP: the source asserts 'the unique continuous process' without argument; measurability of theta_t as a process is also unstated.

NODE: def-arg
KIND: definition
TITLE: Argument process theta_t(z)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#def-arg@L851-L853
PROOF_SOURCE: -
CONTRACT_ID: paper.def-arg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (f_t) centered SLE_Sigma; z in C
SOURCE_QUANTIFIERS: forall z
SOURCE_CONCLUSION: theta_t(z) is the unique continuous argument of f_t(z) on [0,T_z) with theta_0(z) in [0,2pi)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:arg-lift
ROUTES: -
ROUTE_FOR: -
EDGE: step:arg-lift | source/arxiv-2203.07313v4/complex-sle-final.tex#def-arg@L852-L852 | existence/uniqueness of the continuous lift is what makes the definition meaningful
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Normalization theta_0 in [0,2pi) is used when the random point zz has angle density on [0,2pi].

NODE: lem-polar
KIND: lemma
TITLE: Polar decomposition of SLE_Sigma
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L856-L890
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L903-L929
CONTRACT_ID: paper.lem-polar
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (f_t) centered SLE_Sigma with driving BMs B, B~ as in (1.6) (Sigma PSD, ab>0 needed for the B,B~ representation); z in C fixed; mu,nu as in (2.nu-D)
SOURCE_QUANTIFIERS: forall (f_t); forall z in C; sigma=sigma_z
SOURCE_CONCLUSION: hat-theta_t~ = theta_sigma(t~)(z) and hat-f_t~ = f_sigma(t~)(z) satisfy (2.25) dtheta = mu dt~ - sqrt(a) sin(theta) dW + sqrt(b) cos(theta) dW~; (2.26) dlog|f| = nu dt~ + sqrt(a) cos(theta) dW + sqrt(b) sin(theta) dW~; (2.27) dlog|f'| = -2cos(2theta) dt~; where (W,W~) =_d (B,B~)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-sigma, def-arg, eqn-def-ft, eqn-nu-D.mu, eqn-nu-D.nu, step:polar-time-change, step:polar-W-law, step:polar-derivative-sde
ROUTES: -
ROUTE_FOR: -
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L865-L865 | sigma-time parametrization
EDGE: def-arg | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L865-L868 | theta_t(z)
EDGE: eqn-def-ft | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L858-L858 | SDE for f_t(z) driven by B,B~
EDGE: eqn-nu-D.mu | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L860-L863 | coefficient mu in (2.25)
EDGE: eqn-nu-D.nu | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L860-L863 | coefficient nu in (2.26)
EDGE: step:polar-time-change | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L922-L926 | time-changed SDEs (2.25),(2.26)
EDGE: step:polar-W-law | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L927-L927 | (W,W~) =_d (B,B~)
EDGE: step:polar-derivative-sde | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L928-L928 | (2.27)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Covers eqn-def-mu, eqn-theta-t, eqn-abs-zt, eqn-abs-zt' (P= (2.25)-(2.27)). Typo reading: statement writes d log|f_t'(z)| with hat-f_t (uses t, not t~) in (2.27); read as hat-f_{t~}. R6 driver representation is step:driver-representation (slice A) used inside step:polar-ito-log. Circularity note: the statement presupposes sigma_z defined on (0,infty), which remark-sigma deduces from this lemma; treated as local (t~-range of sigma) with no graph cycle, remark-sigma depends on lem-polar.

NODE: step:polar-ito-log
KIND: step
TITLE: Ito computation of d log f_t(z)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L904-L910
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L904-L910
CONTRACT_ID: paper.step:polar-ito-log
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f_t(z) solves (1.6); t<T_z
SOURCE_QUANTIFIERS: forall t<T_z
SOURCE_CONCLUSION: d log f_t(z) = f^-2 (2 - a/2 + b/2 - ic) dt + f^-1 (sqrt a dB + i sqrt b dB~), expanded in polar form with theta_t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-def-ft, step:driver-representation, ext:ito-complex, def-arg
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-def-ft | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L904-L904 | SDE for f_t(z) is the input to Ito
EDGE: step:driver-representation | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L908-L908 | U = sqrt a B + i sqrt b B~ gives the stated martingale term
EDGE: ext:ito-complex | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L904-L904 | Ito's lemma for complex semimartingales applied to log
EDGE: def-arg | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L909-L909 | polar form uses f_t = ∣f_t∣ e^{i theta_t}
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The bracket d<f,f> is folded into the stated drift; no separate hypothesis. log is applied along a continuous branch (log|f|+i theta).

NODE: step:polar-real-imag
KIND: step
TITLE: Real and imaginary parts: SDEs for log|f_t| and theta_t in capacity time
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L911-L921
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L911-L921
CONTRACT_ID: paper.step:polar-real-imag
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d log f_t(z) as in step:polar-ito-log
SOURCE_QUANTIFIERS: forall t<T_z
SOURCE_CONCLUSION: d log|f_t| = |f_t|^-2 nu(theta_t)dt + |f_t|^-1 (sqrt a cos dB + sqrt b sin dB~) (eqn-abs-zt-op); d theta_t = |f_t|^-2 mu(theta_t) dt - |f_t|^-1 (sqrt a sin dB + sqrt b cos dB~) (eqn-theta-t-op)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:polar-ito-log, eqn-nu-D.mu, eqn-nu-D.nu, def-arg
ROUTES: -
ROUTE_FOR: -
EDGE: step:polar-ito-log | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L911-L911 | real and imaginary parts taken
EDGE: eqn-nu-D.mu | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L918-L918 | identification of imaginary drift with mu
EDGE: eqn-nu-D.nu | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L913-L913 | identification of real drift with nu
EDGE: def-arg | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L917-L917 | imaginary part of the continuous log is theta_t
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Covers eqn-abs-zt-op, eqn-theta-t-op.

NODE: step:polar-time-change
KIND: step
TITLE: Time change by sigma: definition of W, W~ and the sigma-time SDEs
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L922-L926
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L922-L926
CONTRACT_ID: paper.step:polar-time-change
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (2.28),(2.29) hold; sigma as in defn-sigma
SOURCE_QUANTIFIERS: forall t~
SOURCE_CONCLUSION: with W_t~ = int_0^sigma(t~) |f_s|^-1 dB_s and W~ likewise, hat-theta and log|hat-f| satisfy (2.25) and (2.26)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:polar-real-imag, defn-sigma
ROUTES: -
ROUTE_FOR: -
EDGE: step:polar-real-imag | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L922-L922 | SDEs in capacity time being time-changed
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L924-L924 | sigma and its inverse relation t~ = int ∣f∣^-2
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Time change of stochastic integrals by the (stopping-time) family sigma(t~); sigma domain issue (circularity with remark-sigma) noted in lem-polar.

NODE: step:polar-W-law
KIND: step
TITLE: (W,W~) has the law of (B,B~)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L927-L927
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L927-L927
CONTRACT_ID: paper.step:polar-W-law
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W,W~ as in step:polar-time-change
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: (W_t~,W~_t~) =_d (B_t~,B~_t~): continuous martingales with the same quadratic variations (t~) and cross-variations (c t~/sqrt(ab))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: ext:levy-characterization, defn-sigma, step:polar-time-change, step:driver-representation
ROUTES: -
ROUTE_FOR: -
EDGE: ext:levy-characterization | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L927-L927 | equality of law from equal quadratic (cross-)variations
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L927-L927 | <W>_t~ = int_0^sigma(t~) ∣f∣^-2 ds = t~ by the definition of sigma
EDGE: step:polar-time-change | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L924-L927 | W and W~ are the stochastic integrals defined there
EDGE: step:driver-representation | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L927-L927 | (B,B~) are standard BMs with cross-variation c t/sqrt(ab)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Needs sigma(t~) < infinity for all t~ (see remark-sigma) so W is defined on all of [0,infty).

NODE: step:polar-derivative-sde
KIND: step
TITLE: SDE for log|f_t'(z)| and its sigma-time version
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L928-L928
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L928-L928
CONTRACT_ID: paper.step:polar-derivative-sde
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f_t(z) solves (1.6)
SOURCE_QUANTIFIERS: forall t<T_z
SOURCE_CONCLUSION: d log f_t'(z) = -2 f_t(z)^-2 dt; real part and time change by sigma give d log|hat-f'| = -2cos(2 hat-theta) dt~
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-def-ft, defn-sigma, def-arg
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-def-ft | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L928-L928 | differentiate the SDE for f_t(z) in z
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L928-L928 | time change
EDGE: def-arg | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L928-L928 | f_t^-2 = ∣f_t∣^-2 e^{-2i theta_t}, real part -2cos(2 theta)/∣f∣^2
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: differentiation of the SDE with respect to z (interchange of derivative and stochastic integral, z-differentiability of f_t(z)) is asserted, not justified. Only the ODE-like drift term appears since the noise term is z-independent.

NODE: remark-sigma
KIND: claim
TITLE: sigma_z is defined on all of (0,infty) and maps it onto (0,T_z)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#remark-sigma@L893-L896
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#remark-sigma@L893-L896
CONTRACT_ID: paper.remark-sigma
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (f_t) centered SLE_Sigma; z in C (R5 not required by the source)
SOURCE_QUANTIFIERS: forall z
SOURCE_CONCLUSION: a.s. the domain of sigma_z is (0,infty) (and sigma maps (0,infty) onto (0,T_z))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-polar, step:sigma-bounded-coefficients, lem-endpt-cont, defn-sigma
ROUTES: -
ROUTE_FOR: -
EDGE: lem-polar | source/arxiv-2203.07313v4/complex-sle-final.tex#remark-sigma@L893-L893 | SDEs with bounded coefficients on the sigma-time scale
EDGE: step:sigma-bounded-coefficients | source/arxiv-2203.07313v4/complex-sle-final.tex#remark-sigma@L894-L895 | ∣hat f∣ and ∣hat f'∣ bounded away from 0, infinity on compacts
EDGE: lem-endpt-cont | source/arxiv-2203.07313v4/complex-sle-final.tex#remark-sigma@L895-L895 | lim ∣f_t(z)∣ = 0 as t -> T_z- on {T_z<infinity}
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#remark-sigma@L894-L895 | the claim concerns the domain of sigma_z defined by t~ = int_0^sigma ∣f_s∣^-2 ds
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Covers inv:L847 range claim. SOURCE_GAP: the argument rules out finite domain by contradiction when T_z<infinity; the case T_z=infinity (sigma finite domain with sigma(T-) = infinity) and surjectivity onto (0,T_z) are not argued.

NODE: step:sigma-bounded-coefficients
KIND: step
TITLE: Bounded coefficients keep |hat f| and |hat f'| away from 0 and infinity on compacts
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#remark-sigma@L894-L894
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#remark-sigma@L894-L894
CONTRACT_ID: paper.step:sigma-bounded-coefficients
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: SDEs (2.26),(2.27) have bounded coefficients
SOURCE_QUANTIFIERS: forall compact [0,T] in the domain of sigma
SOURCE_CONCLUSION: a.s. sup and inf of |hat f_t~|, |hat f'_t~| over [0,T] are finite/positive, hence liminf_{t->T-} |hat f_t| > 0 if the domain were [0,T]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-polar
ROUTES: -
ROUTE_FOR: -
EDGE: lem-polar | source/arxiv-2203.07313v4/complex-sle-final.tex#remark-sigma@L894-L894 | (2.26),(2.27) give the semimartingale decompositions of log∣hat f∣ and log∣hat f'∣
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Standard fact on SDEs with bounded drift and diffusion coefficients (non-explosion of the logarithm).

NODE: lem-stationary.admissible
KIND: definition
TITLE: Admissible stationary density (hypothesis package of Lemma 2.14)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L963-L966
PROOF_SOURCE: -
CONTRACT_ID: paper.def.IsAdmissibleDensity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: forall a,b,c; forall p: R -> R
SOURCE_CONCLUSION: IsAdmissibleDensity a b c p: p continuous, p>=0, pi-periodic, int_0^{2pi} p = 1, and exists x with p twice continuously differentiable on R minus (x+pi Z) solving -[mu p]' + [D p]'' = 0 there, and D p continuously differentiable on R (mu,D of (2.nu-D))
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Defs/IsAdmissibleDensity.lean
FROZEN_DECL: ComplexSLE.IsAdmissibleDensity
FROZEN_ANCHOR_ID: def.IsAdmissibleDensity.v1
FROZEN_ABI_SHA256: 2429786912c3915fecf74d5df2467dd2b5c0a7d89ff34a4e3f77a86c0af43b7c
DEPS: eqn-nu-D.mu, eqn-nu-D.D
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-nu-D.mu | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L965-L965 | the ODE (2.13) uses mu
EDGE: eqn-nu-D.D | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L965-L965 | the ODE (2.13) and the C^1 condition use D
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: R7/R15: Lemma 2.14's hypotheses define admissibility; Thm 1.8 and Props 3.1/3.2 hold for every admissible p. The null-set vanishing property is NOT a hypothesis (SOURCE_GAP step handled by slice C).

NODE: lem-stationary
KIND: lemma
TITLE: Stationarity of the argument process started from an admissible density
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L963-L967
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L972-L994
CONTRACT_ID: paper.lem-stationary
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b>0; c^2<=ab (R5); p admissible (IsAdmissibleDensity); zz random point on the unit circle independent of the driving BM with angle density p 1_[0,2pi]
SOURCE_QUANTIFIERS: forall a,b,c; forall admissible p; zz independent of U
SOURCE_CONCLUSION: the law of e^{i theta_{sigma(t~)}(zz)} = f_sigma(t~)(zz)/|f_sigma(t~)(zz)| is stationary in t~
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-stationary.admissible, lem-polar, step:stat-martingale-qv, step:stat-theta-bm-sde, step:stat-apply-kolmogorov-noncritical, step:stat-apply-kolmogorov-critical, step:stat-pi-reduction
ROUTES: -
ROUTE_FOR: -
EDGE: lem-stationary.admissible | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L963-L966 | hypotheses of the lemma are admissibility of p
EDGE: lem-polar | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L973-L977 | SDE (2.25) for hat-theta provides the martingale part M
EDGE: step:stat-martingale-qv | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L973-L979 | <M> = 2D dt~ and dM = sqrt(2D) dW'
EDGE: step:stat-theta-bm-sde | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L980-L983 | one-noise SDE (2.30) on which Lemma A.1 is run
EDGE: step:stat-apply-kolmogorov-noncritical | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L988-L988 | case ∣c∣ != sqrt(ab)
EDGE: step:stat-apply-kolmogorov-critical | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L988-L993 | case c = +-sqrt(ab)
EDGE: step:stat-pi-reduction | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L984-L984 | from stationarity of e^{2i theta} to e^{i theta}
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: R7: for every admissible p. Remark: the source assumes zz independent of U; the SDE with random initial condition arg(zz) independent of (W',...) is used implicitly (SOURCE_GAP recorded in step:stat-theta-bm-sde).

NODE: step:stat-martingale-qv
KIND: step
TITLE: Martingale part of the theta-SDE has quadratic variation 2D and is sqrt(2D) dW'
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L973-L979
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L973-L979
CONTRACT_ID: paper.step:stat-martingale-qv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: hat-theta solves (2.25); M_t~ = -sqrt a int sin(hat theta) dW + sqrt b int cos(hat theta) dW~
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: M is a continuous martingale with d<M,M> = 2D(hat theta) dt~, hence dM = sqrt(2D(hat theta)) dW' for a standard BM W'
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-polar, eqn-nu-D.D, ext:levy-characterization
ROUTES: -
ROUTE_FOR: -
EDGE: lem-polar | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L973-L977 | SDE (2.25)
EDGE: eqn-nu-D.D | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L978-L978 | 2D = a sin^2 + b cos^2 - 2c sin cos is the quadratic variation density
EDGE: ext:levy-characterization | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L979-L979 | representation dM = sqrt(h) dW' of a martingale with absolutely continuous bracket (possibly on an enlarged space when h vanishes)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP-adjacent: when D vanishes (c=+-sqrt(ab)) W' is built from M via a martingale representation that needs an enlargement of the probability space; the source says 'where W' is a standard linear BM' without comment. Uses (W,W~) correlated with covariance structure of lem-polar.

NODE: step:stat-theta-bm-sde
KIND: step
TITLE: One-noise SDE for the sigma-time argument process
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L979-L983
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L979-L983
CONTRACT_ID: paper.step:stat-theta-bm-sde
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: M as in step:stat-martingale-qv
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: d hat-theta = mu(hat theta) dt~ + sqrt(2D(hat theta)) dW' (eqn-theta-t-bm), with initial condition arg(zz) ~ p 1_[0,2pi] independent of W'
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:stat-martingale-qv, lem-polar
ROUTES: -
ROUTE_FOR: -
EDGE: step:stat-martingale-qv | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L980-L980 | substitute dM into (2.25)
EDGE: lem-polar | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L980-L980 | SDE (2.25)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: independence of the initial angle from W' and the identification of the law of hat-theta with the law of THE solution of the SDE (weak uniqueness in law, including the degenerate case c=+-sqrt(ab) where the coefficient sqrt(2D) is only Lipschitz where D>0) are used when Lemma A.1 is applied but are not stated.

NODE: step:driver-negation-symmetry
KIND: step
TITLE: -U has the same law as U (reflection symmetry of the driver)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L984-L984
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L984-L984
CONTRACT_ID: paper.step:driver-negation-symmetry
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U planar BM with covariance Sigma (R6)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: (-U_t)_{t>=0} =_d (U_t)_{t>=0}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: defn-sle
ROUTES: -
ROUTE_FOR: -
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L984-L984 | Gaussian independent-increment definition is symmetric under negation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: 'reflection symmetry of Brownian motion', used for (f_t(zz))_t =_d (f_t(-zz))_t.

NODE: step:stat-pi-reduction
KIND: step
TITLE: Stationarity of e^{2i theta} implies stationarity of e^{i theta}
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L984-L984
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L984-L984
CONTRACT_ID: paper.step:stat-pi-reduction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: pi-periodic p, so -zz =_d zz; zz independent of U; stationarity of the law of e^{2i theta_sigma(t~)(zz)} (from Lemma A.1)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: -e^{i theta_sigma(t~)(zz)} =_d e^{i theta_sigma(t~)(zz)} and stationarity of e^{2i theta} implies stationarity of e^{i theta}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-reflect, step:driver-negation-symmetry, def-arg, step:stat-apply-kolmogorov-noncritical, step:stat-apply-kolmogorov-critical, lem-stationary.admissible
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-reflect | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L984-L984 | (2.2): multiplying the driving function by -1 gives f_t -> -f_t(-.)
EDGE: step:driver-negation-symmetry | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L984-L984 | -U =_d U
EDGE: def-arg | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L984-L984 | carrier change theta <-> e^{2i theta}, e^{i theta}
EDGE: step:stat-apply-kolmogorov-noncritical | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L984-L984 | stationarity of e^{2i theta} (case ∣c∣ != sqrt(ab)) is the premise being upgraded
EDGE: step:stat-apply-kolmogorov-critical | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L984-L984 | stationarity of e^{2i theta} (case c = +-sqrt(ab)) is the premise being upgraded
EDGE: lem-stationary.admissible | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L984-L984 | p is pi-periodic, so -zz =_d zz
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Carrier change theta <-> e^{2 i theta} -> e^{i theta}. The step from invariance of the law of the process e^{2i theta}, plus the symmetry -zz =_d zz, to invariance of e^{i theta} is only sketched.

NODE: step:stat-kolmogorov-normalization
KIND: step
TITLE: Apply Lemma A.1 to 2p (normalization int_0^pi = 1 and alpha = mu, beta^2 = 2D)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L987-L987
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L984-L993
CONTRACT_ID: paper.step:stat-kolmogorov-normalization
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: p admissible (int_0^{2pi} p = 1, pi-periodic)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: 2p satisfies the hypotheses of lem-kolmogorov with alpha = mu, beta = sqrt(2D) (resp. beta of (2.31)): int_0^pi 2p = int_0^{2pi} p = 1, and (2.13) is (A.2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-kolmogorov, lem-stationary.admissible, eqn-nu-D.mu, eqn-nu-D.D
ROUTES: -
ROUTE_FOR: -
EDGE: lem-kolmogorov | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L987-L987 | Lemma A.1 is the invoked result
EDGE: lem-stationary.admissible | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L987-L987 | hypotheses on p to be matched
EDGE: eqn-nu-D.mu | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L988-L988 | alpha = mu
EDGE: eqn-nu-D.D | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L988-L988 | beta^2 = 2D
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: R9 ruling: A.1 normalized with int_0^pi; here p is replaced by 2p. Initial law p 1_[0,2pi] of e^{2i theta}: with pi-periodic p it equals the law of the Lemma A.1 initial point mod pi (carrier change [0,2pi] -> [0,pi]).

NODE: step:D-structure
KIND: step
TITLE: Structure of D: positivity if |c|<sqrt(ab); D = (1/2)(sqrt a sin -+ sqrt b cos)^2 if c = +-sqrt(ab)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L988-L992
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L988-L992
CONTRACT_ID: paper.step:D-structure
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a,b>0; c^2<=ab
SOURCE_QUANTIFIERS: forall a,b,c
SOURCE_CONCLUSION: if |c|<sqrt(ab) then D>0 on R; if c = +-sqrt(ab) then 2D = beta^2 with beta(u) = sqrt a sin u -+ sqrt b cos u, vanishing exactly on arctan(+-sqrt(b/a)) + pi Z
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-nu-D.D
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-nu-D.D | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L988-L988 | explicit quadratic form D(u)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Used at L988, L992, L1026 (Case 1: D>0), L1092 (D^-1(0) = x + pi Z), L1165. Source states it three times without proof (algebra). For c=-sqrt(ab) the zero set sign convention follows the source +-.

NODE: step:stat-apply-kolmogorov-noncritical
KIND: application
TITLE: Lemma A.1 applied in the nondegenerate case |c| != sqrt(ab)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L988-L988
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L988-L988
CONTRACT_ID: paper.step:stat-apply-kolmogorov-noncritical
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: |c| != sqrt(ab) (so |c|<sqrt(ab) under PSD)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: hypotheses of lem-kolmogorov hold (mu, sqrt(2D) smooth, pi-periodic, sqrt(2D) never zero); stationarity of e^{2i theta_sigma(t~)(zz)}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-kolmogorov, step:stat-kolmogorov-normalization, step:D-structure, step:stat-theta-bm-sde
ROUTES: -
ROUTE_FOR: -
EDGE: lem-kolmogorov | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L988-L988 | the stationarity statement used
EDGE: step:stat-kolmogorov-normalization | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L988-L988 | 2p, alpha, beta matching
EDGE: step:D-structure | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L988-L988 | D>0 so beta=sqrt(2D) is smooth, nonvanishing
EDGE: step:stat-theta-bm-sde | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L988-L988 | the SDE (2.30)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Smoothness and pi-periodicity of sqrt(2D) (not just of beta^2 as demanded by A.1) are immediate from D>0 smooth.

NODE: step:stat-apply-kolmogorov-critical
KIND: application
TITLE: Lemma A.1 applied in the critical case c = +-sqrt(ab)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L988-L993
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L989-L993
CONTRACT_ID: paper.step:stat-apply-kolmogorov-critical
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c = +-sqrt(ab), a,b>0
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: with beta(u)=sqrt a sin u -+ sqrt b cos u the SDE (2.31) has smooth coefficients; beta vanishes only on arctan(+-sqrt(b/a))+piZ where mu beta' = -+4 sqrt(ab/(a+b)) != 0; hence lem-kolmogorov applies and e^{2i theta_sigma(t~)(zz)} is stationary
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-kolmogorov, step:stat-kolmogorov-normalization, step:D-structure, step:stat-theta-bm-sde, eqn-nu-D.mu
ROUTES: -
ROUTE_FOR: -
EDGE: lem-kolmogorov | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L993-L993 | Hormander-condition hypothesis (A.1) checked at zeros of beta
EDGE: step:stat-kolmogorov-normalization | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L993-L993 | 2p, alpha=mu, beta
EDGE: step:D-structure | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L988-L992 | 2D = beta^2 and zero set of beta
EDGE: step:stat-theta-bm-sde | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L989-L992 | rewrite with W'' and beta
EDGE: eqn-nu-D.mu | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L993-L993 | value of mu(u) beta'(u) at the zeros of beta
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Value of mu beta' at zeros of beta (mu(x) = -4 sqrt(ab)/(a+b), beta' = +-sqrt(a+b)) is computed in the statement, with no derivation. Sign +- consistent with c = +-sqrt(ab); sqrt(ab/(a+b)) vs the (4 sqrt(ab))/(a+b) of L1097 times sqrt(a+b) agree. W'' (replacing W') is a BM by the same representation argument.

NODE: lem-p.exists
KIND: theorem
TITLE: Lemma 2.13, existence of an admissible density
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L941-L955
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1024-L1111
CONTRACT_ID: paper.lem2_13.exists
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a>0; b>0; c^2<=ab (R5, R7)
SOURCE_QUANTIFIERS: forall a,b,c
SOURCE_CONCLUSION: exists p, IsAdmissibleDensity a b c p
CONSTANT_SCOPE: none
FROZEN_FILE: ComplexSLE/Frozen/Lemma_2_13_Exists.lean
FROZEN_DECL: ComplexSLE.exists_admissibleDensity
FROZEN_ANCHOR_ID: thm.exists_admissibleDensity.v1
FROZEN_ABI_SHA256: 8f546735c8b4d71b3075c5f4038fdc3cd05cd83517ffa087db4f91baec22d461
DEPS: lem-stationary.admissible, step:p-wlog-c-nonneg, step:p-case1, step:p-case2
ROUTES: -
ROUTE_FOR: -
EDGE: lem-stationary.admissible | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1025-L1025 | target is to meet the hypotheses of Lemma 2.14
EDGE: step:p-wlog-c-nonneg | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1026-L1026 | reduction to c>=0
EDGE: step:p-case1 | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1029-L1088 | case c<sqrt(ab)
EDGE: step:p-case2 | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1091-L1110 | case c=sqrt(ab)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: R5: a,b>0 (R-P2: Lemma 2.13 literally allows ab=0, out of scope). R7: p is merely admissible; the 'furthermore' stationary property and strict positivity off a discrete set are carried by node lem-p (not by this root). Nodes step:p-case1/step:p-case2 must deliver all admissibility fields incl. the normalization int_0^{2pi} p=1 (SOURCE_GAP in case 2, see step:p-case2).

NODE: lem-p
KIND: lemma
TITLE: Lemma 2.13 (full): non-negative pi-periodic solution, positive off a discrete set, giving a stationary argument process
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L941-L955
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1024-L1111
CONTRACT_ID: paper.lem-p
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a>0; b>0; c^2<=ab (R5); mu, D as in (2.nu-D); zz random on the unit circle independent of U with angle density p 1_[0,2pi]
SOURCE_QUANTIFIERS: forall a,b,c; exists p; (then) zz independent of U
SOURCE_CONCLUSION: exists p >= 0, pi-periodic, solving -[mu p]'+[D p]''=0 with int_0^{2pi} p = 1, p>0 except on a discrete set, such that e^{i theta_sigma(t~)(zz)} is stationary in t~
CONSTANT_SCOPE: p chosen depending only on (a,b,c)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-p.exists, step:p-positive-off-discrete, lem-stationary
ROUTES: -
ROUTE_FOR: -
EDGE: lem-p.exists | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L948-L950 | existence of the admissible solution
EDGE: step:p-positive-off-discrete | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L953-L953 | strict positivity off a discrete set
EDGE: lem-stationary | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L954-L954 | Lemma 2.14 yields the stationary property of the constructed admissible p
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Full source statement (spans three claims). 'Furthermore, the solution p can be taken...' is read as: the SAME p. R7/R15: any admissible p is stationary; this node needs the constructed p to be simultaneously positive off a discrete set, which is why step:p-positive-off-discrete follows the construction. Covers inv:L957 prose on pi-periodicity (no extra claim).

NODE: step:p-wlog-c-nonneg
KIND: step
TITLE: Reduction to c >= 0 for the density construction
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1026-L1026
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1026-L1026
CONTRACT_ID: paper.step:p-wlog-c-nonneg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: tilde-mu(u) = -mu(-u), tilde-D(u) = D(-u) (c -> -c)
SOURCE_QUANTIFIERS: forall a,b,c
SOURCE_CONCLUSION: if p is admissible for (a,b,c) then tilde-p(u)=p(-u) is admissible for (a,b,-c) (x -> -x); positivity-off-a-discrete-set is preserved
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: eqn-nu-D.mu, eqn-nu-D.D, lem-stationary.admissible
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-nu-D.mu | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1026-L1026 | symmetry mu(c)(u) = -mu(-c)(-u)
EDGE: eqn-nu-D.D | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1026-L1026 | symmetry D(c)(u) = D(-c)(-u)
EDGE: lem-stationary.admissible | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1026-L1026 | "if p satisfies the hypotheses of Lemma 2.14 then p~ does"
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Distinct from slice A's step:wlog-c-nonneg (L323, conjugation of the driver); this one is about the density constructed in Lemma 2.13.

NODE: step:p-case1-first-order-solutions
KIND: step
TITLE: p_0, p_1 smooth and solve the first-order ODEs -mu p_j + [D p_j]' = j
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1030-L1045
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1030-L1045
CONTRACT_ID: paper.step:p-case1-first-order-solutions
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: |c|<sqrt(ab), so D>0 (a,b>0)
SOURCE_QUANTIFIERS: forall j in {0,1}
SOURCE_CONCLUSION: p_0(u) = exp(int_0^u (mu-D')/D) and p_1(u) = D(u)^-1 exp(int_0^u mu/D) int_0^u exp(-int_0^s mu/D) ds are smooth on R and satisfy -mu p_j + [D p_j]' = j; p_0(0)=1, p_1(0)=0; the source also asserts p_0, p_1 >= 0 (L1030) and uses p_1(pi) > 0 (L1054, L1065) without argument
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:D-structure, eqn-nu-D.mu, eqn-nu-D.D
ROUTES: -
ROUTE_FOR: -
EDGE: step:D-structure | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1030-L1030 | D>0 on R
EDGE: eqn-nu-D.mu | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1032-L1032 | integrand mu/D
EDGE: eqn-nu-D.D | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1032-L1032 | integrand D'/D, 1/D
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Covers eqn-defn-p0, eqn-defn-p1, eqn-p0-p1-ODE. Verification of the ODEs is direct differentiation. SOURCE_GAP: the source says p_0,p_1 : R -> [0,infty) and later 'p_1(pi) > 0' and 'p_0, p_1 clearly non-negative' with no argument; p_1(u) < 0 for u < 0, so nonnegativity holds only on [0,pi] where it is used. Downstream nodes step:p-case1-periodic and step:p-case1-nonneg consume 'p_1(pi) > 0' and 'p_1 >= 0 on [0,pi]' from this node.

NODE: step:p-case1-periodic
KIND: step
TITLE: p = k(p_0 + r_* p_1) is pi-periodic
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1048-L1063
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1048-L1063
CONTRACT_ID: paper.step:p-case1-periodic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: r_* = (p_0(0)-p_0(pi))/p_1(pi); p_1(pi)>0; mu, D pi-periodic
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: p(0)=p(pi) and p, p(.+pi) solve the same first-order ODE -mu p + [D p]' = k r_*, so p is pi-periodic; p solves (2.13) on R
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p-case1-first-order-solutions, ext:picard-lindelof
ROUTES: -
ROUTE_FOR: -
EDGE: step:p-case1-first-order-solutions | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1048-L1048 | p_0+r p_1 solves (2.13) for every r; first-order ODEs
EDGE: ext:picard-lindelof | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1063-L1063 | uniqueness gives p(u+pi)=p(u)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Derivation of (2.13) from the first-order ODE: differentiate -mu p + [D p]' = const.

NODE: step:p-case1-mu-over-D-integral
KIND: step
TITLE: Evaluation of int_0^pi mu/D = 8 pi c (2 sqrt(ab-c^2)-(a+b))/(sqrt(ab-c^2)((a-b)^2+4c^2)) <= 0
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1073-L1084
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1073-L1084
CONTRACT_ID: paper.step:p-case1-mu-over-D-integral
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<=c<sqrt(ab), a,b>0
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: int_0^pi mu(u)/D(u) du = 8 pi c (2 sqrt(ab-c^2)-(a+b)) / (sqrt(ab-c^2)((a-b)^2+4c^2)) <= 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:D-structure, eqn-nu-D.mu, eqn-nu-D.D
ROUTES: -
ROUTE_FOR: -
EDGE: step:D-structure | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1073-L1073 | D>0 so the antiderivative is smooth on [0,pi] (arctan branch)
EDGE: eqn-nu-D.mu | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1074-L1074 | integrand mu
EDGE: eqn-nu-D.D | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1074-L1074 | integrand 1/D
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Direct computation: the source states the antiderivative (with log and arctan terms; the arctan branch jump across u=pi/2 must be accounted for) and the result without verification. Sign claim: 2 sqrt(ab-c^2) <= a+b (AM-GM). Edge case unmentioned: the prefactor 1/((a-b)^2+4c^2) is singular exactly when a=b and c=0, where the integral is 0 and the formula must be read as a limit.

NODE: step:p-case1-nonneg
KIND: step
TITLE: r_* >= 0 and hence p >= 0
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1065-L1084
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1065-L1084
CONTRACT_ID: paper.step:p-case1-nonneg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c>=0 after reduction; p_1(pi)>0; p_0(0)=1
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: r_* >= 0, equivalently p_0(pi) <= 1, equivalently int_0^pi (mu-D')/D <= 0; hence p = k(p_0 + r_* p_1) >= 0 on [0,pi] (and on R by periodicity)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p-case1-first-order-solutions, step:p-case1-mu-over-D-integral, step:p-case1-periodic
ROUTES: -
ROUTE_FOR: -
EDGE: step:p-case1-first-order-solutions | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1065-L1065 | p_0, p_1 >= 0 on [0,pi], p_1(pi)>0
EDGE: step:p-case1-mu-over-D-integral | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1073-L1084 | sign of int mu/D
EDGE: step:p-case1-periodic | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1065-L1070 | nonnegativity extends from [0,pi] to R via pi-periodicity
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Also uses int_0^pi D'/D = log D(pi) - log D(0) = 0 (L1071, elementary). Uncertainty: source says 'p_0(pi) < 1'; the proven inequality is <= (equality at c=0). Nonnegativity of p_1 on [0,pi] 'clearly'.

NODE: step:p-case1-zero-set
KIND: step
TITLE: p vanishes only on a discrete set (case 1)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1086-L1086
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1086-L1086
CONTRACT_ID: paper.step:p-case1-zero-set
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: p = k(p_0 + r_* p_1)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: if r_*=0, p = k p_0 > 0; if r_* != 0, -mu p + [D p]' = k r_* != 0 at each zero of p, so zeros are isolated
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p-case1-first-order-solutions, step:p-case1-periodic
ROUTES: -
ROUTE_FOR: -
EDGE: step:p-case1-first-order-solutions | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1086-L1086 | p_0>0 and first-order ODE
EDGE: step:p-case1-periodic | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1086-L1086 | ODE for p with constant right side k r_*
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Isolated zeros because p(u0)=0 and p'(u0) = (k r_*)/D(u0) != 0.

NODE: step:p-case1
KIND: step
TITLE: Case 1 assembly: smooth admissible density for c<sqrt(ab) with int_0^{2pi} p = 1
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1029-L1088
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1029-L1088
CONTRACT_ID: paper.step:p-case1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<=c<sqrt(ab), a,b>0
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: p = k(p_0 + r_* p_1), with k>0 chosen so int_0^{2pi} p = 1, is smooth (C^2 everywhere, so the x-condition holds vacuously), nonnegative, pi-periodic, solves (2.13), and D p is C^1; i.e. admissible
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p-case1-first-order-solutions, step:p-case1-periodic, step:p-case1-nonneg, step:p-case1-zero-set, lem-stationary.admissible
ROUTES: -
ROUTE_FOR: -
EDGE: step:p-case1-periodic | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1058-L1063 | pi-periodicity and the ODE
EDGE: step:p-case1-nonneg | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1065-L1065 | nonnegativity
EDGE: step:p-case1-zero-set | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1088-L1088 | int_0^{2pi}(p_0+r_* p_1) > 0 so k exists
EDGE: lem-stationary.admissible | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1025-L1025 | admissibility target
EDGE: step:p-case1-first-order-solutions | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1041-L1041 | p_0, p_1 smooth, so p is C^2 on R and D p is C^1 (x-condition vacuous)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Covers L969 preview (smooth for |c|<sqrt(ab)). Choice of normalizing constant k is a parameter choice; independence of k from nothing else (k depends on a,b,c).

NODE: step:p-case2-welldefined
KIND: step
TITLE: Case 2: p defined by (2.32) is well defined, positive, smooth on (x,x+pi) and solves -mu p + [D p]' = 1
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1091-L1101
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1091-L1101
CONTRACT_ID: paper.step:p-case2-welldefined
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c = sqrt(ab), a,b>0; x in [0,pi) with tan x = sqrt(b/a)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: D^-1(0)=x+piZ; mu(x)=mu(x+pi)=-4sqrt(ab)/(a+b)<0; int_{x+pi/2}^u mu/D -> +infty as u->x and -infty as u->x+pi; hence the outer integral in (2.32) is finite on (x,x+pi) and p>0, smooth there with -mu p+[D p]'=1 (2.33)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:D-structure, eqn-nu-D.mu, eqn-nu-D.D
ROUTES: -
ROUTE_FOR: -
EDGE: step:D-structure | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1092-L1092 | D vanishes exactly on x+piZ
EDGE: eqn-nu-D.mu | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1097-L1097 | value of mu at x and x+pi
EDGE: eqn-nu-D.D | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1095-L1095 | definition of p via D
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Covers eqn-critical-p, eqn-critical-p-ode. Behaviour of int mu/D at endpoints relies on D vanishing to second order at x (D(u)~ (u-x)^2). Verification of the value mu(x) = -4sqrt(ab)/(a+b) is a direct trig computation, not shown.

NODE: step:p-case2-limits
KIND: step
TITLE: Case 2: l'Hopital limits of p at x and x+pi equal (a+b)/(4 sqrt(ab))
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1102-L1109
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1102-L1109
CONTRACT_ID: paper.step:p-case2-limits
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: p as in (2.32)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: lim_{u->x+} p(u) = lim_{u->(x+pi)-} p(u) = (a+b)/(4 sqrt(ab)) = -1/mu(x) > 0 (l'Hopital, using D(x)=D'(x)=0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p-case2-welldefined, eqn-nu-D.mu
ROUTES: -
ROUTE_FOR: -
EDGE: step:p-case2-welldefined | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1102-L1102 | numerator, denominator of (2.32) both tend to 0 at the endpoints
EDGE: eqn-nu-D.mu | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1104-L1104 | D'(x)-mu(x) = -mu(x)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Covers eqn-lhop-down, eqn-lhop-up. l'Hopital applied to a quotient whose denominator is D(u) exp(-int mu/D); requires differentiability and derivative-quotient limit; stated as 'by applying l'Hopital's rule' without detail.

NODE: step:p-case2-regularity
KIND: step
TITLE: Case 2: periodic extension is continuous, smooth off x+piZ, solves (2.13) there and D p is C^1 with zero derivative on x+piZ
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1110-L1110
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1110-L1110
CONTRACT_ID: paper.step:p-case2-regularity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (2.33), (2.34), (2.35)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: p extends to a continuous pi-periodic function R -> [0,infty), smooth off x+piZ, solving (2.13) off x+piZ; [D p]' = 1+mu p -> 0 at x+piZ from both sides and D p is pi-periodic, so D p is C^1 on R with vanishing derivative on x+piZ
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p-case2-limits, step:p-case2-welldefined
ROUTES: -
ROUTE_FOR: -
EDGE: step:p-case2-limits | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1110-L1110 | continuity at x+n pi and one-sided limits of [D p]'
EDGE: step:p-case2-welldefined | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1110-L1110 | ODE (2.33) i.e. [D p]' = 1 + mu p off the singular points (the source's "By (2.19)" is this same equation, valid in Case 2 only through (2.33))
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Uses the (commented-out) calculus lemma: continuous f with one-sided derivative limits is differentiable; D p = D * p, with D(x)=0 and p bounded, gives continuity at x. Derivation of (2.13) from the first-order ODE as in case 1. 'by (2.19)' cites the ODE (2.19) established for j=1 in case 1; in case 2 the ODE is (2.33): the same equation.

NODE: step:p-case2
KIND: step
TITLE: Case 2 assembly: admissible density for c = sqrt(ab) with int_0^{2pi} p = 1
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1091-L1110
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1091-L1110
CONTRACT_ID: paper.step:p-case2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c = sqrt(ab), a,b>0
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: a positive multiple of p from (2.32) is continuous, nonnegative (in fact positive), pi-periodic, C^2 off x+piZ and solves (2.13) there, D p is C^1 on R, and int_0^{2pi} p = 1; i.e. admissible
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p-case2-regularity, step:p-case2-welldefined, lem-stationary.admissible
ROUTES: -
ROUTE_FOR: -
EDGE: step:p-case2-regularity | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1110-L1110 | continuity, regularity and ODE
EDGE: step:p-case2-welldefined | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1098-L1098 | positivity of p on (x,x+pi)
EDGE: lem-stationary.admissible | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1025-L1025 | admissibility target
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Covers L969-L970 preview. SOURCE_GAP: the proof of case 2 never rescales p to obtain int_0^{2pi} p = 1 (in case 1 the constant k is chosen); also the positivity and finiteness of the integral int_0^{2pi} p are not stated (p is continuous and positive, so it is finite and positive: trivial). x is a witness choice (Lemma 2.14's x).

NODE: step:p-positive-off-discrete
KIND: step
TITLE: The constructed p is positive except on a discrete set
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L953-L953
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1086-L1110
CONTRACT_ID: paper.step:p-positive-off-discrete
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: p constructed as in the proof of lem-p
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: the constructed p is strictly positive on R minus a discrete set (case 1 by step:p-case1-zero-set; case 2 p>0 everywhere)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p-case1-zero-set, step:p-case2, step:p-wlog-c-nonneg
ROUTES: -
ROUTE_FOR: -
EDGE: step:p-case1-zero-set | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1086-L1086 | case 1
EDGE: step:p-case2 | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1098-L1098 | case 2: positive on (x,x+pi) and limit (a+b)/(4 sqrt(ab))>0 at the endpoints
EDGE: step:p-wlog-c-nonneg | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L1026-L1026 | transfer to c<0 via p(-u)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Positive-set claim for case 2 is implicit in the source ('p is well-defined, positive').

NODE: step:p0-c0-r-star-zero
KIND: step
TITLE: For c=0, r_*=0 so that p = k p_0
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#remark-p0@L1136-L1138
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#remark-p0@L1136-L1138
CONTRACT_ID: paper.step:p0-c0-r-star-zero
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c=0; a,b>0
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: (mu-D')/D is odd and pi-periodic, so int_0^pi (mu-D')/D = 0, p_0(pi)=1, r_*=0 and p = k p_0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p-case1-first-order-solutions, step:p-case1
ROUTES: -
ROUTE_FOR: -
EDGE: step:p-case1-first-order-solutions | source/arxiv-2203.07313v4/complex-sle-final.tex#remark-p0@L1137-L1137 | p_0 and its exponent
EDGE: step:p-case1 | source/arxiv-2203.07313v4/complex-sle-final.tex#remark-p0@L1137-L1137 | p=k(p_0+r_* p_1)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Source says only 'integrand is odd and pi-periodic'; r_*=0 is derived (p_0(0)=1). Remark presupposes the construction of case 1 (c=0<sqrt(ab)).

NODE: remark-p0
KIND: claim
TITLE: Remark 2.15: for c=0 the periodic solution p of Lemma 2.13 is a constant times p_0
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#remark-p0@L1136-L1138
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#remark-p0@L1136-L1138
CONTRACT_ID: paper.remark-p0
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c=0; a,b>0 (R5); p the solution constructed in Lemma 2.13
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: p = const * p_0, p_0 of (2.17)
CONSTANT_SCOPE: p is the constructed solution (not every admissible p)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p0-c0-r-star-zero, lem-p
ROUTES: -
ROUTE_FOR: -
EDGE: step:p0-c0-r-star-zero | source/arxiv-2203.07313v4/complex-sle-final.tex#remark-p0@L1137-L1137 | oddness gives r_*=0
EDGE: lem-p | source/arxiv-2203.07313v4/complex-sle-final.tex#remark-p0@L1137-L1137 | refers to the solution p of Lemma 2.13
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Applies to the constructed p only; uniqueness of admissible p is not proved (P4/R7).

NODE: lem-recurrence
KIND: lemma
TITLE: Recurrence of the stationary argument process
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1155-L1163
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1164-L1230
CONTRACT_ID: paper.lem-recurrence
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a>0; b>0; c^2<=ab (R5); p as in Lemma 2.13 (read as: admissible, R7/R15); zz in unit circle independent of U with angle density p 1_[0,2pi]; hat-theta_t~(zz) = theta_sigma(t~)(zz)
SOURCE_QUANTIFIERS: forall a,b,c; forall admissible p; zz independent
SOURCE_CONCLUSION: if |c|<sqrt(ab): for each w on the unit circle, a.s. there exist arbitrarily large t~ with e^{2i hat-theta_t~(zz)} = w; if |c|=sqrt(ab): a.s. arbitrarily large t~ with e^{2i hat-theta_t~(zz)} = e^{2ix}, tan x = sqrt(b/a), x in [0,pi)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-stationary, step:wlog-c-nonneg, step:rec-reduction-to-x, step:rec-renewal, step:rec-tau-finite, step:rec-angle-hit-unif
ROUTES: -
ROUTE_FOR: -
EDGE: lem-stationary | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1187-L1187 | stationarity of e^{2i theta}
EDGE: step:wlog-c-nonneg | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1165-L1165 | c>=0 WLOG
EDGE: step:rec-reduction-to-x | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1165-L1165 | suffices to hit e^{2ix}
EDGE: step:rec-renewal | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1177-L1183 | infinitely many hits on {tau_k<infty for all k}
EDGE: step:rec-tau-finite | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1185-L1190 | a.s. some eps with all tau_k^eps finite
EDGE: step:rec-angle-hit-unif | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1167-L1171 | claim (2.45) fed to renewal argument
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: R5. Statement says 'p as in Lemma 2.13': read per R7/R15 as admissible p (the proof only uses stationarity of the law of e^{2i theta}, absolute continuity of its law, and pi-periodic coefficients). In the |c|<sqrt(ab) case the source says 'Let w in bdy D'; in the critical case w = e^{2ix} is forced.

NODE: step:rec-reduction-to-x
KIND: step
TITLE: Reduction to hitting e^{2ix} for a single x
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1165-L1165
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1165-L1165
CONTRACT_ID: paper.step:rec-reduction-to-x
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c>=0; x in [0,pi) (tan x = sqrt(b/a) if c=sqrt(ab); arbitrary if c<sqrt(ab)); D^-1(0)=x+piZ in the critical case
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: both bullets follow from: a.s. arbitrarily large t~ with e^{2i hat-theta_t~} = e^{2ix}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:D-structure, step:wlog-c-nonneg
ROUTES: -
ROUTE_FOR: -
EDGE: step:D-structure | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1165-L1165 | D^-1(0)=x+piZ in the critical case
EDGE: step:wlog-c-nonneg | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1165-L1165 | WLOG c>=0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Every w = e^{2ix} with x in [0,pi), so non-critical bullet reduces to arbitrary x.

NODE: step:rec-angle-hit-unif
KIND: step
TITLE: Uniform hitting estimate (2.45)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1167-L1171
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1210-L1229
CONTRACT_ID: paper.step:rec-angle-hit-unif
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: P^y = law of the solution to (2.25) from hat-theta_0=y; eps>0
SOURCE_QUANTIFIERS: forall eps>0; exists T,delta>0 (depending on eps and x, a,b,c); forall y in [x,x+pi-eps]
SOURCE_CONCLUSION: P^y[exists t~ in [0,T], hat-theta_t~ = x] >= delta
CONSTANT_SCOPE: T, delta depend only on eps, x, a, b, c; not on y
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:rec-monotone-in-y
ROUTES: -
ROUTE_FOR: -
EDGE: step:rec-monotone-in-y | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1229-L1229 | monotonicity in y reduces uniform bound to the worst y=x+pi-eps (itself built on the fixed-y bound)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Covers eqn-angle-hit-unif. 'We will prove at the end' (L1171). Quantifier closure: T,delta chosen after eps, uniformly in y.

NODE: step:rec-renewal
KIND: step
TITLE: Renewal times tau_k^eps: conditional hitting probability >= delta per window gives infinitely many hits
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1173-L1183
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1173-L1183
CONTRACT_ID: paper.step:rec-renewal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: T,delta as in (2.45); [theta] in [x,x+pi) the representative mod pi; tau_0^eps=0, tau_k^eps = inf{t~ >= tau_{k-1}+T : [theta_t~] in [x,x+pi-eps]}
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: on the event that all tau_k^eps<infty, [hat-theta_t~(zz)] hits x infinitely often a.s.
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:rec-angle-hit-unif, ext:strong-markov-bm, ext:martingale-convergence, step:stat-theta-bm-sde
ROUTES: -
ROUTE_FOR: -
EDGE: step:rec-angle-hit-unif | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1183-L1183 | conditional probability >= delta in each window
EDGE: ext:strong-markov-bm | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1182-L1182 | strong Markov property at tau_k
EDGE: ext:martingale-convergence | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1183-L1183 | conditional Borel-Cantelli to conclude infinitely many hits
EDGE: step:stat-theta-bm-sde | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1182-L1182 | pi-periodic coefficients of SDE (2.30) give the same conditional law from [theta_tau]
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: (i) the conditional Borel-Cantelli argument is implicit; (ii) strong Markov property is for the SDE solution (weak uniqueness, pi-periodic coefficients) and is not separately cited; (iii) hitting x for [theta] with probability >= delta covers hitting x mod pi, and the identification with hitting e^{2ix} is by carrier change theta -> [theta] -> e^{2i theta}.

NODE: step:rec-tau-finite
KIND: step
TITLE: A.s. exists eps with tau_k^eps<infty for all k
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1185-L1190
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1185-L1190
CONTRACT_ID: paper.step:rec-tau-finite
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: stationarity of the law of e^{2i hat-theta_t~(zz)} with a density (non-atomic); x deterministic
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: a.s. there is eps>0 with tau_k^eps<infty for every k; else lim e^{2i hat-theta_t~} = e^{2ix} which has probability 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-stationary, lem-stationary.admissible, step:rec-renewal
ROUTES: -
ROUTE_FOR: -
EDGE: lem-stationary | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1187-L1187 | stationary law of e^{2i theta}
EDGE: lem-stationary.admissible | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1187-L1187 | the admissible p is a density (angle law p 1_[0,2pi]), so the image law is non-atomic
EDGE: step:rec-renewal | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1177-L1180 | the stopping times tau_k^eps are defined there
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The step 'a.s. limit = e^{2ix} has probability 0' uses stationarity + nonatomic law: a.s. convergence to a deterministic point would force the marginal law to converge to the point mass (contradicting stationarity). Reading: 'p as in Lemma 2.13' used only through the density.

NODE: step:rec-time-change-omega
KIND: step
TITLE: Time change omega(r) with r = 2 int_0^omega D: X_r satisfies dX = mu/(2D) dr + dZ
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1192-L1208
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1192-L1208
CONTRACT_ID: paper.step:rec-time-change-omega
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: R = inf{r>0 : X_r in {x,x+pi}}; X_r = hat-theta_omega(r) for r in [0,R]
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: for r in [0,R], dX_r = mu(X_r)/(2D(X_r)) dr + dZ_r with Z_r = int_0^omega(r) sqrt(2D(hat theta)) dW' a standard linear BM
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:stat-theta-bm-sde, ext:levy-characterization, step:D-structure
ROUTES: -
ROUTE_FOR: -
EDGE: step:stat-theta-bm-sde | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1200-L1200 | time-change of (2.30)
EDGE: ext:levy-characterization | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1208-L1208 | Z is a continuous martingale with <Z>_r = r
EDGE: step:D-structure | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1192-L1198 | D>0 on (x,x+pi) so omega is well defined before R
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Covers eqn-omega-time, eqn-omega-sde. Time change defined only until R (exit of (x,x+pi)).

NODE: step:rec-scale-function-hit
KIND: application
TITLE: Scale-function argument: with positive probability R<infinity and X_R = x
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1210-L1223
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1210-L1223
CONTRACT_ID: paper.step:rec-scale-function-hit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: psi(v) = int_{x+pi/2}^v exp(-int_{x+pi/2}^s mu/D) ds on (x,x+pi)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: liminf_{v->x} psi(v) > -infinity, hence by [Law05, Lemma 1.24] with positive probability R<infinity and X_R = x
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: ext:scale-function, step:rec-time-change-omega, step:D-structure, step:p-case2-welldefined
ROUTES: -
ROUTE_FOR: -
EDGE: ext:scale-function | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1210-L1210 | Lemma 1.24 of Lawler
EDGE: step:rec-time-change-omega | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1210-L1210 | the diffusion X to which the scale function applies
EDGE: step:D-structure | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1215-L1215 | D(x)!=0 if c<sqrt(ab) (finite limit); D(x)=0 if c=sqrt(ab)
EDGE: step:p-case2-welldefined | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1215-L1215 | mu(x)<0 gives mu/D -> -infinity as t->x when c=sqrt(ab)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Covers inv:cite L1210, L1223. The hypotheses of the cited lemma at the other endpoint x+pi are not checked in the source (uncertainty). The conclusion R<infinity is in r-time (see step:rec-hit-fixed-y).

NODE: step:rec-hit-fixed-y
KIND: step
TITLE: Positive probability of hitting x in finite theta-time from each y in (x,x+pi)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1225-L1228
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1225-L1228
CONTRACT_ID: paper.step:rec-hit-fixed-y
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: y in (x,x+pi); X is a time change of hat-theta
SOURCE_QUANTIFIERS: forall y in (x,x+pi); exists T<infty
SOURCE_CONCLUSION: P^y[exists t~ in [0,T] with hat-theta_t~ = x] > 0 (eqn-angle-hit-fixed)
CONSTANT_SCOPE: T may depend on y
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:rec-scale-function-hit, step:rec-time-change-omega
ROUTES: -
ROUTE_FOR: -
EDGE: step:rec-scale-function-hit | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1225-L1225 | positive probability event in r-time
EDGE: step:rec-time-change-omega | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1225-L1225 | X is a time change of hat-theta
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Covers eqn-angle-hit-fixed. SOURCE_GAP: R<infinity in r-time does not by itself give omega(R) = int_0^R dr/(2D(X_r)) < infinity; in the critical case 1/D is not integrable near x, so finiteness of the theta-time of the hit is not argued.

NODE: step:rec-monotone-in-y
KIND: step
TITLE: Hitting probability within time T is non-increasing in y; uniform bound
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1229-L1229
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1229-L1229
CONTRACT_ID: paper.step:rec-monotone-in-y
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: continuity of paths; strong Markov property
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: y -> P^y[exists t~ in [0,T], hat-theta = x] is non-increasing on (x,x+pi), so for each eps there exist T,delta with (2.45) on [x,x+pi-eps]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:rec-hit-fixed-y, ext:strong-markov-bm
ROUTES: -
ROUTE_FOR: -
EDGE: step:rec-hit-fixed-y | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1229-L1229 | choose y=x+pi-eps, T from the fixed-y bound
EDGE: ext:strong-markov-bm | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1229-L1229 | strong Markov at the hitting time of an intermediate y' in (x,y)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Argument needs: from y>y' the process reaching x must first hit y' (continuity), then use time remaining <= T. Endpoint y=x (hit prob 1) included in [x,x+pi-eps].

NODE: lem-kolmogorov
KIND: lemma
TITLE: Kolmogorov forward equation for periodic SDEs (stationary law)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2318-L2334
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2360-L2402
CONTRACT_ID: paper.lem-kolmogorov
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: alpha,beta: R -> R smooth (P6/R9; source writes [0,infty)); alpha and beta^2 pi-periodic; for all u at least one of beta(u), beta'(u)alpha(u) nonzero; p continuous, >=0, pi-periodic; exists x with p C^2 on R minus (x+piZ) solving -[alpha p]'+(1/2)[beta^2 p]''=0 there, int_0^pi p = 1; beta^2 p is C^1 on R; X solves dX=alpha(X)dt+beta(X)dB with X_0 ~ p 1_[0,pi]
SOURCE_QUANTIFIERS: forall alpha,beta; forall p; exists x (given); B standard BM
SOURCE_CONCLUSION: the law of (e^{2iX_t})_{t>=0} is stationary
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-hormander, step:kol-shift-start, step:kol-ito-expectation, step:kol-derivative-at-zero, step:kol-integration-by-parts, step:kol-semigroup-smooth, step:kol-markov-semigroup, step:kol-derivative-vanishes-all-times, step:kol-process-stationarity
ROUTES: -
ROUTE_FOR: -
EDGE: lem-hormander | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2396-L2396 | T_s f smooth
EDGE: step:kol-shift-start | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2361-L2361 | start from [x,x+pi]
EDGE: step:kol-ito-expectation | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2365-L2374 | Ito formula
EDGE: step:kol-derivative-at-zero | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2376-L2380 | (A.3)
EDGE: step:kol-integration-by-parts | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2382-L2394 | (A.4)
EDGE: step:kol-semigroup-smooth | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2396-L2396 | T_s f is C^2 and pi-periodic
EDGE: step:kol-markov-semigroup | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2397-L2400 | Markov property
EDGE: step:kol-derivative-vanishes-all-times | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2401-L2401 | d/ds E_p f(X_s) = 0
EDGE: step:kol-process-stationarity | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2401-L2401 | conclusion for the process law
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Covers eqn-kolmogorov-sde, eqn-hormander-cond, eqn-kolmogorov. P6: alpha,beta: R->R (source's [0,infty) is a typo: mu changes sign). R9: A.1 keeps int_0^pi p = 1; Lemma 2.14 applies it to 2p (step:stat-kolmogorov-normalization). beta^2 pi-periodic only: beta smooth with beta^2 periodic; solution X assumed to exist (strong/weak well-posedness).

NODE: step:kol-shift-start
KIND: step
TITLE: Starting distribution may be taken on [x,x+pi]
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2361-L2361
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2361-L2361
CONTRACT_ID: paper.step:kol-shift-start
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: p and the coefficients pi-periodic
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: the law of (e^{2iX_t}) is the same for X_0 ~ p 1_[0,pi] and X_0 ~ p 1_[x,x+pi]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Carrier change [0,pi] <-> [x,x+pi]: translation by multiples of pi leaves e^{2iX_t} unchanged because coefficients are pi-periodic (beta^2 periodic suffices since only beta^2 enters the law).

NODE: step:kol-ito-expectation
KIND: application
TITLE: Ito formula for f(X_t), f in C^2 pi-periodic: integral form of E_p f(X_t)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2363-L2375
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2365-L2375
CONTRACT_ID: paper.step:kol-ito-expectation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f C^2, pi-periodic (so f', f'' bounded); alpha, beta^2 periodic and continuous (bounded)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: E_p f(X_t) = int_0^t int_x^{x+pi} E_u(f'(X_s)alpha(X_s) + (1/2) f''(X_s) beta^2(X_s)) p(u) du ds
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: ext:ito-complex
ROUTES: -
ROUTE_FOR: -
EDGE: ext:ito-complex | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2365-L2365 | Ito formula (real case)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The stochastic integral int f'(X)beta(X) dB is a true martingale because the integrand is bounded (f' periodic bounded; beta^2 periodic); Fubini over the initial distribution p. These justifications are unstated.

NODE: step:kol-derivative-at-zero
KIND: step
TITLE: Derivative of E_p f(X_t) at t=0 (A.3)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2376-L2380
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2376-L2380
CONTRACT_ID: paper.step:kol-derivative-at-zero
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (A.3 preliminary integral form)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: d/dt|_{t=0} E_p f(X_t) = int_x^{x+pi} (f'(u)alpha(u) + (1/2) f''(u) beta^2(u)) p(u) du
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:kol-ito-expectation, ext:dct
ROUTES: -
ROUTE_FOR: -
EDGE: step:kol-ito-expectation | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2376-L2376 | differentiate the integral form in t
EDGE: ext:dct | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2376-L2376 | continuity at s=0 of the integrand under dominated convergence
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Covers eqn-periodic-deriv0. Continuity in s of s -> E_u(Lf(X_s)) uniform enough for DCT is not discussed.

NODE: step:kol-integration-by-parts
KIND: step
TITLE: Integration by parts with vanishing boundary terms: derivative is 0 (A.4)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2382-L2394
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2382-L2394
CONTRACT_ID: paper.step:kol-integration-by-parts
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f,alpha,beta^2,p pi-periodic; p C^2 on (x,x+pi); beta^2 p C^1 on R; p solves (A.2) on (x,x+pi)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: d/dt|_{t=0}E_p f(X_t) = int_x^{x+pi} f(u)(-[alpha p]' + (1/2)[beta^2 p]'')du = 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:kol-derivative-at-zero
ROUTES: -
ROUTE_FOR: -
EDGE: step:kol-derivative-at-zero | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2382-L2382 | integrand to be integrated by parts
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Covers eqn-periodic-deriv. Boundary terms: f alpha p |_x^{x+pi} (periodicity, p continuous) and f(beta^2 p)' |_x^{x+pi} (beta^2 p C^1 periodic); and f' beta^2 p |. Integration by parts requires (beta^2 p)' absolutely continuous on (x,x+pi) with (beta^2 p)'' = ODE: p is C^2 on the open interval, with the one-sided behavior at endpoints (beta^2 p C^1) used. The source states the derivation only for the double by-parts of f'' beta^2 p.

NODE: step:kol-semigroup-smooth
KIND: step
TITLE: T_s f is pi-periodic and smooth (so it is admissible as a test function)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2396-L2396
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2396-L2396
CONTRACT_ID: paper.step:kol-semigroup-smooth
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: T_s f(u) = E_u f(X_s); f C^2 pi-periodic
SOURCE_QUANTIFIERS: forall s>=0
SOURCE_CONCLUSION: T_s f is pi-periodic and C^2 (smooth for s>0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lem-hormander
ROUTES: -
ROUTE_FOR: -
EDGE: lem-hormander | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2396-L2396 | smoothness of u -> E_u f(X_s)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Periodicity of T_s f needs pi-periodicity of the SDE law in the starting point (coefficients alpha, beta^2 periodic). T_0 f = f. Smoothness at s=0 is trivial since f is C^2 only (A.2 gives t>=0, source flaw noted in lem-hormander).

NODE: step:kol-markov-semigroup
KIND: step
TITLE: Markov property: E_p(T_s f(X_t)) = E_p f(X_{t+s})
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2397-L2400
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2397-L2400
CONTRACT_ID: paper.step:kol-markov-semigroup
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: X solves the SDE; Markov property
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: E_p(T_s f(X_t)) = E_p(E_{X_t} f(X_s)) = E_p f(X_{t+s})
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: ext:strong-markov-bm
ROUTES: -
ROUTE_FOR: -
EDGE: ext:strong-markov-bm | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2397-L2397 | Markov property of the SDE solution
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Markov property of the SDE solution requires uniqueness in law of the SDE (smooth coefficients: fine); not cited.

NODE: step:kol-derivative-vanishes-all-times
KIND: step
TITLE: d/ds E_p f(X_s) = 0 for all s, hence E_p f(X_s) = E_p f(X_0)
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2401-L2401
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2401-L2401
CONTRACT_ID: paper.step:kol-derivative-vanishes-all-times
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (A.4) applies to every C^2 pi-periodic test function; step:kol-markov-semigroup
SOURCE_QUANTIFIERS: forall s>=0; forall f C^2 pi-periodic
SOURCE_CONCLUSION: E_p f(X_s) = E_p f(X_0) = int_x^{x+pi} f p du
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:kol-integration-by-parts, step:kol-semigroup-smooth, step:kol-markov-semigroup
ROUTES: -
ROUTE_FOR: -
EDGE: step:kol-integration-by-parts | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2401-L2401 | (A.4) applied to T_s f
EDGE: step:kol-semigroup-smooth | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2401-L2401 | T_s f is a valid test function
EDGE: step:kol-markov-semigroup | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2401-L2401 | d/dt∣_{t=0}E_p T_s f(X_t) = d/ds E_p f(X_s)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP-adjacent: (A.4) at t=0 gives a right derivative in s at each s; concluding that E_p f(X_s) is constant from vanishing right derivative needs continuity of s -> E_p f(X_s) (true by path continuity and bounded convergence), unstated.

NODE: step:kol-process-stationarity
KIND: step
TITLE: From invariance of E_p f(X_s) for C^2 f to stationarity of the law of the process (e^{2iX_t})
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2401-L2401
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2401-L2401
CONTRACT_ID: paper.step:kol-process-stationarity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E_p f(X_s) = int f p for all C^2 pi-periodic f
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: the law of (e^{2iX_t})_{t>=0} is stationary for X_0 ~ p 1_[x,x+pi]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:kol-derivative-vanishes-all-times
ROUTES: -
ROUTE_FOR: -
EDGE: step:kol-derivative-vanishes-all-times | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2401-L2401 | one-dimensional marginal invariance
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: the source concludes stationarity of the whole process law from invariance of the one-time marginal for C^2 test functions; this needs the Markov property of e^{2iX} (or of the periodic SDE) to pass from marginals to finite-dimensional laws, and an extension from C^2 functions to bounded measurable functions of e^{2iu} (density of C^2 periodic functions among continuous ones), neither stated.

NODE: lem-hormander
KIND: lemma
TITLE: Smooth density and smooth semigroup for the periodic SDE
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-hormander@L2340-L2344
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-hormander@L2345-L2356
CONTRACT_ID: paper.lem-hormander
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting of Lemma A.1 (alpha,beta smooth R->R; alpha, beta^2 pi-periodic; at each u one of beta(u), beta'(u)alpha(u) nonzero)
SOURCE_QUANTIFIERS: forall u in R; forall t>=0 [source; t>0 needed]; forall bounded f: R -> R
SOURCE_CONCLUSION: the law of X_t under P_u has a smooth density with respect to Lebesgue measure; u -> E_u f(X_t) is smooth
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:horm-stratonovich, step:horm-span-condition, step:horm-apply-hairer
ROUTES: -
ROUTE_FOR: -
EDGE: step:horm-stratonovich | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-hormander@L2346-L2349 | Stratonovich form (A.5)
EDGE: step:horm-span-condition | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-hormander@L2352-L2355 | span condition equals Hormander hypothesis
EDGE: step:horm-apply-hairer | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-hormander@L2351-L2351 | application of the criterion
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Covers eqn-stratanovich. SOURCE_GAP: for t=0 the law of X_t under P_u is a Dirac mass with no density, so 't>=0' should read 't>0' (statement as written is false at t=0); step:kol-semigroup-smooth uses T_0 f = f directly.

NODE: step:horm-stratonovich
KIND: step
TITLE: Stratonovich form of the SDE
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-hormander@L2346-L2349
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-hormander@L2346-L2349
CONTRACT_ID: paper.step:horm-stratonovich
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: beta C^1
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: dX = gamma(X)dt + beta(X) o dB with gamma = alpha - (1/2) beta' beta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Standard Ito-Stratonovich conversion (Stratonovich correction (1/2)<beta(X),B>' = (1/2)beta'beta dt); no external cited.

NODE: step:horm-span-condition
KIND: step
TITLE: Hormander span condition is equivalent to: beta(u) or beta'(u)alpha(u) nonzero
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-hormander@L2351-L2355
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-hormander@L2351-L2355
CONTRACT_ID: paper.step:horm-span-condition
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: gamma = alpha - (1/2) beta' beta
SOURCE_QUANTIFIERS: forall u
SOURCE_CONCLUSION: {beta(u), beta'(u)gamma(u) - gamma'(u)beta(u)} spans R iff beta(u) != 0 or beta'(u)alpha(u) != 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:horm-stratonovich
ROUTES: -
ROUTE_FOR: -
EDGE: step:horm-stratonovich | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-hormander@L2353-L2353 | gamma enters the bracket
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: At beta(u)=0 the bracket reduces to beta'(u)gamma(u) = beta'(u)alpha(u). Algebra: beta'gamma - gamma'beta = beta'alpha - alpha'beta + (1/2)beta^2 beta''; one direction trivial.

NODE: step:horm-apply-hairer
KIND: application
TITLE: Application of the one-dimensional Hormander criterion
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-hormander@L2351-L2351
PROOF_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-hormander@L2351-L2351
CONTRACT_ID: paper.step:horm-apply-hairer
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: span condition at every u
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: smooth transition density and smooth semigroup of the SDE
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: ext:hormander-1d, step:horm-span-condition, step:horm-stratonovich
ROUTES: -
ROUTE_FOR: -
EDGE: ext:hormander-1d | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-hormander@L2351-L2351 | Hairer's Theorem 1.3
EDGE: step:horm-span-condition | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-hormander@L2352-L2355 | hypothesis at every u in R
EDGE: step:horm-stratonovich | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-hormander@L2351-L2351 | Stratonovich coefficients of the theorem
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: Hairer's theorem needs bounded derivatives of all orders of the (Stratonovich) coefficients (here periodic up to sign: beta^2 periodic and beta smooth give bounded derivatives, plausible but unstated) and gives a smooth density; smoothness of u -> E_u f(X_t) for bounded f is stated in the lemma but the criterion's conclusion as cited ('the smoothness conditions in the lemma statement') is not spelled out.

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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
DEPS: item-I, item-II, eqn-nu-D.nu, defn-sigma, def-arg, lem-p, lem-stationary, lem-stationary.admissible
ROUTES: -
ROUTE_FOR: -
EDGE: item-I | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1259-L1259 | left side of the first identity
EDGE: item-II | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1260-L1260 | left side of the second identity
EDGE: eqn-nu-D.nu | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1257-L1260 | nu is pi-periodic and enters both integrands
EDGE: defn-sigma | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1255-L1255 | sigma-time change defining theta^_t
EDGE: def-arg | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1255-L1255 | argument process theta behind theta^
EDGE: lem-p | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1255-L1255 | 'as in Lemma 2.13': p 1_[0,2pi] is the law of arg zz (stationary p of Lemma 2.13)
EDGE: lem-stationary | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1257-L1257 | stationarity of e^{i theta^_t(zz)} for every admissible p (R7/R15); the source cites only Lemma 2.13
EDGE: lem-stationary.admissible | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-integral-nu@L1255-L1257 | p ranges over admissible densities (R7/R15)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
DEPS: item-I, defn-loewner.absorbing-time, step:prop-i-a-not-to-minus-infinity, lem-swallow-distance, step:all-z-apply-Tz, lem-all-z
ROUTES: -
ROUTE_FOR: -
EDGE: item-I | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1265-L1266 | sign hypothesis on (I)
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1268-L1268 | T_z in the conclusion
EDGE: step:prop-i-a-not-to-minus-infinity | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1406-L1406 | log∣f^_t(zz)∣ does not tend to -infinity when (I) >= 0
EDGE: lem-swallow-distance | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1407-L1407 | T_zz < infinity would force log∣f^_t(zz)∣ -> -infinity, so T_zz = infinity a.s.
EDGE: step:all-z-apply-Tz | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1407-L1407 | discharges the scale-invariance/future-dependence hypotheses of Lemma 3.3 for {T_z = infinity}
EDGE: lem-all-z | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1407-L1407 | extends a.s. T_zz = infinity to each fixed z != 0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
DEPS: item-I, defn-loewner.absorbing-time, eqn-neg-I1-bd, step:prop-i-b-ode-comparison, step:all-z-apply-Tz, lem-all-z
ROUTES: -
ROUTE_FOR: -
EDGE: item-I | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1265-L1270 | sign hypothesis on (I)
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1270-L1270 | T_z in the conclusion
EDGE: eqn-neg-I1-bd | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1409-L1412 | pathwise upper bound on log∣f_t(zz)∣ on (t_*,T_zz) in capacity time
EDGE: step:prop-i-b-ode-comparison | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1413-L1415 | F'(t) e^{-alpha F(t)} > 1 forces T_zz <= t_* + e^{-alpha F(t_*)}/alpha < infinity
EDGE: step:all-z-apply-Tz | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1416-L1416 | hypotheses of Lemma 3.3 for {T_z < infinity}
EDGE: lem-all-z | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1416-L1416 | extends a.s. T_zz < infinity to each fixed z != 0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
DEPS: item-II, defn-hulls.left, defn-loewner.absorbing-time, step:prop-ii-a-koebe-limit, step:all-z-apply-dist, lem-all-z
ROUTES: -
ROUTE_FOR: -
EDGE: item-II | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1276-L1279 | sign hypothesis on (II)
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1279-L1279 | L_t in the conclusion
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1279-L1279 | T_z in the conclusion
EDGE: step:prop-ii-a-koebe-limit | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1459-L1468 | a.s. dist(zz,L_t) -> 0 as t -> T_zz
EDGE: step:all-z-apply-dist | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1468-L1468 | discharges the hypotheses of Lemma 3.3 for the event {lim dist(z,L_t)=0}
EDGE: lem-all-z | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1468-L1468 | extends to each fixed z != 0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
DEPS: item-II, defn-hulls.left, defn-loewner.absorbing-time, step:prop-ii-b-martingale-zero-one
ROUTES: -
ROUTE_FOR: -
EDGE: item-II | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1276-L1281 | sign hypothesis on (II)
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1281-L1281 | L_t in the conclusion
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1281-L1281 | T_z in the conclusion
EDGE: step:prop-ii-b-martingale-zero-one | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-ii@L1815-L1815 | indicator of {lim dist > 0} is a.s. >= q_*, hence equals 1
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
DEPS: lem-stationary-sde, step:stationary-sde-X-form, lem-polar, lem-recurrence, lem-stationary, lem-p, eqn-integral-nu
ROUTES: -
ROUTE_FOR: -
EDGE: lem-stationary-sde | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1402-L1402 | conclusion of Lemma 3.4 for Y = log∣f^(zz)∣
EDGE: step:stationary-sde-X-form | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1403-L1403 | SDEs for X and Y in the form required
EDGE: lem-polar | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1402-L1403 | SDE (eqn-abs-zt) for log∣f^_t(zz)∣ with drift nu(theta^)
EDGE: lem-recurrence | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1403-L1403 | recurrence of X (hits a fixed xbar at arbitrarily large times)
EDGE: lem-stationary | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1403-L1403 | stationarity of the law of X_t = e^{2 i theta^_t(zz)} for every admissible p
EDGE: lem-p | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1402-L1402 | stationary choice of zz as in Lemma 2.13
EDGE: eqn-integral-nu | source/arxiv-2203.07313v4/complex-sle-final.tex#prop-i@L1402-L1402 | E f^0(X_0) = E nu(theta^_0(zz)) = (I)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The source says only 'the second part follows from applying Lemma 3.4'; the premise discharge parallels step:prop-i-apply-stationary-sde. Y_0 = log(|f_0'(zz)|/|f_0(zz)|) = log(1/|zz|) = 0.

NODE: step:zero-in-left-hull
KIND: step
TITLE: 0 belongs to every left hull (and to the future hulls L_{t,s+t})
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
DEPS: defn-hulls.left, defn-loewner.absorbing-time
ROUTES: -
ROUTE_FOR: -
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1558-L1558 | L_t = {z : T_z <= t}
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-log-finite-exp@L1558-L1558 | T_0 = 0 because the driver starts at the singular point 0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: R4: U_0 = 0, so T_0 = 0 and 0 in L_t for all t. Used at L1558 and L1768 ('0 in L_{t,s+t}'). The shifted-driver statement for L_{t,s+t} is the same fact applied to the chain driven by U(.+t)-U(t).

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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
DEPS: claim:gt-conformal, defn-hulls.left, defn-hulls.right
ROUTES: -
ROUTE_FOR: -
EDGE: claim:gt-conformal | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1702-L1705 | f_t : C\L_t -> C\R_t conformal
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1702-L1702 | L_t
EDGE: defn-hulls.right | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-converse-w-o-upgrade@L1702-L1702 | R_t
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
DEPS: step:computation-scaling-markov, lem-stationary, lem-p
ROUTES: -
ROUTE_FOR: -
EDGE: step:computation-scaling-markov | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-computation@L1526-L1526 | f~ =_D f and independent of the past
EDGE: lem-stationary | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-computation@L1526-L1526 | stationarity: f_{sigma(t^)}(zz)/∣f_{sigma(t^)}(zz)∣ =_D zz
EDGE: lem-p | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-computation@L1526-L1526 | stationarity cited as Lemma 2.13
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
SOURCE_HYPOTHESES: a,b > 0; c = 0; p admissible (R7/R15)
SOURCE_QUANTIFIERS: a,b > 0
SOURCE_CONCLUSION: p(u) = Z^{-1}(a+b+(b-a)cos 2u)^{4/(b-a)} for a != b and Z^{-1} exp((4/a)cos^2 u) for a = b, with normalizing Z = Z(a,b) > 0; p = p_0 in the proof of Lemma 2.13 (r_* = 0)
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP (R7/R15): 'we can explicitly solve (2.24)' identifies the stationary density with the displayed formula only for the constructed p (Remark 2.15, Lemma 2.13 proof with r_* = 0). The theorem is stated for every admissible p; uniqueness of the normalized pi-periodic ODE solution (so every admissible p equals (3.19)) is not argued. Also, differentiating/solving the ODE and checking the normalization/regularity (e.g. on {a = b}) are not written.

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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-C/sonnet
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: reviewer-C/sonnet (proposed split of step:zero-in-left-hull)
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The source writes 'the fact that 0 in L_{t,s+t}' at L1768 without argument (read as the shifted-driver version of L1558; not a SOURCE_GAP beyond what L1558 already assumes). Split out of step:zero-in-left-hull so each EDGE locator cites its own use site.

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
NOTE: SOURCE_GAP: as stated the lemma is trivial for U = empty (the empty set is open, bounded, disjoint from L_t and disconnected from infinity). Non-emptiness of U (U = U^- or U^+ of the proof) is implicit and is read as part of the statement; consumers (proof-a, proof-b) need it. The hypothesis c>=0 is supplied at consumers by step:wlog-c-nonneg.

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
NOTE: SOURCE_GAP: existence of non-empty open U^+- satisfying both requirements (distance >= 2 eps from the imaginary axis; mapped by z -> sqrt(z^2+4T) into B_{eps/2}(x -+ 2 i eps)) is asserted at L2165, not shown. Reviewer computation (to be confirmed by the orchestrator): the preimage of w = x -+ 2 i eps is z with z^2 = w^2-4T, |Re z| ~ 2 x eps / sqrt(4T-x^2), and the preimage of B_{eps/2}(w) has |Re z| <= ~ 2.5 x eps / sqrt(4T-x^2) as eps -> 0. A point at distance >= 2 eps from the imaginary axis therefore needs x / sqrt(4T-x^2) >~ 0.8. For the choice made in the proof of Lemma 4.4 (x = 2C, y = 7C, so x/y = 2/7) and any T > y^2/2 one has x / sqrt(4T-x^2) < 0.21 (numerically max |Re z|/eps = 0.72 at C = 1, T = 13, eps = 0.01), so U^+- would be empty. Lemma 4.4 is stated existentially ('we can choose 0<x<y'), so the proof of Lemma 4.1 may not re-pick x, y. The text also writes (B_t) for measurability; the hulls depend on U = (B, B~).

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

## Append-only structural amendments

<!-- BEGIN PROOF DEPGRAPH GENERATED -->
Regenerated by `proof_depgraph.py`; do not hand-edit.

### Dashboard

* Total nodes: **274**
* Frozen anchors: **31**
* Versioned statement contracts: **274**
* Total edges: **716**
* Root-closure nodes: **274**
* Dependency leaves in root closure: **34**
* Assumption boundary leaves: **0**
* External boundary leaves: **19**
* Alternative routes: **0**
* Topology review queue: **274**
* Explicit source gaps: **41**
* Coverage items: **300**; excluded: **98**

### Roots

* `defn-loewner.well-defined` [PROPOSED; frozen] — contract `paper.def1_1.wellDefined@1`
* `lem-p.exists` [PROPOSED; frozen] — contract `paper.lem2_13.exists@1`
* `nonsource.exists-sle-driver` [PROPOSED; frozen] — contract `paper.nonsource.existsSLEDriver@1`
* `thm-phases` [PROPOSED; frozen] — contract `paper.thm1_8.phases@1`
* `thm-phases.c-zero` [PROPOSED; frozen] — contract `paper.thm1_8.cZero@1`
* `thm-disconnects.a` [PROPOSED; frozen] — contract `paper.thm1_10.a@1`
* `thm-disconnects.b` [PROPOSED; frozen] — contract `paper.thm1_10.b@1`
* `prop-i.a` [PROPOSED; frozen] — contract `paper.prop3_1.a@1`
* `prop-i.b` [PROPOSED; frozen] — contract `paper.prop3_1.b@1`
* `prop-ii.a` [PROPOSED; frozen] — contract `paper.prop3_2.a@1`
* `prop-ii.b` [PROPOSED; frozen] — contract `paper.prop3_2.b@1`
* `lem-connected.left` [PROPOSED; frozen] — contract `paper.lem2_4.leftHull@1`
* `eqn-scale.left` [PROPOSED; frozen] — contract `paper.prop2_1_scaling.leftHull@1`
* `eqn-reflect.left` [PROPOSED; frozen] — contract `paper.prop2_2_reflection.leftHull@1`

### Topology review queue

* `claim:gt-conformal` [PROPOSED] — g_t is conformal from C\L_t onto C\(R_t+U_t); z(g_t(z)-z) -> 2t
* `claim:hull-nonempty` [PROPOSED] — L_t contains the starting point U_0
* `claim:hulls-monotone` [PROPOSED] — Left hulls are increasing
* `def-arg` [PROPOSED] — Argument process theta_t(z)
* `def-disconnect` [PROPOSED] — S disconnects S' from infinity
* `defn-chordal-loewner` [PROPOSED] — Chordal Loewner chains (forward and reverse)
* `defn-hulls.left` [PROPOSED] — Left hull L_t
* `defn-hulls.right` [PROPOSED] — Right hull R_t
* `defn-loewner.absorbing-time` [PROPOSED] — Absorbing time T_z
* `defn-loewner.solution` [PROPOSED] — Loewner initial value problem (solution predicate)
* `defn-loewner.well-defined` [PROPOSED] — Well-definedness of the Loewner chain
* `defn-phases.dense` [PROPOSED] — Dense phase
* `defn-phases.hitting` [PROPOSED] — Hitting phase
* `defn-phases.swallowing` [PROPOSED] — Swallowing phase
* `defn-phases.thin` [PROPOSED] — Thin phase
* `defn-sigma` [PROPOSED] — sigma-time parametrization of a centered SLE_Sigma at a fixed point
* `defn-sle` [PROPOSED] — SLE_Sigma driving process (planar BM with covariance Sigma)
* `defn-sle.gaussian-law` [PROPOSED] — Centered Gaussian law on C = R^2
* `eqn-c0-integrals` [PROPOSED] — Integrals (I),(II) for c = 0 (3.20)
* `eqn-c0-phase-show` [PROPOSED] — Positivity (3.21): int_0^{2pi} cos(2u)p(u) du > 0
* `eqn-computation-tilde-f` [PROPOSED] — Rescaled future chain f~_u (3.3)
* `eqn-conc` [PROPOSED] — Concatenation property (2.3)
* `eqn-cov-matrix` [PROPOSED] — Covariance matrix Sigma
* `eqn-def-ft` [PROPOSED] — SDE (1.6) for the centered SLE_Sigma maps f_t
* `eqn-disconnect-mart` [PROPOSED] — Conditional lower bound P(disconnect z before T_z | F_{sigma_z(t~)}) >= q_*
* `eqn-dist-1` [PROPOSED] — Rearrangement (3.11)
* `eqn-dist-2` [PROPOSED] — Bound on E_s^c, first part (3.16)
* `eqn-dist-3` [PROPOSED] — Main distance inequality (3.6)
* `eqn-dist-cases` [PROPOSED] — Case formula (3.13)
* `eqn-dist-es` [PROPOSED] — Bound on E_s^ (3.15)
* `eqn-dist-esc` [PROPOSED] — Bound on E_s^c (3.17)
* `eqn-dist-event` [PROPOSED] — Definition of the event E_s^ (3.12)
* `eqn-hit-koebe` [PROPOSED] — Koebe estimate (3.5): |f_t'(zz)| asymp dist(f_t(zz),R_t)/dist(zz,L_t) <= |f_t(zz)|/dist(zz,L_t)
* `eqn-integral-nu` [PROPOSED] — Integrals (I),(II) as stationary expectations (3.1)
* `eqn-koebe-t` [PROPOSED] — Koebe for f_t on C\L_{s+t} (3.10)
* `eqn-koebe-union` [PROPOSED] — Koebe on E_s^ (3.14)
* `eqn-log-finite-end` [PROPOSED] — (3.2'): P(tau_k <= sigma(qN)) <= C_N 2^{-k}
* `eqn-log-finite-show` [PROPOSED] — Tail bound (3.18): P(dist(zz,L_{sigma(t^)}) <= 16^{-k}) <= C_{t^} 2^{-k+1}
* `eqn-neg-I1-bd` [PROPOSED] — Pathwise bound (3.2): log|f_t(zz)| < -(alpha/2) int_0^t |f_s(zz)|^{-2} ds
* `eqn-nu-D.D` [PROPOSED] — Diffusion coefficient D(u)
* `eqn-nu-D.mu` [PROPOSED] — Drift mu(u)
* `eqn-nu-D.nu` [PROPOSED] — Log-drift nu(u)
* `eqn-reflect` [PROPOSED] — Reflection property (2.2), full
* `eqn-reflect.left` [PROPOSED] — Reflection property for left hulls
* `eqn-scale` [PROPOSED] — Scaling property (2.1), full
* `eqn-scale.left` [PROPOSED] — Scaling property for left hulls
* `eqn-sde-ratio` [PROPOSED] — SDE (3.4) for log(|f^_t'|/|f^_t|)
* `eqn-two-dist-ratio` [PROPOSED] — Comparison (3.9) of the two Koebe formulas
* `eqn-two-formulas` [PROPOSED] — Koebe for f_{t,s+t} on C\L_{t,s+t} (3.7)
* `eqn-two-formulas-b` [PROPOSED] — Koebe for f_{t,s+t} on C\(L_{t,s+t} u R_t) (3.8)
* `eqn-wt-L-dist` [PROPOSED] — Joint law identity (3.4)
* `ext:birkhoff` [PROPOSED] — Birkhoff ergodic theorem
* `ext:blumenthal` [PROPOSED] — Blumenthal zero-one law: germ sigma-field of Brownian motion is trivial
* `ext:bm-existence` [PROPOSED] — Existence of planar Brownian motion with covariance Sigma
* `ext:bm-support` [PROPOSED] — Support theorem: a Brownian motion stays uniformly within delta of a given admissible continuous path on [0,T] with positive probability
* `ext:dct` [PROPOSED] — Dominated convergence
* `ext:durrett-7.3.2` [PROPOSED] — Durrett Theorem 7.3.2 (recurrence of Z-valued stationary sequences)
* `ext:girsanov` [PROPOSED] — Girsanov theorem
* `ext:hormander-1d` [PROPOSED] — Hormander criterion, one-dimensional case
* `ext:ito-complex` [PROPOSED] — Ito formula for complex semimartingales
* `ext:koebe-distortion` [PROPOSED] — Koebe distortion estimate (Lawler Corollary 3.23)
* `ext:koebe-quarter` [PROPOSED] — Koebe quarter theorem (Lawler Corollary 3.18)
* `ext:kolmogorov-zero-one` [PROPOSED] — Kolmogorov zero-one law (tail sigma-algebra of BM is trivial)
* `ext:lawler-4.5` [PROPOSED] — Lawler Theorem 4.5: g_t is conformal onto H minus hull; z(g_t-z) -> 2t
* `ext:levy-characterization` [PROPOSED] — Levy characterization / Dambis-Dubins-Schwarz
* `ext:loewner-convergence` [PROPOSED] — Lawler Prop 4.43: locally uniform convergence of driving functions gives locally uniform convergence of Loewner maps away from the hull
* `ext:martingale-convergence` [PROPOSED] — Levy upward martingale convergence (conditional Borel-Cantelli)
* `ext:picard-lindelof` [PROPOSED] — Picard-Lindelof ODE existence and uniqueness
* `ext:scale-function` [PROPOSED] — Scale-function hitting lemma
* `ext:strong-markov-bm` [PROPOSED] — Strong Markov property of Brownian motion
* `item-I` [PROPOSED] — Integral (I)
* `item-II` [PROPOSED] — Integral (II)
* `lem-all-z` [PROPOSED] — Lemma 3.3: from the stationary point zz to every z
* `lem-c-event` [PROPOSED] — Positive-probability event on the increments of the driving BMs
* `lem-c0-bdy` [PROPOSED] — Lemma 3.12: c = 0, a - b = 8 is in the hitting phase
* `lem-c0-phases` [PROPOSED] — Lemma 3.11: phases for c = 0 away from the swallowing/hitting boundary
* `lem-computation` [PROPOSED] — Lemma 3.9: stationarity of the pair (point, future hull)
* `lem-connected.left` [PROPOSED] — Left hulls are connected
* `lem-converse-w-o-upgrade` [PROPOSED] — Lemma 3.8: (II) > 0 implies P(lim dist(zz,L_t) = 0) < 1
* `lem-disconnect-2` [PROPOSED] — Left hulls disconnect a fixed open set with positive probability
* `lem-endpt-cont` [PROPOSED] — |f_t(z)| tends to 0 at the absorbing time
* `lem-forward-reverse-ext` [PROPOSED] — Real and imaginary drivers recover forward and reverse chordal chains
* `lem-haus` [PROPOSED] — Continuity of Loewner maps and of left/right hulls in the driving function
* `lem-hormander` [PROPOSED] — Smooth density and smooth semigroup for the periodic SDE
* `lem-integral-ii` [PROPOSED] — Lemma 3.7: E log(|f^'|/|f^|)(zz) = -t^ (II), and divergence when (II) < 0
* `lem-kolmogorov` [PROPOSED] — Kolmogorov forward equation for periodic SDEs (stationary law)
* `lem-line-approx` [PROPOSED] — Hulls and map of an SLE_Sigma chain are close to the zero-driver chain
* `lem-log-finite-exp` [PROPOSED] — Lemma 3.10: E log(1/dist(zz,L_{sigma(t^)})) < infinity
* `lem-markov` [PROPOSED] — Markov property of SLE_Sigma
* `lem-mult-by-i` [PROPOSED] — Multiplying by i converts reverse to forward chains
* `lem-p` [PROPOSED] — Lemma 2.13 (full): non-negative pi-periodic solution, positive off a discrete set, giving a stationary argument process
* `lem-p.exists` [PROPOSED] — Lemma 2.13, existence of an admissible density
* `lem-polar` [PROPOSED] — Polar decomposition of SLE_Sigma
* `lem-pos-hits-before-neg` [PROPOSED] — Re f_2 changes sign across a segment [x,y] disjoint from L_2 with positive probability
* `lem-recurrence` [PROPOSED] — Recurrence of the stationary argument process
* `lem-recurrent` [PROPOSED] — Lemma 3.5: recurrence for stationary sequences with E(xi_1|I) = 0
* `lem-scaling` [PROPOSED] — Scale invariance of SLE_Sigma
* `lem-stationary` [PROPOSED] — Stationarity of the argument process started from an admissible density
* `lem-stationary-sde` [PROPOSED] — Lemma 3.4: law of large numbers and recurrence for stationary SDE functionals
* `lem-stationary.admissible` [PROPOSED] — Admissible stationary density (hypothesis package of Lemma 2.14)
* `lem-swallow-distance` [PROPOSED] — Lemma 3.6: log|f^_t(z)| -> -infinity when T_z < infinity
* `lem:re-im-bounds` [PROPOSED] — Pathwise bounds on increments of Re f_t(z), Im f_t(z) while |f_t(z)|>1
* `nonsource.exists-sle-driver` [PROPOSED] — Existence of an SLE_Sigma driver
* `prop-i.a` [PROPOSED] — Proposition 3.1(a): (I) >= 0 implies T_z = infinity
* `prop-i.b` [PROPOSED] — Proposition 3.1(b): (I) < 0 implies T_z < infinity
* `prop-ii.a` [PROPOSED] — Proposition 3.2(a): (II) < 0 implies dist(z,L_t) -> 0
* `prop-ii.b` [PROPOSED] — Proposition 3.2(b): (II) > 0 implies lim dist(z,L_t) > 0
* `remark-p0` [PROPOSED] — Remark 2.15: for c=0 the periodic solution p of Lemma 2.13 is a constant times p_0
* `remark-sigma` [PROPOSED] — sigma_z is defined on all of (0,infty) and maps it onto (0,T_z)
* `step:D-structure` [PROPOSED] — Structure of D: positivity if |c|<sqrt(ab); D = (1/2)(sqrt a sin -+ sqrt b cos)^2 if c = +-sqrt(ab)
* `step:all-z-apply-Tz` [PROPOSED] — Lemma 3.3 hypotheses hold for {T_z < infinity} (and its complement)
* `step:all-z-apply-dist` [PROPOSED] — Lemma 3.3 hypotheses hold for {lim_{t->T_z} dist(z,L_t) = 0}
* `step:all-z-lambda-conull` [PROPOSED] — Lambda has full Lebesgue measure in the unit circle
* `step:all-z-markov-transfer` [PROPOSED] — Conditioning at a stopping time tau < T_z
* `step:all-z-null-set-density` [PROPOSED] — An admissible p vanishes only on a Lebesgue-null set
* `step:all-z-stopping-time-choice` [PROPOSED] — Choice of tau with e^{i theta_tau(z)} in Lambda with probability >= q
* `step:arg-lift` [PROPOSED] — Existence and uniqueness of the continuous argument lift
* `step:bm-scaling` [PROPOSED] — Brownian scaling for the planar driver
* `step:c-event-E1` [PROPOSED] — Event E_1: sqrt(b)B~_1>=4 and sqrt(a)|B_t|<=C-2t on [0,1] has positive probability for large C
* `step:c-event-E2` [PROPOSED] — Event E_2: 2+4C<=sqrt(a)(B_2-B_1)<=5C-2 and sqrt(b)(B~_t-B~_1)>=2t-3 on [1,2] has positive probability for large C
* `step:c-event-combine` [PROPOSED] — E_1 and E_2 are independent and positive, so all four conditions hold with positive probability
* `step:c0-bdy-capacity-time` [PROPOSED] — limsup_{t->T_z^-} |f_t'(z)|/|f_t(z)| = infinity
* `step:c0-bdy-drift-vanishes` [PROPOSED] — nu(.) + 2cos(2.) = 0 when c = 0 and a - b = 8
* `step:c0-bdy-finite-time` [PROPOSED] — T_z < infinity when c = 0 and a - b = 8
* `step:c0-bdy-hitting-from-limsup` [PROPOSED] — limsup |f_t'|/|f_t| = infinity implies dist(z,L_t) -> 0
* `step:c0-bdy-martingale-bm` [PROPOSED] — log(|f^'|/|f^|)(z) is a time-changed BM with limsup +infinity
* `step:c0-explicit-density` [PROPOSED] — Explicit stationary density p for c = 0 (3.19)
* `step:c0-positivity-reduction` [PROPOSED] — Reduction of positivity of int cos(2u)p(u) du to [0,pi/2]
* `step:c0-positivity-reflection` [PROPOSED] — Reflection across pi/4: |cos(2(pi/2-u))p(pi/2-u)| < cos(2u)p(u) on [0,pi/4)
* `step:c0-sign-analysis` [PROPOSED] — Signs of (I),(II) for c = 0
* `step:computation-scaling-markov` [PROPOSED] — f~ has the law of f and is independent of the evolution up to sigma(t^)
* `step:computation-time-change-identity` [PROPOSED] — sigma~(s^) = |f_{sigma(t^)}(zz)|^{-2}(sigma(s^+t^) - sigma(t^))
* `step:connected-homotopy` [PROPOSED] — Loop images stay in C\{0}: f_t o loop homotopic to loop
* `step:connected-loop-criterion` [PROPOSED] — Connectedness of L_t from loops not surrounding the origin
* `step:connected-region-misses-hull` [PROPOSED] — Winding number argument: bounded region misses L_t
* `step:converse-conclude` [PROPOSED] — Contrapositive: lim dist = 0 a.s. implies (II) <= 0
* `step:converse-event-converges` [PROPOSED] — 1_{E_s^} -> 1 as s^ -> infinity (under the contrapositive hypothesis)
* `step:converse-lhs-nonneg` [PROPOSED] — E[left side of (3.6)] >= 0
* `step:converse-rhs-limit` [PROPOSED] — Limit of E[right side of (3.6)] as s^ -> infinity
* `step:disc-E1-positive` [PROPOSED] — P(E_1)>0 for every T, eps>0
* `step:disc-E2E3-positive` [PROPOSED] — P(E_2 cap E_3)>0 for some eps,K and any T (Lemma 4.4 applied to the restarted chain)
* `step:disc-E4-positive` [PROPOSED] — P(E_4)>0 for every K, eps>0 (by Markov property and Lemma 4.3)
* `step:disc-a-hit-Lambda` [PROPOSED] — A closed positive-measure set Lambda' is hit by e^{i theta^_tz(z)} with positive probability
* `step:disc-a-markov-restart` [PROPOSED] — Conditional probability given F at sigma_z(tau) is at least q(e^{i theta^_tau(z)})
* `step:disc-a-martingale-limit-one` [PROPOSED] — The indicator of the disconnection event is a.s. 1 by martingale convergence
* `step:disc-a-open-condition` [PROPOSED] — Disconnection before T_z is stable under small perturbation of the point
* `step:disc-a-positive-measure-set` [PROPOSED] — The set of unit z with q(z)>0 has positive 1-d Lebesgue measure
* `step:disc-a-q-positive-all-z` [PROPOSED] — q(z)>0 for every z in C minus {0}
* `step:disc-a-q-scale-invariance` [PROPOSED] — q(z)=q(z/|z|) by scale invariance
* `step:disc-a-uniform-lower-bound` [PROPOSED] — There is q_*>0 with q(z)>=q_* for every z in C minus {0}
* `step:disc-b-blumenthal` [PROPOSED] — Almost surely there are arbitrarily small times t with non-empty interior of the disconnected set
* `step:disc-b-monotone-extension` [PROPOSED] — Monotonicity extends the property from small times to all times
* `step:disc-b-positive-for-all-t` [PROPOSED] — That probability is positive for every t>0
* `step:disc-b-scale-invariance` [PROPOSED] — P(set disconnected by L_t has non-empty interior) is independent of t
* `step:disc-concatenation-transfer` [PROPOSED] — On E_1..E_4, L_{T,T+2+K} meets S but not B_{3eps}(x)
* `step:disc-independence-product` [PROPOSED] — E_1, E_2 cap E_3, E_4 are independent, hence P(E_1 cap E_2 cap E_3 cap E_4)>0
* `step:disc-pullback-conclusion` [PROPOSED] — Pull back the disconnection through f_T by concatenation: L_{T+2+K} disconnects U^+- avoiding it
* `step:disc-setup` [PROPOSED] — Choice of parameters T, eps, K, the sets U^{+-} and the four events E_1..E_4
* `step:disc-topological-separation` [PROPOSED] — L_{T,T+2+K} cup R_T disconnects one of f_T(U^+-) from infinity without hitting it
* `step:driver-negation-symmetry` [PROPOSED] — -U has the same law as U (reflection symmetry of the driver)
* `step:driver-representation` [PROPOSED] — Representation U = sqrt(a) B + i sqrt(b) B~ for a planar BM with covariance Sigma
* `step:endpt-finite-upcrossings` [PROPOSED] — Finitely many upcrossings before T_z
* `step:endpt-liminf` [PROPOSED] — liminf |f_t(z)| = 0 at a finite absorbing time
* `step:endpt-upcrossing-bound` [PROPOSED] — Upcrossings of [alpha,beta] have duration at least epsilon
* `step:forward-real-driver` [PROPOSED] — Real driver: complex chain extends the forward chordal chain by Schwarz reflection
* `step:future-point-outside-hulls` [PROPOSED] — zz not in L_{s+t}; f_t(zz) not in R_t u L_{t,s+t}
* `step:haus-contradiction-L-t` [PROPOSED] — g_t cannot extend conformally to a set V meeting L_t
* `step:haus-limit-conformal-extension` [PROPOSED] — Normal-family argument: g^n_t converges on V to a conformal limit extending g_t
* `step:haus-maps-converge` [PROPOSED] — Convergence of forward (and reverse) Loewner maps from convergence of drivers
* `step:haus-right-hull-reduction` [PROPOSED] — Right-hull and reverse-map versions via left hulls of reverse chains
* `step:haus-subsequence-limit-contained` [PROPOSED] — Hausdorff-subsequential limit L' of L^n_t lies in L_t
* `step:haus-subsubsequence-closure` [PROPOSED] — Subsequence principle: from limit identification to the quantitative statement for all large n
* `step:horm-apply-hairer` [PROPOSED] — Application of the one-dimensional Hormander criterion
* `step:horm-span-condition` [PROPOSED] — Hormander span condition is equivalent to: beta(u) or beta'(u)alpha(u) nonzero
* `step:horm-stratonovich` [PROPOSED] — Stratonovich form of the SDE
* `step:hulls-compact` [PROPOSED] — L_t and R_t are compact (premise of the Koebe theorems)
* `step:integral-ii-apply-stationary-sde` [PROPOSED] — Apply Lemma 3.4 with Y = log(|f^'|/|f^|)(zz)
* `step:integral-ii-expectation` [PROPOSED] — E log(|f^'|/|f^|)(zz) = -t^ (II)
* `step:kol-derivative-at-zero` [PROPOSED] — Derivative of E_p f(X_t) at t=0 (A.3)
* `step:kol-derivative-vanishes-all-times` [PROPOSED] — d/ds E_p f(X_s) = 0 for all s, hence E_p f(X_s) = E_p f(X_0)
* `step:kol-integration-by-parts` [PROPOSED] — Integration by parts with vanishing boundary terms: derivative is 0 (A.4)
* `step:kol-ito-expectation` [PROPOSED] — Ito formula for f(X_t), f in C^2 pi-periodic: integral form of E_p f(X_t)
* `step:kol-markov-semigroup` [PROPOSED] — Markov property: E_p(T_s f(X_t)) = E_p f(X_{t+s})
* `step:kol-process-stationarity` [PROPOSED] — From invariance of E_p f(X_s) for C^2 f to stationarity of the law of the process (e^{2iX_t})
* `step:kol-semigroup-smooth` [PROPOSED] — T_s f is pi-periodic and smooth (so it is admissible as a test function)
* `step:kol-shift-start` [PROPOSED] — Starting distribution may be taken on [x,x+pi]
* `step:line-apply-haus` [PROPOSED] — Apply Lemma 4.3 with U = 0 to deduce the Hausdorff and map bounds
* `step:line-small-driver-positive` [PROPOSED] — The planar driver stays uniformly near 0 on [0,T] with positive probability
* `step:line-zero-driver-chain` [PROPOSED] — Zero driver: g_t = sqrt(z^2+4t), L_t=[-2 t^{1/2} i,2 t^{1/2} i], R_t=[-2 t^{1/2},2 t^{1/2}]
* `step:loewner-glue-maximal` [PROPOSED] — Gluing: a solution exists on all of [0,T_z)
* `step:loewner-local-solution` [PROPOSED] — Local existence and uniqueness for the Loewner ODE away from U_t
* `step:log-finite-binomial` [PROPOSED] — Binomial tail bound on the number of successful scales
* `step:log-finite-distortion` [PROPOSED] — Distortion estimate: f_{tau_k}(B_{16^{-k-1}}(zz))/|f_{tau_k}(zz)| in B_{1/2}
* `step:log-finite-exit-times` [PROPOSED] — T_k <= tau_{k+1}
* `step:log-finite-iid` [PROPOSED] — The integral int_{tau_k}^{T_k} |f_v(zz)|^{-2} dv is independent of F_{tau_k} with k-free law
* `step:log-finite-q-choice` [PROPOSED] — Choice of the constant q = q(Sigma)
* `step:log-finite-tail-to-expectation` [PROPOSED] — Tail bound implies E log(1/dist) < infinity
* `step:markov-driver` [PROPOSED] — Strong Markov property for the planar driver
* `step:p-case1` [PROPOSED] — Case 1 assembly: smooth admissible density for c<sqrt(ab) with int_0^{2pi} p = 1
* `step:p-case1-first-order-solutions` [PROPOSED] — p_0, p_1 smooth and solve the first-order ODEs -mu p_j + [D p_j]' = j
* `step:p-case1-mu-over-D-integral` [PROPOSED] — Evaluation of int_0^pi mu/D = 8 pi c (2 sqrt(ab-c^2)-(a+b))/(sqrt(ab-c^2)((a-b)^2+4c^2)) <= 0
* `step:p-case1-nonneg` [PROPOSED] — r_* >= 0 and hence p >= 0
* `step:p-case1-periodic` [PROPOSED] — p = k(p_0 + r_* p_1) is pi-periodic
* `step:p-case1-zero-set` [PROPOSED] — p vanishes only on a discrete set (case 1)
* `step:p-case2` [PROPOSED] — Case 2 assembly: admissible density for c = sqrt(ab) with int_0^{2pi} p = 1
* `step:p-case2-limits` [PROPOSED] — Case 2: l'Hopital limits of p at x and x+pi equal (a+b)/(4 sqrt(ab))
* `step:p-case2-regularity` [PROPOSED] — Case 2: periodic extension is continuous, smooth off x+piZ, solves (2.13) there and D p is C^1 with zero derivative on x+piZ
* `step:p-case2-welldefined` [PROPOSED] — Case 2: p defined by (2.32) is well defined, positive, smooth on (x,x+pi) and solves -mu p + [D p]' = 1
* `step:p-positive-off-discrete` [PROPOSED] — The constructed p is positive except on a discrete set
* `step:p-wlog-c-nonneg` [PROPOSED] — Reduction to c >= 0 for the density construction
* `step:p0-c0-r-star-zero` [PROPOSED] — For c=0, r_*=0 so that p = k p_0
* `step:polar-W-law` [PROPOSED] — (W,W~) has the law of (B,B~)
* `step:polar-derivative-sde` [PROPOSED] — SDE for log|f_t'(z)| and its sigma-time version
* `step:polar-ito-log` [PROPOSED] — Ito computation of d log f_t(z)
* `step:polar-real-imag` [PROPOSED] — Real and imaginary parts: SDEs for log|f_t| and theta_t in capacity time
* `step:polar-time-change` [PROPOSED] — Time change by sigma: definition of W, W~ and the sigma-time SDEs
* `step:pos-choose-C-x-y` [PROPOSED] — Choice of C>=1 on the event of Lemma 4.6 and of x=2C, y=7C
* `step:pos-imag-part-bound` [PROPOSED] — Im f_t(z)<=-1 on [1,2] and hence rho_z>=2 for z in [x,y]
* `step:pos-real-part-lower-bound` [PROPOSED] — Re f_t(z)>=C on [0,1] for z in [x,y] and hence rho_z>=1
* `step:pos-real-part-sign-change` [PROPOSED] — -6C<=Re f_2(z)-Re z<=-3C so Re f_2(x)<=-C<0<C<=Re f_2(y)
* `step:pos-segment-disjoint-L2` [PROPOSED] — [x,y] is disjoint from L_2
* `step:prop-i-a-not-to-minus-infinity` [PROPOSED] — (I) >= 0 implies log|f^_t(zz)| does not tend to -infinity
* `step:prop-i-apply-stationary-sde` [PROPOSED] — Apply Lemma 3.4 with Y = log|f^(zz)|, m = 2, X = e^{2 i theta^(zz)}
* `step:prop-i-b-ode-comparison` [PROPOSED] — ODE comparison: F'(t) e^{-alpha F(t)} > 1 forces T_zz < infinity
* `step:prop-ii-a-capacity-time` [PROPOSED] — lim_{t->T_zz^-} |f_t'(zz)|/|f_t(zz)| = infinity
* `step:prop-ii-a-koebe-limit` [PROPOSED] — dist(zz,L_t) -> 0 as t -> T_zz
* `step:prop-ii-b-compactness` [PROPOSED] — Uniform lower bound q >= q_* > 0 on the unit circle and on C\{0}
* `step:prop-ii-b-conditional-lower-bound` [PROPOSED] — P(lim dist > 0 | F_{sigma_z(t^)}) >= q_* for all t^
* `step:prop-ii-b-hit-lambda-prime` [PROPOSED] — P(tau < infinity) > 0 for the first entry time tau into a closed positive-measure subset Lambda'
* `step:prop-ii-b-koebe-ball` [PROPOSED] — Koebe distortion: lim dist(z,L_t) >= r implies the ball B_{r/16}(z) is absorbed at T_z
* `step:prop-ii-b-lambda-full` [PROPOSED] — Lambda is the whole unit circle
* `step:prop-ii-b-lambda-positive-measure` [PROPOSED] — Lambda = {|z|=1 : q(z) > 0} has positive Lebesgue measure
* `step:prop-ii-b-markov-transfer` [PROPOSED] — Conditional probability at sigma_z(tau) equals q(e^{i theta^_tau(z)})
* `step:prop-ii-b-martingale-zero-one` [PROPOSED] — Martingale convergence upgrades to a.s. lim dist(z,L_t) > 0
* `step:prop-ii-b-scale-reduction` [PROPOSED] — q(z) = q(z/|z|)
* `step:re-im-drift-bound` [PROPOSED] — Drift of Re/Im f_t(z) is bounded by 2 in absolute value while |f_t(z)|>=1
* `step:re-im-ft-sde` [PROPOSED] — Real and imaginary parts of f_t(z) satisfy a pair of SDEs
* `step:rec-angle-hit-unif` [PROPOSED] — Uniform hitting estimate (2.45)
* `step:rec-hit-fixed-y` [PROPOSED] — Positive probability of hitting x in finite theta-time from each y in (x,x+pi)
* `step:rec-monotone-in-y` [PROPOSED] — Hitting probability within time T is non-increasing in y; uniform bound
* `step:rec-reduction-to-x` [PROPOSED] — Reduction to hitting e^{2ix} for a single x
* `step:rec-renewal` [PROPOSED] — Renewal times tau_k^eps: conditional hitting probability >= delta per window gives infinitely many hits
* `step:rec-scale-function-hit` [PROPOSED] — Scale-function argument: with positive probability R<infinity and X_R = x
* `step:rec-tau-finite` [PROPOSED] — A.s. exists eps with tau_k^eps<infty for all k
* `step:rec-time-change-omega` [PROPOSED] — Time change omega(r) with r = 2 int_0^omega D: X_r satisfies dX = mu/(2D) dr + dZ
* `step:recurrent-durrett-adaptation` [PROPOSED] — Adaptation of Durrett Thm 7.3.2 to real-valued sequences with E(xi_1|I)=0
* `step:reverse-via-mult-by-i` [PROPOSED] — Part (b): reverse chain by combining part (a) with rotation
* `step:sde-birkhoff-limit` [PROPOSED] — Birkhoff: Y_t/t -> E(Y_1-Y_0 | I)
* `step:sde-continuity-noninteger` [PROPOSED] — Continuity argument for non-integer times
* `step:sde-limit-deterministic` [PROPOSED] — lim Y_t/t is a.s. a deterministic constant
* `step:sde-mean-zero` [PROPOSED] — Mean-zero stochastic integrals and E(Y_1-Y_0) = E f^0(X_0)
* `step:sde-recurrence-zero` [PROPOSED] — Recurrence of Y near 0 when E f^0(X_0) = 0
* `step:sde-regeneration` [PROPOSED] — Post-tau_k increments of Y are independent of B up to tau_k
* `step:sde-stationary-increments` [PROPOSED] — Y has stationary increments
* `step:sigma-bounded-coefficients` [PROPOSED] — Bounded coefficients keep |hat f| and |hat f'| away from 0 and infinity on compacts
* `step:stat-apply-kolmogorov-critical` [PROPOSED] — Lemma A.1 applied in the critical case c = +-sqrt(ab)
* `step:stat-apply-kolmogorov-noncritical` [PROPOSED] — Lemma A.1 applied in the nondegenerate case |c| != sqrt(ab)
* `step:stat-kolmogorov-normalization` [PROPOSED] — Apply Lemma A.1 to 2p (normalization int_0^pi = 1 and alpha = mu, beta^2 = 2D)
* `step:stat-martingale-qv` [PROPOSED] — Martingale part of the theta-SDE has quadratic variation 2D and is sqrt(2D) dW'
* `step:stat-pi-reduction` [PROPOSED] — Stationarity of e^{2i theta} implies stationarity of e^{i theta}
* `step:stat-theta-bm-sde` [PROPOSED] — One-noise SDE for the sigma-time argument process
* `step:stationary-sde-X-form` [PROPOSED] — The SDEs for X = e^{2 i theta^(zz)} and Y have the form required by Lemma 3.4
* `step:swallow-time-change` [PROPOSED] — Capacity-time limit to sigma-time limit
* `step:wlog-c-nonneg` [PROPOSED] — WLOG c >= 0 by conjugation
* `step:zero-in-left-hull` [PROPOSED] — 0 belongs to every left hull (and to the future hulls L_{t,s+t})
* `step:zero-in-right-hull` [PROPOSED] — 0 belongs to every right hull R_t
* `thm-disconnects#proof-a` [PROPOSED] — Proof assembly of Theorem 1.10(a) from Lemma 4.1
* `thm-disconnects#proof-b` [PROPOSED] — Proof assembly of Theorem 1.10(b) from Lemma 4.1
* `thm-disconnects.a` [PROPOSED] — SLE_Sigma disconnects points: (a)
* `thm-disconnects.b` [PROPOSED] — SLE_Sigma disconnects points: (b)
* `thm-phases` [PROPOSED] — Phases of SLE_Sigma
* `thm-phases#assembly-c-zero` [PROPOSED] — Thm 1.8 proof: c = 0 phases from Lemmas 3.11 and 3.12
* `thm-phases#assembly-sign-cases` [PROPOSED] — Thm 1.8 proof: Props 3.1/3.2 give the four sign-case phases
* `thm-phases.c-zero` [PROPOSED] — Phases of SLE_Sigma when c = 0

### Dependency leaves in root closure

* `def-disconnect` [PROPOSED] — S disconnects S' from infinity
* `defn-chordal-loewner` [PROPOSED] — Chordal Loewner chains (forward and reverse)
* `defn-loewner.solution` [PROPOSED] — Loewner initial value problem (solution predicate)
* `defn-sle.gaussian-law` [PROPOSED] — Centered Gaussian law on C = R^2
* `eqn-computation-tilde-f` [PROPOSED] — Rescaled future chain f~_u (3.3)
* `eqn-cov-matrix` [PROPOSED] — Covariance matrix Sigma
* `eqn-dist-event` [PROPOSED] — Definition of the event E_s^ (3.12)
* `eqn-nu-D.D` [PROPOSED] — Diffusion coefficient D(u)
* `eqn-nu-D.mu` [PROPOSED] — Drift mu(u)
* `eqn-nu-D.nu` [PROPOSED] — Log-drift nu(u)
* `ext:birkhoff` [PROPOSED] — Birkhoff ergodic theorem
* `ext:blumenthal` [PROPOSED] — Blumenthal zero-one law: germ sigma-field of Brownian motion is trivial
* `ext:bm-existence` [PROPOSED] — Existence of planar Brownian motion with covariance Sigma
* `ext:bm-support` [PROPOSED] — Support theorem: a Brownian motion stays uniformly within delta of a given admissible continuous path on [0,T] with positive probability
* `ext:dct` [PROPOSED] — Dominated convergence
* `ext:durrett-7.3.2` [PROPOSED] — Durrett Theorem 7.3.2 (recurrence of Z-valued stationary sequences)
* `ext:girsanov` [PROPOSED] — Girsanov theorem
* `ext:hormander-1d` [PROPOSED] — Hormander criterion, one-dimensional case
* `ext:ito-complex` [PROPOSED] — Ito formula for complex semimartingales
* `ext:koebe-distortion` [PROPOSED] — Koebe distortion estimate (Lawler Corollary 3.23)
* `ext:koebe-quarter` [PROPOSED] — Koebe quarter theorem (Lawler Corollary 3.18)
* `ext:kolmogorov-zero-one` [PROPOSED] — Kolmogorov zero-one law (tail sigma-algebra of BM is trivial)
* `ext:lawler-4.5` [PROPOSED] — Lawler Theorem 4.5: g_t is conformal onto H minus hull; z(g_t-z) -> 2t
* `ext:levy-characterization` [PROPOSED] — Levy characterization / Dambis-Dubins-Schwarz
* `ext:loewner-convergence` [PROPOSED] — Lawler Prop 4.43: locally uniform convergence of driving functions gives locally uniform convergence of Loewner maps away from the hull
* `ext:martingale-convergence` [PROPOSED] — Levy upward martingale convergence (conditional Borel-Cantelli)
* `ext:picard-lindelof` [PROPOSED] — Picard-Lindelof ODE existence and uniqueness
* `ext:scale-function` [PROPOSED] — Scale-function hitting lemma
* `ext:strong-markov-bm` [PROPOSED] — Strong Markov property of Brownian motion
* `step:horm-stratonovich` [PROPOSED] — Stratonovich form of the SDE
* `step:kol-shift-start` [PROPOSED] — Starting distribution may be taken on [x,x+pi]
* `step:sde-continuity-noninteger` [PROPOSED] — Continuity argument for non-integer times
* `step:sde-mean-zero` [PROPOSED] — Mean-zero stochastic integrals and E(Y_1-Y_0) = E f^0(X_0)
* `step:sde-stationary-increments` [PROPOSED] — Y has stationary increments

### Assumption boundary leaves

* _(none)_

### External boundary leaves

* `ext:birkhoff` [PROPOSED] — Birkhoff ergodic theorem
* `ext:blumenthal` [PROPOSED] — Blumenthal zero-one law: germ sigma-field of Brownian motion is trivial
* `ext:bm-existence` [PROPOSED] — Existence of planar Brownian motion with covariance Sigma
* `ext:bm-support` [PROPOSED] — Support theorem: a Brownian motion stays uniformly within delta of a given admissible continuous path on [0,T] with positive probability
* `ext:dct` [PROPOSED] — Dominated convergence
* `ext:durrett-7.3.2` [PROPOSED] — Durrett Theorem 7.3.2 (recurrence of Z-valued stationary sequences)
* `ext:girsanov` [PROPOSED] — Girsanov theorem
* `ext:hormander-1d` [PROPOSED] — Hormander criterion, one-dimensional case
* `ext:ito-complex` [PROPOSED] — Ito formula for complex semimartingales
* `ext:koebe-distortion` [PROPOSED] — Koebe distortion estimate (Lawler Corollary 3.23)
* `ext:koebe-quarter` [PROPOSED] — Koebe quarter theorem (Lawler Corollary 3.18)
* `ext:kolmogorov-zero-one` [PROPOSED] — Kolmogorov zero-one law (tail sigma-algebra of BM is trivial)
* `ext:lawler-4.5` [PROPOSED] — Lawler Theorem 4.5: g_t is conformal onto H minus hull; z(g_t-z) -> 2t
* `ext:levy-characterization` [PROPOSED] — Levy characterization / Dambis-Dubins-Schwarz
* `ext:loewner-convergence` [PROPOSED] — Lawler Prop 4.43: locally uniform convergence of driving functions gives locally uniform convergence of Loewner maps away from the hull
* `ext:martingale-convergence` [PROPOSED] — Levy upward martingale convergence (conditional Borel-Cantelli)
* `ext:picard-lindelof` [PROPOSED] — Picard-Lindelof ODE existence and uniqueness
* `ext:scale-function` [PROPOSED] — Scale-function hitting lemma
* `ext:strong-markov-bm` [PROPOSED] — Strong Markov property of Brownian motion

### Uncovered graph nodes

* _(none)_

### Nodes outside every root closure

* _(none)_

### Explicit source gaps

* `claim:gt-conformal` [PROPOSED] — g_t is conformal from C\L_t onto C\(R_t+U_t); z(g_t(z)-z) -> 2t
* `claim:hull-nonempty` [PROPOSED] — L_t contains the starting point U_0
* `lem-disconnect-2` [PROPOSED] — Left hulls disconnect a fixed open set with positive probability
* `lem-hormander` [PROPOSED] — Smooth density and smooth semigroup for the periodic SDE
* `remark-sigma` [PROPOSED] — sigma_z is defined on all of (0,infty) and maps it onto (0,T_z)
* `step:all-z-apply-Tz` [PROPOSED] — Lemma 3.3 hypotheses hold for {T_z < infinity} (and its complement)
* `step:all-z-apply-dist` [PROPOSED] — Lemma 3.3 hypotheses hold for {lim_{t->T_z} dist(z,L_t) = 0}
* `step:all-z-null-set-density` [PROPOSED] — An admissible p vanishes only on a Lebesgue-null set
* `step:all-z-stopping-time-choice` [PROPOSED] — Choice of tau with e^{i theta_tau(z)} in Lambda with probability >= q
* `step:arg-lift` [PROPOSED] — Existence and uniqueness of the continuous argument lift
* `step:c0-bdy-finite-time` [PROPOSED] — T_z < infinity when c = 0 and a - b = 8
* `step:converse-event-converges` [PROPOSED] — 1_{E_s^} -> 1 as s^ -> infinity (under the contrapositive hypothesis)
* `step:disc-E1-positive` [PROPOSED] — P(E_1)>0 for every T, eps>0
* `step:disc-E2E3-positive` [PROPOSED] — P(E_2 cap E_3)>0 for some eps,K and any T (Lemma 4.4 applied to the restarted chain)
* `step:disc-a-markov-restart` [PROPOSED] — Conditional probability given F at sigma_z(tau) is at least q(e^{i theta^_tau(z)})
* `step:disc-a-positive-measure-set` [PROPOSED] — The set of unit z with q(z)>0 has positive 1-d Lebesgue measure
* `step:disc-setup` [PROPOSED] — Choice of parameters T, eps, K, the sets U^{+-} and the four events E_1..E_4
* `step:disc-topological-separation` [PROPOSED] — L_{T,T+2+K} cup R_T disconnects one of f_T(U^+-) from infinity without hitting it
* `step:forward-real-driver` [PROPOSED] — Real driver: complex chain extends the forward chordal chain by Schwarz reflection
* `step:haus-contradiction-L-t` [PROPOSED] — g_t cannot extend conformally to a set V meeting L_t
* `step:haus-maps-converge` [PROPOSED] — Convergence of forward (and reverse) Loewner maps from convergence of drivers
* `step:haus-right-hull-reduction` [PROPOSED] — Right-hull and reverse-map versions via left hulls of reverse chains
* `step:horm-apply-hairer` [PROPOSED] — Application of the one-dimensional Hormander criterion
* `step:hulls-compact` [PROPOSED] — L_t and R_t are compact (premise of the Koebe theorems)
* `step:kol-process-stationarity` [PROPOSED] — From invariance of E_p f(X_s) for C^2 f to stationarity of the law of the process (e^{2iX_t})
* `step:line-apply-haus` [PROPOSED] — Apply Lemma 4.3 with U = 0 to deduce the Hausdorff and map bounds
* `step:loewner-glue-maximal` [PROPOSED] — Gluing: a solution exists on all of [0,T_z)
* `step:loewner-local-solution` [PROPOSED] — Local existence and uniqueness for the Loewner ODE away from U_t
* `step:p-case2` [PROPOSED] — Case 2 assembly: admissible density for c = sqrt(ab) with int_0^{2pi} p = 1
* `step:polar-derivative-sde` [PROPOSED] — SDE for log|f_t'(z)| and its sigma-time version
* `step:prop-ii-b-hit-lambda-prime` [PROPOSED] — P(tau < infinity) > 0 for the first entry time tau into a closed positive-measure subset Lambda'
* `step:prop-ii-b-koebe-ball` [PROPOSED] — Koebe distortion: lim dist(z,L_t) >= r implies the ball B_{r/16}(z) is absorbed at T_z
* `step:rec-hit-fixed-y` [PROPOSED] — Positive probability of hitting x in finite theta-time from each y in (x,x+pi)
* `step:rec-renewal` [PROPOSED] — Renewal times tau_k^eps: conditional hitting probability >= delta per window gives infinitely many hits
* `step:recurrent-durrett-adaptation` [PROPOSED] — Adaptation of Durrett Thm 7.3.2 to real-valued sequences with E(xi_1|I)=0
* `step:sde-continuity-noninteger` [PROPOSED] — Continuity argument for non-integer times
* `step:sde-stationary-increments` [PROPOSED] — Y has stationary increments
* `step:stat-theta-bm-sde` [PROPOSED] — One-noise SDE for the sigma-time argument process
* `step:stationary-sde-X-form` [PROPOSED] — The SDEs for X = e^{2 i theta^(zz)} and Y have the form required by Lemma 3.4
* `step:zero-in-right-hull` [PROPOSED] — 0 belongs to every right hull R_t
* `thm-phases#assembly-sign-cases` [PROPOSED] — Thm 1.8 proof: Props 3.1/3.2 give the four sign-case phases
<!-- END PROOF DEPGRAPH GENERATED -->
