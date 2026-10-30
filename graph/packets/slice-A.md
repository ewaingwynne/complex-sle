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
DEPS: defn-hulls.left, defn-loewner.solution
ROUTES: -
ROUTE_FOR: -
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-hulls@L272-L275 | f_t is a map on the complement of L_t whose range complement is R_t
EDGE: defn-loewner.solution | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-hulls@L272-L272 | f_t = g_t - U_t is the centered Loewner map whose range defines R_t
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
SOURCE_HYPOTHESES: p a density (admissible)
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
SOURCE_HYPOTHESES: p a density (admissible)
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
SOURCE_CONCLUSION: near any time t0 with g(t0) != U_{t0} the ODE g-dot = 2/(g-U_t) has a solution, and two solutions agree on their common interval
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: ext:picard-lindelof, defn-loewner.solution
ROUTES: -
ROUTE_FOR: -
EDGE: ext:picard-lindelof | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L674-L674 | "standard existence results for solutions to ODEs": right side is continuous in t and locally Lipschitz in g where g != U_t
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
DEPS: step:loewner-local-solution, defn-loewner.absorbing-time
ROUTES: -
ROUTE_FOR: -
EDGE: step:loewner-local-solution | source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268 | uniqueness lets solutions on shorter intervals be patched into one solution on [0,T_z)
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268 | T_z is the supremum of existence times; the supremum must be attained as an open interval
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
DEPS: defn-loewner.solution, defn-loewner.absorbing-time, step:loewner-local-solution, step:loewner-glue-maximal
ROUTES: -
ROUTE_FOR: -
EDGE: defn-loewner.solution | source/arxiv-2203.07313v4/complex-sle-final.tex#defn-loewner@L253-L256 | the statement concerns solutions of (1.1)
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268 | the solution interval is [0,T_z)
EDGE: step:loewner-local-solution | source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268 | uniqueness on common intervals and local existence
EDGE: step:loewner-glue-maximal | source/arxiv-2203.07313v4/complex-sle-final.tex#absorbing-time@L268-L268 | existence on all of [0,T_z)
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
DEPS: defn-loewner.solution, defn-sle, step:driver-representation
ROUTES: -
ROUTE_FOR: -
EDGE: defn-loewner.solution | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-def-ft@L316-L316 | f_t = g_t - U_t with g_t from the Loewner ODE gives f_t = z + int 2/f ds - (U_t - U_0)
EDGE: defn-sle | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-def-ft@L315-L315 | U is the SLE_Sigma driving BM
EDGE: step:driver-representation | source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-def-ft@L317-L317 | U written as sqrt(a) B + i sqrt(b) B~
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
STATEMENT_SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#defn-chordal-loewner@L588-L601
PROOF_SOURCE: -
CONTRACT_ID: paper.defn-chordal-loewner
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U : [0,infinity) -> R continuous
SOURCE_QUANTIFIERS: U; z in H
SOURCE_CONCLUSION: forward chain g_t(z) solves g-dot = 2/(g-U_t), reverse chain solves g-dot = -2/(g-U_t), g_0(z) = z; centered chain f_t = g_t - U_t
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
NOTE: Definition 2.1; includes displays (2.5), (2.6). The surrounding remarks about Loewner theorem are background.

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
DEPS: defn-loewner.solution, defn-chordal-loewner
ROUTES: -
ROUTE_FOR: -
EDGE: defn-loewner.solution | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-mult-by-i@L641-L641 | "immediate consequence of Definition 1.1": the rotated map solves the forward ODE for iU
EDGE: defn-chordal-loewner | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-mult-by-i@L637-L637 | reverse ODE (2.6) is the hypothesis
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
DEPS: eqn-reflect, defn-chordal-loewner, defn-hulls.right, defn-loewner.well-defined
ROUTES: -
ROUTE_FOR: -
EDGE: eqn-reflect | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L648-L648 | "first assertion is immediate from the reflection property under conjugation": U real so U* = U
EDGE: defn-chordal-loewner | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L626-L626 | forward chordal chain and its hulls
EDGE: defn-hulls.right | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L626-L626 | right hulls are subsets of the real axis
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L648-L648 | complex chain coincides with chordal chain on H by uniqueness
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
DEPS: lem-mult-by-i, step:forward-real-driver
ROUTES: -
ROUTE_FOR: -
EDGE: lem-mult-by-i | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L648-L648 | "second assertion follows from ... Lemma 2.3"
EDGE: step:forward-real-driver | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L648-L648 | combined with the first assertion
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Includes the reversal remark at L644 (forward chain for U gives reverse chain for iU).

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
DEPS: defn-hulls.left
ROUTES: -
ROUTE_FOR: -
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L659-L659 | T_{U_0} = 0 so U_0 in L_t
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
DEPS: defn-hulls.left
ROUTES: -
ROUTE_FOR: -
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662 | L_t is the complement of the domain of f_t
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
DEPS: defn-loewner.well-defined, defn-hulls.left
ROUTES: -
ROUTE_FOR: -
EDGE: defn-loewner.well-defined | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662 | f_s(w) is defined and continuous in (s,w) for w not in L_t, s <= t
EDGE: defn-hulls.left | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L662-L662 | w not in L_t means T_w > t, so f_s(w) != 0 for s <= t
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
DEPS: defn-loewner.absorbing-time, step:endpt-liminf, step:endpt-finite-upcrossings
ROUTES: -
ROUTE_FOR: -
EDGE: defn-loewner.absorbing-time | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L668-L668 | T_z is the absorbing time
EDGE: step:endpt-liminf | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L674-L675 | liminf is 0
EDGE: step:endpt-finite-upcrossings | source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L676-L690 | "it suffices": finitely many upcrossings of every [alpha,beta] with 0<alpha<beta upgrades liminf to limit
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

## Coverage

ITEM: inv:heading:L225
KIND: heading
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#heading:L225@L225-L225
DISPOSITION: EXCLUDED
REASON: structural heading, no mathematical content
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:heading:L228
KIND: heading
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#heading:L228@L228-L228
DISPOSITION: EXCLUDED
REASON: structural heading, no mathematical content
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:cite:L230:lsw-lerw-ust
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L230:lsw-lerw-ust@L230-L230
DISPOSITION: EXCLUDED
REASON: bibliographic citation in motivational/background prose; not used by any proof
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:cite:L230:schramm0
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L230:schramm0@L230-L230
DISPOSITION: EXCLUDED
REASON: bibliographic citation in motivational/background prose; not used by any proof
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:cite:L230:smirnov-cardy
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L230:smirnov-cardy@L230-L230
DISPOSITION: EXCLUDED
REASON: bibliographic citation in motivational/background prose; not used by any proof
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:cite:L230:smirnov-ising
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L230:smirnov-ising@L230-L230
DISPOSITION: EXCLUDED
REASON: bibliographic citation in motivational/background prose; not used by any proof
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:cite:L230:ss-contour
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L230:ss-contour@L230-L230
DISPOSITION: EXCLUDED
REASON: bibliographic citation in motivational/background prose; not used by any proof
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:cite:L231:ss-contour
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L231:ss-contour@L231-L231
DISPOSITION: EXCLUDED
REASON: bibliographic citation in motivational/background prose; not used by any proof
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:cite:L232:lawler-book
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L232:lawler-book@L232-L232
DISPOSITION: EXCLUDED
REASON: bibliographic citation in motivational/background prose; not used by any proof
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:cite:L240:dg-supercritical-lfpp
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L240:dg-supercritical-lfpp@L240-L240
DISPOSITION: EXCLUDED
REASON: bibliographic citation in motivational/background prose; not used by any proof
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:cite:L240:huang-complex-insertion
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L240:huang-complex-insertion@L240-L240
DISPOSITION: EXCLUDED
REASON: bibliographic citation in motivational/background prose; not used by any proof
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:cite:L240:rhodes-vargas-complex-gmt
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L240:rhodes-vargas-complex-gmt@L240-L240
DISPOSITION: EXCLUDED
REASON: bibliographic citation in motivational/background prose; not used by any proof
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:heading:L244
KIND: heading
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#heading:L244@L244-L244
DISPOSITION: EXCLUDED
REASON: structural heading, no mathematical content
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:defn-loewner
KIND: definition
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#defn-loewner@L251-L263
DISPOSITION: NODE defn-loewner.solution, defn-loewner.absorbing-time, defn-loewner.well-defined
REASON: Def 1.1 content split into the solution predicate, absorbing time and the well-definedness root
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:eqn-forward-loewner
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-forward-loewner@L255-L255
DISPOSITION: NODE defn-loewner.solution
REASON: the ODE (1.1)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:defn:L271
KIND: definition
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#defn:L271@L271-L277
DISPOSITION: NODE defn-hulls.left, defn-hulls.right
REASON: Def 1.2: left and right hulls
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:cite:L283:lu-complex-loewner
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L283:lu-complex-loewner@L283-L283
DISPOSITION: EXCLUDED
REASON: citation for a remark about complements of hulls not being connected; background (consumed fact is Thm 1.10 itself)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:cite:L286:lawler-book
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L286:lawler-book@L286-L286
DISPOSITION: NODE ext:lawler-4.5, claim:gt-conformal
REASON: cited analogy for conformality of g_t (SOURCE_GAP)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:cite:L292:rs-complex-sle
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L292:rs-complex-sle@L292-L292
DISPOSITION: EXCLUDED
REASON: bibliographic citation in motivational/background prose; not used by any proof
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:cite:L293:bcd-evolution-families1
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L293:bcd-evolution-families1@L293-L293
DISPOSITION: EXCLUDED
REASON: bibliographic citation in motivational/background prose; not used by any proof
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:cite:L293:tran-complex-loewner
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L293:tran-complex-loewner@L293-L293
DISPOSITION: EXCLUDED
REASON: bibliographic citation in motivational/background prose; not used by any proof
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:remark-radial
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#remark-radial@L295-L297
DISPOSITION: EXCLUDED
REASON: Remark 1.3 excluded by spec Section 7 (R2)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:defn-sle
KIND: definition
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#defn-sle@L301-L308
DISPOSITION: NODE defn-sle, defn-sle.gaussian-law, step:driver-representation, nonsource.exists-sle-driver
REASON: Def 1.4 with R6 driver reading, representation as step, and non-source existence root
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:eqn-cov-matrix
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-cov-matrix@L304-L304
DISPOSITION: NODE eqn-cov-matrix
REASON: covariance matrix definition
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:eqn-def-gt
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-def-gt@L312-L312
DISPOSITION: NODE step:driver-representation
REASON: restatement of the Loewner ODE with the explicit representation U = sqrt(a)B + i sqrt(b)B~
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:eqn-def-ft
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-def-ft@L318-L318
DISPOSITION: NODE eqn-def-ft
REASON: SDE for f_t
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:prop-duality
KIND: proposition
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#prop-duality@L329-L335
DISPOSITION: EXCLUDED
REASON: Prop 1.5 feeds no root (not consumed by any root proof; checked references outside slice A)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:remark-duality
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#remark-duality@L341-L359
DISPOSITION: EXCLUDED
REASON: Remark 1.6 excluded by spec Section 7
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:eqn-sle-kappa-def
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-sle-kappa-def@L345-L345
DISPOSITION: EXCLUDED
REASON: inside Remark 1.6 (excluded)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:eqn-cc
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-cc@L352-L352
DISPOSITION: EXCLUDED
REASON: inside Remark 1.6 (excluded)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:cite:L358:dg-supercritical-lfpp
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L358:dg-supercritical-lfpp@L358-L358
DISPOSITION: EXCLUDED
REASON: bibliographic citation in motivational/background prose; not used by any proof
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:heading:L403
KIND: heading
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#heading:L403@L403-L403
DISPOSITION: EXCLUDED
REASON: structural heading, no mathematical content
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:cite:L406:schramm-sle
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L406:schramm-sle@L406-L406
DISPOSITION: EXCLUDED
REASON: bibliographic citation in motivational/background prose; not used by any proof
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:defn-phases
KIND: definition
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#defn-phases@L409-L417
DISPOSITION: NODE defn-phases.thin, defn-phases.swallowing, defn-phases.hitting, defn-phases.dense
REASON: Def 1.7 four phases
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:eqn-nu-D
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-nu-D@L423-L423
DISPOSITION: NODE eqn-nu-D.mu, eqn-nu-D.nu, eqn-nu-D.D
REASON: (1.10) definitions of mu, nu, D
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:eqn-p-ode
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-p-ode@L431-L431
DISPOSITION: NODE thm-phases
REASON: ODE (1.11) is the defining condition of p in the statement of Thm 1.8; its formal content is admissibility (node lem-stationary.admissible, slice B, a DEPS of thm-phases)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:item-I.2
KIND: theorem
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#item-I.2@L437-L453
DISPOSITION: NODE thm-phases, thm-phases.c-zero
REASON: Theorem 1.8 split by R17 into general and c = 0 roots
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:item-I
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#item-I@L440-L440
DISPOSITION: NODE item-I
REASON: integral (I)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:item-II
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#item-II@L441-L441
DISPOSITION: NODE item-II
REASON: integral (II)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:cite:L477:rs-complex-sle
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L477:rs-complex-sle@L477-L477
DISPOSITION: EXCLUDED
REASON: bibliographic citation in motivational/background prose; not used by any proof
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:def-disconnect
KIND: definition
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#def-disconnect@L497-L499
DISPOSITION: NODE def-disconnect
REASON: Def 1.9
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:thm-disconnects
KIND: theorem
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#thm-disconnects@L502-L511
DISPOSITION: NODE thm-disconnects.a, thm-disconnects.b
REASON: Theorem 1.10 split by R17
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:item-disconnect-z
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#item-disconnect-z@L506-L506
DISPOSITION: NODE thm-disconnects.a
REASON: Thm 1.10(a)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:item-disconnect-t
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#item-disconnect-t@L508-L508
DISPOSITION: NODE thm-disconnects.b
REASON: Thm 1.10(b)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:cite:L514:lu-complex-loewner
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L514:lu-complex-loewner@L514-L514
DISPOSITION: EXCLUDED
REASON: bibliographic citation in motivational/background prose; not used by any proof
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:remark-curve
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#remark-curve@L516-L524
DISPOSITION: EXCLUDED
REASON: Remark 1.11 excluded by spec Section 7
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:cite:L517:schramm-sle
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L517:schramm-sle@L517-L517
DISPOSITION: EXCLUDED
REASON: bibliographic citation in motivational/background prose; not used by any proof
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:cite:L521:schramm-sle
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L521:schramm-sle@L521-L521
DISPOSITION: EXCLUDED
REASON: bibliographic citation in motivational/background prose; not used by any proof
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:heading:L529
KIND: heading
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#heading:L529@L529-L529
DISPOSITION: EXCLUDED
REASON: structural heading, no mathematical content
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:heading:L540
KIND: heading
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#heading:L540@L540-L540
DISPOSITION: EXCLUDED
REASON: structural heading, no mathematical content
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:heading:L543
KIND: heading
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#heading:L543@L543-L543
DISPOSITION: EXCLUDED
REASON: structural heading, no mathematical content
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:cite:L547:lu-complex-loewner
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L547:lu-complex-loewner@L547-L547
DISPOSITION: NODE eqn-scale, eqn-reflect, eqn-conc
REASON: proofs of (2.1)-(2.3) are delegated to Lu Sect. 2 (recorded in node NOTEs; no external node)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:eqn-scale
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-scale@L551-L551
DISPOSITION: NODE eqn-scale.left, eqn-scale
REASON: scaling property: left-hull root and full statement
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:eqn-reflect
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-reflect@L555-L555
DISPOSITION: NODE eqn-reflect.left, eqn-reflect
REASON: reflection property: left-hull root and full statement
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:eqn-conc
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-conc@L560-L560
DISPOSITION: NODE eqn-conc
REASON: concatenation property
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:eqn-duality
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-duality@L568-L568
DISPOSITION: EXCLUDED
REASON: (2.4) duality: feeds no root (used only by Prop 1.5, Lemma 2.4 right-hull part and the simulation section, all excluded)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:heading:L582
KIND: heading
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#heading:L582@L582-L582
DISPOSITION: EXCLUDED
REASON: structural heading, no mathematical content
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:defn-chordal-loewner
KIND: definition
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#defn-chordal-loewner@L588-L601
DISPOSITION: NODE defn-chordal-loewner
REASON: Def 2.1
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:eqn-chordal-loewner
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-chordal-loewner@L592-L592
DISPOSITION: NODE defn-chordal-loewner
REASON: forward chordal ODE (2.5) part of Def 2.1
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:eqn-reverse-loewner
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-reverse-loewner@L597-L597
DISPOSITION: NODE defn-chordal-loewner
REASON: reverse chordal ODE (2.6) part of Def 2.1
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:lem-forward-reverse-ext
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-forward-reverse-ext@L620-L630
DISPOSITION: NODE lem-forward-reverse-ext
REASON: Lemma 2.2
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:lem-mult-by-i
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-mult-by-i@L635-L639
DISPOSITION: NODE lem-mult-by-i
REASON: Lemma 2.3
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:proof:L640
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L640@L640-L642
DISPOSITION: NODE lem-mult-by-i
REASON: proof of Lemma 2.3 (one line, from Def 1.1)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:proof:L647
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L647@L647-L649
DISPOSITION: NODE step:forward-real-driver, step:reverse-via-mult-by-i, lem-forward-reverse-ext
REASON: proof of Lemma 2.2
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:cite:L648:lu-complex-loewner
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L648:lu-complex-loewner@L648-L648
DISPOSITION: NODE step:forward-real-driver
REASON: the cited fact delegated to Lu Sect. 2 is the Schwarz-reflection identification; recorded in the step NOTE (SOURCE_GAP)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:heading:L654
KIND: heading
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#heading:L654@L654-L654
DISPOSITION: EXCLUDED
REASON: structural heading, no mathematical content
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:lem-connected
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-connected@L658-L660
DISPOSITION: NODE lem-connected.left, claim:hull-nonempty
REASON: Lemma 2.4 left-hull part (root); right-hull part excluded (feeds no root)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:proof:L661
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L661@L661-L663
DISPOSITION: NODE step:connected-loop-criterion, step:connected-homotopy, step:connected-region-misses-hull, lem-connected.left
REASON: proof of Lemma 2.4 (left hull part; the final duality sentence for R_t is not consumed)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:lem-endpt-cont
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-endpt-cont@L667-L672
DISPOSITION: NODE lem-endpt-cont
REASON: Lemma 2.5
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:proof:L673
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L673@L673-L691
DISPOSITION: NODE step:endpt-liminf, step:endpt-upcrossing-bound, step:endpt-finite-upcrossings, lem-endpt-cont
REASON: proof of Lemma 2.5
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:eqn-endpt-cont-bd
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-endpt-cont-bd@L681-L681
DISPOSITION: NODE step:endpt-upcrossing-bound
REASON: display (2.7), the upcrossing estimate
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:heading:L696
KIND: heading
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#heading:L696@L696-L696
DISPOSITION: EXCLUDED
REASON: structural heading, no mathematical content
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:lem-cut-glue
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-cut-glue@L712-L719
DISPOSITION: EXCLUDED
REASON: Lemma 2.6 deferred (R2)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:eqn-cut-glue
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-cut-glue@L716-L716
DISPOSITION: EXCLUDED
REASON: inside Lemma 2.6 (R2)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:cite:L722:tran-complex-loewner
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L722:tran-complex-loewner@L722-L722
DISPOSITION: EXCLUDED
REASON: inside Lemma 2.6 proof (R2)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:cite:L723:pom-book
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#cite:L723:pom-book@L723-L723
DISPOSITION: EXCLUDED
REASON: inside Lemma 2.6 proof (R2)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:proof:L730
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L730@L730-L761
DISPOSITION: EXCLUDED
REASON: proof of Lemma 2.6 (R2)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:eqn-simple-conc
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-simple-conc@L733-L733
DISPOSITION: EXCLUDED
REASON: inside Lemma 2.6 proof (R2)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:eqn-simple-tip
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-simple-tip@L738-L738
DISPOSITION: EXCLUDED
REASON: inside Lemma 2.6 proof (R2)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:eqn-simple-lim
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-simple-lim@L742-L742
DISPOSITION: EXCLUDED
REASON: inside Lemma 2.6 proof (R2)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:eqn-simple-increment
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-simple-increment@L747-L747
DISPOSITION: EXCLUDED
REASON: inside Lemma 2.6 proof (R2)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:heading:L768
KIND: heading
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#heading:L768@L768-L768
DISPOSITION: EXCLUDED
REASON: structural heading, no mathematical content
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:lem-scaling
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-scaling@L774-L776
DISPOSITION: NODE lem-scaling
REASON: Lemma 2.7
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:proof:L778
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L778@L778-L780
DISPOSITION: NODE step:bm-scaling, lem-scaling
REASON: proof of Lemma 2.7
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:lem-markov
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-markov@L782-L785
DISPOSITION: NODE lem-markov
REASON: Lemma 2.8
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:proof:L787
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L787@L787-L789
DISPOSITION: NODE step:markov-driver, lem-markov
REASON: proof of Lemma 2.8
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:proof:L795
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#proof:L795@L795-L797
DISPOSITION: EXCLUDED
REASON: proof of Prop 1.5 (excluded: feeds no root)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:L268:endpt-limit
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L268:endpt-limit@L268-L268
DISPOSITION: NODE lem-endpt-cont
REASON: unlabeled sentence "lim |f_t(z)| = 0" (spec Section 6); proved as Lemma 2.5
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:L284:hulls-monotone
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L284:hulls-monotone@L284-L284
DISPOSITION: NODE claim:hulls-monotone
REASON: unlabeled monotonicity of L_t (spec Section 6)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:L286:gt-conformal
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L286:gt-conformal@L286-L286
DISPOSITION: NODE claim:gt-conformal
REASON: unlabeled conformality of g_t and z(g_t - z) -> 2t (spec Section 6)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:L323:wlog-c-nonneg
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L323:wlog-c-nonneg@L323-L323
DISPOSITION: NODE step:wlog-c-nonneg
REASON: WLOG c >= 0 by conjugation (spec Section 4)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:L310:psd-equivalence
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L310:psd-equivalence@L310-L310
DISPOSITION: EXCLUDED
REASON: PSD iff a,b >= 0 and |c| <= sqrt(ab): 2x2 linear algebra below step threshold; recorded in eqn-cov-matrix NOTE
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:L459:c0-bdy-remark
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L459:c0-bdy-remark@L459-L459
DISPOSITION: EXCLUDED
REASON: commentary forward-reference to Lemma 3.12, not a claim of this slice
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:L467:sigma-heuristic
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L467:sigma-heuristic@L467-L473
DISPOSITION: EXCLUDED
REASON: heuristic proof sketch of Thm 1.8 (no new claim; content appears in slice B/C nodes)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -

ITEM: inv:L604:loewner-theorem
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#L604:loewner-theorem@L603-L607
DISPOSITION: EXCLUDED
REASON: background recollection of Loewner theorem for real drivers (not consumed by any node of the graph)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-A/sonnet
REVIEWER: -


## Report

- Source ranges read: paper.tex L225-L804 in full; read-only L1930-L1932 and L2199-L2225 (proofs of Thm 1.8 / 1.10), L2013, and a grep of every reference to slice-A labels in L805-L2406. Also ERRATA.md, graph/EXTRACTION_SPEC.md, graph/INVENTORY.md (slice A), graph/anchor-table.md, the statement parts of the frozen files of the anchors I own, and the skill packet/template docs.
- Counts: 57 nodes, 128 EDGE lines. Of the nodes, 25 are frozen anchors (16 definitions; 9 theorem roots: defn-loewner.well-defined, nonsource.exists-sle-driver, thm-phases, thm-phases.c-zero, thm-disconnects.a, thm-disconnects.b, lem-connected.left, eqn-scale.left, eqn-reflect.left). The other 32 are ordinary: 2 definitions (defn-hulls.right, defn-chordal-loewner), 5 lemmas, 4 displays, 3 claims, 14 steps, 4 externals. Coverage: 95 ITEM records (87 inventory items plus 8 added unlabeled items): 43 mapped to nodes, 52 excluded.
- Cross-slice edges (canonical IDs I do not own): lem-stationary.admissible (B) from thm-phases; prop-i.a, prop-i.b, prop-ii.a, prop-ii.b (C) from thm-phases and thm-phases.c-zero; lem-c0-phases, lem-c0-bdy (C) from thm-phases.c-zero; thm-disconnects#proof-a and thm-disconnects#proof-b (D) from thm-disconnects.a and .b respectively.
- Alternate routes: none (no route nodes).
- SOURCE_GAP nodes: step:loewner-local-solution and step:loewner-glue-maximal (existence/uniqueness of the Loewner IVP is not proved, L268); claim:gt-conformal (L286, by analogy to Lawler Thm 4.5); step:connected-region-misses-hull (T5 sketch); claim:hull-nonempty (nonemptiness not stated in source); step:forward-real-driver (Schwarz-reflection identification delegated to Lu Sect. 2). Properties (2.1)-(2.3) have no proof in the source (cited to Lu Sect. 2); this is noted in NOTE fields, with no external node.
- New ext: IDs: none. Externals first cited here, all using canonical IDs: ext:picard-lindelof, ext:lawler-4.5, ext:strong-markov-bm, ext:bm-existence.
- Exclusions: Prop 1.5 (prop-duality) with its proof, (2.4) eqn-duality, Remarks 1.3/1.6/1.11, Lemma 2.6 with its displays and proof, headings, citations. prop-duality and eqn-duality are in the spec's canonical A list, but no root proof consumes them (only L828 in the excluded simulation section), so I created no nodes. lem-forward-reverse-ext is kept because Lemma 4.3 (L2013) uses it.
- Uncertainty list: (1) defn-hulls.right and the full eqn-scale/eqn-reflect/eqn-conc nodes feed roots only through slice C/D consumers (eqn-conc cited at L1298, L1483, L1668, L1975); the orchestrator should confirm those slices cite them. (2) eqn-nu-D.mu and eqn-nu-D.D are consumed by no node in my slice; they need slice B's lem-stationary.admissible to depend on them, otherwise they are unconsumed anchors. (3) The claim:gt-conformal dependency of step:connected-region-misses-hull is my reading of the T5 sketch. (4) Lemma 2.4 says the loop "does not surround the origin"; it may mean U_0. (5) L286 "lim_{t->infinity} z(g_t(z)-z) = 2t" is read as z -> infinity. (6) lem-markov's filtration is "associated to B_t" in the source; read as the natural filtration of U. (7) thm-disconnects.a/.b depend only on the Section 4 proof-assembly IDs, not on Lemmas 4.x directly. (8) step:driver-representation needs a, b > 0 (R5), while Def 1.4 and eqn-def-ft are stated for a, b >= 0. (9) nonsource.exists-sle-driver has PROOF_SOURCE external:standard#brownian-motion-existence and no paper lines. (10) inv:item-I.2 (Theorem 1.8) is mapped to both thm-phases and thm-phases.c-zero.
- Confirmations: no Lean evidence was sought (I read only the statement parts of the frozen declaration files for anchors I own, to copy identity fields), no anchor ABI was edited or inferred, no Lean was run, and no file other than graph/packets/slice-A.md was written (generator scripts are in the session scratchpad).
