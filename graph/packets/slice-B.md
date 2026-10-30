# Slice B extraction packet

## Nodes

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

## Coverage

ITEM: inv:heading:L805
KIND: heading
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#sec-sim@L805-L805
DISPOSITION: EXCLUDED
REASON: Section 2.4 simulations (L805-830) excluded by R2 / spec section 7; feeds no root
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:cite:L808:kennedy-sle-sim
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#sec-sim@L808-L808
DISPOSITION: EXCLUDED
REASON: Section 2.4 simulations (L805-830) excluded by R2 / spec section 7; feeds no root
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-sim-map
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-sim-map@L815-L815
DISPOSITION: EXCLUDED
REASON: Section 2.4 simulations (L805-830) excluded by R2 / spec section 7; feeds no root
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-sim-driving
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-sim-driving@L819-L819
DISPOSITION: EXCLUDED
REASON: Section 2.4 simulations (L805-830) excluded by R2 / spec section 7; feeds no root
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-sim-set
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-sim-set@L825-L825
DISPOSITION: EXCLUDED
REASON: Section 2.4 simulations (L805-830) excluded by R2 / spec section 7; feeds no root
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:heading:L831
KIND: heading
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#sec-polar@L831-L831
DISPOSITION: EXCLUDED
REASON: section heading; no mathematical claim
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:defn-sigma
KIND: definition
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#defn-sigma@L836-L844
DISPOSITION: NODE defn-sigma
REASON: Definition 2.9
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-defn-sigma
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-defn-sigma@L841-L841
DISPOSITION: NODE defn-sigma
REASON: defining display of sigma
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:def-arg
KIND: definition
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#def-arg@L851-L853
DISPOSITION: NODE def-arg, step:arg-lift
REASON: Definition 2.10 plus its well-definedness (SOURCE_GAP step)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:lem-polar
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar@L856-L890
DISPOSITION: NODE lem-polar
REASON: Lemma 2.11
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-def-mu
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-def-mu@L860-L860
DISPOSITION: NODE lem-polar, eqn-nu-D.mu, eqn-nu-D.nu
REASON: mu, nu: restated from (1.10); canonical anchors owned by slice A are consumed here
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-theta-t
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-theta-t@L873-L873
DISPOSITION: NODE lem-polar, step:polar-time-change
REASON: (2.25), part of the statement of lem-polar
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-abs-zt
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-abs-zt@L877-L877
DISPOSITION: NODE lem-polar, step:polar-time-change
REASON: (2.26)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-abs-zt-prime
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-abs-zt'@L882-L882
DISPOSITION: NODE lem-polar, step:polar-derivative-sde
REASON: (2.27)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:remark-sigma
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#remark-sigma@L893-L896
DISPOSITION: NODE remark-sigma, step:sigma-bounded-coefficients
REASON: Remark 2.12 (sigma(infty)=T_z)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:proof:L903
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-polar-proof@L903-L929
DISPOSITION: NODE step:polar-ito-log, step:polar-real-imag, step:polar-time-change, step:polar-W-law, step:polar-derivative-sde
REASON: proof of Lemma 2.11 split into Ito, real/imaginary parts, time change, Levy characterization, derivative SDE
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:cite:L904:protter
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#protter@L904-L904
DISPOSITION: NODE ext:ito-complex
REASON: Ito formula for complex semimartingales, Protter II.35
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-abs-zt-op
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-abs-zt-op@L914-L914
DISPOSITION: NODE step:polar-real-imag
REASON: capacity-time SDE for log|f|
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-theta-t-op
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-theta-t-op@L919-L919
DISPOSITION: NODE step:polar-real-imag
REASON: capacity-time SDE for theta
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:heading:L936
KIND: heading
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#sec-stationary@L936-L936
DISPOSITION: EXCLUDED
REASON: section heading; no mathematical claim
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:lem-p
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p@L941-L955
DISPOSITION: NODE lem-p, lem-p.exists, step:p-positive-off-discrete
REASON: Lemma 2.13: statement split into the existence root, positivity off a discrete set and stationarity
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-def-D
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-def-D@L945-L945
DISPOSITION: NODE eqn-nu-D.D
REASON: D restated from (1.10); canonical anchor in slice A
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-p-ODE
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-p-ODE@L951-L951
DISPOSITION: NODE lem-stationary.admissible, lem-p
REASON: ODE (2.13) is a clause of the admissibility predicate and of the statement of lem-p
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:lem-stationary
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary@L963-L967
DISPOSITION: NODE lem-stationary, lem-stationary.admissible
REASON: Lemma 2.14 with hypotheses package as the frozen admissibility anchor
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:proof:L972
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-stationary-proof@L972-L994
DISPOSITION: NODE step:stat-martingale-qv, step:stat-theta-bm-sde, step:driver-negation-symmetry, step:stat-pi-reduction, step:stat-kolmogorov-normalization, step:D-structure, step:stat-apply-kolmogorov-noncritical, step:stat-apply-kolmogorov-critical
REASON: proof of Lemma 2.14
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-theta-t-bm
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-theta-t-bm@L981-L981
DISPOSITION: NODE step:stat-theta-bm-sde
REASON: (2.30)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-theta-t-bm-prime
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-theta-t-bm'@L989-L989
DISPOSITION: NODE step:stat-apply-kolmogorov-critical
REASON: (2.31)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:proof:L1024
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-p-proof@L1024-L1111
DISPOSITION: NODE step:p-wlog-c-nonneg, step:p-case1, step:p-case1-first-order-solutions, step:p-case1-periodic, step:p-case1-mu-over-D-integral, step:p-case1-nonneg, step:p-case1-zero-set, step:p-case2, step:p-case2-welldefined, step:p-case2-limits, step:p-case2-regularity, step:p-positive-off-discrete, step:D-structure
REASON: proof of Lemma 2.13
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-defn-p0
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-defn-p0@L1033-L1033
DISPOSITION: NODE step:p-case1-first-order-solutions
REASON: display inside the proof of Lemma 2.13
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-defn-p1
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-defn-p1@L1039-L1039
DISPOSITION: NODE step:p-case1-first-order-solutions
REASON: display inside the proof of Lemma 2.13
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-p0-p1-ODE
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-p0-p1-ODE@L1044-L1044
DISPOSITION: NODE step:p-case1-first-order-solutions
REASON: display inside the proof of Lemma 2.13
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-critical-p
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-critical-p@L1094-L1094
DISPOSITION: NODE step:p-case2-welldefined
REASON: display inside the proof of Lemma 2.13
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-critical-p-ode
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-critical-p-ode@L1099-L1099
DISPOSITION: NODE step:p-case2-welldefined
REASON: display inside the proof of Lemma 2.13
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-lhop-down
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-lhop-down@L1103-L1103
DISPOSITION: NODE step:p-case2-limits
REASON: display inside the proof of Lemma 2.13
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-lhop-up
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-lhop-up@L1107-L1107
DISPOSITION: NODE step:p-case2-limits
REASON: display inside the proof of Lemma 2.13
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:remark-p0
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#remark-p0@L1136-L1138
DISPOSITION: NODE remark-p0, step:p0-c0-r-star-zero
REASON: Remark 2.15
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:heading:L1149
KIND: heading
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#sec-recurrence@L1149-L1149
DISPOSITION: EXCLUDED
REASON: section heading; no mathematical claim
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:lem-recurrence
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence@L1155-L1163
DISPOSITION: NODE lem-recurrence
REASON: Lemma 2.16
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:proof:L1164
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-recurrence-proof@L1164-L1230
DISPOSITION: NODE step:rec-reduction-to-x, step:rec-angle-hit-unif, step:rec-renewal, step:rec-tau-finite, step:rec-time-change-omega, step:rec-scale-function-hit, step:rec-hit-fixed-y, step:rec-monotone-in-y
REASON: proof of Lemma 2.16
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-angle-hit-unif
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-angle-hit-unif@L1168-L1168
DISPOSITION: NODE step:rec-angle-hit-unif
REASON: (2.45)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-omega-time
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-omega-time@L1193-L1193
DISPOSITION: NODE step:rec-time-change-omega
REASON: time change definition
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-omega-sde
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-omega-sde@L1201-L1201
DISPOSITION: NODE step:rec-time-change-omega
REASON: SDE for X_r
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:cite:L1210:lawler-book
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lawler-book@L1210-L1210
DISPOSITION: NODE ext:scale-function
REASON: Lawler Lemma 1.24
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:cite:L1223:lawler-book
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lawler-book@L1223-L1223
DISPOSITION: NODE ext:scale-function
REASON: Lawler Lemma 1.24, second invocation
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-angle-hit-fixed
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-angle-hit-fixed@L1226-L1226
DISPOSITION: NODE step:rec-hit-fixed-y
REASON: fixed-y hitting probability
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:heading:L2314
KIND: heading
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#sec-kolmogorov@L2314-L2314
DISPOSITION: EXCLUDED
REASON: appendix section heading; no mathematical claim
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:lem-kolmogorov
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov@L2318-L2334
DISPOSITION: NODE lem-kolmogorov
REASON: Lemma A.1
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-kolmogorov-sde
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-kolmogorov-sde@L2320-L2320
DISPOSITION: NODE lem-kolmogorov
REASON: SDE in the hypotheses of A.1
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-hormander-cond
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-hormander-cond@L2324-L2324
DISPOSITION: NODE lem-kolmogorov, step:horm-span-condition
REASON: Hormander-type hypothesis (A.1) of A.1 and its equivalence in A.2
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-kolmogorov
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-kolmogorov@L2329-L2329
DISPOSITION: NODE lem-kolmogorov, step:kol-integration-by-parts
REASON: ODE hypothesis (A.2) consumed in the integration by parts
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:lem-hormander
KIND: lemma
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-hormander@L2340-L2344
DISPOSITION: NODE lem-hormander
REASON: Lemma A.2
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:proof:L2345
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-hormander-proof@L2345-L2356
DISPOSITION: NODE step:horm-stratonovich, step:horm-span-condition, step:horm-apply-hairer
REASON: proof of Lemma A.2
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-stratanovich
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-stratanovich@L2347-L2347
DISPOSITION: NODE step:horm-stratonovich
REASON: Stratonovich form
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:cite:L2351:hairer-hormander
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#hairer-hormander@L2351-L2351
DISPOSITION: NODE ext:hormander-1d
REASON: Hairer Thm 1.3
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:proof:L2360
KIND: proof-region
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#lem-kolmogorov-proof@L2360-L2402
DISPOSITION: NODE step:kol-shift-start, step:kol-ito-expectation, step:kol-derivative-at-zero, step:kol-integration-by-parts, step:kol-semigroup-smooth, step:kol-markov-semigroup, step:kol-derivative-vanishes-all-times, step:kol-process-stationarity
REASON: proof of Lemma A.1
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-periodic-deriv0
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-periodic-deriv0@L2377-L2377
DISPOSITION: NODE step:kol-derivative-at-zero
REASON: (A.3)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:eqn-periodic-deriv
KIND: display
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#eqn-periodic-deriv@L2389-L2389
DISPOSITION: NODE step:kol-integration-by-parts
REASON: (A.4)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:cite:L2396:ethier-semigroups
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#ethier-semigroups@L2396-L2396
DISPOSITION: EXCLUDED
REASON: citation appears only in a %-commented sentence fragment at L2396 (not part of the paper); smoothness of T_s f is taken from lem-hormander
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:cite:L2396:gikhman-skorokhod
KIND: citation
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#gikhman-skorokhod@L2396-L2396
DISPOSITION: EXCLUDED
REASON: citation appears only in a %-commented sentence fragment at L2396 (not part of the paper); smoothness of T_s f is taken from lem-hormander
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:L847:sigma-range
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#sigma-range@L847-L847
DISPOSITION: NODE remark-sigma
REASON: unlabeled claim that sigma maps (0,infty) onto (0,T_z), justified in Remark 2.12
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:L969:regularity-preview
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#regularity-preview@L969-L970
DISPOSITION: NODE step:p-case1, step:p-case2
REASON: unlabeled claim: the constructed p is smooth if |c|<sqrt(ab) and smooth off x+piZ (x=arctan sqrt(b/a)) for c=sqrt(ab); discharged by case assemblies
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:L984:pi-reduction
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#pi-reduction@L984-L984
DISPOSITION: NODE step:stat-pi-reduction, step:driver-negation-symmetry
REASON: unlabeled claim -zz =_d zz and stationarity of e^{i theta} from e^{2i theta}; used by Lemma 2.14
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:L959:usage-remark
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#usage-remark@L959-L959
DISPOSITION: EXCLUDED
REASON: expository paragraph describing later uses of Lemma 2.13 (stationarity for general z via scaling); no new claim, uses are recorded at consumers (slice C)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -

ITEM: inv:L2337:hormander-purpose
KIND: claim
SOURCE: source/arxiv-2203.07313v4/complex-sle-final.tex#hormander-purpose@L2337-L2337
DISPOSITION: EXCLUDED
REASON: expository sentence motivating condition (A.1); the claim is Lemma A.2
COVERAGE_STATUS: PROPOSED
EXTRACTOR: extractor-B/sonnet
REVIEWER: -


## Report

**Source ranges read:** paper.tex L805-L1249 (all, with comment blocks L999-1018, L1114-1131, L1140-1146, L1234-1248 skipped per spec) and L2312-L2406 in full. Also read ERRATA.md, graph/EXTRACTION_SPEC.md, graph/INVENTORY.md, graph/anchor-table.md section needed for identity fields, and the two frozen statement files `Defs/IsAdmissibleDensity.lean` and `Lemma_2_13_Exists.lean`. Other ranges were not read.

**Counts:** 67 nodes (8 external, 59 internal: 2 frozen anchors `lem-p.exists`, `lem-stationary.admissible`), 161 DEPS/EDGE lines, 0 ROUTES. Coverage: 64 items (59 inventory + 5 added); 51 mapped to nodes, 13 excluded (§2.4 simulations L805-830: 5 items; 4 headings; 2 commented-out citations at L2396; 2 expository sentences). Added items: `inv:L847:sigma-range`, `inv:L969:regularity-preview`, `inv:L984:pi-reduction`, `inv:L959:usage-remark` (excluded), `inv:L2337:hormander-purpose` (excluded). Graph is acyclic within slice B.

**Cross-slice edges (canonical IDs I do not own):** `defn-sle`, `defn-loewner.absorbing-time`, `eqn-def-ft`, `eqn-reflect`, `lem-endpt-cont`, `step:wlog-c-nonneg`, `step:driver-representation`, `eqn-nu-D.mu`, `eqn-nu-D.nu`, `eqn-nu-D.D`. Slice B nodes consumed by other slices (not recorded here): `lem-p`, `lem-polar`, `lem-stationary`, `lem-recurrence`, `remark-sigma`, `remark-p0`, `defn-sigma`, `def-arg`. Nodes with no in-slice consumer: `remark-sigma`, `remark-p0`, `lem-recurrence` (expected to be consumed by slices C/D).

**Alternate routes:** none found in the source.

**SOURCE_GAP nodes (NOTE contains SOURCE_GAP):** `step:arg-lift`, `step:polar-derivative-sde` (z-differentiation of the SDE), `remark-sigma` (case T_z=∞, surjectivity), `step:stat-theta-bm-sde` (independence of initial angle / uniqueness in law), `step:stat-martingale-qv` (W' on an enlarged space when D vanishes), `step:p-case1-first-order-solutions` (p_1 < 0 for u<0, nonnegativity claimed on all of R), `step:p-case2` (never normalizes int_0^{2pi} p = 1), `step:rec-renewal` (conditional Borel-Cantelli, SDE strong Markov), `step:rec-hit-fixed-y` (finiteness of θ-time ω(R) in the critical case), `step:kol-process-stationarity` (marginals to process law), `step:kol-derivative-vanishes-all-times` (right derivative), `lem-hormander` (t≥0 should be t>0), `step:horm-apply-hairer` (bounded derivatives, smoothness in u).

**New `ext:` IDs:** none. External nodes defined here (first citation in slice B, orchestrator to deduplicate): `ext:ito-complex`, `ext:levy-characterization`, `ext:strong-markov-bm`, `ext:hormander-1d`, `ext:scale-function`, `ext:picard-lindelof`, `ext:martingale-convergence`, `ext:dct`.

**Uncertainty list:**
1. `lem-p.exists` carries only admissibility; strict positivity off a discrete set and the stationary property sit on `lem-p`, which needs the same constructed p (`step:p-positive-off-discrete`).
2. Lemma 2.16 says "p as in Lemma 2.13"; I read it as any admissible p (R7/R15), with `lem-stationary` (not `lem-p`) as the stationarity source; the density property is taken from `lem-p` in `step:rec-tau-finite`.
3. `step:rec-scale-function-hit`: premises of Lawler Lemma 1.24 at the endpoint x+π are not checked in the source.
4. `step:p-case1-mu-over-D-integral`: closed form is quoted without verification; prefactor singular at a=b, c=0 (integral is 0 there). Source says p_0(π)<1 but proves ≤.
5. Lemma 2.11 presupposes σ defined on (0,∞), which Remark 2.12 derives from it; modeled with no graph cycle.
6. `lem-polar` for z=0 (T_0=0, R4) and for ab=0 is not excluded by the source; R5/R6 scope applied in hypotheses only for Lemma 2.13 onward.
7. Appendix A.1 was normalized with α,β: ℝ→ℝ (P6) and ∫₀^π p = 1 (R9); its use for Lemma 2.14 is the explicit step `step:stat-kolmogorov-normalization`.
8. Step granularity of Appendix A.1 (eight steps) and the choice to give `step:D-structure` a separate node are judgment calls.
9. While reading the frozen file `Lemma_2_13_Exists.lean` for its statement, its import line and a `sorry` body were visible in the cat output; I did not seek, use, or record this.

**Confirmations:** no Lean evidence was sought (beyond the inadvertent exposure in item 9, which is not used); no anchor ABI was edited or inferred (identity fields copied verbatim from EXTRACTION_SPEC §8); no file other than `graph/packets/slice-B.md` was changed, apart from a scratch generator script in the session scratchpad directory; nothing committed, no Lean run.
