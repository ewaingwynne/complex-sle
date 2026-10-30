# M6 / S2 — polar decomposition of SLE_Σ (Lemma 2.11) in martingale form (prover brief, Fable, HARD)

Goal: build, as INTERNAL lemmas (no frozen anchors), the polar-decomposition layer that Theorem 1.8 / Props 3.1–3.2 will
consume: Def 2.9 (time change σ_z), Def 2.10 (continuous argument θ_t(z)), Remark 2.12, and Lemma 2.11 (SDEs for
θ̂ and log|f̂|), stated in martingale form (ERRATA R24). Source: source/arxiv-2203.07313v4/complex-sle-final.tex
L831-935. You choose exact internal statements, but they must be honest: no hypothesis that a later step should prove,
and the definitions must mean the source objects (no junk off the valid locus — use subtypes/domains as in
ComplexSLE/Frozen/Defs/{LoewnerMap,CenteredLoewnerMap}.lean, or restrict to t < T_z explicitly).

Graph closure of lem-polar (for orientation; SOURCE_GAP steps are places where the paper only sketches):
- def-arg: theta_t(z) is the unique continuous argument of f_t(z) on [0,T_z) with theta_0(z) in [0,2pi)
- defn-loewner.absorbing-time: T_z in [0,infinity] is the time up to which the solution of (1.1) started at z exists
- defn-loewner.solution: for each z in C, g_t(z) solves g_t(z)-dot = 2/(g_t(z)-U_t), g_0(z) = z; centered chain f_t(z) = g_t(z) - U_t
- defn-loewner.well-defined [SOURCE_GAP]: the IVP (1.1) started at z has a solution on [0,T_z), and any two solutions on a common interval [0,tau) agree
- defn-sigma: sigma=sigma_z is defined by t~ = int_0^{sigma(t~)} |f_s(z)|^-2 ds (eqn-defn-sigma), parametrizing (f_t)_{t in (0,T_z)}
- defn-sle: U has a.s. continuous paths, U_0 = 0, independent increments, U_t - U_s ~ N(0,(t-s)Sigma); SLE_Sigma is the Loewner chain driven by U
- defn-sle.gaussian-law: centered Gaussian law on C identified with R^2 with covariance S (the law of an increment of the driver, ruling R6)
- eqn-cov-matrix: Sigma = [[a,c],[c,b]]
- eqn-def-ft: df_t(z) = (2/f_t(z)) dt - sqrt(a) dB_t - i sqrt(b) dB~_t, f_0(z) = z
- eqn-nu-D.mu: mu(u) = -(2 - a/2 + b/2) sin 2u - c cos 2u
- eqn-nu-D.nu: nu(u) = (2 - a/2 + b/2) cos 2u - c sin 2u
- ext:ito-complex: Ito's formula for (complex) continuous semimartingales (Protter, Ch. II, Thm 35); used in slice B also for real C^2 functions of a real diffusion (Lemma A.1).
- ext:levy-characterization: Continuous (local) martingales with prescribed quadratic (cross-)variations are Brownian motions (equal in law), including time-change/representation form dM = sqrt(h) dW'.
- ext:picard-lindelof: Picard-Lindelof ODE existence and uniqueness
- lem-endpt-cont: lim_{t -> T_z^-} |f_t(z)| = 0
- lem-polar: hat-theta_t~ = theta_sigma(t~)(z) and hat-f_t~ = f_sigma(t~)(z) satisfy (2.25) dtheta = mu dt~ - sqrt(a) sin(theta) dW + sqrt(b) cos(theta) dW~; (2.26) dlog|f| = nu dt~ + sqrt(a) cos(theta) dW + sqrt(b) sin(theta) dW~; (2.27) dlog
- remark-sigma [SOURCE_GAP]: a.s. the domain of sigma_z is (0,infty) (and sigma maps (0,infty) onto (0,T_z))
- step:arg-lift [SOURCE_GAP]: there is a unique continuous t -> theta_t(z) on [0,T_z) with f_t(z)/|f_t(z)| = e^{i theta_t(z)} and theta_0(z) in [0,2pi)
- step:driver-representation: B, B~ are standard linear BMs with Cov(B_t,B~_t) = ct/sqrt(ab) and U = sqrt(a) B + i sqrt(b) B~
- step:endpt-finite-upcrossings: the number of upcrossings of [alpha,beta] is at most T_z/eps
- step:endpt-liminf: liminf_{t -> T_z^-} |f_t(z)| = 0
- step:endpt-upcrossing-bound: beta - alpha <= 2 alpha^{-1}(t2-t1) + rho(t2-t1) hence t2 - t1 >= eps(T_z,alpha,beta) for each upcrossing
- step:endpt-upcrossing-reduction: lim_{t -> T_z^-} |f_t(z)| = 0
- step:loewner-global-uniqueness [SOURCE_GAP]: gamma1 = gamma2 on [0,tau) (the agreement set is nonempty, closed and open, by local uniqueness)
- step:loewner-glue-maximal [SOURCE_GAP]: using uniqueness, solutions on [0,tau) with increasing tau patch together to a solution on [0,T_z), where T_z = sup of such tau
- step:loewner-local-solution [SOURCE_GAP]: near any time t0 with g(t0) != U_{t0} the ODE g-dot = 2/(g-U_t) has a solution, and two solutions that agree at a time t0 agree on a neighbourhood of t0 (local uniqueness only)
- step:polar-W-law: (W_t~,W~_t~) =_d (B_t~,B~_t~): continuous martingales with the same quadratic variations (t~) and cross-variations (c t~/sqrt(ab))
- step:polar-derivative-sde [SOURCE_GAP]: d log f_t'(z) = -2 f_t(z)^-2 dt; real part and time change by sigma give d log|hat-f'| = -2cos(2 hat-theta) dt~
- step:polar-ito-log: d log f_t(z) = f^-2 (2 - a/2 + b/2 - ic) dt + f^-1 (sqrt a dB + i sqrt b dB~), expanded in polar form with theta_t
- step:polar-real-imag: d log|f_t| = |f_t|^-2 nu(theta_t)dt + |f_t|^-1 (sqrt a cos dB + sqrt b sin dB~) (eqn-abs-zt-op); d theta_t = |f_t|^-2 mu(theta_t) dt - |f_t|^-1 (sqrt a sin dB + sqrt b cos dB~) (eqn-theta-t-op)
- step:polar-time-change: with W_t~ = int_0^sigma(t~) |f_s|^-1 dB_s and W~ likewise, hat-theta and log|hat-f| satisfy (2.25) and (2.26)
- step:sigma-bounded-coefficients: a.s. sup and inf of |hat f_t~|, |hat f'_t~| over [0,T] are finite/positive, hence liminf_{t->T-} |hat f_t| > 0 if the domain were [0,T]

Design guidance (yours to refine; write a short design note at the top of your main file first):
- Work on an SLE driver with everywhere-continuous paths adapted to a filtration: `ComplexSLE.IsSLEDriverAdapted`
  (ComplexSLE/Frozen/Defs/IsSLEDriverAdapted.lean). Downstream will produce it via levy_characterization's completion
  clause or by construction; you may assume IsSLEDriverAdapted as the hypothesis of your lemmas (it is the honest
  source setting "U is a Brownian motion w.r.t. ℱ").
- For fixed z ≠ 0 the path t ↦ f_t(z) on [0, T_z) is t ↦ γ t − U t for the solution γ of loewnerMap_exists_solution.
  Define the time change σ_z as the inverse of t ↦ ∫₀ᵗ |f_s(z)|⁻² ds (Def 2.9; Remark 2.12 / remark-sigma: σ_z maps
  [0, ∞) onto [0, T_z) — a SOURCE_GAP the graph flags; prove it, using lemma-2.5-type behaviour f_t(z) → 0 as t → T_z if
  needed: that is lem-endpt-cont, which you may prove here or flag).
- The SDE content in martingale form: with θ̂ the continuous argument and ρ̂ = log|f̂| after the time change, and 𝒢 the
  time-changed filtration ℱ_{σ(·)}: M := θ̂ − θ̂_0 − ∫μ(θ̂), N := ρ̂ − ρ̂_0 − ∫ν(θ̂) are continuous local martingales
  (ComplexSLE.IsContLocalMartingale), with M² − ∫2D(θ̂), N² − ∫(2 − ... ) etc. and MN − ∫(...) continuous local
  martingales — derive the exact brackets from eqn-theta-t / eqn-abs-zt (L870-885). That makes θ̂ an
  ComplexSLE.IsDiffusionSolution 𝒢 μ √(2D) (check the β² convention in IsDiffusionSolution).
- Tools: EXTERNALs `ComplexSLE.External.ito_formula` (ItoFormula.lean) for log f in the original time, then
  `timeChange_isContLocalMartingale` (TimeChangeIsContLocalMartingale.lean, needs σ 0 = 0 and continuity) for the
  time change. The polar-W-law step (Lévy) is not needed in martingale form (the brackets are the content) — say so.
  Driver facts: ComplexSLE/Internal/Driver/* (scaling, symmetries, shift); Re U, Im U as continuous local martingales
  with brackets a t, b t, c t for an IsSLEDriverAdapted — prove this bridge (Gaussian second moments) as a lemma.
- Deterministic facts: ComplexSLE/Internal/Loewner/*, Hull/* (local existence, gluing, f_t ≠ 0 before T_z, etc.).

Allowed inputs: Mathlib; sealed defs and anchors; Internal/Infrastructure lemmas; EXTERNALs ito_formula,
timeChange_isContLocalMartingale, levy_characterization (only if genuinely needed). No DRAFT anchor or provider.
Ownership: new files under ComplexSLE/Internal/Polar/ and source-independent stochastic-calculus helpers under
ComplexSLE/Infrastructure/Stochastic/. No other edits.
Checks: lake build of your modules; `python3 -I tools/leanprobe.py externals <module> <decl>` for each main theorem
(report PROVED/PROVED_REL and the externals); `tools/check.sh --quick`. Don't run full tools/check.sh.
Stop condition: if a needed fact is not provable from the allowed inputs (e.g. an external is too weak for this use),
STOP and report precisely which statement you would need, with a Lean draft — do not weaken a lemma to make it go through.
Budget ~5 hours; if you run out, land what is proved (sorry-free) and report the rest.

## Hard rules (repeat verbatim in every worker brief)


1. Never edit a file under `ComplexSLE/Frozen/`, `frozen-anchor-manifest.json`,
   `DEPGRAPH*.md`, `STATUS.md`, `ERRATA.md`, `lakefile.toml`, `lean-toolchain`
   or `lake-manifest.json`. If a frozen declaration looks wrong, stop and report.
2. No `sorry`, `admit`, `axiom`, `opaque` placeholders, `native_decide`,
   `implemented_by`, `@[extern]`, `unsafe`, or `set_option maxHeartbeats`
   (or any other heartbeat / recursion / debug override) anywhere in tracked files.
   Unfinished work stays out of `ComplexSLE/` or is reported as unfinished.
3. Never add a hypothesis to a source-facing statement to make a proof go through.
   A needed intermediate result is proved, not assumed.
4. Never import a frozen anchor that is in state `DRAFT_SORRY`, nor its provider
   module (see the manifest). Consume only sealed anchors, your own files, and
   `EXTERNAL` inputs through `ComplexSLE/External/` when your brief lists them.
5. Every Lean file is a `module`: copyright comment, `module`, imports
   (`public import` for anything statements need), module docstring,
   `public section` (`@[expose] public section` for source-facing definitions).
6. At most 1500 lines per file. Split larger files.
7. Do not run `lake clean`, delete anything under `.lake/`, or modify Mathlib.
8. Do not commit; the orchestrator commits. Do not touch files you were not given.
9. Scratch and probe files go outside `ComplexSLE/` (e.g. `.lake/probes/`) and are
   deleted after use.
10. Report exactly: files changed, approach, the exact commands run and their output,
    `#print axioms` for every new public theorem, and anything unproved or uncertain.

Handoff: files changed; design note; exact statements of the main lemmas; approach; commands and outputs; externals
status per main theorem; anything unproved or uncertain (with precise statements).
