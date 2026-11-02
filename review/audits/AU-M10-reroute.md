# AU-M10-reroute: audit of the removal of `hormander_oneDim` and `markov_oneDim` (independent, refute-first, 2026-11-02)

Posture: independent, refute-first; I wrote none of the code. No project file was edited; this report is the only file written.
Scratch lived in `.lake/probes/au-reroute/` (deleted at the end; `.lake/probes/closure.py` untouched). No commit, no subagent.

Audited tree: git HEAD `5058dde` (`git log 116be1c..HEAD`, 10 commits: `9fa6168 71e1c2e 09f4721 1fdbbe3 aed0912 f782222 0bfe1e6 1319917
784c47a 5058dde`). At the start the working tree was clean. While the audit ran the orchestrator edited `README.md`, `RESULTS.md`,
`STATUS.md`, added `briefs/M10-RESULTS-final.md`, and, after all Lean checks below had run, made a docstring-only edit of
`ComplexSLE/Internal/Recurrence/StatBridge.lean` (it replaces the stale name of non-blocking note 1). Until that edit,
`git diff HEAD --name-only -- ComplexSLE tools lakefile.toml lean-toolchain lake-manifest.json frozen-anchor-manifest.json DEPGRAPH.md graph`
was empty, so every Lean result below is for the committed tree. Manifest sha256 `a482663a6e7c4bd42d4db1bccc2f37114a247dc5bcf3175fea2cb396428da5c8`
(before: `d476a6c9483e3133d8270ca833ffcf47c08b4f083306f549982d4b5b34f6c490`). Toolchain files and `tools/` are unchanged since `116be1c`.

## Overall verdict: PASS

Items 1-6 pass. I found no blocking defect. I could not construct a statement drift, a smuggled hypothesis, a stray `sorry` or an
undischarged premise. All 36 sealed theorem anchors compute to `PROVED` (no `PROVED_REL`), the six §3 roots and the new
theorems have axioms exactly `propext, Classical.choice, Quot.sound`, and the mathematical spot checks (item 4) found no gap.
The non-blocking list (stale docstrings, dead Hörmander-condition lemmas, graph leaf, status docs in flux) is at the end.

Not done: I did not re-derive the earlier-milestone results that the new files consume (`isDiffusionSolution_thetaHat`,
`lintegral_pathObsAt`, `obsKernel_add_pi`, `exists_continuous_version`, the polar layer); they are covered by the `PROVED` status
and were read only at their interfaces. I did not rebuild from scratch (`lake build --no-build` reports everything up to date, see
item 5). I did not run `.lake/probes/closure.py`: its subject (imports of the two deleted modules) is moot now that the modules are
gone and the whole tree builds.

## Summary table

| # | Item | Result |
|---|---|---|
| 1 | Freeze: Frozen/ diff, External/ deletions, `verify-abi`, manifest, graph hash | PASS |
| 2 | No sorry, no axioms: grep, `externals-all`, axioms of roots, providers and new theorems | PASS |
| 3 | Hypothesis smuggling: 17 listed theorems, applications, binder classification | PASS |
| 4 | Mathematical soundness (a)-(e) | PASS (no gap) |
| 5 | Consumers: exports, imports, build state, module checker | PASS |
| 6 | Graph gate | PASS |
| 7 | Docstrings | 7 stale hits, all non-blocking |

## 1. Freeze: PASS

- `git diff 116be1c -- ComplexSLE/Frozen | wc -l` = `0`.
- `git diff --name-status 116be1c HEAD -- ComplexSLE/External` = exactly `D ComplexSLE/External/HormanderOneDim.lean`,
  `D ComplexSLE/External/MarkovOneDim.lean`. `ls ComplexSLE/External` now lists the 10 sealed files only.
- `python3 -I tools/leanprobe.py verify-abi frozen-anchor-manifest.json` -> `ABI OK (60 anchors)`.
- Manifest versus `git show 116be1c:frozen-anchor-manifest.json` (Python, per-anchor dict equality): 62 -> 60 anchors,
  `removed = ['ext.hormander_oneDim.v1', 'ext.markov_oneDim.v1']`, `added = []`, `changed = []` (no remaining anchor differs in any
  field, so every `abi_sha256`, `prefix_sha256`, `suffix_sha256`, `implementation` is as in `116be1c`); no top-level key
  (`schema_version`, `manifest_state`, `seal_limits`) changed. All 60 anchors are `SEALED` (36 theorems, 24 definitions).
- `sha256sum frozen-anchor-manifest.json` = `a482663a…28da5c8` = `FROZEN_MANIFEST` at line 10 of `DEPGRAPH.md` and of
  `graph/DEPGRAPH.header.md`. The diff of those two files against `116be1c` is that one line only.
- `git diff 116be1c HEAD --stat -- tools lakefile.toml lean-toolchain lake-manifest.json` is empty. The `ERRATA.md` diff is 13 added
  lines (R31), no removed line.

## 2. No sorry, no axioms: PASS

- `grep -rnw sorry ComplexSLE` -> no output (exit 1). A case-insensitive grep for `axiom|opaque|unsafe|native_decide|implemented_by|
  @[extern|ofReduceBool|trustCompiler|admit|set_option|maxHeartbeats|maxRecDepth|bv_decide|run_cmd|#eval|initialize|import Lean` over
  `ComplexSLE` also gives no hit. In the 31 added files: no `Classical.choose`, `Nonempty.some`, `default`, `arbitrary`, `Inhabited`,
  `decide`, macro or syntax; the only `instance` is `IsFiniteMeasure (occupation X P T)` (`OccupationMeasure.lean:52`, proved).
  `tools/check.sh --quick` -> `FROZEN-ANCHOR GUARD OK`, `ALL CHECKS PASSED`.
- `lake build --no-build` replays 113 warnings, none with `sorry`, none an error (`grep -ci sorry build.log` = 0). The two
  `declaration uses sorry` warnings of the previous audit (`HormanderOneDim.lean:43`, `MarkovOneDim.lean:27`) are gone.
- `python3 -I tools/leanprobe.py externals-all frozen-anchor-manifest.json` (44 s, exit 0): `EXTERNALS OK (36 sealed theorems)`.
  Every line has `"externals": []`, `"status": "PROVED"` and axioms `["Classical.choice", "Quot.sound", "propext"]`.
  **`PROVED_REL`: none.** Closure sizes of the six formerly relative roots: `theorem_1_8` 70922, `theorem_1_8_c_zero` 71102,
  `proposition_3_1_a` 68332, `proposition_3_1_b` 68255, `proposition_3_2_a` 70116, `proposition_3_2_b` 70184.
- `python3 -I tools/leanprobe.py axioms <module> <decl>` for the six roots, frozen (`ComplexSLE.Frozen.<File>`, `ComplexSLE.<root>`)
  and provider (`ComplexSLE.Internal.<File>`, `ComplexSLE.Internal.<root>`): all 12 give
  `{"axioms": ["propext", "Classical.choice", "Quot.sound"], "nonstandard": []}`.
- `#print axioms` (one Lean run, `lake env lean .lake/probes/au-reroute/Ax2.lean`) on all of: the 17 theorems of item 3 (including
  the three `*_admissible` ones), `thetaSemigroup_periodic`, `exists_contDiff_beta_sq`, `ae_volume_thetaHat_null`,
  `occupation_zeroSet_eq_zero`, `occupation_inter_ne_zero_eq_zero`, `measure_inter_ne_zero_eq_zero`, `exists_integral_mul_sq_le`,
  `tendsto_cesaro_of_contDiff`, `ae_mem_of_ae_unit`, `lemma_3_3`, and in `Infrastructure`: `exists_periodic_solution_core`,
  `exists_residual_density`, `exists_bounded_solution`, `exists_periodic_C1_of_bounded_solution`: every line reads
  `[propext, Classical.choice, Quot.sound]`.

## 3. Hypothesis smuggling: PASS

I read the statement, the binders and the proof of each listed theorem, and the full type with `#check @…` (pp output in
`.lake/probes/au-reroute/chk.log`, deleted). Result per theorem (file:line of the statement):

| Theorem | Binders | Verdict |
|---|---|---|
| `Infrastructure.exists_periodic_solution_of_doubleZero` (`DoubleZero.lean:94`) | `T>0`; `α, D, r` C² and `T`-periodic; `D ≥ 0`; zero set of `D` is exactly `x₀+Tℤ`; `D''(x₀)>0`; `α(x₀)≠0` | coefficient data and structure; conclusion (a C¹ periodic solution) is not assumed. Hypotheses met by `(µ, D)`, see 4(a) |
| `exists_periodic_poisson_of_pos` (`Poisson.lean:51`) | `T>0`; `α, D, r` continuous, periodic; `D>0` | structural |
| `exists_periodic_poisson_of_solutions` (`PoissonConst.lean:67`) | `D ≥ 0`; **two periodic C¹ solutions** `h₁` of `D h'+αh=1` and `hr` of `D h'+αh=r` | assumes an intermediate existence result, by design (it is the "maximum principle" half). Not source-facing. Both call sites prove the premises: `Poisson.lean:119` (from `exists_periodic_linSol_of_ne`, `contDiff_one_linSol`, `linSol_equation_of_pos`) and `InvariancePoisson.lean:75-83` (from `exists_periodic_solution_of_doubleZero`) |
| `eq_zero_of_periodic_generator_eq_const` (`PoissonMax.lean:66`) | `D ≥ 0`; `g` C² periodic; generator of `g` constantly `C` | the premise is the situation, the conclusion `C=0` is the maximum principle (proved, 20 lines) |
| `thetaSemigroup_add` (`ThetaSemigroup.lean:183`) | `hU`, `0<a`, `c²≤ab`, `f` measurable `π`-periodic bounded | genuine |
| `continuous_thetaSemigroup` (`ThetaSemigroupFeller.lean:102`) | `hU`, `0<a`, `c²≤ab`, `f` continuous periodic | genuine |
| `thetaSemigroup_sub_self` (`ThetaSemigroupDynkin.lean:75`) | `hU`, `a,b>0`, `c²≤ab`, `β` continuous with `β²=2D`, `g` C² periodic | `β` is a universally quantified witness of `√(2D)`; supplied by `exists_contDiff_beta_sq` (`InvarianceCesaro.lean:104`). Not conclusion-shaped |
| `exists_poisson_generator` (`InvariancePoisson.lean:61`) | `a,b>0`, `c²≤ab`, `β²=2D`, `f` C² periodic | genuine; the C, g are produced |
| `poisson_const_eq` (`InvariancePoisson.lean:91`) | as above plus `IsAdmissibleDensity a b c p`, `g` C² periodic with `L g = f - C` | premise is the Poisson equation; conclusion `C = ∫ f dν` comes from `IsKolmogorovDensity.integral_generator_eq_zero` |
| `tendsto_cesaro_of_continuous` (`InvarianceCesaro.lean:145`) | `hU`, `a,b>0`, `c²≤ab`, `hp`, `f` continuous periodic, start `u` | genuine |
| `integral_thetaSemigroup_admissible` (`InvarianceStationary.lean:45`) | same, `s`, `f` continuous periodic | genuine; invariance is proved, see 4(c) |
| `ae_volume_occupation_null` (`Occupation.lean:69`) | see the table below | genuine |
| `exists_pos_measure_thetaHat_preimage_eq_zero` (`OccupationThetaHat.lean:70`) | `hU`, `a,b>0`, `c²≤ab`, `z≠0`, `N` null | conclusion `∃ t>0, P(θ̂_t(z)∈N)=0` is proved from the previous theorem by Fubini on `Ω×[1,2]` |
| `exists_zero_lattice_diffusionD` (`CriticalCoefficients.lean:90`) | `a,b>0`, `c²=ab` | pure coefficient algebra, proved |

**Binders of the three `*_admissible` theorems** (`integral_comp_thetaHat_prod_admissible`, `map_addCircle_thetaHat_prod_eq_admissible`,
`map_exp_thetaHat_prod_eq_admissible`, `InvarianceStationary.lean:111,128,148`; types in `chk.log`):

| Binder | Class |
|---|---|
| `Ω, m, P, ℱ, a, b, c, U` (implicit), `[IsProbabilityMeasure P]` | ambient data and instance, the same as in every §3 theorem |
| `hU : IsSLEDriverAdapted a b c U P ℱ` | frozen vocabulary: the SLE_Σ driver adapted to `ℱ` (paper hypothesis) |
| `0 < a`, `0 < b`, `c² ≤ a*b` | the paper's parameter hypotheses |
| `{p}`, `hp : IsAdmissibleDensity a b c p` | the frozen R7 predicate (continuous, `≥ 0`, `π`-periodic, `∫₀^{2π}p=1`, stationary Kolmogorov equation, `Dp ∈ C¹`). It says `p` solves the adjoint equation. It does **not** say that `θ̂` is stationary under `P⊗ν`; that is the proved conclusion. The frozen §3 statements carry the same `p, hp` as binders (`Proposition_3_1_A.lean:30` passes `p hp hI`) |
| `s : ℝ≥0` | universally quantified time |
| `{f}`, `hf : Continuous f`, `hfper : Periodic f π` (first theorem only) | the test-function class; the conclusion holds for all of them |

**Binders of `ae_volume_occupation_null`:**

| Binder | Class | Discharge at the call sites (`OccupationThetaHat.lean:63,80`) |
|---|---|---|
| `[IsProbabilityMeasure P]`, `ℱ`, `β`, `X` | data | - |
| `0<a`, `0<b`, `c²≤ab` | paper hypotheses | passed from the caller's own paper hypotheses |
| `hX : IsDiffusionSolution ℱ (µ a b c) β X P` | hypothesis on the process: martingale problem (frozen vocabulary R24/R25), not the occupation property | `exists_continuous_version_thetaHat` (`OccupationThetaHat.lean:41`) from `isDiffusionSolution_thetaHat` and `exists_continuous_version` on the completed `σ`-filtration |
| `hXc : ∀ ω, Continuous (X · ω)` | regularity: everywhere-continuous paths, needed for joint measurability of `(ω,t)↦X_t(ω)` | from the same continuous version (`∀ ω, Continuous`) |
| `hβc : Continuous β`, `hβsq : β² = 2D` | witness of `√(2D)` | `continuous_const.mul … |>.sqrt`, `sq_sqrt_two_mul_diffusionD` |
| `N`, `hN : volume N = 0`, `T` | the null set and horizon | the call sites use `toMeasurable` to make `N` measurable |

None of these is conclusion-shaped, and none assumes a bound on occupation. The strength of the theorem comes from
`exists_integral_mul_sq_le` (Dynkin bound) and `occupation_zeroSet_eq_zero` (critical lattice), both proved.

Premises of every application are discharged by terms (the build is green with no sorry, and the six roots have no extra axiom).
I additionally listed all call sites of the 17 theorems (`grep -rnw`): `integral_thetaSemigroup_admissible` is called only from
`InvarianceStationary.lean:125`; `integral_comp_thetaHat_prod_admissible` from `ErgodicMean.lean:141`, `ErgodicRatioBirkhoff.lean:155`
and the two `*_prod_eq_admissible`; `map_addCircle_thetaHat_prod_eq_admissible` from `ErgodicConstRec.lean:352`;
`map_exp_thetaHat_prod_eq_admissible` from `Lemma37.lean:137` and `PathStat.lean:76`; `exists_pos_measure_thetaHat_preimage_eq_zero`
from `AllZ.lean:70`. Each passes `hU ha hb hc hp` from its own context, which reach the frozen binders of the §3 roots.

R6 binder removals (diff `784c47a..5058dde`): every change is `(hMO : MarkovOneDim)` deleted from a binder list and from the
corresponding arguments, or a rename (`_of_markov` -> unsuffixed or `_core`). The old unsuffixed `lemma_3_9` (which discharged
`hMO` with the external) was deleted and `lemma_3_9_of_markov` took its name, with identical remaining binders
(`Lemma37.lean:354-359`). One code change beyond binders: `obtain ⟨β, hβ, hβsq, -⟩ := exists_beta …` became
`obtain ⟨β, hβ, hβsq⟩ := exists_contDiff_beta_sq …` (the dropped component was the Hörmander condition (A.1), not needed there).
The declarations moved by the split commits (`driverLaw`, `isProbabilityMeasure_driverLaw`, `obsKernel`, `measurable_obsKernel`,
`obsKernel_add_pi`, `obsKernel_periodic`, from `PathStat.lean` to `PathStatKernel.lean`; `admissibleMeasure` and its lemmas from
`SLEStatLaw.lean` to `AdmissibleMeasure.lean`) are textually identical after whitespace normalization (Python comparison, all
`IDENTICAL`).

## 4. Mathematical soundness: PASS (no gap found)

### (a) Critical-case ODE route (`Infrastructure/PeriodicODE/DoubleZero*.lean`)

Statement (`DoubleZero.lean:94`): `D ≥ 0` C² periodic with zero set exactly `x₀+Tℤ`, `D''(x₀)>0`; `α, r` C² periodic, `α(x₀)≠0`;
then `D h' + α h = r` has a C¹ periodic solution.

- **Reduction** (`exists_periodic_solution_of_doubleZero`, `exists_periodic_solution_zero`): translate to `x₀=0`; if `α(0)<0`
  reflect `u↦-u` with `α̃(u) = -α(-u)`, `D̃(u) = D(-u)`, `r̃(u) = -r(-u)`. Check by hand: if `h̃` solves the reflected problem, then
  `h(v) = h̃(-v)` has `h'(v) = -h̃'(-v)`, so `D(v)h'(v) = -D̃(-v)h̃'(-v)` and `α(v)h(v) = -α̃(-v)h̃(-v)`; the sum is
  `-(D̃h̃' + α̃h̃)(-v) = -r̃(-v) = r(v)`, as in the Lean proof. `α̃(0) = -α(0) > 0`.
- **Residual** (`exists_residual_density`, `DoubleZeroResidual.lean:147`): `φ = c₀ + c₁ sin(ωu)/ω + c₂(1-cos ωu)/ω²`, `ω = 2π/T`, so
  `φ(0)=c₀, φ'(0)=c₁, φ''(0)=c₂`. With `r̃ = r - (Dφ' + αφ)`: `r̃(0) = r(0) - α(0)c₀` (as `D(0)=0`) so `c₀ = r(0)/α(0)`;
  `r̃'(0) = r'(0) - α'(0)c₀ - α(0)c₁` (`D(0)=D'(0)=0`); `r̃''(0) = r''(0) - D''(0)c₁ - α''(0)c₀ - 2α'(0)c₁ - α(0)c₂`. These are
  exactly the formulas `c0, c1, c2` in the proof (lines 160-170), and the three vanishings are `rt0, rt1, rt2`. `ρ = r̃/D` (0 on the
  lattice) is continuous at 0 because `D ≥ c y²` and `|r̃| ≤ ε y²` near 0 (`exists_sq_bounds`, `abs_le_sq_of_second_order_zero`), and
  continuous elsewhere since `D ≠ 0` on `(0,T)`. Also `ρ(0)=0`. The jet of any C¹ solution at 0 is forced to be `(c₀, c₁)` by
  differentiating the equation once at 0, so the choice is not arbitrary.
- **Interval solution** (`exists_bounded_solution`, `DoubleZeroInterval.lean:105`): `a = α/D`, `A = ∫ a`; `a ≥ c/x²` near 0 and
  `a ≥ c/(T-x)²` near `T` give `A → -∞` at `0⁺` and `A → +∞` at `T⁻` (`tendsto_atBot_of_deriv_ge`: `A + c/x` is monotone near 0; same
  at `T`). `H = e^{-A}∫₀ˣ e^{A}ρ` solves `H' = ρ - aH`.
- **Ends by L'Hôpital** (`DoubleZeroEnds.lean`): with `b = D/α` (`b → 0`, `b' ≥ -1/2` near the ends, from
  `exists_local_data`, `DoubleZeroLocal.lean`): `(e^A b)' = e^A(1+b') ≥ e^A/2`. Left end: `G/e^A` and `G/(e^A b)` are `0/0` with
  `G → 0`, ratios `ρ b → 0` and `ρ/(1+b')`, `|·| ≤ 2|ρ|`; so `H → 0` and `aH → 0`. Right end: `∞/∞`; for the second quotient
  `e^A b → ∞` because `e^{A/2} b` is monotone (`(e^{A/2}b)' = e^{A/2}(1/2+b') ≥ 0`) so `e^A b ≥ κ e^{A/2} → ∞`. The ∞/∞ rule is
  the project's own `lhopital_atTop_left_on_Ioo` (`LHopitalAtTop.lean:26`): hypotheses `g → ∞`, `g' ≠ 0`, `f'/g' → l`, no condition on
  `f`, proved by the Cauchy mean value theorem (read; it is the standard argument and compiles).
- **Gluing** (`exists_periodic_C1_of_bounded_solution`, `DoubleZeroGlue.lean:27`): `K u = H (toIcoMod T 0 u)`, `K' = ρ - aK`; at the
  lattice `K'` has one-sided limits `ρ(0) - 0 = 0` from both sides (`hK'r`, `hK'l`), which is why `ρ(0)=0` and `aH → 0` are needed,
  and `hasDerivAt_of_hasDerivAt_Ioo_Ioo` gives differentiability at 0 with `K'(0)=0`; periodicity transports it to all lattice points.
  In `exists_periodic_solution_core` the final identity `D K' + α K = D ρ` holds off the lattice by `K' = ρ - (α/D)K` and on the
  lattice because `K = 0` and `D = 0` there.
- **Hypotheses met by `(µ, D)` when `c² = ab`** (`InvariancePoisson.lean:72-83`): `α := µ a b c`, C² by `contDiff_mu`; `D := diffusionD`,
  C² by `contDiff_diffusionD`; `r := f` (C²) and `r := 1`; periodic by `mu_periodic`, `diffusionD_periodic` (period `π`);
  `D ≥ 0` by `diffusionD_nonneg ha hb hc` (using `c²≤ab`); the zero set, `D''(x₀)>0` and `µ(x₀)≠0` come from
  `exists_zero_lattice_diffusionD`, whose proof is `D = (R²/2) sin²(u-x₀)` with `R = √a·√(1+(c/a)²)`, `x₀ = arctan(c/a)`
  (`CriticalCoefficients.lean:33`, `:61`), hence zeros `x₀+πℤ`, `D''(x₀)=R²>0`, and `µ(x₀) = -4c/(a+b) ≠ 0` (`c≠0` since `c²=ab>0`).
  Concrete instance by hand: `a=b=c=1`: `D = ½(1 - sin 2u) = sin²(u-π/4)`, `µ = -2 sin 2u - cos 2u`, `µ(π/4) = -2 ≠ 0` (the reflected
  branch `α(0)<0` is exercised), `D''(π/4) = 2 > 0`.
- The Poisson half (`exists_periodic_poisson_of_solutions`) then takes `g' = hr - C h₁` with `C = ∫hr/∫h₁`, `∫h₁ ≠ 0` by the maximum
  principle: if `∫h₁=0`, the primitive `g` would be a C² periodic function with generator `≡ 1`, contradicting `eq_zero_of_periodic_generator_eq_const`.
  The maximum principle itself (`PoissonMax.lean`): at a maximum point `g'=0`, `g''≤0` (second-derivative test: `g''>0`, `g'=0` would give a
  local min, hence `g` locally constant, hence `g''=0`), so `C = D g'' ≤ 0`, and `-g` gives `C ≥ 0`.

### (b) Chapman-Kolmogorov (`ThetaSemigroup.lean`)

- Restart identity (`lintegral_pathObsAt`, `PathStatRestart.lean:210`): for `z ≠ 0` and measurable `F`,
  `E F(Ξ_s) = E ∫ F(obsC(w, θ̂_s(z))) dΛ(w)`. The restart time is `σ_z(s)`, a stopping time for each fixed `s`
  (`isStoppingTime_sigmaTop`, used at `PathStatRestart.lean:217`), a.s. finite since `σ_z` is defined on `[0,∞)`. It is applied once,
  at `thetaSemigroup_add` (`ThetaSemigroup.lean:183-204`), to `F_t(ξ, inc, _) = ofReal(f(arg ξ/2 + inc t) + C)`.
- `thetaObs_pathObsAt` (`:121`): `F_t(Ξ_s) = ofReal(f(θ̂_{s+t}) + C)`. Bookkeeping: `Ξ_s`'s first coordinate is `e^{2iθ̂_s}`;
  `periodic_arg_exp_add` (`:111`) shows `f(arg(e^{2iθ})/2 + x) = f(θ + x)`: `arg(e^{2iθ}) = 2θ - 2kπ` (`Complex.arg_exp_mul_I`,
  `toIocMod`), half is `θ - kπ`, and `f` is `π`-periodic. Then `θ̂_s + (θ̂_{s+t} - θ̂_s) = θ̂_{s+t}`.
- `obsKernel_thetaObs` (`:154`): `H_{F_t}(β) = ofReal(Q_t f(β) + C)`: `obsC(w,β)` has `e^{2iβ}` and the increments of the chain started
  at `e^{iβ}`; pushing forward to `P`, `θ_t(e^{iβ})(ω) = θ̂_t(unitPt β)(ω)` (`rfl`), and a.s. `θ̂_0 = toIcoMod 2π 0 β` (`ae_thetaHat_zero`),
  so `f(β + θ̂_t - toIcoMod 2π 0 β) = f(θ̂_t)`: `β - toIcoMod 2π 0 β = 2kπ` and `f` is `π`-periodic (`periodic_add_sub_toIcoMod`, `:140`). The
  `2π` versus `π` mismatch is harmless because `2kπ = (2k)π`; the `π`-periodicity (not `2π`) is exactly what is needed, since only
  `e^{2iθ̂}` is stationary.
- `thetaSemigroup_periodic` (`:172`): from `obsKernel_add_pi` (reflection `obsC(-w,β) = obsC(w,β+π)` and `-U =_d U`, `PathStatKernel.lean`;
  the proof is identical text to the one at `116be1c`).
- `thetaSemigroup_add`: `Q_{s+t}f(u) + C = E[Q_t f(θ̂_s(u)) + C] = Q_s(Q_t f)(u) + C`, then cancel `C`. `Q_t f` needs only
  measurability and boundedness at this step, not periodicity. For `s=0` it reduces to `Q_0 g = g` for periodic `g`, consistent.
- Feller (`continuous_thetaSemigroup`, `ThetaSemigroupFeller.lean:102`): dominated convergence at a fixed `u₀`; the null set depends on `u₀`
  only (`ae_thetaHat_eq_and_continuous … u₀`, `U 0 = 0` a.s.); pathwise continuity at `u₀` is `continuousAt_comp_argPath_sigmaTime_unit`:
  `u ↦ arg_{σ(s)}-arg_0` is continuous at `u₀` (`continuousAt_argPath_sub_initial`) and `arg_0 = u + 2nπ` so
  `f(arg_{σ} ) = f((arg_σ - arg_0) + u)` by periodicity.
- Dynkin (`thetaSemigroup_sub_self`, `ThetaSemigroupDynkin.lean:75`): through an everywhere-continuous version `X` and
  `IsDiffusionSolution.integral_sub_integral_eq`; uses `θ̂_0 = [u]_{2π}` a.s. and `g([u]_{2π}) = g(u)`; Fubini by
  `intervalIntegral_integral_swap` on the bounded integrand. The bounded local martingale `g(X_t) - g(X_0) - ∫₀ᵗ Lg(X_s)ds` is a true
  martingale, as needed for the expectation form.

### (c) Invariance (`InvarianceStationary.lean`, `InvarianceCesaro.lean`)

- Cesàro for C² periodic `f` (`tendsto_cesaro_of_contDiff`, `InvarianceCesaro.lean:98-142`): `L g = f - C` (`exists_poisson_generator`),
  `C = ∫f dν` (`poisson_const_eq`), Dynkin gives `∫₀ᵀ Q_t f(u)dt = CT + (Q_T g(u) - g(u))`, with `|Q_T g - g| ≤ 2‖g‖`; divide by `T`.
- Continuous `f` (`tendsto_cesaro_of_continuous`, `:145`): uniform `ε/4` approximation by C² periodic `f'` (Fourier density, `InvarianceApprox.lean`),
  `|Q_t f - Q_t f'| ≤ ε/4`, `|∫f dν - ∫f' dν| ≤ ε/4`, three-term triangle inequality; fine.
- Invariance (`integral_thetaSemigroup_admissible`, `InvarianceStationary.lean:45-104`): **Feller continuity is used legitimately**:
  `h = Q_s f` is continuous (Feller) and `π`-periodic, which is exactly what `tendsto_cesaro_of_continuous` needs for its test function; then
  `Q_t h = Q_{t+s} f` (Chapman-Kolmogorov, `:68`), `|∫₀ᵀ φ(t+s)dt - ∫₀ᵀ φ(t)dt| ≤ 2‖f‖s` (`hdiffint`), so the two Cesàro limits `∫h dν`
  and `∫f dν` coincide (`tendsto_nhds_unique`, `:104`). Both limits are taken at the same start `u=0`, as the theorem holds from every start.
- The three `*_admissible` statements follow by Fubini (`integral_prod_symm`, `:123`) and the trigonometric-polynomial density of `Law.lean`.

### (d) Lemma 3.3 (`Phases/AllZ.lean`)

`τ = σ_z(t₀)` for a **deterministic** `t₀ > 0` is an `ℱ`-stopping time (`Polar.isStoppingTime_sigmaTop hU z t₀`, `AllZ.lean:73`; the
lemma is for all `s : ℝ≥0`, the same one that the strong Markov restart uses), a.s. finite (`hfin`, from `ae_thetaHat_eq_and_continuous`).
`t₀` is chosen *first* (`:69-70`) from the null set `N` of bad angles: `θ̂_{t₀}(z) ∉ N` a.s. Then `f_τ(z)/|f_τ(z)| = e^{iθ̂_{t₀}(z)}` is a.s. a
good point, `f_τ(z)` is `ℱ_τ`-measurable (`measurable_fHat`), scale invariance moves the good property from the direction to the point
(`mem_cone_of_direction`), and `ae_mem_postDriver` (strong Markov at `τ`) finishes. The pathwise identification of `E(z)` with `E(f_τ(z))`
uses the same future-dependence argument as before. The diff of `AllZ.lean` against `116be1c` replaces `1` by `t₀` and the density step by
the `exists_pos_measure…` step, and nothing else; the statements of `ae_mem_of_ae_unit` and `lemma_3_3` are unchanged.
The Fubini choice (`OccupationThetaHat.lean:72-123`): `A = {(ω,t) : X_t(ω) ∈ N₁, t ∈ [1,2]}` is `P⊗Leb`-null by `ae_volume_occupation_null`,
hence for a.e. (so for some) `t ∈ [1,2]` the fibre is `P`-null; `θ̂` and `X` agree for all times a.s.

### (e) Critical zero occupation (`OccupationCritical.lean`, `OccupationBump.lean`)

`ψ_N(x) = φ(N² sin²(x-x₀))`, `φ = 1 - smoothTransition(2·)`: C¹, `π`-periodic, `0 ≤ ψ_N ≤ 1`, `ψ_N = 1` on the lattice, `ψ_N = 0` where
`N|sin(x-x₀)| ≥ 1` (`critBump_eq_zero_of_one_le`). Take `g` with `g' = ψ_N - M_N/π` (`exists_periodic_contDiff_two_first_deriv`, periodic since
the mean vanishes, `|g| ≤ 2M_N` by `abs_sub_mean_le`), `M_N = ∫₀^π ψ_N`. Then `L g = µ g' + ½ g'' β² = µ(ψ_N - M_N/π) + ½ ψ_N' β²`, so
`ψ_N µ = L g - ½ ψ_N' β² + (M_N/π) µ` (`hid`, `:130-132`). Dynkin against the occupation measure `ρ`: `|∫ L g dρ| ≤ 2‖g‖ ≤ 4M_N`. The key
estimate (`abs_half_deriv_critBump_mul_le`, `OccupationBump.lean:103`): `½ψ_N' β² = φ'(N²s²)·N²R² s³ cos` with `s = sin(x-x₀)`, `|φ'| ≤ K_φ`
and `N²|s|³ ≤ 1/N` on the support `N|s| < 1`, hence `≤ K_φ R²/N`. So
`|∫ψ_N µ dρ| ≤ 4M_N + K_φR²T/N + (M_N/π)‖µ‖T → 0`, because `M_N → 0` (dominated convergence, `ψ_N → 0` off the lattice, a Lebesgue-null set).
On the other hand `ψ_N µ → 1_Z µ(x₀)` boundedly (`µ ≡ µ(x₀)` on `Z` by periodicity), so `µ(x₀) ρ(Z) = 0`, and `µ(x₀) ≠ 0` gives `ρ(Z) = 0`.
The non-critical case has `Z = ∅` (`D > 0`). The generic part (`OccupationBound.lean:52`) is sound: `ψ β² = 2Lg - 2g'µ + (M/π)β²` for
`g'' = ψ - M/π`, constant `K = 16π + 8‖µ‖T + ‖β²‖T/π` independent of `ψ`. The measure-theoretic bridge (`OccupationNullSets.lean`): `min(1, n·dist(·, Oᶜ))`
is continuous and `π`-periodic for a periodic open `O` with nonempty complement, dominated convergence gives `∫1_O w dρ ≤ K·Leb(O∩(0,π])`; a null `N` lies
in an open `O'` of measure `< ε ≤ π`, its periodization is open, periodic, has nonempty complement (else `π ≤ vol O' < π`) and
`Leb(periodize O ∩ (0,π]) ≤ Leb(O)` (`volume_periodize_inter_Ioc_le`, a disjoint-union argument), so `∫1_N w dρ ≤ Kε` for all `ε`.

## 5. Consumers: PASS

- **Provider exports.** A Python pass over the manifest: 36 anchors have an `implementation`; for each, the module file exists and declares the
  `implementation.export` short name; `lake env lean .lake/probes/au-reroute/Exports.lean` (imports the 36 provider modules, `#check @<export>`)
  gives 36 successful lines and no error. The manifest `implementation` fields are unchanged versus `116be1c` (item 1), and no renamed
  declaration (`proposition_3_1_a_core`, `proposition_3_1_b_core`, `lemma_3_9`, `converse_w_o_upgrade`, `proposition_3_2_a_main`) is an export.
- **No module imports a deleted module.** `grep -rnE "HormanderOneDim|MarkovOneDim|AllZDensity|Stationary\.(KernelBasic|KernelInvariance|KernelLaw|Kolmogorov|SLEStat|SLEStatKernel|SLEStatLaw)\b" ComplexSLE tools lakefile.toml`
  prints nothing. The deleted Lean modules are those 10 (`git diff --name-status`: `D` ×10).
- **Build state.** `lake build --no-build` ends `All targets up-to-date (8054 jobs).` (113 replayed warnings: unused variables and long lines, none
  with `sorry`; the two new long lines are `ThetaSemigroup.lean:41` and `AdmissibleMeasure.lean:12`). Tracked Lean files 376 = files on disk 376, untracked 0.
  I also compiled the 34 new or touched load-bearing files directly (`lake env lean <file>`): no error, no warning, 1-3 s each. The harness works
  (a planted `rfl : 1 = 2` is rejected, a mutated proof step in a scratch copy of `ThetaSemigroup.lean` is rejected).
- `python3 -I tools/check_lean_modules.py --root . --max-lines 1500` -> `check_lean_modules: PASS (376 Lean files, 0 comparator configurations)`;
  the largest new file is `OccupationNullSets.lean` (279 lines); the largest file in the tree is `Polar/PolarThetaBrIto.lean` (697, pre-existing).

## 6. Graph gate: PASS

`python3 tools/proof_depgraph.py --db DEPGRAPH.md --manifest DEPGRAPH_COVERAGE.md --source-root . --require-reviewed
--require-complete-coverage --require-initial-lean-status --require-all-reachable --check`: exit 0, no output. Negative test: the same command
with `--db` a scratch copy whose `FROZEN_MANIFEST` hash is altered exits 1 with `FROZEN_MANIFEST sha256 does not match
frozen-anchor-manifest.json`, so the gate is live. `grep -n "markov_oneDim\|hormander_oneDim\|MarkovOneDim\|HormanderOneDim" DEPGRAPH.md DEPGRAPH_COVERAGE.md`
finds nothing; the source-level node `ext:hormander-1d` (DEPGRAPH.md:1797, `FROZEN_ANCHOR_ID: -`) remains as a paper input, see non-blocking note 4.

## 7. Docstrings (non-blocking)

Grep of `ComplexSLE/` for `hMO|MarkovOneDim|markov_oneDim|hormander_oneDim|IsDiffusionKernel|kernelOp|SLEStatKernel|AllZDensity|HormanderOneDim|of_markov`
gives 4 hits, all the same stale name; additional greps for "EXTERNAL", "pending Markov external", "Hörmander", "PROVED_REL" give the rest:

| Hit | Statement | Misstates a dependency? |
|---|---|---|
| `Internal/Recurrence/StatBridge.lean:20,35,143,210` | cites `map_addCircle_eq_of_markov`, deleted in R6 (it was `Stationary/Law.lean:200` at `116be1c`) | no (the file imports no Stationary module and assumes the law as a hypothesis); the replacement is `map_addCircle_thetaHat_prod_eq_admissible` |
| `Internal/Recurrence/Renewal.lean:35-36` | `hren` "is to be discharged by the pending Markov external" | no (an explicit hypothesis of a lemma; the strong Markov input is proved) but stale wording |
| `ComplexSLE/Frozen/Defs/{IsContLocalMartingale,IsSLEDriverAdapted,IsDiffusionSolution,PathIntegral}.lean` headers | "auxiliary vocabulary for the martingale-form external inputs, ERRATA.md R24, R25" | no; frozen files, cannot be edited without an author ruling |
| `Internal/Stationary/Occupation*.lean` | "the only classical input is `External.ito_formula`" | accurate (it is now proved in-project, `Internal/ExternalProofs/ItoFormula.lean`) |
| `Internal/Stationary/Coefficients.lean:54,150`, `KolmogorovDensity.lean:275` | `hormander_sqrt_two_mul_diffusionD`, `hormander_betaCrit`, `hormander_span_iff` | not docstrings; proved lemmas with 0 uses (see note 3) |

No docstring claims that a theorem depends on `hormander_oneDim`, `markov_oneDim` or on a still-EXTERNAL input.

## Fix list

Blocking: none.

Non-blocking:

1. Stale docstring: `Internal/Recurrence/StatBridge.lean:20,35,143,210` cite the deleted `map_addCircle_eq_of_markov` at HEAD. The orchestrator's
   uncommitted edit replaces it by `map_addCircle_thetaHat_prod_eq_admissible` (`InvarianceStationary.lean:128`); I read that diff (4 docstring lines,
   no code) but did not rebuild after it. It needs a commit.
2. Stale docstring: `Internal/Recurrence/Renewal.lean:35-36` ("pending Markov external"). Not introduced by R6, but it now reads as an open input.
3. Dead but harmless lemmas with 0 uses after R6: `hormander_sqrt_two_mul_diffusionD`, `hormander_betaCrit` (`Coefficients.lean`),
   `hormander_span_iff` (`KolmogorovDensity.lean`). They verify the paper's Hörmander-condition algebra (A.1), so keeping them is defensible; the
   R6 brief allowed leaving them.
4. `DEPGRAPH.md` is the source-level graph of the paper's proof and still lists `ext:hormander-1d` (a paper-level leaf with `LEAN_STATUS: EXTERNAL`,
   no frozen anchor) used by Lemma A.2's steps. This is accurate for the paper; the project's Lean route (R31) bypasses it. A one-line NOTE on that node
   would avoid a reader inferring a Lean dependency. (Orchestrator-owned file; the gate does not require it.)
5. At the end of the audit `README.md`, `RESULTS.md`, `STATUS.md` and `StatBridge.lean` had uncommitted edits and `briefs/M10-RESULTS-final.md` was untracked. Their claims
   that I could check agree with this audit (376 files, 60 anchors, manifest `a482663a…`, 36 sealed theorems all `PROVED`, 0 `PROVED_REL`, 8 externals deleted in
   total). They should be committed together with this report.
6. Two new long-line warnings (`ThetaSemigroup.lean:41`, `AdmissibleMeasure.lean:12`); the R6 brief allowed long lines only. Cosmetic.
7. Before public release: the license of the Zipper port remains open (R30), unchanged by this campaign.
