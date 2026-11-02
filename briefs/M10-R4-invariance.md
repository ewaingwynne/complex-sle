# M10-R4: invariance of ν under the semigroup of θ̂, and hMO-free one-time stationarity

Context: M10 re-route of the last two externals (`review/plans/M10-reroute.md`, steps 2–4). Everything here must be
free of `hormander_oneDim` and `markov_oneDim`.

Ownership: new files `ComplexSLE/Internal/Stationary/Invariance*.lean` (namespace `ComplexSLE.Internal`,
`open Polar`). Edit no existing file.

**Forbidden imports.** Do not import, directly or transitively, `ComplexSLE.External.HormanderOneDim`,
`ComplexSLE.External.MarkovOneDim`, or any module that imports them: `SLEStat*`, `PathStat.lean`, `KernelLaw`,
`Phases/ErgodicMean` and so on. Check with `python3 .lake/probes/closure.py <Module>`, which must print `clean`.

Inputs, all clean:
- `Infrastructure/PeriodicODE/Poisson*`: `exists_periodic_poisson_of_pos`, `exists_periodic_poisson_of_solutions`,
  `eq_zero_of_periodic_generator_eq_const`;
- `Infrastructure/PeriodicODE/DoubleZero*`: `exists_periodic_solution_of_doubleZero`;
- `Stationary/CriticalCoefficients`: `exists_zero_lattice_diffusionD`;
- `Stationary/ThetaSemigroup*`: `thetaSemigroup` and its lemmas — measurability, bound, periodicity, Feller
  continuity, Chapman–Kolmogorov `thetaSemigroup_add`, time continuity, Dynkin `thetaSemigroup_sub_self`. Read the
  actual names and hypotheses in the files;
- `Stationary/AdmissibleMeasure`: `admissibleMeasure`, `integral_admissibleMeasure`,
  `isProbabilityMeasure_admissibleMeasure`, `integral_two_pi_eq_two_mul_pi`;
- `Stationary/KolmogorovDensity`: `IsAdmissibleDensity.isKolmogorovDensity`,
  `IsKolmogorovDensity.integral_generator_eq_zero`;
- `Stationary/Law`: `map_addCircle_eq_of_forall_integral_eq`, `map_exp_eq_of_forall_integral_eq`; read how it uses
  trigonometric-polynomial density;
- `Stationary/ItoReal`: `generator`;
- `Polar/PolarContMeas`: `measurable_thetaHat_unit`;
- `Stationary/Coefficients`: `exists_beta`-type facts, `sq_sqrt_two_mul_diffusionD`, `betaCrit`, `sq_betaCrit`.

Assume throughout `[IsProbabilityMeasure P]`, `hU : IsSLEDriverAdapted a b c U P ℱ`, `0 < a`, `0 < b`, `c ^ 2 ≤ a * b`,
and `hp : IsAdmissibleDensity a b c p`. Write `ν = admissibleMeasure p`.

Steps:
1. `exists_poisson_generator`: for `β` with `β² = 2D` and `f` with `ContDiff ℝ 2 f` and period `π`, there exist `C`
   and a `C²`, `π`-periodic `g` with `∀ u, generator (mu a b c) β g u = f u - C`. Note
   `generator μ β g = g' μ + ½ g'' β² = μ g' + D g''`.
   - Non-critical (`c² < ab`): use `exists_periodic_poisson_of_pos`.
   - Critical (`c² = ab`): apply `exists_periodic_solution_of_doubleZero` with `r = f` and with `r = 1`, at the
     `x₀` of `exists_zero_lattice_diffusionD`, then `exists_periodic_poisson_of_solutions`.
2. `poisson_const_eq`: in 1, `C = ∫ f dν`. By `integral_generator_eq_zero` for the Kolmogorov density `2p`,
   `∫₀^π (f - C)·2p = 0`; then use `integral_two_pi_eq_two_mul_pi` and `integral_admissibleMeasure`.
3. **Cesàro convergence.** For `f` that is `C²` and `π`-periodic, and every `u`:
   `Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0)..T, thetaSemigroup hU t.toNNReal f u) atTop (𝓝 (∫ f dν))`.
   By Dynkin, `∫₀ᵀ Q_t (Lg) u dt = Q_T g u - g u`, which is bounded by `2 sup |g|`, and `Q_t (f - C) = Q_t f - C`.
4. Extend 3 to continuous `π`-periodic `f`, by uniform approximation with `C²` (for example trigonometric) periodic
   functions; `|Q_t f - Q_t f'| ≤ sup |f - f'|`.
5. **Invariance.** For continuous `π`-periodic `f` and every `s`:
   `∫ u, thetaSemigroup hU s f u ∂ν = ∫ u, f u ∂ν`.
   - `h = Q_s f` is continuous and `π`-periodic (Feller, periodicity). Apply 4 to `h` at any point `u`.
   - Chapman–Kolmogorov gives `Q_t h = Q_{t+s} f`, and
     `T⁻¹∫₀ᵀ Q_{t+s} f - T⁻¹∫₀ᵀ Q_t f → 0`, since the two differ by at most `2 s sup|f| / T`.
   - So both limits are equal, i.e. `∫ h dν = ∫ f dν`. Uniqueness of limits.
6. **hMO-free one-time stationarity.** These are the statements of the existing theorems
   `integral_comp_thetaHat_prod_of_markovOneDim` (`Phases/ErgodicMean.lean`),
   `map_addCircle_thetaHat_prod_eq_of_markovOneDim` and `map_exp_thetaHat_prod_eq_of_markovOneDim`
   (`Stationary/SLEStat.lean`), but **without the `hMO` binder** and under new names:

   ```lean
   theorem integral_comp_thetaHat_prod_admissible [IsProbabilityMeasure P]
       (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
       {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (s : ℝ≥0) {f : ℝ → ℝ} (hf : Continuous f)
       (hfper : Function.Periodic f π) :
       ∫ q, f (thetaHat hU (unitPt q.2) s q.1) ∂(P.prod (admissibleMeasure p)) =
         ∫ u, f u ∂(admissibleMeasure p)

   theorem map_addCircle_thetaHat_prod_eq_admissible [IsProbabilityMeasure P]
       (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b)
       (hc : c ^ 2 ≤ a * b) {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (s : ℝ≥0) :
       (P.prod (admissibleMeasure p)).map
           (fun q : Ω × ℝ => ((thetaHat hU (unitPt q.2) s q.1 : ℝ) : AddCircle π)) =
         (admissibleMeasure p).map ((↑) : ℝ → AddCircle π)

   theorem map_exp_thetaHat_prod_eq_admissible [IsProbabilityMeasure P]
       (hU : IsSLEDriverAdapted a b c U P ℱ) (ha : 0 < a) (hb : 0 < b)
       (hc : c ^ 2 ≤ a * b) {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) (s : ℝ≥0) :
       (P.prod (admissibleMeasure p)).map
           (fun q : Ω × ℝ => Complex.exp (2 * Complex.I * (thetaHat hU (unitPt q.2) s q.1 : ℝ))) =
         (admissibleMeasure p).map (fun u : ℝ => Complex.exp (2 * Complex.I * u))
   ```

   - The first follows from 5 by Fubini (`integral_prod_symm`), as in `integral_comp_thetaHat_prod` in
     `SLEStat.lean`.
   - The other two follow from it as in `map_addCircle_thetaHat_prod_eq_of_kernel` and
     `map_exp_thetaHat_prod_eq_of_kernel`; read those proofs, but do not import their module.

   Pick the hypotheses as stated. If one of them is not needed, keep it anyway: the consumers will call these
   theorems with exactly this signature.

Checks:
- `lake build` of each new module;
- `python3 -I tools/leanprobe.py axioms <Module> ComplexSLE.Internal.<name>` for the three theorems of step 6 and for
  `exists_poisson_generator`, which must report only propext, Classical.choice and Quot.sound;
- `python3 .lake/probes/closure.py <Module>`, which must print `clean`.

Each file must be a module of at most 1500 lines.

If an item does not close within budget, land the finished ones sorry-free and report exactly what is left. Never
leave a `sorry`.

Handoff: files, approach, commands and output, axioms, what is left.

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
11. Do not spawn subagents, forks or parallel workers of your own (the orchestrator enforces a two-agent cap).
