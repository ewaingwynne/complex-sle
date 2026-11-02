# M10-R3: the semigroup of θ̂ (Chapman–Kolmogorov, periodicity, Feller, Dynkin)

Context: M10 re-route of the last two externals (`review/plans/M10-reroute.md`, step 1). The goal is to build the
Markov semigroup of the concrete process `θ̂` directly from the in-project strong Markov restart, without any
transition kernel.

Ownership: new files `ComplexSLE/Internal/Stationary/ThetaSemigroup*.lean` (namespace `ComplexSLE.Internal`, with
`open Polar`). Edit no existing file.

**Forbidden imports.** Do not import, directly or transitively, `ComplexSLE.External.HormanderOneDim`,
`ComplexSLE.External.MarkovOneDim`, or any module that imports them. In particular, these are forbidden:
- `Stationary/SLEStat*.lean`, `Stationary/PathStat.lean`, `Stationary/KernelLaw.lean`;
- `Phases/*` except `AllZLebesgue` and what it imports.

Check every import with `python3 .lake/probes/closure.py <Module>`, which must print `clean`.

Useful modules that are clean:
- `Stationary/ThetaHatSolution` (`ae_thetaHat_zero`, `isDiffusionSolution_thetaHat_of_sq`, `unitPt_ne_zero`);
- `Stationary/PathStatKernel` (`driverLaw`, `obsKernel`, `obsKernel_add_pi`, `periodic_eq_comp_exp`);
- `Stationary/PathStatRestart` (`lintegral_pathObsAt`, `pathObsAt`);
- `Stationary/PathStatMeas` (`thetaC`, `thetaHat_eq_thetaC`, `obsC`, `polarInc`);
- `Stationary/ItoReal` (`generator`, `IsDiffusionSolution.integral_sub_integral_eq`, `pathIntegral`);
- `Polar/PolarThetaHat` (`ae_thetaHat_eq_and_continuous`);
- `Polar/PolarContArg` (`continuousAt_argPath_sub_initial`, `continuousAt_exp_argPath_sigmaTime_initial`);
- `Polar/PolarContClock` (`isOpen_sigmaDomSet`);
- `Polar/PolarContMeas` (`measurable_thetaHat_unit`);
- `Infrastructure/Stochastic/ContinuousModification`.

Definition (exactly this):

```lean
/-- `Q_t f(u) = E f(θ̂_t(e^{iu}))`. -/
@[expose] noncomputable def thetaSemigroup (hU : IsSLEDriverAdapted a b c U P ℱ) (t : ℝ≥0) (f : ℝ → ℝ)
    (u : ℝ) : ℝ :=
  ∫ ω, f (thetaHat hU (unitPt u) t ω) ∂P
```

Results to prove. Assume throughout `[IsProbabilityMeasure P]`, `hU : IsSLEDriverAdapted a b c U P ℱ`, `ha : 0 < a`,
`hb : 0 < b`, `hc : c ^ 2 ≤ a * b`. Take only the hypotheses each item needs; binder names and order are yours.
"Bounded" below means `∃ C, ∀ v, |f v| ≤ C`.
1. `measurable_thetaSemigroup`: if `f` is measurable then `thetaSemigroup hU t f` is measurable (joint measurability
   plus `StronglyMeasurable.integral_prod_right'` or similar). Also give a bound lemma, `|Q_t f u| ≤ C`.
2. `thetaSemigroup_periodic`: if `f` is measurable, bounded and `π`-periodic, so is `Q_t f`, i.e.
   `Function.Periodic (thetaSemigroup hU t f) π`. The `2π` shift is trivial since `unitPt (u + 2π) = unitPt u`.
   For the `π` shift, express `Q_t f(β)` as an `obsKernel (driverLaw hU) F β` (it suffices for `f + C ≥ 0`) and use
   `obsKernel_add_pi`. Alternatively use the reflection lemmas behind it directly.
3. `continuous_thetaSemigroup` (Feller): if `f` is continuous and `π`-periodic then `Q_t f` is continuous.
   - Fix `u₀` and a sequence `uₙ → u₀`, and apply dominated convergence.
   - For a.e. `ω` (`ae_thetaHat_eq_and_continuous` at `z = unitPt u₀`, plus `U 0 ω = 0`),
     `f(θ̂_t(e^{iuₙ})(ω)) → f(θ̂_t(e^{iu₀})(ω))`. Write `f(θ̂_t(e^{iu})) = f((θ̂_t - θ̂_0)(e^{iu}) + u)`: here
     `θ̂_0(e^{iu}) ≡ u (mod 2π)` pathwise when `U 0 ω = 0`, and `f` is `2π`-periodic.
   - The winding `θ̂_t - θ̂_0` is continuous in `z` at `z₀` (`continuousAt_argPath_sub_initial`), and
     `t ∈ sigmaDom` is open in `z` (`isOpen_sigmaDomSet`), so `thetaHat` agrees with `argPath ∘ sigmaTime` near
     `z₀`. `unitPt` is continuous.
4. `thetaSemigroup_add` (Chapman–Kolmogorov): if `f` is measurable, bounded and `π`-periodic then
   `thetaSemigroup hU (s + t) f u = thetaSemigroup hU s (thetaSemigroup hU t f) u`. Route:
   - `lintegral_pathObsAt` (strong Markov at `σ_z(s)`, `z = unitPt u`) applied to
     `F(ξ, inc, _) = ENNReal.ofReal (f(arg ξ / 2 + inc t) + C)`. The first coordinate of `Ξ_s` is
     `e^{2iθ̂_s}`; use `periodic_eq_comp_exp`, which handles the `π` ambiguity of `arg ξ / 2`.
   - Inside, `θ̂_s + (thetaC t w e^{iβ} - thetaC 0 w e^{iβ})` is congruent to `thetaC t w e^{iβ}` mod `2π` for
     `Λ`-a.e. `w`, since `thetaC 0 w e^{iβ} ≡ β`.
   - `∫ f(thetaC t w e^{iβ}) dΛ(w) = Q_t f(β)`, by `thetaHat_eq_thetaC` and `integral_map`.
   - Convert between `lintegral` and `integral` with the shift `+ C`.
5. `continuous_thetaSemigroup_time`: if `f` is continuous and bounded then `t ↦ thetaSemigroup hU t f u` is
   continuous (a.s. path continuity, then dominated convergence).
6. `thetaSemigroup_sub_self` (Dynkin): for `β` continuous with `∀ v, β v ^ 2 = 2 * diffusionD a b c v`, and `g` with
   `ContDiff ℝ 2 g` and `Function.Periodic g π`,
   `thetaSemigroup hU t g u - g u =
      ∫ s in (0 : ℝ)..(t : ℝ), thetaSemigroup hU s.toNNReal (generator (mu a b c) β g) u`.
   - Apply `integral_sub_integral_eq` to an everywhere-continuous version of `θ̂(e^{iu})`. A
     continuous modification exists: see `IsDiffusionKernel.exists_continuous_solution` in `KernelBasic.lean` for
     the pattern, or modify on the null set directly.
   - Use `g(θ̂_0) = g(u)` a.s. (`ae_thetaHat_zero`, `2π`-periodicity), boundedness of `g` and `Lg` (both
     continuous and periodic), and Fubini for `pathIntegral`.

Checks:
- `lake build` of each new module;
- `python3 -I tools/leanprobe.py axioms ComplexSLE.Internal.Stationary.ThetaSemigroup<...> ComplexSLE.Internal.<name>`
  for each item, which must report only propext, Classical.choice and Quot.sound;
- `python3 .lake/probes/closure.py ComplexSLE.Internal.Stationary.ThetaSemigroup<...>`, which must print `clean`.

Each file must be a module of at most 1500 lines.

If an item does not close within budget, land the finished items sorry-free and report exactly what is left. Never
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
