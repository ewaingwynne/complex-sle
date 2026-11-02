# M10-R2: the periodic first-order ODE with a double zero of the leading coefficient

Context: M10 re-route of the last two externals (`review/plans/M10-reroute.md`, step 2, critical case). This packet is
pure real analysis. It imports only Mathlib and `ComplexSLE.Infrastructure.*`.

Goal: prove, sorry-free, in new files `ComplexSLE/Infrastructure/PeriodicODE/DoubleZero*.lean`
(namespace `ComplexSLE.Infrastructure`):

```lean
theorem exists_periodic_solution_of_doubleZero {α D r : ℝ → ℝ} {T x₀ : ℝ} (hT : 0 < T)
    (hα : ContDiff ℝ 2 α) (hD : ContDiff ℝ 2 D) (hr : ContDiff ℝ 2 r)
    (hαper : Function.Periodic α T) (hDper : Function.Periodic D T) (hrper : Function.Periodic r T)
    (hD0 : ∀ u, 0 ≤ D u) (hDzero : ∀ u, D u = 0 ↔ ∃ n : ℤ, u = x₀ + n * T)
    (hD2 : 0 < deriv (deriv D) x₀) (hαx₀ : α x₀ ≠ 0) :
    ∃ h : ℝ → ℝ, ContDiff ℝ 1 h ∧ Function.Periodic h T ∧
      ∀ u, D u * deriv h u + α u * h u = r u
```

(You may weaken the hypotheses, e.g. `ContDiff ℝ 1 α` if it suffices. Do not strengthen them.)

Mathematical route (it is checked; follow it unless you find a simpler correct one):
0. WLOG `α x₀ > 0`. Reflect: `h̃(u) = h(2x₀ - u)` solves the equation for `D̃(u) = D(2x₀-u)`,
   `α̃(u) = -α(2x₀-u)`, `r̃(u) = -r(2x₀-u)`, with the same lattice. Or treat both signs directly.
1. Taylor facts at `x₀`: `D x₀ = 0` and `deriv D x₀ = 0` (minimum). Near `x₀`, `c y² ≤ D(x₀+y) ≤ C y²`.
   `D > 0` off the lattice.
2. Subtract a smooth `T`-periodic `φ` with prescribed `φ(x₀), φ'(x₀), φ''(x₀)`, for instance a combination of
   `1`, `sin (2π(x-x₀)/T)` and `1 - cos (2π(x-x₀)/T)`, chosen so that `r̃ := r - (D φ' + α φ)` satisfies
   `r̃(x₀) = r̃'(x₀) = r̃''(x₀) = 0`. This is a triangular linear system whose diagonal is a nonzero multiple of
   `α x₀`, since `D x₀ = D' x₀ = 0`. Then `ρ := r̃ / D` off the lattice and `ρ := 0` on it is continuous and
   `T`-periodic: `r̃ = o(y²)` by Taylor with Lagrange remainder, and `D ≥ c y²`.
3. On `I = (x₀, x₀ + T)` set `a = α / D` and `A(x) = ∫_{m}^{x} a` for the midpoint `m`.
   - As `x → x₀⁺`, `A → -∞`; as `x → (x₀+T)⁻`, `A → +∞`.
   - Use `a ≥ c'/y²` near the ends, where `y` is the distance to the end. This holds because `α > 0` near both
     ends by periodicity.
   - Define `H(x) = e^{-A(x)} ∫_{x₀}^{x} e^{A(y)} ρ(y) dy`. The integrand is bounded near `x₀`.
   - `H` is `C¹` on `I` with `H' = ρ - a H`, so `D H' + α H = D ρ = r̃`.
4. Key bound. Near either end, `α > 0` and `|(D/α)'| ≤ 1/2`, and
   `d/dy [e^{A} D/α] = e^{A} (1 + (D/α)') ≥ e^{A}/2`. So `∫_{x₁}^{x} e^{A} ≤ 2 e^{A(x)} (D/α)(x)`
   (drop the nonnegative boundary term at `x₁`; at `x₀⁺` the boundary term tends to `0`). Hence:
   - at `x₀⁺`: `|H| ≤ 2 sup_{(x₀,x]} |ρ| · D/α → 0`, and `|a H| ≤ 2 sup_{(x₀,x]} |ρ| → 0`;
   - at `(x₀+T)⁻`, split the integral at a fixed `x₁` near the end:
     - the far piece is `K e^{-A(x)}`, and both it and `a K e^{-A(x)}` tend to `0`, because
       `A(x) ≥ c'/y - C` and `a ≤ C/y²`;
     - the near piece is bounded as at `x₀⁺`, by `2 sup_{[x₁, x]} |ρ|`, which is small for `x₁` close to the end.

   So `H → 0` and `H' → 0` at both ends.
5. Set `h = φ + H̄`, with `H̄` the `T`-periodic extension of `H` and `H̄ = 0` on the lattice.
   - At lattice points, `h` is continuous and `h'` has the limit `φ'(x₀)` from both sides. Mathlib's
     `hasDerivAt_of_hasDerivAt_of_ne` (or a variant) gives differentiability, so `h` is `C¹`.
   - The equation holds on the lattice because `D = 0` there and `α x₀ φ(x₀) = r(x₀)`.

Useful Mathlib: `taylor_mean_remainder_lagrange`, `intervalIntegral.integral_hasDerivAt_right`,
`intervalIntegral.integral_comp_add_right`, `toIcoMod`/`toIcoDiv` (periodic extension),
`Function.Periodic`, `ContDiff.continuous_deriv`, `hasDerivAt_of_hasDerivAt_of_ne`, `tendsto_nhdsWithin_*`.
`ComplexSLE/Infrastructure/PeriodicGlue.lean` may help with the periodic gluing; read it first.

Checks:
- `lake build ComplexSLE.Infrastructure.PeriodicODE.DoubleZero` (plus every helper file);
- `python3 -I tools/leanprobe.py axioms ComplexSLE.Infrastructure.PeriodicODE.DoubleZero ComplexSLE.Infrastructure.exists_periodic_solution_of_doubleZero`,
  which must report only propext, Classical.choice and Quot.sound.

Every new file must be a module of at most 1500 lines. Split the work into several files, for example: Taylor and
residual; the integrating factor and the bounds; the gluing.

If the theorem does not close within budget, land the finished lemmas sorry-free and report exactly what is left.
Never leave a `sorry`.

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
