# M10-R1: the periodic Poisson equation (non-degenerate case, maximum principle, choice of the constant)

Context: M10 re-route of the last two externals (`review/plans/M10-reroute.md`, step 2). This packet is pure real
analysis. It imports only Mathlib and `ComplexSLE.Infrastructure.*`.

Ownership: new file(s) `ComplexSLE/Infrastructure/PeriodicODE/Poisson*.lean` (namespace `ComplexSLE.Infrastructure`).
Do not touch `PeriodicODE/DoubleZero*.lean`, which belongs to the critical-case packet.

Prove sorry-free (the exact statements are below; you may weaken hypotheses, never strengthen them):

```lean
/-- Maximum principle: a `C²` periodic `g` whose generator `α g' + D g''` (`D ≥ 0`) is a constant
`C` has `C = 0`. -/
theorem eq_zero_of_periodic_generator_eq_const {α D g : ℝ → ℝ} {T C : ℝ} (hT : 0 < T)
    (hD : ∀ u, 0 ≤ D u) (hg : ContDiff ℝ 2 g) (hgper : Function.Periodic g T)
    (h : ∀ u, α u * deriv g u + D u * deriv (deriv g) u = C) : C = 0

/-- From periodic `C¹` solutions of `D h' + α h = r` and of `D h' + α h = 1` to the periodic
Poisson equation `α g' + D g'' = r - C`. -/
theorem exists_periodic_poisson_of_solutions {α D r h₁ hr : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hD : ∀ u, 0 ≤ D u) (h₁c : ContDiff ℝ 1 h₁) (h₁per : Function.Periodic h₁ T)
    (h₁eq : ∀ u, D u * deriv h₁ u + α u * h₁ u = 1) (hrc : ContDiff ℝ 1 hr)
    (hrper : Function.Periodic hr T) (hreq : ∀ u, D u * deriv hr u + α u * hr u = r u) :
    ∃ C : ℝ, ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ Function.Periodic g T ∧
      ∀ u, α u * deriv g u + D u * deriv (deriv g) u = r u - C

/-- The periodic Poisson equation when `D > 0` everywhere. -/
theorem exists_periodic_poisson_of_pos {α D r : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hα : Continuous α) (hD : Continuous D) (hDpos : ∀ u, 0 < D u) (hr : Continuous r)
    (hαper : Function.Periodic α T) (hDper : Function.Periodic D T)
    (hrper : Function.Periodic r T) :
    ∃ C : ℝ, ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ Function.Periodic g T ∧
      ∀ u, α u * deriv g u + D u * deriv (deriv g) u = r u - C
```

Route:
1. **Maximum principle.** A continuous periodic `g` attains its maximum at some `x*` (compactness of `[0, T]`).
   There `deriv g x* = 0` (`IsLocalMax.deriv_eq_zero`) and `deriv (deriv g) x* ≤ 0`. For the latter: if it were
   `> 0`, then `g'` would be strictly positive just to the right of `x*` and `g` would increase there; prove this
   small lemma. Hence `C = D g'' ≤ 0`. Symmetrically `C ≥ 0` at the minimum.
2. **From solutions to Poisson.**
   - First, `∫₀ᵀ h₁ ≠ 0`. Otherwise `g₁(x) = ∫₀ˣ h₁` would be `C²` and periodic with generator `≡ 1`,
     contradicting 1.
   - Put `C = (∫₀ᵀ hr) / ∫₀ᵀ h₁`, `h = hr - C h₁` and `g(x) = ∫₀ˣ h`.
   - Then `g' = h`, which is `C¹`, so `g` is `C²`; `g` is periodic because `h` is periodic with `∫₀ᵀ h = 0`.
   - `α g' + D g'' = α h + D h' = r - C`.
3. **Non-degenerate case.**
   - With `a = α/D`, `A(x) = ∫₀ˣ a` and `ρ_s = (r - s)/D`, every solution of `D h' + α h = r - s` is
     `h = e^{-A}(K + ∫₀ˣ e^{A} ρ_s)`.
   - The two conditions "`h(T) = h(0)`" and "`∫₀ᵀ h = 0`" are affine in `(K, s) ∈ ℝ²`.
     - `h(T) = h(0)` implies `h` periodic: `x ↦ h(x + T)` solves the same equation with the same initial value,
       and uniqueness is immediate from `(e^{A} h)' = e^{A} ρ_s` together with `A(x + T) = A(x) + A(T)`.
   - Their linear part is injective. If `r = 0` and `h` is a periodic, mean-zero solution of
     `D h' + α h = -s`, then `g = ∫₀ˣ h` is periodic and `C²` with generator `≡ -s`. So `s = 0` by 1, and then
     `h = K e^{-A}` with mean `0` forces `K = 0`.
   - An injective linear map `ℝ² → ℝ²` is surjective (`LinearMap.injective_iff_surjective`, or a direct
     determinant argument). So there is `(K, s)` solving both conditions, and `g = ∫₀ˣ h`, `C = s` works.

   Alternatively, derive this case from 2 when `A(T) ≠ 0`, and handle `A(T) = 0` by adding `K e^{-A}`. Choose
   whichever is shorter.

Useful Mathlib: `intervalIntegral.integral_hasDerivAt_right`, `Function.Periodic.intervalIntegral_add_eq`,
`intervalIntegral.integral_comp_add_right`, `IsCompact.exists_isMaxOn`, `Function.Periodic.exists_mem_Ico₀`,
`IsLocalMax.deriv_eq_zero`, `ContDiff.iterate_deriv`, `contDiff_succ_iff_deriv`.

Checks:
- `lake build ComplexSLE.Infrastructure.PeriodicODE.Poisson`;
- `python3 -I tools/leanprobe.py axioms ComplexSLE.Infrastructure.PeriodicODE.Poisson ComplexSLE.Infrastructure.<name>`
  for each of the three theorems, which must report only propext, Classical.choice and Quot.sound.

Each file must be a module of at most 1500 lines.

If a theorem does not close within budget, land the finished ones sorry-free and report exactly what is left. Never
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
