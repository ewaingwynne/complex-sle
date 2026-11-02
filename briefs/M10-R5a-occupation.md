# M10-R5a: occupation of null sets by θ̂, and the critical-case coefficients

Context: M10 re-route of the last two externals (`review/plans/M10-reroute.md`, step 5). This replaces the
Lebesgue density of `law θ̂_1(z)`, which came from the Hörmander external, by a weaker fact that is enough for
Lemma 3.3: `θ̂(z)` spends zero time in any Lebesgue-null set.

Ownership: new files `ComplexSLE/Internal/Stationary/Occupation*.lean` and
`ComplexSLE/Internal/Stationary/CriticalCoefficients.lean` (namespace `ComplexSLE.Internal`). Edit no existing file.

**Forbidden imports.** Do not import, directly or transitively, `ComplexSLE.External.HormanderOneDim`,
`ComplexSLE.External.MarkovOneDim`, or any module that imports them. In particular these are forbidden:
- `Stationary/SLEStat*`, `Stationary/PathStat.lean`, `Stationary/KernelLaw`;
- `Phases/AllZ.lean`, `Phases/AllZDensity.lean`.

Check with `python3 .lake/probes/closure.py <Module>`, which must print `clean`.

Clean and useful modules:
- `Stationary/ItoReal`: `generator`, `IsDiffusionSolution.integral_sub_integral_eq`, `pathIntegral`;
- `Stationary/ThetaHatSolution`: `isDiffusionSolution_thetaHat_of_sq`;
- `Stationary/Coefficients`: `betaCrit`, `sq_betaCrit`, `hormander_betaCrit`, `contDiff_betaCrit`;
- `Polar/PolarThetaHat`: `isDiffusionSolution_thetaHat`, `ae_thetaHat_eq_and_continuous`;
- `Density/Basic`: `mu_periodic`, `diffusionD_periodic`, `diffusionD_pos`, `contDiff_mu`;
- `Infrastructure/Stochastic/ContinuousModification`;
- `Stationary/KernelBasic`: `exists_continuous_solution`, a pattern for continuous versions.

## Part A: the critical-case coefficients (`CriticalCoefficients.lean`)

For `0 < a`, `0 < b`, `c ^ 2 = a * b`:

```lean
theorem exists_zero_lattice_diffusionD (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a * b) :
    ∃ x₀ : ℝ, (∀ u, diffusionD a b c u = 0 ↔ ∃ n : ℤ, u = x₀ + n * π) ∧
      0 < deriv (deriv (diffusionD a b c)) x₀ ∧ mu a b c x₀ ≠ 0
```

Hint: `betaCrit a c u = √a sin u - (c/√a) cos u = R sin (u - x₀)`, with `R > 0` and `x₀ = arctan (c/a)`.
Then `D = β²/2`, so `D'' = β'² + β β''`, and at a zero this equals `β'(x₀)² = R² > 0`. Also `μ(x₀) ≠ 0` by
`hormander_betaCrit`.

## Part B: occupation estimates (`Occupation*.lean`)

Let `X` satisfy `IsDiffusionSolution ℱ (mu a b c) β X P`, with every path continuous, `β` continuous and
`∀ v, β v ^ 2 = 2 * diffusionD a b c v`, where `0 < a`, `0 < b`, `c ^ 2 ≤ a * b`. Prove:

```lean
theorem ae_volume_occupation_null ... {N : Set ℝ} (hN : volume N = 0) (T : ℝ) :
    ∀ᵐ ω ∂P, volume {t : ℝ | t ∈ Set.Icc 0 T ∧ X t.toNNReal ω ∈ N} = 0
```

Then the θ̂ form, for `hU : IsSLEDriverAdapted a b c U P ℱ`, `z ≠ 0` and `volume N = 0`:

```lean
theorem exists_pos_measure_thetaHat_preimage_eq_zero ... :
    ∃ t : ℝ≥0, 0 < t ∧ P ((thetaHat hU z t) ⁻¹' N) = 0
```

Derive it from the first through a continuous version of `θ̂(z)`, or by the a.s. continuity directly, plus
Fubini on `[1, 2] × Ω`.

Route for Part B:
1. WLOG `N` is `π`-periodic: replace it by `⋃ n : ℤ, (· + n * π) ⁻¹' N`, which is still null.
2. **Dynkin bound.** For continuous, `π`-periodic `ψ ≥ 0` with mean `m = (1/π)∫₀^π ψ`, let `g` be `C²` and
   periodic with `g'' = ψ - m`:
   - take `G₁(x) = ∫₀ˣ (ψ - m)` (periodic, since it has mean zero over a period), subtract its mean to get `g'`,
     and integrate once more;
   - then `|g'| ≤ 2πm` and `|g| ≤ π·2πm` up to constants.

   `integral_sub_integral_eq` gives `E∫₀ᵀ (g'μ + ½(ψ - m)β²)(X) = E g(X_T) - E g(X_0)`. Hence
   `E∫₀ᵀ ψ(X)β²(X) dt ≤ C_T · m`, with `C_T` depending only on `T`, `sup |μ|` and `sup β²`.
3. **From continuous `ψ` to null sets.**
   - For open periodic `O`, use `ψₙ = min 1 (n · infDist x Oᶜ) ↑ 1_O` (continuous, periodic) and monotone
     convergence: `E∫₀ᵀ 1_O(X)β²(X) ≤ C_T · volume (O ∩ [0, π]) / π`.
   - For null periodic `N`, take open `O ⊇ N ∩ [-π, 2π]` of small measure and periodize it (the measure of the
     periodization on `[0, π]` is at most `volume O`). This gives `E∫₀ᵀ 1_N(X)β²(X) = 0`.
4. **Non-critical case** (`c² < ab`): `β² ≥ 2 min D > 0`, so `E Leb{t ≤ T : X_t ∈ N} = 0`.
5. **Critical case** (`c² = ab`). `β² > 0` off `Z = x₀ + πℤ` (Part A), so 3 gives `Leb{t : X_t ∈ N \ Z} = 0` a.s.
   It remains to show `E Leb{t ≤ T : X_t ∈ Z} = 0`:
   - Let `ψ` be a smooth bump with `ψ(0) = 1` and `0 ≤ ψ ≤ 1`, supported in `[-1, 1]`. Let `ψ_ε` be the periodized
     `ψ((x - x₀)/ε)`, and let `g_ε` be periodic `C²` with `g_ε' = ψ_ε - mean ψ_ε`.
   - Then `|g_ε| = O(ε)`, and `|D g_ε''| = D |ψ'|/ε ≤ K ε` on the support, since `D ≤ K (x - x₀)²` near `x₀`.
     Dynkin therefore gives `|E∫₀ᵀ μ(X) ψ_ε(X)| = O(ε)`.
   - As `ε → 0`, `ψ_ε → 1_Z` boundedly, so `μ(x₀) E∫₀ᵀ 1_Z(X) = 0` (`μ` is `π`-periodic). Conclude with
     `μ(x₀) ≠ 0`.
   - Any `C²` bump works: if you prefer, a piecewise polynomial `C²` bump, or `Real.smoothTransition`-based
     `ContDiffBump`.

Checks:
- `lake build` of each new module;
- `python3 -I tools/leanprobe.py axioms <Module> ComplexSLE.Internal.<name>` for every main theorem, which must report
  only propext, Classical.choice and Quot.sound;
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
