# M10 re-route of the last two externals (author chose (a), 2026-11-02) — DONE (R31, AU-M10-reroute PASS)

Goal: remove `hormander_oneDim` and `markov_oneDim` by re-proving their four uses, with no
Hörmander smoothing and no uniqueness in law. No frozen statement changes.

## Design

Write `Q_t f(u) = E f(θ̂_t(e^{iu}))` for the semigroup of the concrete process θ̂, and
`L g = µ g' + D g''` (`generator µ β`, with `β² = 2D`).

1. **Semigroup facts for θ̂** (R3). These come from the in-project strong Markov restart and polar
   continuity, with no externals:
   - Chapman–Kolmogorov: `Q_{s+t} f = Q_s (Q_t f)`, from `lintegral_pathObsAt`;
   - π-periodicity of `Q_t f`, from the reflection `obsKernel_add_pi`;
   - Feller: `Q_t f` is continuous for continuous π-periodic `f`, from
     `continuousAt_exp_argPath_sigmaTime_initial` and dominated convergence;
   - continuity of `t ↦ Q_t f(u)`;
   - Dynkin: `Q_t g - g = ∫₀ᵗ Q_s(Lg) ds` for `C²` periodic `g`, from `integral_sub_integral_eq`.
2. **Periodic Poisson equation** (R1, R2). This is pure ODE. For every `C²` π-periodic `f` there are a constant `C`
   and a `C²` π-periodic `g` with `L g = f - C`.
   - With `h = g'` the equation reads `D h' + µ h = f - C`.
   - **Non-critical case (`D > 0`, R1).** Use the explicit integrating-factor solution. The unknowns
     `(K, C)` are fixed by periodicity and `∫h = 0`; this is a 2×2 linear system, injective by the
     maximum principle (`L g ≡ const` with `g` periodic forces the constant to be 0) together with
     `e^{-A} > 0`.
   - **Critical case (`D` has a double zero at `x₀ + πℤ`, `µ(x₀) ≠ 0`, R2).**
     - Subtract `φ = A₀ + A₁ sin 2(x-x₀) + A₂(1 - cos 2(x-x₀))`, chosen (by a triangular system with
       diagonal `µ(x₀)`) so that the residual `r̃` vanishes to second order at `x₀`. Then `ρ = r̃/D` is
       continuous with `ρ(x₀) = 0`.
     - The bounded solution on `(x₀, x₀+π)` is `H = e^{-A}∫_{x₀}^x e^{A} ρ`, anchored at the end where
       `e^{A} → 0`.
     - The identity `d/dy[e^{A} D/µ] = e^{A}(1 + (D/µ)')` gives `e^{-A}∫e^{A} ≤ 2D/µ` near both ends,
       so `H → 0` and `H' = ρ - (µ/D)H → 0` there. Hence `φ + H` is a `C¹` periodic solution.
   - In both cases the constant is chosen through `∫ h_1 ≠ 0` (maximum principle).
   - `C = ∫ f dν` is then automatic, by `IsKolmogorovDensity.integral_generator_eq_zero`.
3. **Cesàro convergence from every start** (R4).
   - For `C²` periodic `f`, `(1/T)∫₀ᵀ Q_t f(u) dt - ν(f) = (Q_T g(u) - g(u))/T → 0`.
   - This extends to continuous periodic `f` by uniform approximation with trigonometric polynomials.
4. **Invariance** (R4).
   - For continuous periodic `f`, the function `h = Q_s f` is continuous and periodic (Feller). Hence
     `ν(Q_s f) = lim (1/T)∫₀ᵀ Q_t Q_s f(u) dt = lim (1/T)∫_s^{T+s} Q_t f(u) dt = ν(f)`.
   - Fubini then gives C1–C3 in hMO-free form.
5. **Lemma 3.3 without a density** (R5). C4 (`law θ̂_1(z) ≪ Leb`) is not re-proved. Its one consumer,
   `ae_mem_of_ae_unit`, instead uses:
   - **Occupation estimate.** `E∫₀ᵀ ψ(θ̂_t)β²(θ̂_t) dt ≤ C_T ∫₀^π ψ` for continuous `ψ ≥ 0`, by Dynkin
     with `g'' = ψ - mean ψ`. Hence `E Leb{t ≤ T : θ̂_t ∈ N} = 0` for null `N` where `β² > 0`.
   - **Critical case.** No time is spent at the zero set `x₀ + πℤ`, by Dynkin with a narrowing bump
     for `g'` (the drift `µ(x₀) ≠ 0` gives the bound, and the term `D g''` is `O(ε)`).
   - Fubini then gives some `t ∈ [1, 2]` with `P(θ̂_t(z) ∈ N) = 0`. Run the existing argument at
     `σ_z(t)` instead of `σ_z(1)`.
6. **Removal** (R6). Drop the `hMO` binders, delete both externals, the kernel route that
   depended on them, and their manifest entries. Then seal, audit and push.

## Packets (Sonnet, at most 2 at a time)

| Packet | Content | Depends |
|---|---|---|
| R2 | critical periodic ODE: `C¹` periodic solution of `D h' + α h = r` | — |
| R3 | semigroup `Q` of θ̂: Chapman–Kolmogorov, periodicity, Feller, time continuity, Dynkin | — |
| R1 | non-critical Poisson, maximum principle, choice of the constant | — |
| R5a | occupation estimate, no time at the critical zero | R3 |
| R4 | Poisson for `(µ, D)`, Cesàro, invariance, hMO-free C1–C3 | R1, R2, R3 |
| R5b | Lemma 3.3 at a good time `t ∈ [1,2]` | R5a |
| R6 | binder removal, deletions, seal, audit | all |
