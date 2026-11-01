# M10-B3a: Itô's formula, bounded core (martingale form, no stochastic integrals)

Context: the EXTERNAL `ComplexSLE.External.ito_formula` (`ComplexSLE/External/ItoFormula.lean`, read only) is to be
proved. This packet proves the **bounded core**; packet B3b will localize and assemble the exact statement. Read
the exact statement and the definitions `ComplexSLE/Frozen/Defs/{IsContLocalMartingale,PathIntegral}.lean` first.
Nothing in Mathlib or in the third-party repo proves this (the zipper's `ItoLite/Dynkin.lean` handles additive
Brownian noise only); the route below uses only Mathlib martingales and conditional expectations.

Deliverable: a new directory `ComplexSLE/Infrastructure/Ito/` (several files, each a module, ≤ 1500 lines), importing
no `ComplexSLE.External.*` module directly or transitively (do not import `Infrastructure/Stochastic/StoppedLocalMartingale`
or anything under `ComplexSLE/Internal/Polar` or `ComplexSLE/Internal/Stationary`; check closures). Main theorem
(name e.g. `ComplexSLE.Infrastructure.Ito.martingale_ito_bounded`), roughly:

Setting: filtration `ℱ`, probability `P`; `X A : ℝ≥0 → Ω → (Fin n → ℝ)`, `Q : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ`,
all `IsStronglyProgressive ℱ`; `∀ ω, Continuous (X · ω)`; a compact `K` and open `D ⊇ K`, `F` measurable and
`ContDiffOn ℝ 2 F D`; a constant `C` with, almost surely: `∀ t, X t ω ∈ K`, `∫₀^∞ ‖A s ω‖ ≤ C`,
`∫₀^∞ ‖Q s ω‖ ≤ C` (each entry), and `|M^i t ω| ≤ C` where `M^i t = X^i t - X^i 0 - pathIntegral A^i t`;
`M^i` and `N^{ij} := M^i M^j - pathIntegral Q^{ij}` are `Martingale`s for `ℱ`.
Conclusion: `Y t = F (X t) - F (X 0) - pathIntegral (∑ᵢ ∂ᵢF(X)·Aⁱ + ½ ∑ᵢⱼ ∂ᵢⱼF(X)·Qⁱʲ) t` is a `Martingale`
(use exactly the derivative expressions of the external's conclusion: `fderiv ℝ F x (Pi.single i 1)` and
`iteratedFDeriv ℝ 2 F x ![Pi.single i 1, Pi.single j 1]`). You may adjust the hypothesis packaging if B3b can
supply it from stopped processes; record the final form precisely in your handoff (B3b depends on it).

Route (fix `s < t`, `B ∈ ℱ s`; show `∫_B (Y t - Y s) = 0`):
- Uniform partition `t_k` of `[s,t]` with `N` pieces; `ΔX_k = ΔM_k + ΔD_k`, `D = pathIntegral A`.
- Taylor (second order, integral remainder) along segments inside a `δ`-neighbourhood `K_δ ⊂ D` (compact,
  derivatives bounded, `∂²F` uniformly continuous on `K_δ` with modulus `ϖ`); paths are uniformly continuous on
  `[s,t]`, so a.s. for `N` large every `|ΔX_k| < δ`.
- Write `F(X t) - F(X s) = Z_N + W_N` with
  `Z_N = ∑_k ∇F(X_k)·ΔM_k + ½ ∑_k ∑ᵢⱼ ∂ᵢⱼF(X_k)(ΔMⁱ_k ΔMʲ_k - ΔQⁱʲ_k)` (`ΔQ_k = ∫_{t_k}^{t_{k+1}} Q`) and
  `W_N` the rest. Then `∫_B Z_N = 0`: each summand has a bounded `ℱ_{t_k}`-measurable factor times a martingale
  increment, and `E[ΔMⁱΔMʲ | ℱ_{t_k}] = E[ΔN^{ij} + ΔQ^{ij} | ℱ_{t_k}] - …`, precisely
  `ΔMⁱΔMʲ - ΔQⁱʲ = ΔNⁱʲ - Mⁱ_{t_k} ΔMʲ - Mʲ_{t_k} ΔMⁱ`.
- `W_N → ∫_s^t (∇F(X)·A + ½ ∂²F(X):Q) du` a.s. (Riemann-sum convergence against the integrable `A`, `Q` by
  uniform continuity of `∇F(X_u)`, `∂²F(X_u)` in `u`; cross terms `ΔM ΔD`, `ΔD ΔD` bounded by
  `max_k (|ΔM_k| + |ΔD_k|) · ∫‖A‖ → 0`; Taylor remainder `≤ ϖ(max |ΔX_k|) ∑ |ΔX_k|²`). So `Z_N → Y t - Y s` a.s.
- Uniform integrability of `Z_N`: bounded in `L²`. Key lemma (elementary): for a martingale with `|M| ≤ C` a.s.
  and any partition, `E[(∑_k (ΔM_k)²)²] ≤ 48 C⁴` (expand the square; `E[a_j ∑_{k>j} a_k] = E[a_j (M_t - M_{t_{j+1}})²]`
  by orthogonality of increments). Also `E[(∑ c_k ΔM_k)²] = E[∑ c_k² (ΔM_k)²]` for bounded adapted `c_k`.
  The `ΔQ` part is dominated by `C·C_F` a.s. Then Vitali (`tendsto_Lp_finite_of_tendsto_ae` or
  `UniformIntegrable`) or simply `L²`-boundedness ⇒ `∫_B Z_N → ∫_B (Y t - Y s)`.
- Adaptedness and integrability of `Y t` (bounded a.s. by the constants; strongly measurable for `ℱ t`:
  progressive measurability of `pathIntegral` of a progressive process — look for existing lemmas, e.g.
  `isStronglyProgressive_pathIntegral'` in `Internal/Polar/PolarThetaBrIto.lean` (that file imports the external,
  so copy/adapt the proof, do not import it) and `ComplexSLE/Infrastructure/Stochastic/ProgressiveTools.lean`).

Checks: `lake build` of your modules; `python3 -I tools/leanprobe.py axioms <module> <decl>` for the main theorem
and the key lemmas (only propext, Classical.choice, Quot.sound). If the full theorem does not close within budget,
land the finished lemmas (Taylor, the `L²` bound, Riemann-sum convergence) sorry-free and report precisely what
is left; never leave a `sorry`.
Handoff: files, the exact final statement(s), approach, commands and output, axioms, what is left.

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
