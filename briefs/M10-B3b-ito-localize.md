# M10-B3b: Itô's formula, localization and the exact external statement

Goal: a sorry-free proof of the EXACT statement of `ComplexSLE.External.ito_formula`
(`ComplexSLE/External/ItoFormula.lean`, read only) as `ComplexSLE.Internal.ExternalProofs.ito_formula` in
`ComplexSLE/Internal/ExternalProofs/ItoFormula.lean` (helpers in new files `ComplexSLE/Infrastructure/Ito/Localize*.lean`).
Copy the theorem type verbatim. Import no `ComplexSLE.External.*` module, directly or transitively (note:
`timeChange_isContLocalMartingale` is now SEALED, so modules that import only it are fine; check closures).

Available (external-free): the bounded core `ComplexSLE.Infrastructure.Ito.martingale_ito_bounded`
(`ComplexSLE/Infrastructure/Ito/Bounded.lean`, read its exact hypotheses first: progressive `X A Q`, every path of `X`
continuous, a.s. per-coordinate interval integrability and `∫₀ᵗ |Aⁱ| ≤ C`, `∫₀ᵗ |Qⁱʲ| ≤ C`, a.s. `|Mⁱ| ≤ C`, `Mⁱ` and
`Nⁱʲ = MⁱMʲ - ∫Qⁱʲ` true `Martingale`s, a.s. `X t ∈ K` for a compact `K ⊆ D` open, `F` measurable and `C²` on `D`;
conclusion: the Itô process is a `Martingale`), `isStronglyProgressive_pathIntegral` (`Ito/Progressive.lean`),
`ComplexSLE/Infrastructure/Stochastic/{ContinuousOptionalStopping,LocalMartingaleAlgebra,StoppedLocalMartingale,
TimeChangeTransfer,TimeChangeOptionalSampling,TimeChangeMartingale,TimeChangeExitTimes,BracketInfinity,
ContinuousModification,ProgressiveTools}.lean` (e.g. `isStronglyProgressive_indicator_lt`,
`IsContLocalMartingale.exists_localizing_seq`, `capExitTime`, `continuous_stoppedProcess`) and the closed-set hitting
times `ComplexSLE/Infrastructure/Zipper/QuantumZipper/Proofs/ItoLite/OptionalStopping.lean`.

The one real difficulty: the filtration is arbitrary (not complete, not right-continuous), and `Mⁱ`, `Nⁱʲ` and the
drift integrals are only a.s. continuous / a.s. finite, so "first time `∫|A|` reaches `n`" or "first time `|M|`
reaches `n`" need not be stopping times. Use this device:
- `J_t(ω) = ∫⁻_{[0,t]} ‖A_s ω‖` (lintegral) is `ℱ_t`-measurable, monotone, and finite for all `t` a.s.
  Replace `A` by `Ã_s = A_s · 1_{J_s < ∞}`, which is progressive. Then `V_t = ∫⁻_{[0,t]} ‖Ã_s‖` is continuous as a
  `[0,∞]`-valued process for EVERY `ω`: it either stops growing at the time where integrability is lost, or it
  increases continuously to `∞`. So `ρ_n = inf{t | n ≤ V_t}` is a genuine stopping time (closed-set hitting of a
  continuous adapted process), and on `[0, ρ_n]` the integral `∫ Ã` is finite and continuous for every `ω`. Do the
  same for `Q`. `Ã = A` a.e. in `(s, ω)` on the a.s. set where `J < ∞`.
- Build everywhere-continuous adapted versions `M̂ⁱ = X - X 0 - ∫₀^{·∧ρ} Ã` of the stopped `Mⁱ`. They agree with
  `(Mⁱ)^ρ` a.s. at each time, and two adapted processes that agree a.s. at each time are martingales together,
  through `condExp` congruence. Exit times of `[-n, n]` by `M̂ⁱ`, and of the open sets
  `Uₙ = {x | ‖x‖ < n, 1/n < infDist x Dᶜ}` by `X` (which is everywhere continuous), are genuine stopping times.
- `T_n` = min of those times, the localizing times of all `Mⁱ`, `Nⁱʲ` (finitely many), and `n`. On `{X 0 ∉ Uₙ}`, which
  is in `ℱ 0`, apply the core to the frozen data instead: `X' = X^{T} 1_G + x₀ 1_{Gᶜ}` with
  `G = {X 0 ∈ Uₙ}` and `x₀ ∈ Uₙ`, `A' = A 1_{s < T} 1_G`, etc. Both sides vanish on `Gᶜ`. `T_n → ∞` a.s. because the
  path of `X` on `[0,t]` is a compact subset of `D` a.s.
- Apply `martingale_ito_bounded` with `K = closure Uₙ` (compact, contained in `D`) to get that `Y^{T_n}` is a
  `Martingale`. The stopped `A`, `Q` are `A 1_{s<T}`; their path integrals equal the stopped path integrals.
- Conclude `IsContLocalMartingale`. `Y` must be progressive everywhere: `F ∘ X` plus `isStronglyProgressive_pathIntegral`.
  It must also be a.s. continuous: `F` is continuous on `D`, the path lies in `D` a.s., and the generator is locally
  integrable a.s.

Checks: `lake build ComplexSLE.Internal.ExternalProofs.ItoFormula`, and
`python3 -I tools/leanprobe.py axioms ComplexSLE.Internal.ExternalProofs.ItoFormula ComplexSLE.Internal.ExternalProofs.ito_formula`,
which must report only propext, Classical.choice and Quot.sound. Every new file must be a module of at most 1500 lines.
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
