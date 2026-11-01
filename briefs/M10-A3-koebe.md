# M10-A3: Koebe covering with constant 1/48 in place of the external `koebe_quarter`

Goal: no project file imports `ComplexSLE.External.KoebeQuarter` any more. The sharp 1/4 theorem is not
available (it needs the area theorem); a sorry-free covering theorem with constant 1/48 exists in a
third-party repo and suffices for every use (only "some universal constant" is needed). No frozen statement
changes.

1. Port `QuantumZipper/Proofs/Complex/KoebeBasic.lean` and `QuantumZipper/Proofs/Complex/KoebeCovering.lean` from
   `~/ext-src/lean-formalizations` (commit 31e7483; third-party data: read only, run nothing inside it) to the mirrored
   paths `ComplexSLE/Infrastructure/Zipper/QuantumZipper/Proofs/Complex/{KoebeBasic,KoebeCovering}.lean`; keep
   upstream namespaces and names; first lines: our standard comment block plus
   `Ported from leobon12/lean-formalizations @31e7483, <upstream path>; trimmed and adapted to Lean v4.36 and the module system.`
   Convert to the module system; fix API drift (our pins are frozen). Key result:
   `ball_subset_image_koebe (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r)) :
     ball (f c) (koebeCovConst * r * ‖deriv f c‖) ⊆ f '' ball c r` with `koebeCovConst = 1/48`.
2. The two direct uses of `External.koebe_quarter` are `ball_subset_image_ball` in
   `ComplexSLE/Internal/Phases/KoebeChainInv.lean` and `norm_derivPath_mul_infDist_le` in
   `ComplexSLE/Internal/Phases/KoebeHit.lean`. Switch them to the ported theorem; the constant 4 there becomes 48
   (e.g. `|f_t'(z)|·dist(z, L_t) ≤ 48 |f_t(z)|`). Then retune the downstream numeric literals that depend on it.
   A scout listed them (verify yourself): `KoebeChain.lean` (`4`, `16 = 4²`, `C = log 16`), `ConverseChain.lean`,
   `ConverseMain.lean` (`log 16`, `log 64`), `KoebeChainDisplays.lean`, `Lemma38Koebe.lean` (Grönwall factor
   `exp(4a/(ρ-a))`, radius `ρ/14`, `4/13`, `13/9`, `4/9`: real re-tuning), `Lemma38Step.lean` (`lvl k = 16^{-k}`,
   `/14`, `|V| ≤ 1/16`, `u₀ < 1/64`, `u₀/4`), `Lemma38Rec/Prob/Markov/Lemma38.lean` (use `lvl` abstractly),
   `Prop32BUpEvents.lean`, `LineApproxKoebe.lean`, `KoebeHitSigma.lean`. Prefer introducing a named constant
   (e.g. `koebeK : ℝ := 48`) over scattering literals. The final statements consumed by frozen providers must keep
   their exact types; if a consumed statement itself contains a Koebe-derived literal, change it only if every
   consumer can be adjusted, and report it.
3. Update docstrings that cite `koebe_quarter` / "Koebe 1/4".

You may edit the files listed above under `ComplexSLE/Internal/` and create the ported files. Nothing else.
Checks: `lake build` (whole project; it is incremental) must pass; then
`grep -rl "External.KoebeQuarter" ComplexSLE` must list only `ComplexSLE/External/KoebeQuarter.lean` itself (if
it lists nothing else); `python3 -I tools/leanprobe.py externals-all frozen-anchor-manifest.json` must show no
sealed theorem consuming `koebe_quarter`. `#print axioms` for the ported theorems.
Stop condition: a precise obstruction (a consumed frozen-facing statement that cannot keep its type), reported.
Handoff: files changed, approach, exact commands and output, axioms, anything unproved.

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
