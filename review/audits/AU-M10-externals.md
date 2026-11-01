# AU-M10-externals: audit of the M10 external proofs (independent, refute-first, 2026-11-01)

Posture: independent, refute-first. No project file was edited; this report is the only file written. Scratch lived in
`.lake/probes/au-m10/` (deleted at the end). Audited tree: git HEAD `c6c5bce` (M10 commits `git log 6cc97c1..HEAD`, 13 commits),
working tree clean (`git status --short` empty). Manifest sha256
`d476a6c9483e3133d8270ca833ffcf47c08b4f083306f549982d4b5b34f6c490` (equals `FROZEN_MANIFEST` in `DEPGRAPH.md` and
`graph/DEPGRAPH.header.md`). Toolchain files (`lakefile.toml`, `lean-toolchain`, `lake-manifest.json`) are unchanged since `6cc97c1`.

## Overall verdict: PASS

All eight items pass. I found no blocking defect. I found no way to smuggle a body, a statement change or a stray file through the
amended checker, and no sealed external whose statement differs from its provider's. The non-blocking list (stale status documents,
two stale docstrings, optional checker hardening) is at the end.

Not done: I did not re-derive the mathematical truth of the statements (they are unchanged and were approved in R23-R25), did not
rebuild from scratch (`lake build --no-build` reports `All targets up-to-date (8010 jobs)`, so artifacts match the tree), and did not
review the proofs line by line beyond the spot checks in item 8.

## Summary table

| # | Item | Result |
|---|---|---|
| 1 | Statement freeze of the 10 sealed externals; `verify-abi`; manifest ABI hashes | PASS |
| 2 | Provider types equal external types; axioms; `externals-all` table | PASS |
| 3 | No smuggling; frozen tree untouched; modules and 1500-line cap | PASS |
| 4 | Tooling diff (`check_frozen_anchors.py`, `seal_external.py`), negative tests | PASS (hardening notes) |
| 5 | Deletions; manifest/DEPGRAPH hash; graph gate | PASS |
| 6 | Koebe retune and DDS-free route, two lemmas checked | PASS |
| 7 | Zipper provenance headers and upstream paths | PASS (license note) |
| 8 | Fidelity of provider proofs (`ito_formula`, `support_sleDriver`) | PASS |

## 1. Statement freeze: PASS

- `git diff 6cc97c1 HEAD -- ComplexSLE/External/<each of 10>.lean`: each hunk set is exactly (a) one added line
  `import ComplexSLE.Internal.ExternalProofs.<Name>` (non-public `import`, after the last existing import), (b) the module docstring
  (`# EXTERNAL input:` to `# Classical input (proved):` and the "Assumed, not proved ... permanent `sorry`" sentence replaced by
  "Proved in-project (M10, ruling R30) by `<provider export>`"), (c) the body (`by sorry` to `by exact <provider> <binders>`).
- Byte check by script (old blob via `git show 6cc97c1:<path>` against the current file), for all 10: the text between the module docstring
  and `theorem`, the statement bytes from `theorem` to the `FROZEN_ANCHOR_PROOF_BEGIN` marker (this includes `:=`), and everything
  from `FROZEN_ANCHOR_PROOF_END` on are identical. The only line added before the docstring is the provider import.
- `python3 -I tools/leanprobe.py verify-abi frozen-anchor-manifest.json` gives `ABI OK (62 anchors)`.
- Manifest versus `git show 6cc97c1:frozen-anchor-manifest.json`: 68 to 62 anchors, exactly the six deleted `ext.*` ids removed, none
  added. For the 10 sealed externals `abi_sha256`, `suffix_sha256`, `definition_closure`, `path`, `export`, `split_policy`,
  `author_approval`, `source`, `contract` are unchanged. The changed fields are only `state` (EXTERNAL to SEALED), `implementation`
  (new), `draft_allowlist` (new, both lists empty) and `prefix_sha256` (necessarily, for the import line and docstring). No other anchor
  changed in any field. `seal_limits` is unchanged (3 lines, 240 bytes). The manifest is in canonical `json.dumps(indent=2)` form
  before and after, so no whitespace churn.
- `hormander_oneDim` and `markov_oneDim` files are byte-identical to `6cc97c1`.

## 2. Providers: PASS

- Probe `.lake/probes/au-m10/TypeEq.lean` imports the 10 externals and the 10 providers and compares the constant types in `Environment`:
  for every pair, `ce.type == cp.type` (strict `Expr` equality), equal level parameters (all empty), `isDefEq` true, and both are
  `thmInfo`. So each provider has exactly the external's type, not merely a defeq one.
- `python3 -I tools/leanprobe.py axioms <module> <decl>` on all 10 frozen externals and on all 10 providers:
  `["propext", "Classical.choice", "Quot.sound"]`, `nonstandard: []`.
- `python3 -I tools/leanprobe.py externals-all frozen-anchor-manifest.json` (43 s, exit 0, `EXTERNALS OK (36 sealed theorems)`).
  Cross-checked with `#print axioms` on `theorem_1_10_a`, `theorem_1_10_b` (standard three) and `proposition_3_2_b`, `theorem_1_8`
  (`sorryAx` present).

| Status | Declarations |
|---|---|
| PROVED (30) | `loewner_wellDefined`, `exists_admissibleDensity`, `exists_sleDriver`, `theorem_1_10_a`, `theorem_1_10_b`, `lemma_2_4_leftHull`, `lemma_2_4_rightHull`, `scaling_{leftHull,rightHull,centeredLoewnerMap}`, `reflection_{leftHull,rightHull,centeredLoewnerMap}`, `loewnerMap_eq`, `loewnerMap_exists_solution`, the four `concatenation_*`, `sle_duality`, and the 10 sealed externals `External.{exists_isBrownianReal, support_sleDriver, loewnerMap_conformal, loewnerMap_tendstoUniformly, strongMarkov_sleDriver, blumenthal_sleDriver, birkhoff_stationary, recurrence_stationary, ito_formula, timeChange_isContLocalMartingale}` |
| PROVED_REL (6), all on exactly `{External.hormander_oneDim, External.markov_oneDim}` | `theorem_1_8`, `theorem_1_8_c_zero`, `proposition_3_1_a`, `proposition_3_1_b`, `proposition_3_2_a`, `proposition_3_2_b` |

`externals-all` lists only SEALED theorem anchors; the two remaining EXTERNAL anchors are reached through the closure walk. `lake build
--no-build` replays exactly two `declaration uses sorry` warnings, `External/HormanderOneDim.lean:43` and
`External/MarkovOneDim.lean:27`, and no others in the whole tree.

## 3. No smuggling: PASS

- Tracked files under `ComplexSLE/`: 355, all `.lean`; on-disk files 355, untracked 0.
- `sorry` or `admit` as a word: only `External/HormanderOneDim.lean` (lines 22, 57) and `External/MarkovOneDim.lean` (lines 14, 42).
- Case-insensitive grep for `axiom|opaque|unsafe|native|extern|implemented_by|ofReduceBool|trustCompiler|bv_decide|decide +kernel|
  maxHeartbeats|maxRecDepth|synthInstance|debug.|run_cmd|macro|elab|syntax|initialize|#eval|import Lean`: no hit in code (three hits
  are English words in docstrings: "alternatives", "external"). No `set_option` anywhere. Same patterns in `Infrastructure/Zipper`: none.
  `tools/check.sh --quick` (module headers, frozen-anchor guard, forbidden-construct grep): `ALL CHECKS PASSED`.
- `git diff --stat 6cc97c1 HEAD -- ComplexSLE/Frozen` is empty. Within `ComplexSLE/External/`: 10 modified (the sealed ones), 6 deleted,
  none else.
- In the new non-Zipper files: no `Classical.choice|arbitrary|choose`, `Nonempty.some`, `default`, `Inhabited`, `decide`; the
  `classical` tactic appears twice in `RecurrenceStationary.lean` (ordinary). The only `instance` in the Zipper port is the proved
  `IsProbabilityMeasure stdP`.
- `python3 -I tools/check_lean_modules.py`: `PASS (355 Lean files, 0 comparator configurations)`; every file starts with `module`; the
  largest file has 697 lines (`Internal/Polar/PolarThetaBrIto.lean`, pre-existing).
- `ComplexSLE.Internal.ExternalProofs.*` providers import no `ComplexSLE.External.*` module (grep; hits are docstring mentions).

## 4. Tooling: PASS (non-blocking hardening notes)

Diff of `tools/check_frozen_anchors.py` is three edits, all read in full context:

1. `check_entry`: a theorem anchor in state SEALED may now have a path under `ComplexSLE/External/`. DRAFT_SORRY theorems and all
   definitions still fail there. A SEALED theorem still needs the SEALED schema (mandatory `implementation`, `draft_allowlist`,
   `prefix_sha256`, `suffix_sha256`), `implementation_path` requires the provider file and a non-private export declared exactly once,
   the prefix must import `implementation.module`, and a provider under `ComplexSLE.External.` is rejected.
2. Sealed-body regex: `[ \t]+` to `\s+` between arguments, so arguments may wrap lines. Arguments must still be binder names of the
   frozen header (`binder_names`), the body must be `by exact|simpa using <implementation.export> <binders>*`, and the 3-line /
   240-byte limit still applies. No new token class is admitted: any non-binder token (`sorry`, `<;>`, `--`, a tactic) still fails.
3. `check_external_anchors`: the closed-directory rule now accepts files that are EXTERNAL or SEALED-theorem manifest anchors under
   `External/`. The "EXTERNAL files import only Mathlib, sealed definitions and other EXTERNAL modules" rule still applies to
   state-EXTERNAL anchors; proved externals instead fall under `check_sealed_not_draft` (no import of a DRAFT_SORRY anchor or
   provider) and the implementation-reverse-import check.

Negative tests in a scratch copy of `ComplexSLE/` plus the manifest (`.lake/probes/au-m10/neg.py`, checker run with
`--root <scratch>`); every mutation was applied to a fresh copy:

| Test | Result |
|---|---|
| N0 unmodified | OK |
| N1 sealed external body := `by sorry` | FAIL (body rule and unauthorized `sorry`) |
| N2 wrapped extra arg `sorry` on a second line | FAIL |
| N3 trailing `<;> simp` on a new line | FAIL |
| N4 legitimate binder args wrapped over two lines | OK (the intended relaxation) |
| N5 tactic-block body | FAIL |
| N6 stray `External/Evil.lean` (no sorry) | FAIL (not a manifest anchor) |
| N7 stray `External/Evil2.lean` containing `sorry` | FAIL (both rules) |
| N8 flip `hormander_oneDim` to SEALED, no provider fields | FAIL (schema, implementation, body) |
| N9 flip to SEALED with an unrelated provider, body still `by sorry` | FAIL (body, prefix import, sorry) |
| N10 `sorry` appended to a provider | FAIL |
| N11 sealed external relabelled DRAFT_SORRY | FAIL (path rule, quarantine) |
| N12 provider import removed from prefix | FAIL (prefix hash, missing import) |
| N13 statement mutated (`0 < ε` to `0 ≤ ε`) | FAIL (prefix hash) |
| N14 provider pointed into `External/` | FAIL |

`tools/seal_external.py` (63 lines): refuses anything not in state EXTERNAL; requires the body to be exactly `  by sorry`; inserts one
import after the last import; rewrites the one docstring sentence by regex (aborts unless it matches exactly once); caps the new body
at 3 lines / 240 bytes; never touches `abi_sha256`, `suffix_sha256`, the closure or the statement; writes `implementation`, an empty
allowlist and the new prefix hash; refreshes the `FROZEN_MANIFEST` line in `DEPGRAPH.md` and `graph/DEPGRAPH.header.md`. It cannot weaken
a guard: the guard recomputes every hash independently. A DRAFT or non-trivial body cannot pass, an arbitrary file cannot live under
`External/`, and a SEALED external cannot lack a provider (N6-N9).

## 5. Deletions: PASS

- Manifest ids removed: `ext.{dambis_dubins_schwarz, girsanov_law_equiv, koebe_distortion, koebe_quarter, levy_characterization,
  scale_function_hit}.v1`. Files `External/{DambisDubinsSchwarz, GirsanovLawEquiv, KoebeDistortion, KoebeQuarter, LevyCharacterization,
  ScaleFunctionHit}.lean` are deleted.
- Grep over tracked `ComplexSLE/` for the six constant names and six module names: two docstring-only hits (see non-blocking 2); no
  import, no `External.<name>` term reference. The build is up to date, so nothing refers to a missing constant.
- `sha256sum frozen-anchor-manifest.json` = `d476a6c9...c490` = `FROZEN_MANIFEST` in `DEPGRAPH.md` line 10 and
  `graph/DEPGRAPH.header.md` line 10. The `DEPGRAPH.md` and header diffs are that one line only.
- Graph gate (`python3 tools/proof_depgraph.py --db DEPGRAPH.md --manifest DEPGRAPH_COVERAGE.md --source-root . --require-reviewed
  --require-complete-coverage --require-initial-lean-status --require-all-reachable --check`): exit 0. The graph still carries the
  source-level node `ext:girsanov` (a paper input, not a Lean anchor); it names no deleted Lean constant.

## 6. Koebe retune and DDS-free route: PASS

- `git diff --stat 6cc97c1 HEAD -- ComplexSLE/Internal` (new `ExternalProofs/*` aside): 26 modified files, all under `Internal/Phases/`
  and `Internal/Disconnect/`; none is a frozen file. Frozen statements are unchanged (item 1, `verify-abi`).
- `KoebeChainInv.ball_subset_image_ball`: from the ported `QuantumZipper.CA.Koebe.ball_subset_image_koebe`
  (`B(f c, r‖f'(c)‖/48) ⊆ f(B(c,r))`) with `koebeK = 48 = 1/koebeCovConst` (proved `koebeCovConst_eq_inv`). The `1/4` theorem implies the
  `1/48` one, so the statement is true. The two-sided distance bounds follow as before with `4` replaced by `koebeK`: lower bound from
  `ball(F z, |F'| ρ/K) ⊆ K'ᶜ`, upper bound by applying the same lemma to the local inverse `G` (`G'(F z) = 1/F'(z)`) on
  `B(F z, dist(F z, K'))`. The new unused hypothesis `_hρ` is harmless (empty ball when `ρ ≤ 0`).
- `LineApproxKoebe.infDist_leftHull_top_le`: bound `8 koebeK δ'` (= 384 δ'); at the sharp `K = 4` it is the old `32 δ'`, so the
  generalization is exact. Arithmetic checked by hand: `(c+δ') d ≤ 4K δ'(2c+δ') ≤ (c+δ')·8Kδ'` because `4Kδ'² ≤ 8Kδ'²`, then divide
  by `c+δ' > 0`. The `d = 0` branch is `0 ≤ 8Kδ'`. In `exists_mem_leftHull_im_gt` the choice `δ' = δ/(16K)` gives `8Kδ' = δ/2` and
  `r - δ/2 > 2√T - δ`, matching the old `δ/64` at `K = 4`.
- `Lemma38Koebe`: `koebeN = 1 + 13K/4 = 157` makes `K a/(ρ-a) ≤ 4/13` for `a ≤ ρ/koebeN` (so the paper's `4/9`, `5/9 > 1/2` are
  unchanged; at `K = 4` it is the paper's `14`); `lvlBase = koebeN + 1 = 158 > koebeN` replaces `16 > 14`.
- Axioms of `ball_subset_image_ball`, `infDist_image_le`, `infDist_leftHull_top_le`, the Zipper `ball_subset_image_koebe` and
  `Infrastructure.ae_forall_exists_le_of_bracket_tendsto_atTop`: the standard three.
- DDS-free route (`Internal/Phases/C0Bdy.lean`): the `dambis_dubins_schwarz` call and `Infrastructure.ae_forall_exists_le_of_timeChange`
  are replaced by `ae_forall_exists_le_of_bracket_tendsto_atTop`: for a continuous local martingale `N` with `N 0 = 0` a.s.,
  `N² - A` a continuous local martingale, `A` monotone from 0 and `A → ∞` a.s., a.s. `∀ K, ∃ s, N s ≤ -K`. The statement is true
  (it follows from DDS) and is proved by gambler's ruin; its hypotheses are exactly those the caller already had (`hNm`, `hN0`, `hAm`,
  `hAmart`, `hAtop`). The `Continuous A` conjunct is no longer needed and was dropped from the caller.

## 7. Provenance: PASS

`ComplexSLE/Infrastructure/Zipper/` has 9 files. Each has the header `Ported from leobon12/lean-formalizations @31e7483,` followed by the
upstream path on the next line, and each is a `module`. The named path exists in `~/ext-src/lean-formalizations` (HEAD
`31e748330ee154d5f41537c4b01f71b8a5510c2d`) and equals the file's path under `Zipper/`: `QuantumZipper/Common/Basic.lean`,
`QuantumZipper/Proofs/Probability/{BMExistence,BMMoments}.lean`, `QuantumZipper/Proofs/GFF/CircleContinuity.lean`,
`QuantumZipper/Proofs/GFF/Existence/GaussianSeries.lean`, `QuantumZipper/Proofs/Complex/{KoebeBasic,KoebeCovering}.lean`,
`QuantumZipper/Proofs/ItoLite/OptionalStopping.lean`, `LQGDimension/Existence/AssemblyAux1.lean`.

Note, not a failure: the upstream repository has no license file (`git ls-files | grep -i licen` is empty there), and this repository has
none either. R30 records that this is to be settled before public release. Four other files cite upstream proof routes in prose
(`Stochastic/StrongMarkov{AeFinite,Core,Future}.lean`, `Internal/Phases/KoebeChainInv.lean`); they are adaptations, not ports, and name
the upstream commit.

## 8. Fidelity of provider proofs: PASS

- Probe `.lake/probes/au-m10/Used.lean` (lambda-telescope of each provider's proof term): for all 10 providers every binder of the
  statement occurs in the proof term (0 unreferenced). Stronger: compiling each of the 10 provider files directly gave no
  `unused variable` or any other warning, and the linter is live (a planted unused variable was flagged in a scratch copy).
- `ito_formula`: the provider is one application of `Infrastructure.Ito.isContLocalMartingale_itoProc`, which takes
  `hX hXc hA hQ hAint hQint hM hMM hD hFm hF hXD`, i.e. every frozen hypothesis. The route (module docstring and `LocalizeReduction`
  header) is bounded core, then localization by stopping times of the total variation of the densities and exits from an open
  exhaustion of `D`; no assumption-shaped binder is added. `IsContLocalMartingale` (frozen def) is the standard definition
  (progressively measurable, a.s. continuous, localizing stopping times with martingale stopped processes), so proving it is not trivial.
- `support_sleDriver`: passes to `P.completion` on `NullMeasurableSpace Ω P` (needed because `U s` is only a.e.-measurable), rebuilds
  `Infrastructure.Support.MeasurableDriver` from `hU.{zero, cont, indepFun_shift_past, law_increment}`, supplies positive
  semidefiniteness from `ha hb hc` (`covMatrix_posSemidef'`) and the range condition from `hφS`; `hφ hφ0 T hδ` go to
  `support_of_measurableDriver`. All 19 binders are used, and the set `{ω | ∀ t ≤ T, ‖U t ω - φ t‖ < δ}` is evaluated with `P` unchanged
  (`Measure.completion_apply`).
- `exists_isBrownianReal`: `⟨ℕ → ℝ, inferInstance, stdP, inferInstance, B, hB⟩` from the ported `exists_isBrownianReal_stdP`; no
  data is faked by choice.

## Fix list

Blocking: none.

Non-blocking:

1. Status documents are stale relative to M10: `RESULTS.md` (M9 snapshot: 68 anchors, "18 EXTERNAL", manifest `f06c7d34...`,
   `koebe_quarter` and `dambis_dubins_schwarz` in PROVED_REL lists, `theorem_1_10_a/b` shown PROVED_REL), `README.md` ("13 of the 18
   approved externals", "Koebe quarter theorem", "None ... `sorry` outside 18 files"), and `STATUS.md` (no M10 entry). Regenerate at M10
   close (62 anchors, 36 sealed theorems: 30 PROVED and 6 PROVED_REL on `{hormander_oneDim, markov_oneDim}`, two `sorry`).
2. Two stale docstrings under `ComplexSLE/`: `Infrastructure/Stochastic/ContinuousModification.lean:20` ("compare
   `External.levy_characterization`") and `Internal/Phases/Lemma38.lean:38` (mentions `koebe_distortion` as not needed). Docstring-only.
3. Optional checker hardening: require a SEALED anchor under `ComplexSLE/External/` to have `implementation.module` under
   `ComplexSLE.Internal.ExternalProofs.`, and require modules under that prefix to import no `ComplexSLE.External.*` (the plan states it;
   it is true now by grep, but enforced only by convention and by `externals-all`).
4. Optional: `LoewnerMapTendstoUniformly.lean` has a one-space body indent (accepted by the guard, cosmetic).
5. Before public release: settle the license of the Zipper port (R30 already records it).
