# AU-M9-closure: campaign closure audit (auditor-M9-closure/sonnet, 2026-11-01)

Auditor: `auditor-M9-closure/sonnet`. Date: 2026-11-01. Posture: independent, refute-first. No source file was edited;
this report is the only file written. Scratch lived in `.lake/probes/au-m9/` (deleted at the end) and the session scratchpad.

Audited tree: git HEAD `cb99fd4` (master is 2 commits ahead of `origin/master` = `e3ee94b`). The working tree also carried the
orchestrator's uncommitted edits to `README.md`, `STATUS.md` (new "M9 complete" paragraph) and `review/approvals/M9.md`
(Outcome section). `STATUS.md` was audited in its working-tree form; `README.md` was ignored as instructed.
Manifest sha256 `f06c7d34510166ee661269535eaec1ec6bedb1d57ad35c73e5bbc1c2b17f63e3` (equal to the `FROZEN_MANIFEST`
header of `DEPGRAPH.md`). `source/.../complex-sle-final.tex` sha256 `6f182d3a...` (matches CLAUDE.md).

## Overall verdict: PASS

All seven items pass. Every sealed statement is byte-identical to its freeze, every status figure and per-root external
list in `STATUS.md` and `RESULTS.md` was reproduced from the probe, and I found no PROVED claim that is really
PROVED_REL and no external misreported as used or unused. I found no blocking defect. I found several documentation
defects, two of which I recommend fixing before release because a reader would be misled (stale numbering statements
in `RESULTS.md` that the 940e9c4 rename made false, and an unverifiable "fresh clone of the pushed repo" claim). The
full fix list is at the end.

What this audit did not do: it did not re-derive the mathematical truth of the 18 EXTERNAL statements (covered by
AU-M5-ext1, AU-M5-ext2 and the R29 reviews), did not rebuild from a fresh clone (no network or Mathlib cache here), and
re-checked paper fidelity only for the spot-checked items named below.

---

## 1. Gate

| Check | Result |
|---|---|
| `tools/check.sh` (full) | PASS, exit 0, 38.9 s (build largely replayed from the Lake cache) |
| `lake build` | `Build completed successfully (7672 jobs)`; re-run separately: 0 errors, exactly 18 `declaration uses sorry` warnings, all under `ComplexSLE/External/` |
| module headers | `check_lean_modules: PASS (297 Lean files, 0 comparator configurations)`; largest file 697 lines (limit 1500) |
| frozen anchors | `FROZEN-ANCHOR GUARD OK` |
| ABI | `ABI OK (68 anchors)` |
| externals closure | `EXTERNALS OK (26 sealed theorems)` |
| forbidden constructs | `ALL CHECKS PASSED` |
| graph gate (`proof_depgraph.py ... --require-reviewed --require-complete-coverage --require-initial-lean-status --require-all-reachable --check`) | exit 0 (silent on success). `--report` dashboard: 286 nodes, 794 edges, 31 anchors, 14 roots, 19 external leaves, 62 explicit SOURCE_GAPs, 306 coverage items (96 excluded), topology review queue empty. `LEAN_STATUS`: 267 `NOT_STARTED`, 19 `EXTERNAL` (initial-status policy holds). |

Verdict item 1: PASS.

## 2. Manifest, frozen bytes, bodies, ABIs

States (from `frozen-anchor-manifest.json`, 68 entries, header `manifest_state: AUTHOR_APPROVED`, seal limits 3 lines / 240 bytes):
24 definitions SEALED, 26 theorems SEALED, 18 theorems EXTERNAL, 0 DRAFT_SORRY. Matches the expected 50 SEALED / 18 EXTERNAL / 0 DRAFT.

Bodies (own script over all 68 files): all 26 SEALED theorem files have a single-line body of the form
`by exact <implementation.export> <args>` whose head equals the manifest `implementation.export`
(always in `ComplexSLE.Internal.`), import the provider module, and contain exactly one declaration. All 18 EXTERNAL files
are in `ComplexSLE/External/`, have the body `by sorry` and no `implementation` entry (and exactly one `by sorry` each; the
second `sorry` token per file is the module docstring). The 24 sealed definition files carry no proof markers and no
`sorry`. ABI hashes: `verify-abi` recomputed all 68 and agrees with the manifest.

Extra evidence (not required): the closure walk run on each of the 24 sealed definitions returns PROVED with no externals,
so no definition depends on `sorryAx`.

History of every commit that touched `ComplexSLE/Frozen/`, `ComplexSLE/External/` or `frozen-anchor-manifest.json`
(23 commits; no deletes or renames; classification by a script that splits each file version into
prefix / proof body / suffix and compares consecutive versions; the manifest was diffed field by field):

| Commit | Change | Class |
|---|---|---|
| 4f08222 (M1) | 17 definitions SEALED, 2 draft roots (`loewner_wellDefined`, `exists_admissibleDensity`) | ADD x19 (freeze) |
| 15d7cc9 (M2) | 12 draft roots | ADD x12 (freeze, DRAFT_SORRY) |
| 36678a5 (M4) | `loewner_wellDefined`: `by sorry` -> `by exact Internal...`; DRAFT_SORRY -> SEALED | BODY-ONLY |
| 0fa8d56 (M4) | `scaling_leftHull`, `reflection_leftHull` sealed | BODY-ONLY x2 |
| 067b344 (M4) | `exists_admissibleDensity` sealed | BODY-ONLY |
| 46df1cf (M4) | `loewnerMap`, `centeredLoewnerMap`, `rightHull` + `loewnerMap_eq`, `loewnerMap_exists_solution` (R21; already proved, landed sealed with the definitions) | ADD x5 |
| 6ecf342 (M4) | right-hull and map parts of (2.1), (2.2), Lemma 2.4 (R22) | ADD x5 (DRAFT_SORRY) |
| e4a2e96 (M4) | `scaling_centeredLoewnerMap`, `scaling_rightHull`, `reflection_rightHull`, `reflection_centeredLoewnerMap` sealed | BODY-ONLY x4 |
| d8660dd (M5) | external batch 1 (R23), 4 files; also added the EXTERNAL state to the checker | ADD x4 |
| 7fc6f22 (M4) | `lemma_2_4_leftHull` sealed | BODY-ONLY |
| 7db02bd (M4) | `lemma_2_4_rightHull` sealed | BODY-ONLY |
| 19f3c11 (M5) | external batch 2 (R24, R25): 4 definitions + 13 externals | ADD x17 |
| aa5e699 (M6) | `exists_sleDriver` sealed | BODY-ONLY |
| c356a58 (M6) | four concatenation anchors (AUTO-1) | ADD x4 (DRAFT_SORRY) |
| 230d12f (M6) | concatenation x4 sealed | BODY-ONLY x4 |
| aca794f (M6) | `sle_duality` (R28) | ADD (DRAFT_SORRY) |
| ca431fc (M6) | `sle_duality` sealed | BODY-ONLY |
| 7e1f183 (M7) | `markov_oneDim` (R29) | ADD (EXTERNAL) |
| 16e5b50 (M7) | `proposition_3_1_a`, `_b` sealed | BODY-ONLY x2 |
| 164c44d (M7) | `proposition_3_2_a` sealed | BODY-ONLY |
| ec55bea (M7) | `proposition_3_2_b`, `theorem_1_8`, `theorem_1_8_c_zero` sealed | BODY-ONLY x3 |
| 825da30 (M8) | `theorem_1_10_a` sealed | BODY-ONLY |
| 7a86f96 (M8) | `theorem_1_10_b` sealed | BODY-ONLY |

Totals: 68 ADDs (each file added exactly once), 24 BODY-ONLY seals + 2 files landed sealed (46df1cf) = 26 sealed theorems.
STATEMENT-CHANGE count: 0. In the manifest, no field of any existing entry ever changed except `state`
(`DRAFT_SORRY` -> `SEALED`); prefix/suffix hashes, ABI hashes and definition closures are those recorded at the freeze.
Commits 940e9c4 (docstring and name renames in `Internal/`), cb99fd4 and the M8 proof commits did not touch
`Frozen/`, `External/` or the manifest. The checker tools (`check_frozen_anchors.py`, `leanprobe.py`, `check.sh`,
`check_lean_modules.py`) were last modified at M5 (d8660dd); none was weakened later. `lakefile.toml`, `lean-toolchain`,
`lake-manifest.json` last changed at M0. The R29 draft `review/approvals/drafts/MarkovOneDim.lean.txt` states the same
theorem as the frozen `External/MarkovOneDim.lean`.

I also read every sealed anchor's binder list for hypotheses beyond source premises and rulings: the hypothesis names are
only `ha hb hc hp hI hII hU hz hr ht hω hw hγ h hz₁ hz₂` style premises (positivity of a, b, PSD, admissible p, sign of
(I)/(II), the driver, z ≠ 0, r > 0, t > 0, domain memberships). No `hMO`, measurability or regularity-package binders.

Verdict item 2: PASS.

## 3. Sorry/axiom hygiene and the externals probe

Grep over all 297 tracked `.lean` files:

- `sorry`/`admit` as a word: none outside `ComplexSLE/External/`. Inside, each of the 18 files has exactly one `by sorry`.
- `axiom`, `opaque`, `unsafe`, `native_decide`, `implemented_by`, `@[extern`, `ofReduceBool`, `trustCompiler`,
  `decide := true`, `maxHeartbeats`, `maxRecDepth`, `synthInstance.maxHeartbeats`, `set_option debug`: none.
  There is no `set_option` of any kind in `ComplexSLE/`. No `elab`, `macro`, `syntax`, `initialize`, `run_cmd`,
  `#eval`, `addDecl` or `Lean.Elab`/`Lean.Meta` imports in project code.
- Informational: `lakefile.toml` sets `maxSynthPendingDepth = 3` (Mathlib template value, unchanged since M0). It is a
  synthesis-depth option, not a heartbeat/recursion/debug override, and cannot affect soundness (kernel-checked).
- The tracked `.lean.txt` draft contains one `sorry` as text; it is not a Lean file and is not built.

`python3 -I tools/leanprobe.py externals-all frozen-anchor-manifest.json`, re-run by me (27 lines, `EXTERNALS OK (26 sealed theorems)`).
The 14 roots (external short names: `bmExist` = `exists_isBrownianReal`, `ito` = `ito_formula`, `timeChange` =
`timeChange_isContLocalMartingale`, `strongMarkov` = `strongMarkov_sleDriver`, `hormander` = `hormander_oneDim`,
`birkhoff` = `birkhoff_stationary`, `recurrence` = `recurrence_stationary`, `blumenthal` = `blumenthal_sleDriver`,
`support` = `support_sleDriver`, `ltu` = `loewnerMap_tendstoUniformly`, `ddsch` = `dambis_dubins_schwarz`):

| # | Root (`ComplexSLE.`) | Probe status | Externals |
|---|---|---|---|
| 1 | `loewner_wellDefined` | PROVED | none |
| 2 | `exists_admissibleDensity` | PROVED | none |
| 3 | `exists_sleDriver` | PROVED_REL | bmExist |
| 4 | `theorem_1_8` | PROVED_REL | birkhoff, hormander, ito, koebe_quarter, markov_oneDim, recurrence, strongMarkov, timeChange |
| 5 | `theorem_1_8_c_zero` | PROVED_REL | birkhoff, ddsch, hormander, ito, koebe_quarter, markov_oneDim, recurrence, strongMarkov, timeChange |
| 6 | `theorem_1_10_a` | PROVED_REL | ito, koebe_quarter, ltu, strongMarkov, support, timeChange |
| 7 | `theorem_1_10_b` | PROVED_REL | blumenthal, koebe_quarter, ltu, support |
| 8 | `proposition_3_1_a` | PROVED_REL | birkhoff, hormander, ito, markov_oneDim, recurrence, strongMarkov, timeChange |
| 9 | `proposition_3_1_b` | PROVED_REL | birkhoff, hormander, ito, markov_oneDim, strongMarkov, timeChange |
| 10 | `proposition_3_2_a` | PROVED_REL | birkhoff, hormander, ito, koebe_quarter, markov_oneDim, strongMarkov, timeChange |
| 11 | `proposition_3_2_b` | PROVED_REL | hormander, ito, koebe_quarter, markov_oneDim, strongMarkov, timeChange |
| 12 | `lemma_2_4_leftHull` | PROVED | none |
| 13 | `scaling_leftHull` | PROVED | none |
| 14 | `reflection_leftHull` | PROVED | none |

The other 12 sealed theorems (`loewnerMap_eq`, `loewnerMap_exists_solution`, `scaling_centeredLoewnerMap`,
`scaling_rightHull`, `reflection_rightHull`, `reflection_centeredLoewnerMap`, `lemma_2_4_rightHull`, the four
`concatenation_*`, `sle_duality`) are all PROVED with no externals. Totals: PROVED 17, PROVED_REL 9; among roots PROVED 5,
PROVED_REL 9. The union of externals over the 26 sealed theorems is 13 of the 18; the 5 consumed by none are
`loewnerMap_conformal`, `scale_function_hit`, `koebe_distortion`, `levy_characterization`, `girsanov_law_equiv`
(no sealed closure contains them, and no module outside `External/` imports them).

Cross-check of the probe against Lean's own `#print axioms` on 10 roots (`loewner_wellDefined`, `exists_admissibleDensity`,
`lemma_2_4_leftHull`, `sle_duality` clean; `exists_sleDriver`, `theorem_1_8`, `theorem_1_8_c_zero`, `theorem_1_10_a`,
`theorem_1_10_b`, `proposition_3_2_b` carry `sorryAx`): agrees in every case. The closure walker reports no `SORRYUSER`
constant outside genuine EXTERNAL exports, and the build log shows `sorry` warnings only in the 18 External files.

Verdict item 3: PASS.

## 4. Status reporting (STATUS.md, RESULTS.md)

STATUS.md (working tree):

- `DRAFT_ANCHORS: 0`, `UNREGISTERED_SORRIES: 0`, `DRAFT_IMPORT_VIOLATIONS: 0`: correct (no DRAFT entries; no `sorry` outside the 18 manifest-registered files; nothing to violate).
- `PROVED: 17  PROVED_REL: 9`, `SEALED DEFINITIONS: 24` (17 + 3 + 4), `EXTERNALS: 18` (4 + 13 + 1), "Manifest: 68 anchors", graph figures
  (286 nodes, 794 edges, 31 anchors, 19 external leaves, 62 SOURCE_GAPs, 306 coverage items, 96 excluded): all reproduced.
- Per-root `PROVED_REL{...}` lists in the M7 and M8 blocks (`theorem_1_10_a/b`, `theorem_1_8`, `theorem_1_8_c_zero`,
  `proposition_3_1_a/b`, `proposition_3_2_a/b`, `exists_sleDriver`): compared by script with the probe; 9 of 9 agree
  (STATUS uses long names, RESULTS the short names).

RESULTS.md:

- Header facts: 68 anchors (24 + 26 + 18), manifest sha prefix `f06c7d34`, 297 modules, 49,419 lines: all reproduced (`wc -l` over tracked `.lean`).
- §2 root table (14 rows: status and externals): compared by script with the probe: 14 of 14 agree.
- §5 external table (18 rows): the "Consumers" column was recomputed from the probe and agrees for all 18 rows; the 5 "none" rows
  are exactly the 5 unused externals; `markov_oneDim` is consumed as the hypothesis `MarkovOneDim` and discharged at the
  roots (`Internal/Proposition_3_1_A.lean`, `Internal/Phases/Prop32A.lean`, `ConverseMain.lean`, `Lemma37.lean`).
- §1 counts: 49 rows in §3, tags FULL 19 / RULED 11 / PARTIAL 13 / EXT 2 / NONE 4: recounted from the table, agree.
- §3 statuses, spot-check by re-running the probe on the named declarations: 20 declarations through the CLI
  `python3 -I tools/leanprobe.py externals MODULE DECL` and 52 more through `leanprobe.externals_many` (the same code), 72 in total
  (34 PROVED, 38 PROVED_REL), 0 mismatches. Rows covered: §2 (rows 19, 22-25, 27, 29), §3 (rows 32-33, 35-41), §4 (rows 42-45), App. A (rows 48, 49), plus
  rows 15, 18, 20, 21 and 26. CLI set: `tendsto_norm_fPath_nhdsWithin`, `isDiffusionSolution_thetaHat`, `ae_clockSup_eq_top`,
  `sle_hits_lower`, `lemma_3_3`, `birkhoff_cosInt_const`, `ae_tendsto_sigmaLogNorm_atBot`, `converse_w_o_upgrade`,
  `integrable_log_inv_distSigma`, `c0_integral_signs`, `lemma_4_1`, `lineApprox`, `exists_lemma44_path`,
  `map_exp_eq_of_markov`, `exists_isDiffusionKernel`, `lemma_3_12`, `map_pathObs_eq_zero`,
  `rightHull_eq_image_leftHull_revDriver`, `IsSLEDriver.indep_shift_past`, `lemma_3_9`. Every declaration RESULTS calls PROVED
  (34 probed) is PROVED with no externals; every PROVED_REL list matches exactly. The `[hMO]` convention is honest: the
  declarations flagged `[hMO]` take `hMO : MarkovOneDim(For)` and no unflagged cited declaration does.
- Gaps (§7), three gap items refuted-by-grep (no fuller Lean statement exists):
  - Row 11/16/17 (Def 2.1, Lemmas 2.2, 2.3): no occurrence of `chordal`, Schwarz reflection or prime ends in any Lean file;
    the only "upper half" hits are Koebe-chain and sign docstrings.
  - Gap 9 / row 2 (normalization z(g_t(z) - z) -> 2t): no `Tendsto` statement about `loewnerMap` at infinity anywhere;
    only `centeredLoewnerMap_norm_ge` (growth) exists (`Internal/Disconnect/Growth.lean`).
  - Gap 19 / row 44 (Lemma 4.3 only for U = 0): every use of `loewnerMap_tendstoUniformly` is in `LineApproxSeq.lean` with the
    constant-zero driver; no Hurwitz argument and no general-driver second bullet. Also confirmed Gap 12 (no `(W, W~) =_d (B, B~)`
    statement; `levy_characterization` is consumed by nothing) and Gap 13 (only `e^{2i theta}`-stationarity lemmas exist).
- Every numbered paper environment of the `.tex` (lemmas, props, theorems, definitions, remarks) appears in RESULTS rows or §6.
  The `remark-dense` environment is commented out in the source.
- FULL items checked for "not weaker than the paper":
  - Lemma 2.5 (row 19): Lean `tendsto_norm_fPath_nhdsWithin`, `T_z != top` and `Tendsto ‖f_t(z)‖ (nhdsWithin (life set) T_z) (nhds 0)`
    for continuous `U`, any `z : C`; `fPath` is tied to the frozen `centeredLoewnerMap` by `centeredLoewnerMap_eq_fPath`. Equal to the paper.
  - Lemma 4.1 (row 42): `exists V t` with `IsOpen V`, bounded, nonempty (extra, makes it non-trivial), `0 < t`, and
    `0 < P{Disjoint V L_t and DisconnectsFromInfinity}` for a, b > 0, c^2 <= ab. Not weaker (a, b > 0 is the R5 equivalent of a, b != 0 under PSD).
  - Def 1.9 (row 8): `DisconnectsFromInfinity S S'` is the literal source clause (S' disjoint from each unbounded component of S^c).
  - Lemma 2.4 (row 18): `IsConnected (leftHull U t)` for continuous `U`, all `t`: equals the paper (nonempty included).
  - Lemma 3.6 (row 35), Lemma 3.8 (row 37), Lemma 3.12 (row 41): statements as described; 3.8 is the R14 epsilon-form on the product space.
  Qualification (documentation, see fix F3): rows 25, 35, 36, 37 and 39 are tagged FULL but are stated for `IsSLEDriverAdapted`
  drivers (`IsSLEDriver` plus every path continuous plus a filtration with independent increments), which is a stronger hypothesis than
  the source's a.s.-continuous SLE_Sigma driver. The sealed roots take plain `IsSLEDriver`, so no sealed statement is affected.

Verdict item 4: PASS, with the documentation qualification F3.

## 5. Audit report per sealed root and approved externals

Every sealed entry's manifest `approval_ref` points at existing files (checked). Mapping (manifest id -> audit file in `review/audits/`):

| Sealed anchor | Audit |
|---|---|
| `loewner_wellDefined` | AU-M4-D1-loewner.md (PASS, PROVED) |
| `exists_admissibleDensity` | AU-M4-D3-density.md (PASS, PROVED) |
| `exists_sleDriver` | AU-M6-S0-exists-driver.md (PASS, PROVED_REL{exists_isBrownianReal}) |
| `theorem_1_8`, `theorem_1_8_c_zero` | AU-M7-G-thm18.md (PASS, PASS) |
| `theorem_1_10_a` | AU-M8-A-thm110a.md (PASS) |
| `theorem_1_10_b` | AU-M8-B-thm110b.md (PASS) |
| `proposition_3_1_a`, `_b` | AU-M7-C2-prop31.md (PASS) |
| `proposition_3_2_a` | AU-M7-D2-prop32a.md (PASS) |
| `proposition_3_2_b` | AU-M7-E-prop32b.md (PASS) |
| `lemma_2_4_leftHull`, `lemma_2_4_rightHull` | AU-M4-D2 / AU-M4-D2b (PROVED_REL{loewnerMap_conformal}), superseded by AU-M7-U1-lemma-2-4-noext.md (PASS, now PROVED) |
| `scaling_leftHull`, `reflection_leftHull` | AU-M4-D1b-scaling-reflection.md (PASS) |
| `scaling_centeredLoewnerMap`, `scaling_rightHull`, `reflection_rightHull`, `reflection_centeredLoewnerMap` | AU-M4-D1c-maps-righthulls.md (PASS) |
| `loewnerMap_eq`, `loewnerMap_exists_solution` (and defs `loewnerMap`, `centeredLoewnerMap`, `rightHull`) | AU-M4-gt.md (PASS) |
| `concatenation_*` x4 | AU-M6-D1d-concatenation.md (PASS) |
| `sle_duality` | AU-M6-S4-duality.md (PASS) |
| 17 M1 definitions; M2 statements | AU-M1-carriers.md; AU-M2-roots.md (drafts ACCEPT, C1-C4 resolved by R13-R16) |
| 4 R25 definitions and 13 externals | AU-M5-ext2.md (PASS) |
| 4 R23 externals and the tooling | AU-M5-ext1.md (PASS) |
| `markov_oneDim` (R29) | no AU file: two reviews (reviewer-M7-markov-1, -2) recorded in `review/approvals/M7.md` and ERRATA R29 (see F6) |

Staleness check: the externals sets named in the M6-S0, M7-C2, M7-D2, M7-E, M7-G, M8-A and M8-B audits equal the current probe
output for the same roots (compared by script). The renaming commit 940e9c4 changed only comments/docstrings plus the two renames
`lemma_3_2 -> lemma_3_3`, `lemma_3_7 -> lemma_3_9`; the gate and all spot-check statuses are unaffected.

PROVED_REL roots name only approved externals: every external in any root's closure is one of the 18 manifest EXTERNAL entries, each
with `approved_by: Ewain Gwynne`, an `approval_ref` (R23 for 4, R25 for 13, R29 for `markov_oneDim`) and `approval_version` 1 (dates
2026-10-30, and 2026-10-31 for R29). The R23/R25 batches match ERRATA (4 + 13 names); R29 is recorded in ERRATA and the M7 packet
("Item 1 answered 2026-10-31: approved as R29").

Verdict item 5: PASS (F6 is an optional record-keeping improvement).

## 6. Approvals consistency (five spot-checks, plus four more)

- R14 (epsilon-form in Props 3.2): `proposition_3_2_a` concludes `forall eps > 0, exists t : R>=0, t < T_z and infDist z (L t) < eps`;
  `proposition_3_2_b` concludes `exists eps > 0, forall t, t < T_z -> eps <= infDist z (L t)`, both a.s., both for every `z != 0`, and
  with the R7/R15 admissible-p hypothesis, R5 (a, b > 0), R12 (`Omega : Type`). Matches R14 verbatim.
- R20 (Lemma 4.1 repair): `Internal/Disconnect/Lemma41Core.lean` follows the two-scale construction: `x = 2C`, target points
  `2C +- i/2` (eps = 1/4), preimages of the zero-driver map `exists_zeroMap_eq` (`pp`, `pm`), `d = min(dist(pp, slit), dist(pm, slit))`,
  `delta = min(d/2, 1/8)` (R20's `delta <= min(eta/2, eps/2, ...)`), events E1 (small on [0,T]), E23, E4. The frozen statements of
  Lemma 4.1's consumers are unchanged.
- R27 (hitting lemma replaces Girsanov): `sle_hits_lower` is consumed in `Prop32BUp.lean`, `Prop32BUpHit.lean` and
  `Thm110AMarkov.lean` (single point Lambda' = {e^{i theta*}}, fixed rational sigma-time); `girsanov_law_equiv` is in no sealed closure and
  no `Internal/` or `Infrastructure/` file mentions it except docstrings.
- R28 (Prop 1.5 coupling form): `sle_duality` takes `0 <= a, 0 <= b, c^2 <= ab, 0 < t`, driver
  `U~ s = I (U (t - s) - U t) + I (U (max s t) - U t)` (NNReal truncated subtraction = `(t - s)^+`), concludes `IsSLEDriver b a (-c) U~` and the
  a.s. hull and map identities `L~_t = i R_t`, `R~_t = i L_t`, `f~_t(w) = i z`. Matches R28 word for word. (Cosmetic: the frozen
  docstring still says "proposed ruling"; it is in the frozen prefix, left alone, see F8.)
- R29 (`markov_oneDim`): `External/MarkovOneDim.lean` states what R29 describes (Markov property and pi-equivariance of the transition kernel
  for smooth pi-periodic coefficients with the Hormander condition; `hp0 : 0 <= p` present, the fix from review 1). The in-project predicate
  `MarkovOneDim` (`Internal/Stationary/SLEStatKernel.lean`) is discharged by `External.markov_oneDim` at the roots, which type-checks, so
  the internal hypothesis is no stronger than the approved external.
- Also checked: R18 (`concatenation_image_leftHull` reads `f_t(L_{s+t} \ L_t) = L_{t,s+t} \ R_t`), R10/P7 (`theorem_1_10_b` is `forall t > 0` inside one
  a.s. quantifier), R11/R17 (`theorem_1_8_c_zero` one theorem with thin/swallowing/hitting for a, b > 0), R6/P3 (`IsSLEDriver` fields),
  R7 (`IsAdmissibleDensity` body), AUTO-1 (four concatenation anchors with `approval_ref` naming AUTO-1 and the two reviews; T12 confirmed in the M6 packet).
- R26 safety rule "AUTO never applies to EXTERNAL inputs": all 18 externals carry R23, R25 or R29 (author approvals), none AUTO.

Verdict item 6: PASS.

## 7. Misleading or stale statements

I found no substantive misreport: no PROVED that is PROVED_REL (all 17 sealed PROVED and all 34 probed internal PROVED were confirmed),
no external claimed unused that is consumed (the 5 "none" rows are in no closure and imported by no module) and none claimed used that is not
(all 13 appear in at least one closure with the consumers listed). The items below are documentation defects only.

1. **RESULTS.md §0 (line 28-29), row 19 notes, and §8.1 last paragraph (lines 259-260) are now false.** They say ERRATA.md ("Lemma 3.8, L1590-1600") and
   STATUS.md ("Lemma 3.9 (converse without the upgrade") still use the earlier §3 numbers and that STATUS.md "Next (M9)" still lists Lemma 2.5 as
   remaining. Commit 940e9c4 already changed ERRATA.md to "Lemma 3.10 (lem-log-finite-exp)" and STATUS.md to "Lemma 3.8 (converse without the upgrade"
   and the STATUS "Next (M9)" line says "Lemma 2.5 is proved".
2. **RESULTS.md header** says "git HEAD `e3ee94b`; this file uncommitted". HEAD is `cb99fd4` and RESULTS.md is committed (cb99fd4).
3. **"A fresh clone of the pushed repo builds and passes the full gate"** (new STATUS.md M9 paragraph, and `review/approvals/M9.md` first lines): not
   verifiable here, and `origin/master` is still `e3ee94b` (2 commits behind), so a clone of the pushed repo cannot have exercised the M9 tree. Re-run the
   fresh-clone gate on the final pushed commit or word the claim with the commit tested.
4. **"Adapted" is never defined in RESULTS.md** (see item 4): rows 25, 35, 36, 37 and 39 are FULL only in adapted-driver form.
5. **ERRATA.md "Further open modeling questions from the global reviews" (lines ~194-206), the heading "Open (found during M3; awaiting the author)", and the
   last STATUS.md paragraph ("Next (M4): ... Deferred anchors: ... Lemma 2.5, Lemma 4.3, and the externals E1-E13 (M5)")** are stale: every item has been
   resolved by R18-R22, R27, R29 or proved in M7/M8 (the list already annotates one bullet "Resolved in M7").
6. **STATUS.md "M9 packet outcome: release as is, ..."** can be read as an author ruling. `review/approvals/M9.md` records that the author replied only "continue
   working" and that the orchestrator took the changes-nothing defaults. No frozen artifact depends on it, but the wording should say so.
7. Row 4 and §6 describe Prop 1.5 as having no DEPGRAPH node: correct (only a coverage item `inv:prop-duality`).

Verdict item 7: PASS with the documentation fixes below.

---

## Fix list (none blocks closure)

Should fix before release (readers are misled):

- **F1.** `RESULTS.md` lines 28-29, row 19 notes (parenthetical "STATUS.md 'Next (M9)' still lists..."), and §8.1 last paragraph (lines 259-260): delete or
  rewrite; ERRATA.md and STATUS.md already use the paper numbering since 940e9c4. Keep only the statement that module file names `Lemma37*.lean`/`Lemma38*.lean`
  keep the earlier numbers.
- **F2.** Replace "A fresh clone of the pushed repo builds and passes the full gate" (STATUS.md M9 paragraph; `M9.md` header) by a verified statement:
  push cb99fd4 plus the pending edits, clone that commit into an empty directory, run `tools/check.sh`, and record the commit hash tested.

Optional documentation clean-up:

- **F3.** Define "adapted" in `RESULTS.md` §0 (`IsSLEDriverAdapted` = `IsSLEDriver` + all paths continuous + filtration with independent increments) and tag rows
  25, 35, 36, 37, 39 "FULL (adapted-driver form)" or add a note that the roots convert via `hU.exists_adapted`.
- **F4.** `RESULTS.md` header: replace "git HEAD `e3ee94b`; this file uncommitted" by the commit actually audited (or drop the hash).
- **F5.** ERRATA.md and STATUS.md: mark the "Further open modeling questions" list and the trailing "Next (M4)" paragraph as resolved/historical.
- **F6.** Add a short audit record for R29 `markov_oneDim` (or cite the two reviews' verdicts in the manifest `approval_ref`, already naming `review/approvals/M7.md`).
- **F7.** STATUS.md wording: "M9 packet outcome (orchestrator defaults; the author gave no pick)".
- **F8.** Informational: the frozen docstring of `Frozen/Proposition_1_5.lean` still says "(proposed ruling)" although R28 approved it. Changing it needs a versioned
  successor, so leave it; optionally note it in ERRATA R28.
- **F9.** Informational: `review/approvals/drafts/MarkovOneDim.lean.txt` is a tracked draft containing `sorry` (text, not built); consider deleting it before any
  public release. `lakefile.toml` sets `maxSynthPendingDepth = 3` (Mathlib template; not an override of the forbidden kind).

## Commands run (all from `~/complex-sle`, `export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"`)

- `tools/check.sh` (full); `lake build` (second run, log scanned for `declaration uses`/errors).
- `python3 tools/proof_depgraph.py --db DEPGRAPH.md --manifest DEPGRAPH_COVERAGE.md --source-root . --require-reviewed --require-complete-coverage --require-initial-lean-status --require-all-reachable --check` (exit 0) and `--report`.
- `python3 -I tools/leanprobe.py externals-all frozen-anchor-manifest.json` (27 lines saved and compared by script); `python3 -I tools/leanprobe.py externals MODULE DECL` x20;
  `leanprobe.externals_many` on 52 internal declarations and on the 24 sealed definitions; `python3 -I tools/leanprobe.py axioms MODULE DECL` x10.
- Git history scripts over `ComplexSLE/Frozen`, `ComplexSLE/External`, `frozen-anchor-manifest.json` (per-version prefix/body/suffix comparison; manifest field diff per commit);
  `git diff HEAD --stat`; `git log origin/master..HEAD`.
- Greps listed in section 3 over `git ls-files '*.lean'`, and the `.tex` environment/label coverage scan of section 4.

Scratch `.lake/probes/au-m9/` was deleted after writing this report. `leanprobe` itself writes and deletes temporary `.lake/probes/tmp*.lean` files;
a pre-existing `.lake/probes/rdual` belongs to another session and was left untouched.
