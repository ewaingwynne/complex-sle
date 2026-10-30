# Status ledger

M5 in progress — 2026-10-30: EXTERNAL state live (tools/leanprobe.py externals-all computes PROVED/PROVED_REL in check.sh).
M4 complete — 2026-10-30 (Tier D, except Lemma 2.4 which needs the external ext:lawler-4.5 and duality (2.4); see M5). P10 resolved by R20; P11/P12 accepted as R18/R19.

M3 dependency graph published — 2026-10-30 (M2 roots frozen earlier the same day).

```text
DRAFT_ANCHORS: 10
  ComplexSLE/Frozen/Lemma_2_4_RightHull.lean            ComplexSLE.lemma_2_4_rightHull
  ComplexSLE/Frozen/ExistsSLEDriver.lean       ComplexSLE.exists_sleDriver
  ComplexSLE/Frozen/Theorem_1_8.lean           ComplexSLE.theorem_1_8
  ComplexSLE/Frozen/Theorem_1_8_CZero.lean     ComplexSLE.theorem_1_8_c_zero
  ComplexSLE/Frozen/Theorem_1_10_A.lean        ComplexSLE.theorem_1_10_a
  ComplexSLE/Frozen/Theorem_1_10_B.lean        ComplexSLE.theorem_1_10_b
  ComplexSLE/Frozen/Proposition_3_1_A.lean     ComplexSLE.proposition_3_1_a
  ComplexSLE/Frozen/Proposition_3_1_B.lean     ComplexSLE.proposition_3_1_b
  ComplexSLE/Frozen/Proposition_3_2_A.lean     ComplexSLE.proposition_3_2_a
  ComplexSLE/Frozen/Proposition_3_2_B.lean     ComplexSLE.proposition_3_2_b
UNREGISTERED_SORRIES: 0
DRAFT_IMPORT_VIOLATIONS: 0
SEALED_THIS_TURN (M4): 10 (loewner_wellDefined, scaling_leftHull, reflection_leftHull, exists_admissibleDensity,
  loewnerMap_eq, loewnerMap_exists_solution, scaling_centeredLoewnerMap, scaling_rightHull, reflection_rightHull,
  reflection_centeredLoewnerMap)
SEALED DEFINITIONS: 20 (17 in M1; loewnerMap, centeredLoewnerMap, rightHull in M4, R21)
EXTERNALS: 4 frozen (R23): exists_isBrownianReal, support_sleDriver, loewnerMap_conformal,
  loewnerMap_tendstoUniformly  (ComplexSLE/External/)
PROVED: 10   PROVED_REL: 1
  PROVED_REL{loewnerMap_conformal}  ComplexSLE.lemma_2_4_leftHull  (AU-M4-D2)
  PROVED  scaling_centeredLoewnerMap, scaling_rightHull, reflection_rightHull, reflection_centeredLoewnerMap (AU-M4-D1c)
  Source items fully proved: Def 1.1 well-definedness, (2.1), (2.2), Lemma 2.13 (existence).
  PROVED  ComplexSLE.loewnerMap_eq, ComplexSLE.loewnerMap_exists_solution  (AU-M4-gt; characterization of g_t)
  PROVED  ComplexSLE.exists_admissibleDensity  (AU-M4-D3; Case 1 by an authorised route replacing step:p-case1-*)
  PROVED  ComplexSLE.scaling_leftHull, ComplexSLE.reflection_leftHull  (AU-M4-D1b; left-hull parts of (2.1)/(2.2) per R16)
  PROVED  ComplexSLE.loewner_wellDefined  (audit review/audits/AU-M4-D1-loewner.md)
```

Manifest: 45 anchors (graph header FROZEN_MANIFEST hash refreshed after each manifest change; graph anchor fields unchanged). Gate: `tools/check.sh` passes (build, modules, guard, ABI, forbidden).

Graph: DEPGRAPH.md / DEPGRAPH_COVERAGE.md. 286 nodes, 794 edges, 31 anchors, 19 external leaves,
62 explicit SOURCE_GAP nodes, 306 coverage items (96 excluded). Every record has an independent review
(slice reviewers A–D, global-reviewer, and global-verifier as GLOBAL_REVIEWER). The full gate passes:
`proof_depgraph.py --require-reviewed --require-complete-coverage --require-initial-lean-status
--require-all-reachable --check`.
Author items open: the modeling questions in ERRATA.md. Graph amendments R20-disc-setup and
R20-disc-E1-positive (reviewed: graph/reviews/R20-amend.review.md) encode R20.

Next (M4): Lean proofs of the Tier-D frontier (deterministic Loewner core, stationary density).
Deferred anchors: g_t / f_t / R_t (after `loewner_wellDefined` is proved), Prop 1.5,
right-hull and f_t parts of (2.1)–(2.4) and Lemma 2.4, the concatenation property, Lemma 2.5,
Lemma 4.3, and the externals E1–E13 (M5).
