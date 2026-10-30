# Status ledger

M2 roots frozen — 2026-10-30.

```text
DRAFT_ANCHORS: 14
  ComplexSLE/Frozen/LoewnerWellDefined.lean    ComplexSLE.loewner_wellDefined
  ComplexSLE/Frozen/Lemma_2_13_Exists.lean     ComplexSLE.exists_admissibleDensity
  ComplexSLE/Frozen/ExistsSLEDriver.lean       ComplexSLE.exists_sleDriver
  ComplexSLE/Frozen/Theorem_1_8.lean           ComplexSLE.theorem_1_8
  ComplexSLE/Frozen/Theorem_1_8_CZero.lean     ComplexSLE.theorem_1_8_c_zero
  ComplexSLE/Frozen/Theorem_1_10_A.lean        ComplexSLE.theorem_1_10_a
  ComplexSLE/Frozen/Theorem_1_10_B.lean        ComplexSLE.theorem_1_10_b
  ComplexSLE/Frozen/Proposition_3_1_A.lean     ComplexSLE.proposition_3_1_a
  ComplexSLE/Frozen/Proposition_3_1_B.lean     ComplexSLE.proposition_3_1_b
  ComplexSLE/Frozen/Proposition_3_2_A.lean     ComplexSLE.proposition_3_2_a
  ComplexSLE/Frozen/Proposition_3_2_B.lean     ComplexSLE.proposition_3_2_b
  ComplexSLE/Frozen/Lemma_2_4_LeftHull.lean    ComplexSLE.lemma_2_4_leftHull
  ComplexSLE/Frozen/Scaling_LeftHull.lean      ComplexSLE.scaling_leftHull
  ComplexSLE/Frozen/Reflection_LeftHull.lean   ComplexSLE.reflection_leftHull
UNREGISTERED_SORRIES: 0
DRAFT_IMPORT_VIOLATIONS: 0
SEALED_THIS_TURN: 0
SEALED DEFINITIONS: 17 (M1)
EXTERNALS: 0 frozen
PROVED: 0   PROVED_REL: 0
```

Manifest: 31 anchors. Gate: `tools/check.sh` passes (build, modules, guard, ABI, forbidden).

Next (M3): source dependency graph (build-proof-dependency-graph), slices A–D.
Deferred anchors: g_t / f_t / R_t (after `loewner_wellDefined` is proved), Prop 1.5,
right-hull and f_t parts of (2.1)–(2.4) and Lemma 2.4, the concatenation property, Lemma 2.5,
Lemma 4.3, and the externals E1–E13 (M5).
