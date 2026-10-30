# AU-M4-D1 — `ComplexSLE.loewner_wellDefined` (auditor-M4-D1/sonnet, 2026-10-30)

Verdict: **PASS** (two keys: prover M4-D1/sonnet; fresh auditor). Status: **PROVED** (no External inputs;
`ext:picard-lindelof` supplied by Mathlib's `ODE_solution_unique_of_mem_Icc_right`).

1. Frozen bytes / ABI: guard OK; abi_sha256 627a9c24…0257f = manifest. PASS
2. Statement fidelity (Def 1.1, L251-268; carriers R4–R12): existence on [0,T_z), uniqueness for every τ;
   degenerate cases z = U 0 (T_z = 0), τ = 0, T_z = ⊤ behave as in the source. PASS
3. Binders: U, z (TYPING), hU (SOURCE); EXCESS 0. PASS
4. Provider: 150 lines, imports only Defs.AbsorbingTime + Mathlib ODE; no forbidden constructs. PASS
5. Axioms: propext, Classical.choice, Quot.sound. PASS
6. tools/check.sh --quick: ALL CHECKS PASSED. PASS
Minor: no separate independently-typed `example`; the ABI match pins the type.
