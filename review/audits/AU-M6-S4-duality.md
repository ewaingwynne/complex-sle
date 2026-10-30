# AU-M6-S4 — `ComplexSLE.sle_duality` (Prop 1.5, coupling form R28) (auditor-M6-S4/sonnet, 2026-10-30)

Verdict: **PASS** (prover M6-S4/sonnet). Status: **PROVED** (no externals). ABI = manifest; guard OK; EXCESS 0
(ha, hb, hc standing; ht, hU source; unused by the proof). Locality of hulls/maps in the driver on [0,t]; pathwise
identities use U 0 = 0 only for R̃_t and f̃_t; driver law via finite-dimensional laws (past/future independence +
time reversal of the past), continuity and Ũ 0 = 0 supplied directly, not transferred. Non-vacuity checked via
exists_sleDriver. Note: equality in law itself is not a Lean theorem; it follows from the coupling given measurability
of the hull functionals and uniqueness of the driver law on path space (as in the R28 docstring).
