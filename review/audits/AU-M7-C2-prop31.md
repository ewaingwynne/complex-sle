# AU-M7-C2 — `ComplexSLE.proposition_3_1_a`, `proposition_3_1_b` (auditor-M7-C2/sonnet, 2026-10-31)

Verdict: **PASS** for both. Status (mechanical):
- (a) PROVED_REL{birkhoff_stationary, hormander_oneDim, ito_formula, markov_oneDim, recurrence_stationary,
  strongMarkov_sleDriver, timeChange_isContLocalMartingale}
- (b) the same without recurrence_stationary.
ABI = manifest (unchanged since M2); fidelity vs L1265-1269 and R4–R7, R9, R15; EXCESS 0. All externals are author-approved
(R25, R29) and used within scope; no hypothesis smuggling (lemma_3_3's event hypotheses discharged by PROVED lemmas; hMO
discharged by External.markov_oneDim). Spot-checks sound: Lemma 3.3 density route, constancy of the Birkhoff limit, renewal
recursion, ODE comparison. Import closure (152 modules) has no DRAFT anchor/provider. Cosmetic issues (stale "pending"
docstrings, long lines) fixed by the orchestrator.
