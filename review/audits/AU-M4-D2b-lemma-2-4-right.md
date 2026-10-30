# AU-M4-D2b — `ComplexSLE.lemma_2_4_rightHull` (auditor-M4-D2b/sonnet, 2026-10-30)

Verdict: **PASS** (prover M4-D2b/sonnet; fresh auditor). Status: **PROVED_REL{ComplexSLE.External.loewnerMap_conformal}**
(inherited from lemma_2_4_leftHull). ABI = manifest; guard OK; EXCESS 0.
Route: duality (2.4) proved in-project (Internal/Loewner/Duality.lean): R_t^U = (−i)·L_t^V with V(s) = i(U(t−s) − U_t)
(constant for s ≥ t), via time reversal of closed-interval solutions; equivalent to the printed (2.4) since L^{−V} = −L^V.
Then lemma_2_4_leftHull for V and the image under z ↦ −iz. Lemma 2.4 (both parts, R16) is now proved relative to
loewnerMap_conformal.
