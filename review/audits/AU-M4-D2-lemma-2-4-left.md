# AU-M4-D2 — `ComplexSLE.lemma_2_4_leftHull` (auditor-M4-D2/sonnet, 2026-10-30)

Verdict: **PASS** (prover M4-D2/fable; fresh auditor). Status: **PROVED_REL{ComplexSLE.External.loewnerMap_conformal}**
(mechanical: leanprobe externals). ABI = manifest; guard OK; EXCESS 0.
Route (replaces the source sketch, SOURCE_GAP T5): separation L_t = A ⊔ B; minimiser of the lower-semicontinuous T_z on
compact B; thickening V of B with ∂V ∩ L_t = ∅; backward stability bound |f_s| ≥ η on ∂V; maximum modulus for 1/f_s on V
contradicts absorption of the minimiser. The external supplies openness of ℂ∖L_s, boundedness of L_t and holomorphy of g_s.
Helper files LocalExistence/BackwardBound/PicardLindelofBall were checked via their statements, not line by line.
