# AU-M4-D1b — `ComplexSLE.scaling_leftHull`, `ComplexSLE.reflection_leftHull` (auditor-M4-D1b/sonnet, 2026-10-30)

Verdict: **PASS** for both (prover M4-D1b/sonnet; fresh auditor). Status: **PROVED** (no External inputs).
ABI 0b072ed0…259f5 / a622f14f…c7cb7 = manifest; guard OK; axioms propext, Classical.choice, Quot.sound.
Statement fidelity: (2.1) L549-552 with r>0, t/r² in ℝ≥0, driver s ↦ rU(s/r²); (2.2) L553-557 both conj and
negation parts; U : ℝ≥0 → ℂ per T7. Binders: EXCESS 0 (hU is a source premise, unused — strengthening, harmless).
Provider: Transform.lean (imports only Defs.LeftHull + Mathlib); ℝ≥0∞ / toNNReal arithmetic checked.
Independently typed `example`s compile. Per R16 these are the left-hull parts only; source nodes (2.1)/(2.2)
count as proved once the right-hull and f_t parts are proved.
Non-blocking: stale "quarantined" docstrings (fixed by orchestrator).
