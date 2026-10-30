# AU-M4-D3 — `ComplexSLE.exists_admissibleDensity` (auditor-M4-D3/sonnet, 2026-10-30)

Verdict: **PASS** (prover M4-D3/fable; fresh auditor). Status: **PROVED** (no External inputs).
ABI 8f546735…d461 = manifest; guard OK; full tools/check.sh passes; axioms propext, Classical.choice, Quot.sound.
Statement: binders a, b, c; 0<a, 0<b, c²≤ab (R5); IsAdmissibleDensity = Lemma 2.14 hypotheses (R7); no junk
satisfaction (C² off the open set makes the `deriv` clause genuine; normalisation excludes p = 0). EXCESS 0.
Route: c² < ab via q = e^Φ ∫_u^{u+π} e^{−Φ}, p = kq/D (orchestrator-authorised; replaces graph steps
step:p-case1-*; checked correct by hand). c² = ab via (2.32) (abstract SingularData core, ∞/∞ L'Hôpital at the
right endpoint, periodic gluing); c = −√(ab) by u ↦ −u (step:p-wlog-c-nonneg; consistent with R19).
Notes: positivity off a discrete set is not part of the frozen statement (open ERRATA modeling item for Lemma 3.3).
SingularODE.lean (452 lines) was checked structurally, not line by line.
