# AU-M6-S0 — `ComplexSLE.exists_sleDriver` (auditor-M6-S0/sonnet, 2026-10-30)

Verdict: **PASS** (prover M6-S0/sonnet). Status: **PROVED_REL{ComplexSLE.External.exists_isBrownianReal}** (mechanical).
ABI = manifest; guard OK; EXCESS 0 (a, b > 0 by R13; hb unused). Construction: two independent copies of a standard BM on
Ω₀ × Ω₀, U = L(B₁, B₂) with matrix A = [[√a, 0], [c/√a, √(b − c²/a)]], A Aᵀ = covMatrix a b c; independence via
iIndepFun_prod_pair; increment law via a new characteristic-function lemma for linear images of product Gaussians
(Infrastructure/Gaussian/MapProd.lean). The only sorryAx user in the 57 692-constant closure is the external.
