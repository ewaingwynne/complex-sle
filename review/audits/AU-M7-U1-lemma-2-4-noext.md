# AU-M7-U1 — Lemma 2.4 rerouted without externals (auditor-M7-U1/sonnet, 2026-10-30)

Anchors `lemma_2_4_leftHull`, `lemma_2_4_rightHull` (frozen bytes and ABI unchanged). Providers repointed to
Internal/Hull/ConnectedNoExt.lean (prover M7-U1/sonnet), using in-project openness of ℂ∖L_t (Polar/PolarDerivShift),
holomorphy of w ↦ solPath w t (Polar/PolarDeriv, Grönwall remainder estimate, checked by hand), agreement with loewnerMap,
and a direct boundedness proof for L_t. Verdict: **PASS** for both. Status upgraded from PROVED_REL{loewnerMap_conformal}
to **PROVED** (mechanical: externals []). The old external-based Hull/Connected.lean was dead code and has been removed.
`External.loewnerMap_conformal` is now consumed by no proved result.
