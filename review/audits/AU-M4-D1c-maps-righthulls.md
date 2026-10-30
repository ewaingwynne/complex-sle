# AU-M4-D1c — maps and right hulls of (2.1)/(2.2) (auditor-M4-D1c/sonnet, 2026-10-30)

Anchors: scaling_centeredLoewnerMap, scaling_rightHull, reflection_rightHull, reflection_centeredLoewnerMap
(author approval ERRATA.md R22; split R16). Prover: M4-D1c/sonnet. Verdict: **PASS** for all four. Status: **PROVED**.
ABI = manifest; guard OK; axioms propext, Classical.choice, Quot.sound. Fidelity checked against L536-557; paired
membership binders are domain typing; EXCESS 0. Providers use loewnerMap_exists_solution + loewnerMap_eq (no unfolding
of Classical.choose) and the left-hull Transform lemmas; no DRAFT_SORRY anchor/provider imported. Independently typed
examples compile. With the left-hull parts (AU-M4-D1b), source items (2.1) and (2.2) are now fully proved (R16).
