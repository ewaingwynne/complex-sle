# AU-M4-gt — g_t / f_t / R_t unit (auditor-M4-gt/sonnet, 2026-10-30)

Anchors: def.loewnerMap.v1, def.centeredLoewnerMap.v1, def.rightHull.v1 (SEALED definitions);
thm.loewnerMap_eq.v1, thm.loewnerMap_exists_solution.v1 (SEALED, PROVED). Author approval: ERRATA.md R21.
Verdict: **PASS** for all five. ABI = manifest; frozen bytes reproduce the approved drafts; definitions mean the source
objects on ℂ∖L_t with no junk; unique choice justified by the PROVED loewner_wellDefined; the two theorems are a full
characterization; EXCESS 0; axioms propext, Classical.choice, Quot.sound; check.sh --quick passes.
Minor: Defs/LoewnerMap.lean depends on the sealed theorem anchor loewner_wellDefined (visible via imports only, since
definition_closure lists definition files).
