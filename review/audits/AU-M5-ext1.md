# AU-M5-ext1 — EXTERNAL tooling and batch-1 externals (auditor-M5-ext1/sonnet, 2026-10-30)

Part A (tools/check_frozen_anchors.py, leanprobe.py `externals`/`externals-all`, manifest_add.py, check.sh): **PASS**.
Negative fixtures (stray sorry, custom axiom, opaque with sorry, sorry in types/hypotheses/instances, native_decide,
impostor external) are all UNSOUND; stray files under External/ fail; EXTERNAL import restrictions hold.
Minor gaps fixed by the orchestrator: symlinks under External/ are rejected; definition and EXTERNAL anchors may not
reach a DRAFT_SORRY module. Noted, not fixed: the Python import regex ignores «»-quoted names and several modules per
line (defence in depth only; the Lean closure walk catches any resulting sorry).
Part B: the four files under ComplexSLE/External/ reproduce the R23-approved statements byte-for-byte; ABI = manifest;
full tools/check.sh passes (EXTERNALS OK, 10 sealed theorems PROVED).
