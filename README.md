# complex-sle

Lean 4 / Mathlib formalization of

> E. Gwynne and J. Pfeffer, *Loewner evolution driven by complex Brownian motion*,
> arXiv:2203.07313v4 (2023).

Status: **Phase 0 (skeleton)**. Nothing has been formalized yet. See `PLAN.md` for the
campaign plan and `STATUS.md` for the ledger.

Results that depend on classical inputs absent from Mathlib (stochastic calculus, Koebe
theorems, …) are reported as *proved relative to* explicitly listed, author-approved
external statements. They are never counted as unconditionally proved.

Toolchain: Lean `v4.36.0-rc2`, Mathlib `v4.36.0-rc2` (see `lake-manifest.json`).
