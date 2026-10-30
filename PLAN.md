# Launch plan: Lean formalization of arXiv:2203.07313v4

*Loewner evolution driven by complex Brownian motion* (Gwynne–Pfeffer, v4, 20 Jul 2023).
Draft 2026-10-30. Author rulings of 2026-10-30 (answers to Q1–Q3):
- **Q1 externals:** option (a), relative-to-externals. Each classical input is an exact,
  author-approved Lean statement in state `EXTERNAL`. Results consuming them are
  `PROVED_REL{…}`; cheap externals are discharged in-project later.
- **Q2 scope:** skip §2.4 and §5; skip Remarks 1.3, 1.6, 1.11 and footnote 2; defer Lemma 2.6
  to an optional last phase.
- **Q3 GitHub:** private repo `ewaingwynne/complex-sle`; push automatically at each milestone.

## 0. Ground rules (from lean-orchestrator / build-proof-dependency-graph)

- Required order: **author-frozen anchors → reviewed source dependency graph → Lean proofs.**
- Every anchor is an exact Lean declaration that the author has approved, alone in its own
  `Frozen/` file, recorded in `frozen-anchor-manifest.json`, and created as
  `DRAFT_SORRY` (`by sorry`). Only proofs may be provisional. Sealing replaces the body
  with `by exact Provider.result`.
- PROVED needs two keys: the prover's evidence (checker, compiling the exact export,
  `#print axioms` showing only `propext`, `Classical.choice`, `Quot.sound`), plus a fresh
  Sonnet auditor who tries to refute it.
- Agents: **at most 2 concurrent subagents in total** (Fable counts toward the cap).
  Sonnet does the writing, extraction and every audit. Fable is used only for packets
  flagged HARD (§6). I (orchestrator) do source interpretation, shared APIs, merges,
  commits and seals, and I review every diff myself.
- No custom axioms, no unregistered `sorry`, no heartbeat overrides, files ≤ 1500 lines,
  every file a `module`. Stage explicit paths and never `git commit -a` while writers run.
  The previous campaign's hard rules (`~/formalization/briefs/_hard_rules.md`) are reused
  with `Conjugate/` → `ComplexSLE/`.

## 1. The central feasibility fact

Compared with the pinned Mathlib (commit 9d581dff, 2026-10-27, Lean v4.36.0-rc2):

| Needed by the paper | In Mathlib? |
|---|---|
| Brownian motion (`IsBrownianReal`, scaling, shift, neg) | yes (predicate; independent increments) |
| Filtrations, stopping times, hitting times, martingale convergence, optional stopping | yes |
| Picard–Lindelöf, ODE uniqueness, Schwarz reflection, Hausdorff distance | yes |
| Stochastic integrals, Itô formula (complex), time change / Lévy characterization | **no** |
| Strong Markov property of BM, time reversal of BM, Blumenthal 0-1, Girsanov | **no** |
| Birkhoff pointwise ergodic theorem, invariant σ-algebra results | **no** |
| Hörmander's criterion / smoothing of the SDE semigroup (Lemma A.2) | **no** |
| Feller scale-function hitting lemma [Law05, Lemma 1.24] | **no** |
| Koebe quarter theorem / distortion [Law05, Cor. 3.18, 3.23] | **no** |
| Loewner chains, prime ends [Pom92], Loewner convergence [Law05, Prop. 4.43] | **no** |

So the results split into three tiers:

- **Tier D (deterministic/analytic, feasible now):** Def 1.1, 1.2, 1.9; properties
  (2.1)–(2.4); Lemmas 2.3, 2.5, 2.4, 2.2, 4.3, 4.5; the functions µ, ν, D and the ODE
  construction in Lemma 2.13 (including the closed-form integral
  ∫₀^π µ/D = 8πc(2√(ab−c²)−(a+b))/(√(ab−c²)((a−b)²+4c²))); Remark 2.15; the c = 0
  computations (3.30)–(3.34) and the identity ν + 2cos2u ≡ 0 when c = 0, a − b = 8;
  Lemma 3.5 (ergodic theory, discrete).
- **Tier S (needs stochastic calculus):** Def 1.4 (SLE_Σ), Prop 1.5, Lemmas 2.7, 2.8, 2.11,
  2.14, 2.16, 3.3, 3.4, 3.6–3.10, 4.1, 4.2, 4.4, 4.6, A.1, A.2, Props 3.1, 3.2,
  Thms 1.8, 1.10.
- **Tier X (heavy classical complex analysis):** Lemma 2.6 (prime ends); Koebe theorems.

Tier S is impossible to finish honestly without a decision on external inputs (**[Q1]**).

## 2. Scope (proposed; **[Q2]**)

In scope (every numbered result gets a Lean theorem):
Defs 1.1, 1.2, 1.4, 1.7, 1.9, 2.1, 2.9, 2.10; Prop 1.5; Thm 1.8 (all four phase bullets +
the explicit c = 0 description); Thm 1.10(a),(b); properties (2.1)–(2.4); Lemmas 2.2–2.5,
2.7, 2.8, 2.11, 2.13, 2.14, 2.16, 3.3–3.12, 4.1–4.6, A.1, A.2; Props 3.1, 3.2;
Remarks 2.12, 2.15 (they are claims used later).

Proposed exclusions: §2.4 simulations (no theorem); §5 open questions; Remarks 1.3, 1.6,
1.11 (expository); footnote 2 (non-monotonicity of hulls for U = i√κB, which relies on
[RS05] duality); Lemma 2.6 deferred to an optional last phase (prime-end theory, which
the paper says is "not directly relevant"; prime ends are absent from Mathlib).

## 3. Repository and setup (Phase 0)

- Local project `~/complex-sle`, Lake package `ComplexSLE`, pinned to the **same**
  toolchain and Mathlib commit as `~/formalization`, so the cache is reused.
- Layout: `ComplexSLE/Frozen/` (anchors, one per file), `ComplexSLE/<Area>/` (providers),
  `source/` (arXiv v4 LaTeX eprint + PDF, sha256 pinned), `briefs/`, `review/audits/`,
  `graph/`, `ERRATA.md`, `STATUS.md`, `RESULTS.md` (paper → Lean map), `DEPGRAPH*.md`,
  `frozen-anchor-manifest.json`, `tools/` (checker, depgraph linter, module checker,
  copied from `~/formalization/tools` and the skills), `CLAUDE.md`.
- GitHub: create `ewaingwynne/complex-sle` with `gh repo create` (visibility **[Q3]**),
  set `origin`, push the skeleton. Pushes after that happen at milestones (**[Q3]**).
- Pin the source: download the v4 LaTeX eprint from arXiv into its own directory, use
  `paper.tex` line numbers as graph locators, and record hashes.

## 4. Phase 1: source pass, carriers, errata (orchestrator)

Transcribe every in-scope statement with premises, quantifier order and constant scope.
Watch items found on the first read, for ERRATA rulings by the author:

1. (1.11) says p is "2π-periodic"; Lemma 2.13/2.14 say π-periodic. Rule on which one
   Thm 1.8 quantifies over.
2. Thm 1.8 depends on the choice of p (footnote 1: uniqueness not proved). Proposed
   carrier: **for every** p meeting the Lemma 2.14 regularity hypotheses, the sign
   conclusions hold, plus the existence of such a p (Lemma 2.13). Needs a ruling.
3. Thm 1.8 c = 0 bullet: "hitting phase if a − b ≥ 8" vs Lemma 3.11 "a − b > 8" plus
   Lemma 3.12 for a − b = 8. Consistent, but the split must be recorded.
4. Thm 1.10 assumes a, b ≠ 0; Lemma 4.4 assumes a, b > 0 (the same thing under PSD). Thm
   1.10(b)'s "a.s. for each t > 0" is uniform in t (monotonicity argument).
5. Lemma 3.4 typo "E(f⁰(X₀⁰))"; Lemma 4.4 proof "ℜf₁(x) ≤ −C" should be ℜf₂; Lemma 2.6 proof
   "fₜ = f_{s,t} ∘ f_s|_{Lₜ}" should restrict to ℂ∖Lₜ; Fig. 8 caption s = σ(s+t) − σ(s)
   should be −σ(t).
6. Lemma 2.4's proof says "a.s." in a deterministic lemma, and the argument for "loop not
   surrounding the origin" is sketchy. It may become a SOURCE_GAP node.
7. Lemma 2.13 asserts the solution is "strictly positive except possibly on a discrete set".
   That is used in Lemma 3.3 (density nonzero a.e.).
8. Prop 3.2 is stated "regardless of whether T_z < ∞". The meaning of
   lim_{t→T_z−} dist(z, Lₜ) when T_z = ∞ (the limit exists by monotonicity of Lₜ) must be
   pinned in the carrier.
9. Lemma 4.3's cited proof [Law05, Prop. 4.43] is "extended by replacing ℍ by ℂ". This is
   an external input whose extension is asserted, not proved (SOURCE_GAP).

Carrier proposals, shown to the author as exact Lean before any freeze:

- Driving function `U : ℝ → ℂ` continuous (values on [0,∞) only matter) or `C(ℝ≥0, ℂ)`.
- Loewner flow: maximal solution of ġ = 2/(g − Uₜ). This is a *characterized* object, so
  per the skill: first an exact ∃! well-definedness theorem (frozen, proved, audited),
  then the definition, plus a sorry-free characterization theorem in the same commit.
  Absorbing time `T z : ℝ≥0∞`; hulls `L t = {z | T z ≤ t}`, `R t = (range f_t)ᶜ`.
- SLE_Σ as a predicate on an arbitrary probability space: `(Ω, P, B, B̃)` with B, B̃
  `IsBrownianReal`, jointly Gaussian with Cov(Bₜ, B̃ₜ) = ct/√(ab), and its filtration. All
  theorems quantify over every such space, so no existence of BM is needed.
- Phases (Def 1.7) and "disconnects from ∞" (Def 1.9) are literal `def … : Prop`.
- µ, ν, D: literal formulas. (I), (II): integrals against a given p.

## 5. Phase 1b: anchor selection and freezing

Following the author's ruling in the last campaign, freeze **roots and meaning-carrying
definitions only**. Internal lemmas become graph nodes, are proved under distinct names,
and are mapped in RESULTS.md. Proposed roots (each its own frozen file, so a source theorem
may be split into several anchors with author approval):

- Thm 1.8: four phase bullets (maybe one joint anchor) + c = 0 explicit phases.
- Thm 1.10(a), Thm 1.10(b).
- Prop 1.5 (duality in law), Props 3.1(a,b), 3.2(a,b).
- Lemma 2.13 (existence/properties of p) and Lemma 2.14 (stationarity), both reused by the
  main theorems and of independent interest.
- Deterministic standalone results: (2.1)–(2.4), Lemmas 2.2, 2.4, 2.5, 4.3.
- Definitions: Loewner chain (+ ∃! theorem + characterization), hulls, SLE_Σ predicate,
  phases, disconnection, σ-time change (Def 2.9; this is also a characterized object, via
  Remark 2.12), argument process (Def 2.10; characterized by continuity + lift).

Process per batch (as in the last campaign): I draft the exact declarations, a transient
probe checks they elaborate, a fresh Sonnet runs a statement audit (lean-statement-audit)
against the source, the author sees the complete code, the files are frozen and added to the
manifest, and the checker runs.

## 6. Phase 2: dependency graph (build-proof-dependency-graph)

- Extraction spec (`graph/EXTRACTION_SPEC.md`), mechanical inventory of `paper.tex`, and
  a coverage manifest.
- Four slices aligned to statement/proof units:
  **A** §1–2.3 deterministic Loewner; **B** §2.5–2.7 + App. A; **C** §3; **D** §4.
  Extraction runs two Sonnet extractors at a time (A+B, then C+D). I am the single
  writer/adjudicator. Every node gets a fresh Sonnet reviewer (not its extractor), and one
  fresh Sonnet global reviewer covers the whole closure.
- External results are explicit `EXTERNAL` leaf nodes, each a precise statement with its
  citation (list in §7). Gaps become `SOURCE_GAP` step nodes.
- The gate is the linter with `--require-reviewed --require-complete-coverage
  --require-initial-lean-status --require-all-reachable --check`.

## 7. External inputs (what Tier S consumes), **[Q1]**

E1 complex Itô formula + stochastic integrals against BM [Pro05 II.35];
E2 Lévy characterization / time change of continuous local martingales (used in 2.11, 2.14, 2.16, 3.12);
E3 strong Markov property of (correlated) BM; E4 time reversal of BM on [0,T];
E5 Blumenthal 0-1; E6 Girsanov (only to get P(τ < ∞) > 0 in Prop 3.2(b));
E7 Birkhoff ergodic theorem (continuous-time, stationary increments);
E8 Hörmander's 1-D criterion [Hai11 Thm 1.3] → smooth semigroup (Lemma A.2);
E9 scale-function hitting lemma [Law05, Lemma 1.24];
E10 Koebe quarter theorem [Law05 Cor 3.18] and E11 Koebe distortion [Law05 Cor 3.23];
E12 Loewner convergence under uniform driving convergence [Law05 Prop 4.43, extended];
E13 Brownian support theorem ("BM stays near any continuous path with positive probability")
used in 4.2 and 4.6, standard but unproved in the paper.

Options for the author:
- **(a) Relative-to-externals (recommended).** Each Eᵢ is an exact Lean statement, approved by
  the author, in its own file, with manifest state `EXTERNAL` (a permanent `by sorry`,
  quarantined from everything except a single `ComplexSLE/External/` interface). Results are
  reported as `PROVED_REL{E…}`, never as plain PROVED, and the closure audit lists exactly
  which externals each theorem uses. Later infrastructure phases can discharge the cheaper
  ones in-project (E3, E4, E5, E7, E10, E11, E13 are realistic), which upgrades statuses.
- (b) Build everything in-project. This is a multi-year Mathlib-scale effort (stochastic
  integration alone).
- (c) Tier D only now; Tier S postponed.

## 8. Phase 3: proofs, ordered by the frontier

Tracks (≤ 2 agents at once; each packet gets one Sonnet writer, then a separate Sonnet auditor):

1. **D1 Loewner core:** ∃! maximal ODE solution, absorbing time, Lemma 2.5 (upcrossing
   argument), concatenation (2.3), scaling (2.1), reflection (2.2), Lemma 2.3.
2. **D2 hull geometry:** duality (2.4), Lemma 2.4 (connectedness; *Fable, HARD*),
   Lemma 2.2 (Schwarz reflection + Def 2.1), Lemma 4.5.
3. **D3 stationary density:** Lemma 2.13's analytic content: p₀, p₁, r*, the closed-form
   antiderivative of µ/D (*Fable, HARD*), Case 2 L'Hôpital limits, Remark 2.15, (3.30)–(3.34).
4. **D4 Lemma 4.3** (Hurwitz / normal families; *Fable, HARD*, may need E12).
5. **S1 SLE_Σ layer:** Def 1.4, Lemmas 2.7, 2.8, Prop 1.5, Lemma 2.11, Remark 2.12, Def 2.9/2.10.
6. **S2 stationarity/recurrence:** A.1, A.2, 2.14, 2.13 (stationarity half), 2.16.
7. **S3 §3:** 3.3, 3.4, 3.5, 3.6 → Prop 3.1; 3.7 → Prop 3.2(a); 3.9, 3.10, 3.8
   (*Fable, HARD*: the Koebe chain (3.17)–(3.28)) → Prop 3.2(b); 3.11, 3.12 → Thm 1.8.
8. **S4 §4:** 4.6 → 4.4, 4.2, 4.1 (*Fable, HARD*: the topology of the disconnection) → Thm 1.10.
9. (optional) **X1 Lemma 2.6**, prime ends.

Tracks D1–D3 have no external inputs and can start as soon as their anchors are frozen.
D1 ∥ D3 is the first concurrent pair.

## 9. Sealing, audits, landing, reporting

Seal → checker + compile export + axioms → fresh Sonnet audit (refute-first; binders,
carriers, consumption, axioms) → PROVED / PROVED_REL. Every status report carries
`DRAFT_ANCHORS / UNREGISTERED_SORRIES / DRAFT_IMPORT_VIOLATIONS / SEALED_THIS_TURN`, plus
`EXTERNALS_USED`. The closure audit at the end is by a fresh Sonnet. Then README, RESULTS.md,
and a fresh-clone build before the final push.

## 10. Milestones (each ends with a commit and, if authorized, a push)

M0 skeleton + repo · M1 errata + carrier rulings · M2 definitions + roots frozen ·
M3 graph reviewed · M4 Tier D proved · M5 externals interface frozen · M6 §2.5–2.7 ·
M7 Thm 1.8 · M8 Thm 1.10 · M9 closure audit + release.

## 11. Tooling notes

- `tools/check_frozen_anchors.py` (copied from the previous campaign) knows `DRAFT_SORRY`
  and sealed states only. Before M5 it must be extended with an `EXTERNAL` state: a permanent
  allowlisted `by sorry`, importable only via `ComplexSLE/External/`. The axiom probe must
  then report `sorryAx` provenance per external, so `PROVED_REL{…}` sets are computed
  mechanically and are never typed by hand.
