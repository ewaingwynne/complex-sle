# Status ledger

M7 complete — 2026-10-31 (§3: Theorem 1.8). All six §3 roots sealed and audited: Props 3.1(a,b), 3.2(a,b),
Theorem 1.8 and Theorem 1.8 for c = 0 (AU-M7-C2, AU-M7-D2, AU-M7-E, AU-M7-G). Lemma 3.9 (converse without the upgrade,
Internal/Phases/ConverseMain.lean) and the upgrade from the random point to every z (Internal/Phases/Prop32BUp*.lean,
R27 hitting lemma at a fixed rational σ-time; no Girsanov) give Prop 3.2(b); Theorem 1.8 is the deterministic glue of
Props 3.1/3.2 (every hull contains U 0), and the c = 0 case adds Lemmas 3.11 (c0_integral_signs) and 3.12 (lemma_3_12).
Clean-up: the duplicate `goodSet` of Lemma38.lean renamed `goodSetAt`; the import-clash copy ConverseLemma38.lean deleted.
Next (M8): Theorem 1.10(a,b) — Lemmas 4.1–4.6 (R20), externals bm-support, loewner-convergence, koebe_quarter, Blumenthal.

M6 complete — 2026-10-30 (§2.3–2.7 SLE_Σ layer). Packet answered (R27, R28). Done: exists_sleDriver (PROVED_REL),
concatenation (2.3) and sle_duality / Prop 1.5 (PROVED), Lemma 2.4 upgraded to PROVED (no externals), driver lemmas,
stochastic infrastructure (optional stopping, local-martingale algebra, continuous versions, conditioning, progressive
path integrals), polar layer = Lemma 2.11 complete (Def 2.9/2.10, path measurability, Itô for log|f| and θ, Remark 2.12,
σ-time change; isDiffusionSolution_thetaHat and the joint decomposition thetaHat_sigmaLogMart_decomposition,
PROVED_REL{ito_formula, timeChange}), derivative of g_t and (2.27) (PROVED), stationarity layer (Lemma A.1 modulo the
Markov hypothesis — external markov_oneDim pending in review/approvals/M7.md), recurrence Lemma 2.16 (both signs of c,
Markov-free) and the R27 hitting lemma, stationarity→recurrence bridge, c = 0 analytic layer (M7-F1, PROVED).
Next (M7, plan review/plans/M7.md): M7-A Lemma 3.3 SLE form incl. the product extension with the random point 𝐳
(SOURCE_GAP step:section3-product-extension) and path-level stationarity; M7-B Lemma 3.2; M7-C/D/E Props 3.1, 3.2(a), 3.2(b);
M7-F2 c = 0 boundary; assembly. Fable budget: the author asked (2026-10-30) to be conservative — default to Sonnet.
Proof-route substitutions (graph models the source; Lean follows the ruling): step:p-case1-* → Lemma 2.13
periodic-solution route; lem-connected.left → max-modulus route; step:prop-ii-b-hit-lambda-prime and
step:disc-a-hit-Lambda → R27 hitting lemma (ext:girsanov not consumed); Lemma 2.16 renewal → deterministic windows +
conditioning lemma (no Markov external).
M5 complete — 2026-10-30: EXTERNAL state live; external boundary frozen (R23, R25). Open author item P13 (Girsanov, critical case) (tools/leanprobe.py externals-all computes PROVED/PROVED_REL in check.sh).
M4 complete — 2026-10-30 (Tier D; Lemma 2.4 both hulls proved in M5 relative to loewnerMap_conformal). P10 resolved by R20; P11/P12 accepted as R18/R19.

M3 dependency graph published — 2026-10-30 (M2 roots frozen earlier the same day).

```text
DRAFT_ANCHORS: 2
  ComplexSLE/Frozen/Theorem_1_10_A.lean        ComplexSLE.theorem_1_10_a
  ComplexSLE/Frozen/Theorem_1_10_B.lean        ComplexSLE.theorem_1_10_b
UNREGISTERED_SORRIES: 0
DRAFT_IMPORT_VIOLATIONS: 0
SEALED_THIS_TURN (M4): 10 (loewner_wellDefined, scaling_leftHull, reflection_leftHull, exists_admissibleDensity,
  loewnerMap_eq, loewnerMap_exists_solution, scaling_centeredLoewnerMap, scaling_rightHull, reflection_rightHull,
  reflection_centeredLoewnerMap)
SEALED DEFINITIONS: 24 (17 in M1; loewnerMap, centeredLoewnerMap, rightHull in M4, R21; 4 martingale-form vocabulary, R25)
EXTERNALS: 18 frozen (R29: markov_oneDim added) (R23 batch 1: 4; R25 batch 2: 13) in ComplexSLE/External/ — complete external boundary
  of the graph (ext:dct, ext:martingale-convergence, ext:picard-lindelof, ext:kolmogorov-zero-one are Mathlib-supplied)
PROVED: 17   PROVED_REL: 7
SEALED_THIS_TURN (M7 close): 3 (proposition_3_2_b, theorem_1_8, theorem_1_8_c_zero)
  PROVED_REL{birkhoff, dambis_dubins_schwarz, hormander, ito, koebe_quarter, markov_oneDim, recurrence, strongMarkov,
             timeChange}  ComplexSLE.theorem_1_8_c_zero (AU-M7-G)
  PROVED_REL{birkhoff, hormander, ito, koebe_quarter, markov_oneDim, recurrence, strongMarkov, timeChange}
             ComplexSLE.theorem_1_8 (AU-M7-G)
  PROVED_REL{hormander, ito, koebe_quarter, markov_oneDim, strongMarkov, timeChange}  ComplexSLE.proposition_3_2_b (AU-M7-E)
  PROVED_REL{birkhoff, hormander, ito, koebe_quarter, markov_oneDim, strongMarkov, timeChange}  ComplexSLE.proposition_3_2_a (AU-M7-D2)
  PROVED_REL{birkhoff, hormander, ito, markov_oneDim, recurrence, strongMarkov, timeChange}  ComplexSLE.proposition_3_1_a (AU-M7-C2)
  PROVED_REL{birkhoff, hormander, ito, markov_oneDim, strongMarkov, timeChange}  ComplexSLE.proposition_3_1_b (AU-M7-C2)
  PROVED  ComplexSLE.sle_duality (Prop 1.5, coupling form R28; AU-M6-S4)
  PROVED  concatenation_{centeredLoewnerMap,leftHull,image_leftHull,rightHull}  (AUTO-1; AU-M6-D1d) — (2.3) fully proved
  PROVED_REL{exists_isBrownianReal}  ComplexSLE.exists_sleDriver (AU-M6-S0)
  PROVED  ComplexSLE.lemma_2_4_leftHull, ComplexSLE.lemma_2_4_rightHull  (upgraded from PROVED_REL{loewnerMap_conformal};
          AU-M7-U1 — no external; duality (2.4) proved in-project)
  PROVED  scaling_centeredLoewnerMap, scaling_rightHull, reflection_rightHull, reflection_centeredLoewnerMap (AU-M4-D1c)
  Source items fully proved: Def 1.1 well-definedness, (2.1), (2.2), Lemma 2.13 (existence).
  PROVED  ComplexSLE.loewnerMap_eq, ComplexSLE.loewnerMap_exists_solution  (AU-M4-gt; characterization of g_t)
  PROVED  ComplexSLE.exists_admissibleDensity  (AU-M4-D3; Case 1 by an authorised route replacing step:p-case1-*)
  PROVED  ComplexSLE.scaling_leftHull, ComplexSLE.reflection_leftHull  (AU-M4-D1b; left-hull parts of (2.1)/(2.2) per R16)
  PROVED  ComplexSLE.loewner_wellDefined  (audit review/audits/AU-M4-D1-loewner.md)
```

Manifest: 68 anchors (graph header FROZEN_MANIFEST hash refreshed after each manifest change; graph anchor fields unchanged). Gate: `tools/check.sh` passes (build, modules, guard, ABI, forbidden).

Graph: DEPGRAPH.md / DEPGRAPH_COVERAGE.md. 286 nodes, 794 edges, 31 anchors, 19 external leaves,
62 explicit SOURCE_GAP nodes, 306 coverage items (96 excluded). Every record has an independent review
(slice reviewers A–D, global-reviewer, and global-verifier as GLOBAL_REVIEWER). The full gate passes:
`proof_depgraph.py --require-reviewed --require-complete-coverage --require-initial-lean-status
--require-all-reachable --check`.
Author items open: the modeling questions in ERRATA.md. Graph amendments R20-disc-setup and
R20-disc-E1-positive (reviewed: graph/reviews/R20-amend.review.md) encode R20.

Next (M4): Lean proofs of the Tier-D frontier (deterministic Loewner core, stationary density).
Deferred anchors: g_t / f_t / R_t (after `loewner_wellDefined` is proved), Prop 1.5,
right-hull and f_t parts of (2.1)–(2.4) and Lemma 2.4, the concatenation property, Lemma 2.5,
Lemma 4.3, and the externals E1–E13 (M5).
