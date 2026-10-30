# Dependency-graph extraction specification (frozen before extraction)

Writer (single merger and adjudicator): `orchestrator/opus-5.5/session-a85056b9`.
Workflow: `~/.claude/skills/build-proof-dependency-graph/SKILL.md` and its
`references/agent-packets.md`. Node schema: `~/.claude/skills/build-proof-dependency-graph/assets/DEPGRAPH.template.md`.

## 1. Roots (author-frozen theorem anchors)

`defn-loewner.well-defined`, `lem-p.exists`, `nonsource.exists-sle-driver`, `thm-phases`, `thm-phases.c-zero`,
`thm-disconnects.a`, `thm-disconnects.b`, `prop-i.a`, `prop-i.b`, `prop-ii.a`, `prop-ii.b`,
`lem-connected.left`, `eqn-scale.left`, `eqn-reflect.left`.

Every graph root is one of these. Every other graph node must feed at least one root. Results
that feed no root (e.g. Prop 1.5 unless some root's proof consumes it) are `EXCLUDED` in coverage
with the reason "feeds no current root"; they join the graph when anchored later.

## 2. Corpus

`source/arxiv-2203.07313v4/complex-sle-final.tex` (arXiv:2203.07313v4, sha256
`6f182d3af83b14781ad6c96c634a6d211230b0a54490453aca70cb52f77db252`).
Locators: `source/arxiv-2203.07313v4/complex-sle-final.tex#<stable-anchor>@Lx-Ly` (anchor = LaTeX
label or semantic slug; line numbers are revisable locators only, never part of a node ID).
External results: `external:<bib-key>#<result>` (bib keys as in `\cite`; unnamed standard
results `external:standard#<name>`). Text inside `\begin{comment}…\end{comment}` (L999-1018,
L1114-1131, L1140-1146, L1234-1248, L1878-1903) and `%`-commented lines are not part of the paper.

## 3. Conventions and author rulings to track (`ERRATA.md`)

- R4: phases and Thm 1.10(a) quantify over z ∈ ℂ∖{0}. U₀ = 0, so T₀ = 0 and 0 ∈ L_t.
- R5: Lemma 2.13 onward (2.13, 2.14, 2.16, Props 3.1, 3.2, Thm 1.8, and Thm 1.10) assume a, b > 0; Σ is PSD
  (c² ≤ ab) throughout.
- R6: the driver is a planar BM U with covariance Σ (continuous paths, U₀ = 0, independent
  increments, Gaussian increments); the representation U = √a B + i√b B̃ is a step node where used.
- R7/R15: Thm 1.8 and Props 3.1/3.2 hold for every admissible p (Lemma 2.14 hypotheses). The step
  "an admissible p vanishes only on a Lebesgue-null set" (needed in Lemma 3.3) is a SOURCE_GAP step.
- R9: Lemma A.1 is normalized with ∫₀^π; its use in Lemma 2.14 applies it to 2p (a step node).
- R14: "lim_{t→T_z−} dist(z, L_t)" uses ε-forms; L_t is increasing, so the limit is the infimum.
- R16: Lemma 2.4, (2.1) and (2.2) roots cover left hulls only; right-hull / f_t parts are ordinary
  (non-anchored) nodes if some root's proof consumes them.
- Typos T1–T7 (ERRATA.md) are read as corrected; mention them in NOTE where relevant.
- Time-change notation: σ = σ_z (Def 2.9), hats denote σ-time; the stationary random point is
  written 𝐳 (`\zz`) in the source.

## 4. Standing assumptions

`STANDING_ASSUMPTIONS: -`. Section-wide settings (e.g. "throughout this section, 𝐳 is sampled from
p", L1252-1259; "assume c ≥ 0", L1949-1952) are **local hypothesis packages**: record them in each
consuming node's `SOURCE_HYPOTHESES`, and record at each application which node supplies them. A
WLOG reduction (c ≥ 0 by conjugation, L323 and L1949) is a step node that consumes the reflection
property.

## 5. External-input policy

Cited literature results and named standard theorems that a proof explicitly invokes are
`KIND: external` leaves (`LEAN_STATUS: EXTERNAL`). Use these canonical IDs. Add new ones only with
prefix `ext:`, and report them.

| ID | Statement source | Plan ref |
|---|---|---|
| `ext:ito-complex` | `external:protter#II.35` (Itô formula, complex semimartingales) | E1 |
| `ext:levy-characterization` | `external:standard#levy-characterization` (continuous martingales with equal (cross-)variations are equal in law; DDS time change) | E2 |
| `ext:strong-markov-bm` | `external:standard#strong-markov-brownian-motion` | E3 |
| `ext:bm-time-reversal` | `external:standard#brownian-time-reversal` (B_t and B_{T−t} − B_T on [0,T]) | E4 |
| `ext:blumenthal` | `external:standard#blumenthal-zero-one` | E5 |
| `ext:girsanov` | `external:standard#girsanov` | E6 |
| `ext:birkhoff` | `external:standard#birkhoff-ergodic-theorem` | E7 |
| `ext:hormander-1d` | `external:hairer-hormander#thm-1.3` | E8 |
| `ext:scale-function` | `external:lawler-book#lemma-1.24` | E9 |
| `ext:koebe-quarter` | `external:lawler-book#cor-3.18` | E10 |
| `ext:koebe-distortion` | `external:lawler-book#cor-3.23` | E11 |
| `ext:loewner-convergence` | `external:lawler-book#prop-4.43` (extension to ℂ asserted, T6: SOURCE_GAP) | E12 |
| `ext:bm-support` | `external:standard#brownian-support` (BM stays uniformly near a given continuous path on [0,T] with positive probability) | E13 |
| `ext:bm-existence` | `external:standard#brownian-motion-existence` (planar BM with covariance Σ exists) | E14 (for R13) |
| `ext:picard-lindelof` | `external:standard#picard-lindelof` (in Mathlib) | — |
| `ext:martingale-convergence` | `external:standard#levy-upward-martingale-convergence` (in Mathlib) | — |
| `ext:dct` | `external:standard#dominated-convergence` (in Mathlib) | — |
| `ext:durrett-7.3.2` | `external:durrett#thm-7.3.2` (Lemma 3.5 "essentially identical"; SOURCE_GAP) | — |
| `ext:lawler-4.5` | `external:lawler-book#thm-4.5` (conformality of g_t, L286, asserted by analogy; SOURCE_GAP) | — |

Routine algebra and calculus below the step threshold are not nodes.

## 6. Step threshold

Create a `step` / `application` node when omitting it would hide a plausible independent Lean
lemma or an independently failing obligation. That includes a nontrivial estimate, a
construction, a case split, a witness or parameter choice, an application of a theorem whose
premises must be discharged, a quantifier closure, a carrier change (capacity time ↔ σ-time,
z ↔ 𝐳, θ ↔ e^{2iθ}, ∫₀^π ↔ ∫₀^{2π}), or a reused claim. Also create nodes for unlabeled claims
that a proof uses, for example:
- L268 lim |f_t(z)| = 0, L284 monotonicity of L_t, L286 conformality of g_t;
- (2.3) concatenation;
- the "Itô SDE (1.6) for f_t" (L315-319);
- Remark 2.12 (σ(∞) = T_z);
- (3.1) and (3.5);
- the Koebe chain (3.18)–(3.28).
An asserted but unproved bridge is a `step` with `NOTE: SOURCE_GAP: …`. Alternatives in the source
are separate `KIND: route` nodes.

## 7. Exclusions (orchestrator decides; extractors may propose more with reasons)

- §1.1 (L228-243) motivation; Remarks 1.3 (remark-radial), 1.6 (remark-duality), 1.11
  (remark-curve) and footnote 2 (R2); figures and captions.
- §2.2 Lemma 2.6 (lem-cut-glue, L696-767): deferred (R2).
- §2.4 simulations (L805-830); §5 open problems (L2230-2311); bibliography.
- Statements that feed no root (for example Prop 1.5, Lemma 2.4 right-hull part, (2.4) duality)
  unless a root's proof consumes them; mark them `EXCLUDED` with that reason.

## 8. Frozen anchors (copy these fields exactly; never infer or edit)

Manifest: `frozen-anchor-manifest.json | sha256:2828acc43590018a4ecb51212013762c7de09abea5cb78e81aea33e0e52ef3ed`.

| NODE | kind | FROZEN_ANCHOR_ID | FROZEN_FILE | FROZEN_DECL | CONTRACT_ID / VERSION | FROZEN_ABI_SHA256 | manifest source range |
|---|---|---|---|---|---|---|---|
| `defn-loewner.solution` | definition | `def.IsLoewnerSolution.v1` | `ComplexSLE/Frozen/Defs/IsLoewnerSolution.lean` | `ComplexSLE.IsLoewnerSolution` | `paper.def.IsLoewnerSolution` / `1` | `bbe2299b871e2374841a91b93b4f6762ad46fdaed6a82c43893c005089db4d29` | paper.tex:251-263 |
| `defn-loewner.absorbing-time` | definition | `def.absorbingTime.v1` | `ComplexSLE/Frozen/Defs/AbsorbingTime.lean` | `ComplexSLE.absorbingTime` | `paper.def.absorbingTime` / `1` | `f831e140c92a7542b39fb4f416dbd3ffaf931cb64e30ff1cd9362379efa590f1` | paper.tex:268 |
| `defn-hulls.left` | definition | `def.leftHull.v1` | `ComplexSLE/Frozen/Defs/LeftHull.lean` | `ComplexSLE.leftHull` | `paper.def.leftHull` / `1` | `c203d2a3a6eb3db7f822226cccc6b9ad6add6cd583a36c32bc8619bd900e809e` | paper.tex:271-277 |
| `def-disconnect` | definition | `def.DisconnectsFromInfinity.v1` | `ComplexSLE/Frozen/Defs/DisconnectsFromInfinity.lean` | `ComplexSLE.DisconnectsFromInfinity` | `paper.def.DisconnectsFromInfinity` / `1` | `396f675756de6faa68b7c805e29e8d726cae4320d590f5a714e96ee80ee540c2` | paper.tex:497-499 |
| `eqn-cov-matrix` | definition | `def.covMatrix.v1` | `ComplexSLE/Frozen/Defs/CovMatrix.lean` | `ComplexSLE.covMatrix` | `paper.def.covMatrix` / `1` | `9c7db20131aa7365837343dbfe0137f267d6d9583f10c6217364b322317c9dc2` | paper.tex:304-306 |
| `defn-sle.gaussian-law` | definition | `def.complexGaussian.v1` | `ComplexSLE/Frozen/Defs/ComplexGaussian.lean` | `ComplexSLE.complexGaussian` | `paper.def.complexGaussian` / `1` | `35770535322d991e762fad0a8fe630fa74e550a8a476439b08129e00de75c486` | paper.tex:301-308 |
| `defn-sle` | definition | `def.IsSLEDriver.v1` | `ComplexSLE/Frozen/Defs/IsSLEDriver.lean` | `ComplexSLE.IsSLEDriver` | `paper.def.IsSLEDriver` / `1` | `a3e7b316bc3a0ef59101d633fadad41bf1cf76893aaccc318657527c33d60af5` | paper.tex:301-319 |
| `defn-phases.thin` | definition | `def.IsThinPhase.v1` | `ComplexSLE/Frozen/Defs/IsThinPhase.lean` | `ComplexSLE.IsThinPhase` | `paper.def.IsThinPhase` / `1` | `7727fa4e3bd47573921bd91b01e159429ee6bf9918604c734f8eae2575c8142c` | paper.tex:409-417 (item 412) |
| `defn-phases.swallowing` | definition | `def.IsSwallowingPhase.v1` | `ComplexSLE/Frozen/Defs/IsSwallowingPhase.lean` | `ComplexSLE.IsSwallowingPhase` | `paper.def.IsSwallowingPhase` / `1` | `da5f6acbe728f180308ef886460f4e1cb38a7ac67b56a6fa0a79da36708ee72f` | paper.tex:409-417 (item 413) |
| `defn-phases.hitting` | definition | `def.IsHittingPhase.v1` | `ComplexSLE/Frozen/Defs/IsHittingPhase.lean` | `ComplexSLE.IsHittingPhase` | `paper.def.IsHittingPhase` / `1` | `f226bef104f2e8332fb32fce332025566773b0e16564ff8d199410f001b307d0` | paper.tex:409-417 (item 414) |
| `defn-phases.dense` | definition | `def.IsDensePhase.v1` | `ComplexSLE/Frozen/Defs/IsDensePhase.lean` | `ComplexSLE.IsDensePhase` | `paper.def.IsDensePhase` / `1` | `1ee346e80cf2a6167b73f56641824ee302db6becb222740bf3701d7971e7e5df` | paper.tex:409-417 (item 415) |
| `eqn-nu-D.mu` | definition | `def.mu.v1` | `ComplexSLE/Frozen/Defs/Mu.lean` | `ComplexSLE.mu` | `paper.def.mu` / `1` | `cd3369a3cc72d9850889657ec3f058716a2c7cbc084efbddfcc84738b784297b` | paper.tex:424 |
| `eqn-nu-D.nu` | definition | `def.nu.v1` | `ComplexSLE/Frozen/Defs/Nu.lean` | `ComplexSLE.nu` | `paper.def.nu` / `1` | `f9ff6a5f33ed2c7350371531fdb5f1700586fdc010eb37a4a4c11857b1ce23e3` | paper.tex:425 |
| `eqn-nu-D.D` | definition | `def.diffusionD.v1` | `ComplexSLE/Frozen/Defs/DiffusionD.lean` | `ComplexSLE.diffusionD` | `paper.def.diffusionD` / `1` | `ae71cf207fc738d3a8f3b0629a9e5bc1c4b8e6c767665016cbbb6630db368cc2` | paper.tex:426 |
| `lem-stationary.admissible` | definition | `def.IsAdmissibleDensity.v1` | `ComplexSLE/Frozen/Defs/IsAdmissibleDensity.lean` | `ComplexSLE.IsAdmissibleDensity` | `paper.def.IsAdmissibleDensity` / `1` | `2429786912c3915fecf74d5df2467dd2b5c0a7d89ff34a4e3f77a86c0af43b7c` | paper.tex:963-966 |
| `item-I` | definition | `def.integralI.v1` | `ComplexSLE/Frozen/Defs/IntegralI.lean` | `ComplexSLE.integralI` | `paper.def.integralI` / `1` | `5971ead00dfc488c751540f8e58da9f1b4f95e192413d7e6f2712586ba7823ad` | paper.tex:440 |
| `item-II` | definition | `def.integralII.v1` | `ComplexSLE/Frozen/Defs/IntegralII.lean` | `ComplexSLE.integralII` | `paper.def.integralII` / `1` | `f79d30902daa10ab3c6b8002e63af5af5c565a7558faa9d8067507619f09211c` | paper.tex:441 |
| `defn-loewner.well-defined` | theorem | `thm.loewner_wellDefined.v1` | `ComplexSLE/Frozen/LoewnerWellDefined.lean` | `ComplexSLE.loewner_wellDefined` | `paper.def1_1.wellDefined` / `1` | `627a9c24bc589b835afd7829fa4c0ca50499a5167908b24c5ac70bd838f0257f` | paper.tex:251-268 |
| `lem-p.exists` | theorem | `thm.exists_admissibleDensity.v1` | `ComplexSLE/Frozen/Lemma_2_13_Exists.lean` | `ComplexSLE.exists_admissibleDensity` | `paper.lem2_13.exists` / `1` | `8f546735c8b4d71b3075c5f4038fdc3cd05cd83517ffa087db4f91baec22d461` | paper.tex:941-955 |
| `nonsource.exists-sle-driver` | theorem | `thm.exists_sleDriver.v1` | `ComplexSLE/Frozen/ExistsSLEDriver.lean` | `ComplexSLE.exists_sleDriver` | `paper.nonsource.existsSLEDriver` / `1` | `cb6850fe26b9549e5e5795f68670c65beb5f354084bfe7c0b086b6192ca62fdc` | paper.tex:301-308 |
| `thm-phases` | theorem | `thm.theorem_1_8.v1` | `ComplexSLE/Frozen/Theorem_1_8.lean` | `ComplexSLE.theorem_1_8` | `paper.thm1_8.phases` / `1` | `a6e1ebdf58aaf0db8d9b0eecfdd5cb139c91a84c01bda7b0b4de6db3e4f5475b` | paper.tex:437-449 |
| `thm-phases.c-zero` | theorem | `thm.theorem_1_8_c_zero.v1` | `ComplexSLE/Frozen/Theorem_1_8_CZero.lean` | `ComplexSLE.theorem_1_8_c_zero` | `paper.thm1_8.cZero` / `1` | `2ac1a2c03ab122e2d2b04cd9d4f8d9ceaa4f35e452106838a9322f0c47d08bcd` | paper.tex:450 |
| `thm-disconnects.a` | theorem | `thm.theorem_1_10_a.v1` | `ComplexSLE/Frozen/Theorem_1_10_A.lean` | `ComplexSLE.theorem_1_10_a` | `paper.thm1_10.a` / `1` | `4075bd36d6a8503eb38319a978b1826157dc31f0b0800820be15fde67340548a` | paper.tex:502-507 |
| `thm-disconnects.b` | theorem | `thm.theorem_1_10_b.v1` | `ComplexSLE/Frozen/Theorem_1_10_B.lean` | `ComplexSLE.theorem_1_10_b` | `paper.thm1_10.b` / `1` | `a4e294f2aeaf5af14560b8ff75ed1e705bf450412093f7d1877c04ce72501f47` | paper.tex:502-509 |
| `prop-i.a` | theorem | `thm.proposition_3_1_a.v1` | `ComplexSLE/Frozen/Proposition_3_1_A.lean` | `ComplexSLE.proposition_3_1_a` | `paper.prop3_1.a` / `1` | `98149ac34067ca49e2b3a5155685d35078ede80ef870a1e3917076c77a93a902` | paper.tex:1265-1269 |
| `prop-i.b` | theorem | `thm.proposition_3_1_b.v1` | `ComplexSLE/Frozen/Proposition_3_1_B.lean` | `ComplexSLE.proposition_3_1_b` | `paper.prop3_1.b` / `1` | `80b1301f8349878a927cecf5bb3e25558a8e4f99a13edc51752231df161fa236` | paper.tex:1265-1270 |
| `prop-ii.a` | theorem | `thm.proposition_3_2_a.v1` | `ComplexSLE/Frozen/Proposition_3_2_A.lean` | `ComplexSLE.proposition_3_2_a` | `paper.prop3_2.a` / `1` | `7bbf7b70ad8ac1714e12908c49ba28298a6e77844f927984651fff3b2fc3f161` | paper.tex:1276-1281 |
| `prop-ii.b` | theorem | `thm.proposition_3_2_b.v1` | `ComplexSLE/Frozen/Proposition_3_2_B.lean` | `ComplexSLE.proposition_3_2_b` | `paper.prop3_2.b` / `1` | `68e7f561920bc47ded181922aa3709800fd30024d385e40bf7734750bb063c67` | paper.tex:1276-1283 |
| `lem-connected.left` | theorem | `thm.lemma_2_4_leftHull.v1` | `ComplexSLE/Frozen/Lemma_2_4_LeftHull.lean` | `ComplexSLE.lemma_2_4_leftHull` | `paper.lem2_4.leftHull` / `1` | `346e1871675ffbff3149f1eba8ce7064deda3bae36480f3631f217663d08e7ab` | paper.tex:658-666 |
| `eqn-scale.left` | theorem | `thm.scaling_leftHull.v1` | `ComplexSLE/Frozen/Scaling_LeftHull.lean` | `ComplexSLE.scaling_leftHull` | `paper.prop2_1_scaling.leftHull` / `1` | `0b072ed0d86d49729df12aafd3234c5371ca05e7bd4e7563aca829a4ad0259f5` | paper.tex:549-552 |
| `eqn-reflect.left` | theorem | `thm.reflection_leftHull.v1` | `ComplexSLE/Frozen/Reflection_LeftHull.lean` | `ComplexSLE.reflection_leftHull` | `paper.prop2_2_reflection.leftHull` / `1` | `a622f14fdc883f8e0806d2d8df7ef10f345eba58d229d3bea9f50da620fc7cb7` | paper.tex:553-557 |

Every frozen-anchor node uses these exact `FROZEN_FILE`, `FROZEN_DECL`, `FROZEN_ANCHOR_ID`,
`FROZEN_ABI_SHA256`, `CONTRACT_ID`, `CONTRACT_VERSION`. All other nodes use `-` for the four
`FROZEN_*` fields and their own `CONTRACT_ID` (`paper.<node-id>`) with `CONTRACT_VERSION: 1`.
For anchors, the source-statement fields describe the **source statement as modified by the cited
rulings**; record each ruling in NOTE.

Definitions: a node depends on a definition node where its proof uses that definition's content
(not merely its name in the statement). Each definition anchor must end up consumed by some node.

## 9. Slices (node ownership is exclusive; read-only context may overlap)

| Slice | Lines | Owns |
|---|---|---|
| A | L225-L804 | §1 and §2.1–2.3: Defs 1.1, 1.2, 1.4, 1.7, 1.9; (1.10)–(1.11) incl. µ, ν, D anchors; Thm 1.8 statement-level roots `thm-phases`, `thm-phases.c-zero` (proofs at L1930-1932: record DEPS on the canonical §3 IDs); Thm 1.10 roots `thm-disconnects.a/.b` (proof in §4: record DEPS on canonical §4 IDs); Prop 1.5; (2.1)–(2.4) incl. roots `eqn-scale.left`, `eqn-reflect.left`; Def 2.1; Lemmas 2.2–2.5 incl. root `lem-connected.left`; Lemmas 2.7, 2.8; roots `defn-loewner.well-defined`, `nonsource.exists-sle-driver`; `item-I`, `item-II`. |
| B | L805-L1249, L2312-L2406 | §2.4 (exclusion), §2.5–2.7: Defs 2.9, 2.10, Lemma 2.11, Remark 2.12, Lemma 2.13 incl. root `lem-p.exists`, Lemma 2.14 incl. anchor `lem-stationary.admissible`, Remark 2.15, Lemma 2.16; Appendix A (Lemmas A.1, A.2). |
| C | L1250-L1946 | §3: (3.1), Props 3.1/3.2 roots `prop-i.a/.b`, `prop-ii.a/.b`, Lemmas 3.3–3.12, and the proof of Thm 1.8 (L1930-1932) as node `thm-phases#assembly` only if needed (prefer: slice A's `thm-phases` DEPS cite the canonical C IDs). |
| D | L1947-L2311 | §4: Lemmas 4.1–4.6 and the proof of Thm 1.10 (L2199-2225) as step nodes; §5 exclusion. |

Proofs of roots in another slice: the owner of the root records its DEPS on the canonical
cross-slice IDs below, and the slice owning the proof text owns the step nodes inside that proof
(slice C owns the steps of Thm 1.8's proof; slice D the steps of Thm 1.10's proof, which A's root nodes then depend on).

Canonical cross-slice IDs (use exactly):
- **A:** `lem-forward-reverse-ext` (2.2), `lem-mult-by-i` (2.3), `lem-endpt-cont` (2.5), `lem-scaling` (2.7), `lem-markov` (2.8),
  `eqn-scale` (full (2.1) incl. f_t), `eqn-reflect` (full (2.2)), `eqn-conc` ((2.3)), `eqn-duality` ((2.4)),
  `eqn-def-ft` (the SDE (1.6) for f_t), `claim:hulls-monotone` (L284), `claim:gt-conformal` (L286),
  `step:wlog-c-nonneg` (L323, conjugation reduces to c ≥ 0), `step:driver-representation` (U = √a B + i√b B̃ under R6).
- **B:** `defn-sigma` (2.9), `def-arg` (2.10), `lem-polar` (2.11), `remark-sigma` (2.12), `lem-p` (2.13, full),
  `lem-stationary` (2.14), `remark-p0` (2.15), `lem-recurrence` (2.16), `lem-kolmogorov` (A.1), `lem-hormander` (A.2).
- **C:** `eqn-integral-nu` ((3.1)), `lem-all-z` (3.3), `lem-stationary-sde` (3.4), `lem-recurrent` (3.5),
  `lem-swallow-distance` (3.6), `lem-integral-ii` (3.7), `lem-converse-w-o-upgrade` (3.8), `lem-computation` (3.9),
  `lem-log-finite-exp` (3.10), `lem-c0-phases` (3.11), `lem-c0-bdy` (3.12), `eqn-hit-koebe` ((3.5)).
- **D:** `lem-disconnect-2` (4.1), `lem-line-approx` (4.2), `lem-haus` (4.3), `lem-pos-hits-before-neg` (4.4),
  `lem:re-im-bounds` (4.5, unlabeled, L2042), `lem-c-event` (4.6), `thm-disconnects#proof-a`, `thm-disconnects#proof-b`
  (the two proof assemblies at L2199-2225, step nodes owned by D; slice A's roots depend on them).

Note the label collision: `lem-recurrence` is Lemma 2.16 and `lem-recurrent` is Lemma 3.5.

## 10. Field rules (from the template)

Every node block uses exactly the schema fields. Initial Lean fields: `LEAN_STATUS: NOT_STARTED`
(`EXTERNAL` for external nodes), `LEAN_REF: -`, `LEAN_NOTE: -`. `TOPOLOGY_STATUS: PROPOSED`,
`REVIEWER: -`. Write one `EDGE:` line per DEPS/ROUTES entry, citing where the **consumer's** proof
uses it. `DEPS` direction is `NODE -> prerequisite`. External nodes are owned by the first slice
that cites them; extractors in other slices refer to the canonical ID and do not redefine it (the
orchestrator deduplicates).
