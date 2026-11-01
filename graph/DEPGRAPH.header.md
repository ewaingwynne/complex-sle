# Proof dependency database — arXiv:2203.07313v4 (Loewner evolution driven by complex Brownian motion)

GRAPH_VERSION: 4
ROOTS: defn-loewner.well-defined, lem-p.exists, nonsource.exists-sle-driver, thm-phases, thm-phases.c-zero, thm-disconnects.a, thm-disconnects.b, prop-i.a, prop-i.b, prop-ii.a, prop-ii.b, lem-connected.left, eqn-scale.left, eqn-reflect.left
CORPUS: source/arxiv-2203.07313v4/complex-sle-final.tex sha256:6f182d3af83b14781ad6c96c634a6d211230b0a54490453aca70cb52f77db252
CONVENTIONS: see graph/EXTRACTION_SPEC.md §3 (rulings R4-R17: z ≠ 0; a, b > 0 from Lemma 2.13 on; planar-BM driver; every admissible p; ε-form limits; left-hull splits; typos T1-T7)
STANDING_ASSUMPTIONS: -
EXTERNAL_POLICY: cited literature results and named standard theorems explicitly invoked by a proof are KIND external leaves (graph/EXTRACTION_SPEC.md §5); routine facts below the step threshold are not nodes
FROZEN_ANCHORS: defn-loewner.solution, defn-loewner.absorbing-time, defn-hulls.left, def-disconnect, eqn-cov-matrix, defn-sle.gaussian-law, defn-sle, defn-phases.thin, defn-phases.swallowing, defn-phases.hitting, defn-phases.dense, eqn-nu-D.mu, eqn-nu-D.nu, eqn-nu-D.D, lem-stationary.admissible, item-I, item-II, defn-loewner.well-defined, lem-p.exists, nonsource.exists-sle-driver, thm-phases, thm-phases.c-zero, thm-disconnects.a, thm-disconnects.b, prop-i.a, prop-i.b, prop-ii.a, prop-ii.b, lem-connected.left, eqn-scale.left, eqn-reflect.left
FROZEN_MANIFEST: frozen-anchor-manifest.json | sha256:ba479929ee5cccf831580978742a40b5fbc7b715aafc249b7f3b16b204bc3315
WRITER: orchestrator/opus-5.5/session-a85056b9
GLOBAL_REVIEWER: global-verifier/sonnet
GLOBAL_REVIEW_REF: graph/reviews/global-verify.review.md (final verification; first global review graph/reviews/global.review.md)

The dependency direction is `NODE -> prerequisite`. `DEPS` is conjunctive. `ROUTES` lists
alternative `KIND: route` nodes; one route is sufficient. Lean fields are initialized planning
metadata and are not evaluated here. Node schema: see
`~/.claude/skills/build-proof-dependency-graph/assets/DEPGRAPH.template.md`.

## Nodes
