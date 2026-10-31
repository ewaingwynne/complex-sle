# AU-M8-A — `ComplexSLE.theorem_1_10_a` (auditor-M8-A/sonnet, 2026-10-31)

Verdict: **PASS**. Status: **PROVED_REL{ito_formula, koebe_quarter, loewnerMap_tendstoUniformly, strongMarkov_sleDriver,
support_sleDriver, timeChange_isContLocalMartingale}**. ABI = manifest (`4075bd36…40548a`, unchanged since 15d7cc9; prefix/suffix
hashes unchanged; the only diff against `15d7cc9:ComplexSLE/Frozen/Theorem_1_10_A.lean` is line 34 `by sorry` →
`by exact ComplexSLE.Internal.theorem_1_10_a a b c ha hb hc Ω P U hU z hz`; the only manifest diff for
`thm.theorem_1_10_a.v1` is `state: DRAFT_SORRY → SEALED`). Fidelity vs L502-507 and Def 1.9 (L497-499) with R4, R5, R6, R12:
EXCESS 0. `tools/check.sh --quick` passes; `leanprobe verify-abi` (68 anchors) and `externals-all` OK. Audited at the working tree
of 7a86f96 (HEAD moved from the seal commit 825da30 during the audit); 825da30..7a86f96 touches only 1.10(b) files, none in the
provider's import closure, so every result below holds at 825da30.

Checked mathematics (read in full, no step found wrong):
- Planar: `disconnectsFromInfinity_of_two_connected` (P2; sign of Im((q-z₁)/(q-z₂)) > 0 and Im((p-z₁)/(p-z₂)) < 0, IVT on A,
  contradiction with |Im w| < ε on A; hypotheses suffice, A and B only need compact + preconnected and common points q, p),
  `exists_dist_le_of_chain_crossing` (CL; Φ ≠ 0 on B, opposite signs at b₁, b₂ from rays, IVT), the compactness limit
  (`exists_mem_image_of_chain_crossing`, `exists_hit`: last exit / next entry gives a chain inside N(C) with F-image from
  Re ≤ -1/2 to Re ≥ 1/2, using C ≥ 2), pullback (`disconnectsFromInfinity_pullback`).
- `lemma41_core`: hit point β* ∈ R_T ∩ N(C) with f_2(β*) ∈ L_K(W'); β* ∈ L_{K+2}(W) via `concatenation_leftHull` (f_2 avoids R_2);
  L_{K+2}(W) ∩ B_{3/4}(2C) = ∅ (Re f_2 ≤ Re z - 3C < -5/4 against |Re| < 1/2); P2 with A = R_T(u) (|Im| < δ ≤ 1/8 < 1/4), B = L_{K+2}(W),
  q = 0, p = β*; two target balls B_r(p_±) via R20 (d = dist to slit_I(T), δ ≤ d/2, r ≤ d/4, continuity of the zero map);
  pullback through `concatenation_leftHull u hu (K+2) T`; R20 (two scales) is correctly implemented.
- `exists_lemma44_path`: φ = S(t)(√a + i√b) in range Σ for c ≥ 0 (explicit v), ODE bootstrap (Re(γ-W) ≥ 2 on [0,1], Im(γ-W) ≤ -4 on [1,2],
  speed ≤ 2), existence on [0,2] from `lt_absorbingTime_of_norm_sub_ge`, estimates at time 2 with C = 4 + 5√a/√b ≥ 4.
- `lineApprox`: the lower bound for the hull tip is the Koebe distance bound (`norm_deriv_fPath_mul_infDist_le`) at z₀ = i(2√T + δ'),
  Cauchy estimate for f_T' - zeroMap', d ≤ 32 δ'; right hulls by `leftHull_dualDriver` and ‖dualDriver V T s‖ < 2ρ; E12 only
  through the ε-ρ contradiction argument `exists_small_driver_approx`.
- Probability assembly in `lemma41_nonneg`: the three increment events are on [0,T], [T,T+2], [T+2,T+2+K] (shifts V → W1 → W2),
  independent by `indep_shift_past` applied twice, each of positive probability by `support_sleDriver` with paths 0, φ, 0 (in range Σ),
  measurable (continuous version), union bound for the two balls; c < 0 by conjugation (`IsSLEDriver.conjugate`, `reflection_leftHull`,
  `disconnectsFromInfinity_conj`, measure_mono_ae).
- 1.10(a) upgrade: Λ ≠ ∅ from Lemma 4.1 (0 ∈ L_t forces z₀ ≠ 0), lower semicontinuity of q by a Fatou argument on sets (sections
  of Disc are open), Λ = ℝ by the R27 hitting lemma at a rational σ-time with the one-sided Markov inequality (restart implication
  `disc_of_disc_restart`), uniform bound q ≥ q_* by compactness of the unit circle, Lévy 0-1 for the ⨆𝒢_n-measurable event `discSeq`.
- No hypothesis smuggling: `hL41` is discharged by `lemma_4_1` (same binders, V open/bounded/nonempty, t > 0, `0 < P {…}` outer
  measure; sound since only monotonicity is used downstream); no placeholder in Disconnect/, Planar/ or the provider.

Import closure of the provider (193 ComplexSLE modules) contains no DRAFT_SORRY anchor or provider (the only DRAFT anchor at the seal
commit, theorem_1_10_b, and Thm110B* are outside it).

Note for the orchestrator (not part of the verdict): `STATUS.md` still lists `DRAFT_ANCHORS: 2` and no M8 entry.
