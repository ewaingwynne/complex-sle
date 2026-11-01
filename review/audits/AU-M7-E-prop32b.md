# AU-M7-E — `ComplexSLE.proposition_3_2_b` (auditor-M7-E/sonnet, 2026-10-31)

Verdict: **PASS**. Status: **PROVED_REL{hormander_oneDim, ito_formula, koebe_quarter, markov_oneDim,
strongMarkov_sleDriver, timeChange_isContLocalMartingale}**. ABI = manifest (`68e7f561…063c67`, unchanged since 15d7cc9;
prefix/suffix hashes unchanged; the only diff against `15d7cc9:ComplexSLE/Frozen/Proposition_3_2_B.lean` is line 37
`by sorry` → `by exact ComplexSLE.Internal.proposition_3_2_b a b c ha hb hc p hp hII Ω P U hU z hz`). Fidelity vs L1276-1283
with R5, R6, R9, R14, R15: EXCESS 0. `tools/check.sh --quick` and the full `tools/check.sh` both pass (ABI OK 68 anchors, EXTERNALS OK).
Checked mathematics: Koebe ball (`absorbingTime_le_of_staysAwayBy`: Grönwall form of the Koebe step on B(z, r), f_t(w) → 0 and
continuity at T_z give T_w ≤ T_z; then `15r/16`); Markov identity at the σ-time σ_z(s) (`measure_inter_postDriver` from the
EXTERNAL strong Markov + independence, `ae_event_iff_postDriver` pathwise future dependence) and `q(rξ) = q(ξ)` (scaled driver
r U(·/r²) is again an SLE_Σ driver); Λ nonempty (Fubini from `hconv`), open (Koebe ball + monotone union), Λ = ℝ (R27 hitting lemma
for the continuous version of θ̂, `2π`-periodic level shift, openness of Λ gives a rational σ-time with `P(θ̂_s ∈ Λ) > 0`, then
`q(z) = ∫ q(f̂_s) dP > 0`; the fixed-time substitution for the hitting-time strong Markov step is sound); Lévy 0-1 step
(`staysAwaySeq ∈ ⨆ 𝒢_n`, 𝒢_n = ℱ_{σ_z(n)}, `{hitTime_r ≤ σ_z(n)} ∈ ℱ_{σ_z(n)}`, a.s. equal to the event, Lévy upward + `q_*`);
Lemma 3.8 (F ⊆ E by Koebe quarter, `chain_sigma_of_event` with log 16 on F, `chain_sigma_le` with log 64 on Fᶜ, `E[LHS] ≥ 0` by
Lemma 3.9, dominated convergence to `−t̃(II) + log 16 ≥ 0`, contradiction for large t̃).
No hypothesis smuggling: `hconv` of `proposition_3_2_b_of_conv_on` is discharged by `converse_w_o_upgrade` (identical statement),
whose `MarkovOneDim` input is `External.markov_oneDim` (R29). An independent closure probe finds exactly six `sorryAx` users
(the six externals above, all in `ComplexSLE/External/`, registered EXTERNAL, author-approved R25/R29); no `sorry` in `Internal/`
or `Infrastructure/`. Import closure (190 modules) contains no DRAFT_SORRY anchor and no draft provider.
