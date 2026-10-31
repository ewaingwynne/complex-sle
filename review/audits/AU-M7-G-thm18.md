# AU-M7-G — `ComplexSLE.theorem_1_8` and `ComplexSLE.theorem_1_8_c_zero` (auditor-M7-G/sonnet, 2026-10-31)

Verdicts: `theorem_1_8` **PASS**; `theorem_1_8_c_zero` **PASS**.
Status: `theorem_1_8` **PROVED_REL{birkhoff_stationary, hormander_oneDim, ito_formula, koebe_quarter, markov_oneDim,
recurrence_stationary, strongMarkov_sleDriver, timeChange_isContLocalMartingale}**; `theorem_1_8_c_zero`
**PROVED_REL** of the same eight plus `dambis_dubins_schwarz`. Both manifest ids (`thm.theorem_1_8.v1`,
`thm.theorem_1_8_c_zero.v1`) are SEALED in the working tree; fidelity EXCESS 0 for both.

## Checked

1. **ABI.** `git diff HEAD` of each frozen file is exactly `by sorry` -> `by exact ComplexSLE.Internal.<export> ...`;
   `git diff 15d7cc9 HEAD` (the freeze commit) of both files and of the four phase defs is empty. Manifest diff: only
   `state` DRAFT_SORRY -> SEALED (prefix, suffix and ABI hashes untouched). `leanprobe abi` reproduces
   `a6e1ebdf...5475b` (theorem_1_8) and `2ac1a2c0...08bcd` (c_zero); `regions` prefix/suffix hashes equal the manifest;
   `verify-abi` OK (68 anchors); `tools/check.sh --quick` ALL CHECKS PASSED; the manifest sha in DEPGRAPH.md and
   graph/DEPGRAPH.header.md equals `sha256sum frozen-anchor-manifest.json`. All eight files compile with no warnings.
2. **Fidelity (paper.tex:L437-450, R4, R5, R7, R11, R12, R14, R15).** Binders of `theorem_1_8`: `a b c` (TY), `0<a, 0<b`
   (R5), `c^2 <= a*b` (PSD standing, R3/P3), `p, hp : IsAdmissibleDensity` (R7): EXCESS 0. Four cases (I>=0,II>0 thin;
   I<0,II>0 swallowing; I<0,II<0 hitting; I>=0,II<0 dense) match L441-448; `integralI/II` are the frozen
   `∫₀^{2π} ν p`, `∫₀^{2π} (ν + 2cos 2u) p`. `theorem_1_8_c_zero`: binders `a b`, `0<a`, `0<b` only (R5/R11), EXCESS 0;
   thresholds `a-b <= 4`, `4 < a-b < 8`, `8 <= a-b` = L449-450. Phase defs vs Def 1.7 (L412-415): thin `z ∉ closure ⋃ L_t`;
   swallowing `T_z < ∞ ∧ z ∉ closure ⋃_{t<T_z} L_t`; hitting `T_z < ∞ ∧ z ∈ closure ⋃_{t<T_z} L_t`; dense
   `z ∈ closure ⋃ L_t \ ⋃ L_t`; each `∀ z ≠ 0, ∀ᵐ ω` (R4, R12) with `IsSLEDriver a b c` over every `Ω : Type`.
3. **Glue (`Internal/Theorem_1_8.lean`).** Binder order of each sealed Prop 3.1/3.2 call is correct. Thin = 3.1(a) + 3.2(b)
   (T_z = ∞ makes `t < T_z` vacuous in `t`; `infDist_le_dist_of_mem` gives `ε ≤ dist z w`); swallowing = 3.1(b) + 3.2(b)
   (union over `t < T_z`); hitting = 3.1(b) + 3.2(a) via `mem_closure_of_infDist_lt`; dense = 3.1(a) + 3.2(a) (closure
   with `S = univ`; `z ∈ L_t` would give `T_z <= t < ∞`). R14 ε-form is not vacuous: `leftHull_nonempty U t` holds for every
   `U` and `t` (`U 0 ∈ L_t`, from `absorbingTime_driver_zero`: a solution on `[0,τ)` with `τ > 0` forces `γ 0 ≠ U 0`, but
   `γ 0 = U 0`), `#print axioms` = {propext, Classical.choice, Quot.sound}, status PROVED, no hypotheses; hence
   `Metric.infDist_lt_iff` returns a genuine `w ∈ L_t`, avoiding the `infDist z ∅ = 0` junk value. The hitting-phase ε-form
   also forces `T_z > 0` (needs `t < T_z`).
4. **c = 0 assembly.** `c0_integral_signs` is PROVED (standard axioms, no externals). `integralI_c0_eq`,
   `integralII_c0_eq`: `(I) = (2 - a/2 + b/2) S`, `(II) = (4 - a/2 + b/2) S`, `S = ∫₀^{2π} cos 2u p` (= L1838-1841);
   `S > 0` via `eq_c0Shape_div`: every admissible `p` for `c = 0` equals `c0Shape/∫ c0Shape` (first-order reduction
   `(Dp)' = J + µp`, `R = p/P` periodic with `R' = J/(DP)` forces `J = 0` and `p = CP`; `(D P)' = µ P` verified by hand for both
   `a ≠ b` (exponent `4/(b-a)`) and `a = b`), then the three-case reflection `c0F(-t) < c0F(t)` and the `[0, π/4]`
   reduction (= L1851-1900). Signs/thresholds: (I)>=0 iff `a-b<=4`; (II)>0 iff `a-b<8`; (II)=0 iff `a-b=8` with (I)=-2S<0.
   `theorem_1_8_c_zero` case split correct, the `a-b = 8` branch calls `lemma_3_12` (`rcases h.lt_or_eq`). `lemma_3_12`
   statement is exactly `(a b) (0<a) (0<b) (a - b = 8) : IsHittingPhase a b 0`, no extra hypothesis. Its proof: `T_z < ∞` from the
   sealed `proposition_3_1_b` with `(I) < 0`; closure clause from `ratioDriftHat ≡ 0` (`2 - a/2 + b/2 = -2`), the identity
   `ratio = -log|f_0| - M`, bracket `>= min a b · s` (so `A → ∞`), EXTERNAL `dambis_dubins_schwarz` (hypotheses all discharged:
   `hNm`, `hN0`, `hAprog`, `hAc`, `hAmart`, `hAtop`), `ae_forall_exists_le_of_timeChange`, Koebe hit bound; the adapted
   version `U'` agrees with `U` a.s. (`exists_adapted`) and the closure clause is transported. No undischarged
   conclusion-shaped hypothesis.
5. **Axioms.** `externals` for `theorem_1_8` and `theorem_1_8_c_zero`: status PROVED_REL, axioms {Classical.choice,
   Quot.sound, propext, sorryAx}, externals exactly as expected (8, resp. 9 with `dambis_dubins_schwarz`); no SORRYUSER
   offender, so `sorryAx` enters only through these. Each is an `EXTERNAL` manifest entry approved by Ewain Gwynne
   (R25, `markov_oneDim` R29). `grep -w sorry` outside `External/` finds only the two DRAFT anchors Theorem_1_10_A/B.
6. **Import closures** (parsed from `import`/`public import`, 317/316/338/337 modules for the frozen and provider files
   of `theorem_1_8`/`theorem_1_8_c_zero`): no `Theorem_1_10_*` module (frozen or Internal), no DRAFT_SORRY anchor; frozen
   anchors reached are all SEALED (Props 3.1/3.2 a/b, Lemma 2.13 existence, `LoewnerMap_*`, `LoewnerWellDefined`, and for c = 0
   `Theorem_1_8`).

## Notes (no action needed for the seals)

- STATUS.md has not been updated for the two seals (orchestrator-owned).
- The c = 0 proof depends on the sealed `theorem_1_8` and on the sealed `exists_admissibleDensity`; both are consumed through
  `_root_.ComplexSLE.*` (no shadowing by `ComplexSLE.Internal.theorem_1_8`).
- Not rechecked here (given): sealed Prop 3.1(a,b), 3.2(a,b) internals; `proposition_3_2_b` is audited separately.
