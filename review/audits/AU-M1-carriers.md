# AU-M1-carriers: statement audit of `.lake/probes/Carriers.lean`

Auditor: independent, refute-first. Source: `paper.tex` = `source/arxiv-2203.07313v4/complex-sle-final.tex`.
Target: `/home/ewain/complex-sle/.lake/probes/Carriers.lean` (compiles; only 5 `sorry` warnings, all in the 5 theorems).
No manifest exists for a probe, so identity pinning is by file content as read. All verdicts are DRAFT-level
(DECLARATION_FIDELITY), PROOF_STATUS: FROZEN_UNPROVED for the theorems.

## Summary verdicts

| Declaration | Verdict |
|---|---|
| IsLoewnerSolution | ACCEPT |
| absorbingTime | ACCEPT |
| loewner_wellDefined | ACCEPT-WITH-NOTE (recommend R2: uniqueness for every tau) |
| leftHull | ACCEPT |
| DisconnectsFromInfinity | ACCEPT |
| covMatrix | ACCEPT |
| complexGaussian | ACCEPT-WITH-NOTE (junk dirac for non-PSD; unreachable under R1 hypotheses) |
| IsSLEDriver | ACCEPT-WITH-NOTE (no filtration, no PSD field; both fine) |
| IsThinPhase / IsSwallowingPhase / IsHittingPhase / IsDensePhase | ACCEPT-WITH-NOTE (junk for non-PSD, unused) |
| mu, nu, diffusionD | ACCEPT |
| IsAdmissibleDensity | ACCEPT (shown satisfiable at a=b=2,c=0) |
| integralI, integralII | ACCEPT |
| phases | ACCEPT-WITH-NOTE (needs separate existence root R3) |
| phases_c_zero | ACCEPT |
| disconnects_point | **REJECT** (R1) |
| disconnects_open | **REJECT** (R1) |

## Required changes

**R1 (REJECT cause).** `disconnects_point` and `disconnects_open` take `ha : a ≠ 0`, `hb : b ≠ 0`, `hc : c^2 ≤ a*b`.
This admits a, b < 0 (e.g. a = b = -1, c = 0). Source (paper.tex:L301-309) has a standing assumption
that Σ is PSD, i.e. a, b ≥ 0 and |c| ≤ √(ab); with a, b ≠ 0 (paper.tex:L503-504) this is a, b > 0.
In Lean, for non-PSD S, `multivariateGaussian 0 S = dirac 0` (Mathlib `multivariateGaussian_of_not_posSemidef`),
so for a = b = -1 and s < t, `complexGaussian ((t-s)•Σ) = dirac 0`. I proved
`IsSLEDriver (-1) (-1) 0 (fun _ _ => 0) (dirac ())` (scratch a2, `zero_driver`), so the hypotheses are
satisfiable by U ≡ 0. For U ≡ 0, γ² = z² + 4t, L_t = {iy : y² ≤ 4t} (a segment), whose complement is connected and unbounded:
(a) fails for z = 1 (T_1 = ∞, and L_t never disconnects 1), and (b) fails (the disconnected set is L_t itself, interior empty).
So both theorems are FALSE as drafted (argument for L_t by hand; the satisfiability of the hypotheses is machine-checked).
Replacement (elaborated, scratch a5):
```lean
theorem disconnects_point (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ℝ≥0 → Ω → ℂ) (hU : IsSLEDriver a b c U P) (z : ℂ) (hz : z ≠ 0) : ... (unchanged)
theorem disconnects_open (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b) ... (unchanged)
```
`0 < a, 0 < b, c^2 ≤ ab` is exactly "a,b ≠ 0, Σ PSD" and implies (t-s)•Σ is PSD (proved, scratch a6 `psd`).
Binder bins after fix: a,b,c,Ω,P,U,z typing; ha,hb (SOURCE: a,b≠0 + PSD standing, ruling-compatible);
hc SOURCE (|c| ≤ √ab); hz RULED P1; hU SOURCE (Def 1.4/P3); IsProbabilityMeasure TYPING/P9. EXCESS count 0.
Same fix is not needed for `phases` (already 0<a, 0<b). Add the ruling note to P2: Thm 1.10 also needs PSD, so a,b>0.

**R2 (recommended, not blocking).** Strengthen the uniqueness half of `loewner_wellDefined` to every τ, so the later
definition of g_t can be shown to agree with ANY solution on [0,τ), not just ones on the full [0,T_z):
```lean
theorem loewner_wellDefined (U : ℝ≥0 → ℂ) (hU : Continuous U) (z : ℂ) :
    (∃ γ, IsLoewnerSolution U z (absorbingTime U z) γ) ∧
      ∀ (τ : ℝ≥0∞) (γ₁ γ₂ : ℝ → ℂ), IsLoewnerSolution U z τ γ₁ →
        IsLoewnerSolution U z τ γ₂ →
          Set.EqOn γ₁ γ₂ {t | 0 ≤ t ∧ ENNReal.ofReal t < τ}
```
(compiles, scratch a5). With the draft version, a solution on a shorter [0,τ) is not covered by the stated uniqueness.

**R3 (required companion root, per P4).** Freeze, in the same batch, the existence half so `phases` is not vacuous:
```lean
theorem exists_admissibleDensity (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b) :
    ∃ p, IsAdmissibleDensity a b c p
```
(compiles, scratch a5). Without it a proof of `phases` could not be distinguished from a proof that IsAdmissibleDensity is empty.

**R4 (optional).** Add the docstring note that `IsThinPhase a b c` etc. are meaningful only for PSD Σ (for non-PSD,
drivers are the zero process via the Mathlib fallback). No Lean change needed because every consuming theorem has a,b>0, c²≤ab.

## Per-declaration audit

### IsLoewnerSolution (paper.tex:L251-263) ACCEPT
Binders: U (typing), z (typing), τ (typing: existence time), γ (typing: candidate). No premises.
Body: `γ 0 = z` and for real t ≥ 0 with ofReal t < τ: `γ t ≠ U t.toNNReal` and `HasDerivWithinAt γ (2/(γ t - U t)) (Ici 0) t`.
For t > 0, Ici 0 is a neighbourhood so this is HasDerivAt; at t = 0 it is the right derivative. `toNNReal` is the identity on t ≥ 0.
Off-source behaviour of γ on t < 0 is unconstrained and never compared (EqOn only on [0,τ)). The requirement γ t ≠ U t is
required for the ODE to make sense (paper's solution is defined up to T_z where f → 0, paper.tex:L265-268). For τ = 0 the
predicate is just γ 0 = z (so τ = 0 is always attainable, set non-empty). For z = U 0 and τ > 0 it is unsatisfiable.

### absorbingTime (paper.tex:L265-268) ACCEPT
sSup in ℝ≥0∞ (complete lattice, no empty/unbounded junk; set contains 0). The set is downward closed (restriction), so sSup is the
maximal existence time given gluing = what `loewner_wellDefined` supplies. Machine-checked: `absorbingTime U (U 0) = 0` for every U (a2 `abs_U0`).

### loewner_wellDefined (Def 1.1) ACCEPT-WITH-NOTE
Binders: U, z typing; hU SOURCE (paper.tex:L253 "continuous"). Conclusion states existence on [0,T_z) (including T_z = ∞ and T_z = 0, where it is
vacuous) and uniqueness on [0,T_z). Nothing extra (no estimate, no measurability) and nothing missing for the definition of g_t on the
domain of f_t. True mathematically: solutions of an ODE with locally Lipschitz field on {g ≠ U_t}; gluing of solutions on [0,τ), τ<T, by uniqueness.
Note R2: uniqueness only for τ = T_z.

### leftHull (paper.tex:L271-277) ACCEPT
`{z | absorbingTime U z ≤ ↑t}` is literally {T_z ≤ t} for t : ℝ≥0 (coercion into ℝ≥0∞ checked in the elaborated body). Since U 0 ∈ L_0, L_t ∋ U 0 for all t
(a2 `zero_mem_leftHull`), so L_t is nonempty (used by P5).

### DisconnectsFromInfinity (Def 1.9, paper.tex:L497-499) ACCEPT
Components of ℂ∖S are `connectedComponentIn Sᶜ x`, x ∈ Sᶜ; "unbounded" is ¬IsBounded; S' disjoint from each. Points of S (and S'∩S ≠ ∅) are allowed:
checked `S' ⊆ S → DisconnectsFromInfinity S S'` (a4 `disc_sub`). Sanity: `¬ DisconnectsFromInfinity ∅ {0}` (a4 `not_disc_empty`).

### covMatrix, complexGaussian (paper.tex:L304-306) ACCEPT / ACCEPT-WITH-NOTE
covMatrix: `!![a,c;c,b]` exact. complexGaussian S: map of `multivariateGaussian 0 S` by x ↦ x 0 + x 1 i, coordinates (re, im).
Mathlib: `covariance_eval_multivariateGaussian (hS : S.PosSemidef) i j : cov[x i, x j] = S i j`, so Cov(Re,Im) = c, Var Re = a, Var Im = b. The map is continuous, hence no
map-of-nonmeasurable junk. Fallback: `multivariateGaussian_of_not_posSemidef` gives dirac 0. With a,b>0, c²≤ab and r = t-s ≥ 0, `r•covMatrix a b c` is PSD (proved, a6 `psd`),
so the fallback does not bite under the R1 hypotheses; it does bite for a,b<0 (R1). At s = t, r = 0, 0•Σ = 0 is PSD, law dirac 0, correct.

### IsSLEDriver (Def 1.4 with P3) ACCEPT-WITH-NOTE
Binders: Ω, MeasurableSpace Ω (typing), a,b,c (typing), U, P (typing). Fields: a.s. continuity, U 0 = 0 a.s., `HasIndepIncrements U P` (Mathlib: for every n and monotone
t : Fin (n+1) → ℝ≥0, the increments are `iIndepFun`), `HasLaw` of each increment with law N(0,(t-s)Σ) on ℂ. HasLaw includes AEMeasurable of increments, so U t - U 0 is AEMeasurable.
Equivalent to "(Re U, Im U) planar BM with covariance Σ" for PSD Σ (independent Gaussian increments + a.s. continuity + U₀ = 0). Does not assert PSD (junk for non-PSD, R1/R4).
Satisfiable: a2 `zero_driver` shows the structure is inhabited (at the junk parameters); for a,b>0 inhabitation needs Wiener measure, which is a true fact, not provable from Mathlib alone but not needed for the audit.
Filtration: not included; a Markov-property consumer takes the natural (completed) filtration and derives independence of future increments from σ(U_s : s ≤ t) via the π-λ theorem. This is a proof step, not a carrier premise. Not required in the carrier.
Note: Mathlib's iIndepFun is stated on comap σ-algebras with no a.e. quotient; any genuine measurable BM satisfies it, and since all conclusions are a.s. path statements, restricting to such versions loses nothing.

### IsThinPhase / IsSwallowingPhase / IsHittingPhase / IsDensePhase (Def 1.7, paper.tex:L409-417; P1, P9) ACCEPT-WITH-NOTE
All four: ∀ Ω : Type, MeasurableSpace, P prob, U with IsSLEDriver, ∀ z ≠ 0, `∀ᵐ ω`. Compared to the paper:
- thin: z ∉ closure(⋃_t L_t), `⋃ t : ℝ≥0`. OK.
- swallowing: T_z < ∞ and z ∉ closure(⋃_{t<T_z} L_t). The paper writes T_z := inf{t : z ∈ L_t}; since L_t = {T_z ≤ t}, the inf equals the ODE T_z (also inf ∅ = ∞). OK.
- hitting, dense: OK; dense = closure(⋃L_t) \ ⋃L_t.
Union over t : ℝ≥0 with `(t : ℝ≥0∞) < T_z` is exactly real t ∈ [0,T_z). For T_z = ∞ it is all t. `∀ᵐ` means null complement (P9). Vacuity: not trivially true or false (thin: asserts z ∉ closure); it is inhabited by Wiener-space drivers (true fact, not Mathlib-constructed). Non-PSD parameters are junk (R4).
P1 verification below.

### mu, nu, diffusionD (paper.tex:L424-426) ACCEPT
Character-by-character: mu = -(2 - a/2 + b/2) sin 2u - c cos 2u; nu = (2 - a/2 + b/2) cos 2u - c sin 2u; D = a/2 sin²u + b/2 cos²u - c cos u sin u.
Precedence in Lean: `a / 2 * sin u ^ 2` = (a/2)·(sin u)²; `-(…) * sin (2*u)` = (-(…))·sin(2u). `sin, cos, π` are Real (open Real, elaboration shows ℝ). a2 check: mu 2 2 0 u = -2 sin 2u, diffusionD 2 2 0 = 1.

### IsAdmissibleDensity (Lemma 2.14 hypotheses, paper.tex:L963-966; P4) ACCEPT
Fields: Continuous, ≥ 0, `Function.Periodic p π`, `∫ u in 0..2π, p u = 1` (parses as (∫ p) = 1), ∃x: ContDiffOn ℝ 2 p {u | ∀ n:ℤ, u ≠ x+nπ} (open set), ODE `-(deriv (µ p)) u + deriv (deriv (D p)) u = 0` off x+πℤ, ContDiff ℝ 1 (D·p). On the open set p is C², so deriv(µp) and deriv∘deriv(Dp) are the genuine derivatives (D p is C¹ globally, C² off the exceptional set). Matches the hypotheses of Lemma 2.14. For a,b,c with c²<ab one may take x arbitrary (set removed anyway; harmless).
Non-vacuity: machine-checked `∃ p, IsAdmissibleDensity 2 2 0 p` with p = K exp(cos 2u), K⁻¹ = ∫₀^{2π} exp(cos 2u) (a3 `satisfiable`). It is an equality of both D·p ODE, periodicity, normalization, C¹, so the encoding is not unsatisfiable by a formalization slip.

### integralI, integralII (paper.tex:L440-441) ACCEPT
Exact.

### phases (Thm 1.8, paper.tex:L437-453; P2, P4) ACCEPT-WITH-NOTE
Binders: a,b,c typing; ha,hb RULED P2; hc = |c| ≤ √ab ⇔ c² ≤ ab (given a,b>0) SOURCE (Def 1.4 PSD); p RULED P4 (the paper's "the p"); hp RULED P4 (admissible).
Quantifier order: parameters, then p, then four implications — matches Thm 1.8 read with P4. Signs: (I≥0,II>0 → thin), (I<0,II>0 → swallowing), (I<0,II<0 → hitting), (I≥0,II<0 → dense): exact.
Strictness relative to the paper: ∀ admissible p is stronger than "the p constructed in §2.4" and footnote 1 (paper.tex:L430-433) supports it; the class is π-periodic only, whereas (1.11) says 2π-periodic; footnote 1 speaks of any 2π-periodic non-negative solution with mild regularity, and the draft class is smaller. That is acceptable because Lemma 2.14 (what the proof uses) is π-periodic; record it. Existence is not in the statement: R3. EXCESS count 0 (hp is the p of the theorem).

### phases_c_zero (Thm 1.8 last sentence, L450; P2, P8) ACCEPT
a,b > 0 RULED P2; a−b ≤ 4 thin, 4 < a−b < 8 swallowing, a−b ≥ 8 hitting: exact (boundary a−b=8 is Lemma 3.12; a−b=4 included in thin per the paper). No p. c=0 so hc is trivially true.

### disconnects_point, disconnects_open: REJECT, see R1
Other checks (modulo R1): (a) conclusion `∃ t > 0, z ∉ L_t ∧ L_t disconnects {z}` matches paper.tex:L506-507 with z ≠ 0 (P1). (b) P7: `∀ᵐ ω, ∀ t>0, interior{w | L_t disconnects {w}} ≠ ∅` matches paper.tex:L508-509, and the paper's proof (L2224-2230) obtains it by monotonicity, so uniformity in t is exactly what is proved.
Paper-level note on (b): by Def 1.9 (L497-499, and L2227 "each subset of L_t is considered disconnected") the set {w : L_t disconnects w} contains L_t, so the literal statement is weaker than the prose claim "complements of the hulls are not connected" (L1950, L513, L518); Lemma 3.? disconnect-2 (L1957-1960) does give U ∩ L_t = ∅ but monotonicity in t does not preserve this. Do not use (b) later as "ℂ∖L_t is disconnected".
Also paper.tex:L495 says "a ≠ b" in prose while Thm 1.10 (L503) does not; the theorem governs; the draft correctly has no a ≠ b.

## Rulings: independent checks

- **P1 CORRECT, and stronger than stated.** With U₀ = 0, abs_U0 gives T_0 = 0, so 0 ∈ L_t for all t (a2 `zero_mem_leftHull`).
  Literally at z = 0: thin fails (0 ∈ ⋃ L_t ⊂ closure); dense fails (0 ∈ ⋃ L_t); hitting fails (⋃_{t<0} = ∅, a2 `zero_not_hitting`); swallowing TRUE (T_0 = 0 < ∞ and closure ∅ = ∅).
  So the literal reading makes Thm 1.8 false for the thin, hitting, dense cases. Thm 1.10(a) fails at 0 (0 ∉ L_t impossible). Suggest extending the ruling text with the swallowing remark. Props 3.1/3.2 already use z ≠ 0.
- **P2 CORRECT.** Re-derived: Lemma 2.13 Case 2 needs tan x = √(b/a), μ(x) = −4√(ab)/(a+b) ≠ 0 (paper.tex:L1112-1125). For a = 0 (x = π/2) or b = 0 (x = 0), μ(x) = −(2±…) sin 2x = 0, so (2.32)-(2.33) divide by D'(x) − μ(x) = 0, and θ = x is a fixed point (drift and 2D both vanish). Strengthening: the unrestricted c=0 bullet of Thm 1.8 is FALSE at Σ = 0: U ≡ 0, z = i has T_z = 1/4 < ∞, contradicting "thin if a−b ≤ 4". So restriction is needed, not merely convenient. Objection/note: P2 also drops the cases b = 0 (Rohde–Schramm) and a = 0 < b which the paper literally includes; this is a recorded scope reduction, not an error. Thm 1.10 needs a,b>0 too (R1).
- **P3 CORRECT.** Paper literally gives only marginal BMs with correlation; joint Gaussianity is the intended meaning. Add to ruling text: PSD of Σ is a standing assumption (needed since IsSLEDriver itself is junk for non-PSD) and U₀ = 0 holds only a.s. (consistent with draft).
- **P4 ACCEPTABLE.** Noting that it restricts to π-periodic p (vs 2π in (1.11)) and requires the separate existence root R3. The ∀p claim is consistent with footnote 1 and is mathematically plausible (any admissible p is a stationary density; sign of (I),(II) independent of choice) but it implicitly asserts that (I),(II) signs do not depend on p; this is the SOURCE_GAP the ruling already mentions.
- **P6 CORRECT.** A.1 normalizes ∫₀^π p = 1 and π-periodic p gives ∫₀^{2π} p = 2∫₀^π p, so the application uses 2p (ODE is linear homogeneous). Lemma 2.14's SDE is dθ = µ dt + √(2D) dW (paper.tex:L980-990), so α = µ, β² = 2D; ∫₀^π µ = 0 (sin 2u, cos 2u integrate to 0) hence µ takes both signs unless ≡ 0, and β = √a sin ∓ √b cos (L1003) takes both signs. So "[0,∞)" is a typo, α,β : ℝ → ℝ is right.
- **P5, P7, P8, P9**: no objection (P5 is only graph; `⨅` is junk 0 only when T_z = 0, i.e. z = U₀, excluded by z ≠ 0; P7 see note above; P8 consistent with Lemmas 3.11/3.12; P9 matches the draft).

## Commands run and outputs

All with `export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"`; `cd /home/ewain/complex-sle`; warnings about canonicalize/getpwuid filtered.
1. `lake env lean .lake/probes/Carriers.lean` -> warnings: declaration uses `sorry` at lines 27,134,143,150,158 only.
2. `lake env lean .lake/probes/audit/a1.lean` (`#print` of multivariateGaussian, HasIndepIncrements, HasLaw, stdGaussian): multivariateGaussian = map (μ + toEuclideanCLM (CFC.sqrt S)) of stdGaussian; HasIndepIncrements = ∀ n t, Monotone t → iIndepFun increments; HasLaw has aemeasurable and map_eq.
3. `grep -n multivariateGaussian .../Gaussian/Multivariate.lean`: `multivariateGaussian_of_not_posSemidef` (= dirac μ), `covariance_eval_multivariateGaussian (hS : S.PosSemidef)`.
4. a2.lean (head of Carriers + tests): compiled with only the `sorry` of loewner_wellDefined; contains proved `abs_U0`, `zero_mem_leftHull`, `zero_not_hitting`, `zero_not_thin`, `cg_of_not_psd`, `cg_zero`, `zero_driver : IsSLEDriver (-1) (-1) 0 (fun _ _ => 0) (dirac ())`.
5. a3.lean: `satisfiable : ∃ p, IsAdmissibleDensity 2 2 0 p` compiled with no errors.
6. a4.lean: `disc_sub`, `not_disc_empty` compiled.
7. a5.lean: R2, R3, R1 replacements compiled (4 sorry warnings only).
8. a6.lean: `psd : 0<a → 0<b → c^2 ≤ a*b → 0 ≤ r → (r • covMatrix a b c).PosSemidef` compiled.
Scratch files under `.lake/probes/audit/` deleted after the run.
