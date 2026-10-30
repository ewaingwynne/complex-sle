# Errata and author rulings

Source: `paper.tex` = `source/arxiv-2203.07313v4/complex-sle-final.tex` (sha256 6f182d3a…).

## Rulings

- R1 (2026-10-30) External inputs: relative-to-externals (PLAN.md §7 option (a)).
- R2 (2026-10-30) Scope: skip §2.4, §5, Remarks 1.3/1.6/1.11, footnote 2; Lemma 2.6 deferred.
- R3 (2026-10-30) GitHub: private `ewaingwynne/complex-sle`, push at each milestone.

- R4–R12 (2026-10-30) The author approved proposals P1–P9 below, as amended by audit AU-M1,
  together with the carrier declarations in the M1 probe (definitions, `loewner_wellDefined`,
  `exists_admissibleDensity`). P1→R4, P2→R5, P3→R6, P4→R7, P5→R8, P6→R9, P7→R10, P8→R11, P9→R12.

## Rulings P1–P9 (approved 2026-10-30 as R4–R12)

Each item gives the problem, where it is, and the **proposed ruling**. "Substantive" items
change what a frozen statement says. "Typo" items only affect graph notes.

### Substantive

**P1. The point z = 0 in Def 1.7 and Thm 1.10(a).** `paper.tex:L409-417, L502-511`.
With U₀ = 0 the ODE is singular at z = 0, so T₀ = 0 and 0 ∈ L₀. Taken literally with
"for each z ∈ ℂ", the thin phase fails at z = 0 (0 ∈ ⋃ L_t), the hitting phase fails at
z = 0 (⋃_{t<0} L_t = ∅), and Thm 1.10(a) fails at z = 0 (0 ∈ L_t for all t). Props 3.1 and
3.2 already say z ∈ ℂ∖{0}.
**Proposed:** Def 1.7 and Thm 1.10(a) quantify over z ∈ ℂ∖{0}.

**P2. Degenerate Σ (ab = 0) in Lemma 2.13 and Thm 1.8.** `paper.tex:L941-955, L1086-1135`.
When ab = 0 we have c = 0 = √(ab), so Case 2 applies. But tan x = √(b/a) is undefined for
a = 0, and the proof needs µ(x) = −4√(ab)/(a+b) ≠ 0 (the L'Hôpital limits (2.32)–(2.33),
and the Hörmander condition µβ′ ≠ 0 in Lemma 2.14). With ab = 0 we get µ(x) = 0, and θ = x
is a fixed point of the SDE (the real axis when b = 0, the imaginary axis when a = 0), so
the construction breaks down. Σ = 0 is trivially degenerate as well. The c = 0 part of
Lemma 3.11 explicitly uses "a, b > 0" (L1851-1856).
**Proposed:** Lemmas 2.13, 2.14, 2.16, Props 3.1, 3.2 and Thm 1.8 (both parts) assume
a > 0 and b > 0. The classical case b = 0 (SLE_a) and the reverse case a = 0 < b are out of scope; this is a scope reduction relative to the literal Thm 1.8, which includes them. Thm 1.10 ("a, b ≠ 0") is frozen with 0 < a, 0 < b, which is equivalent under PSD; the draft's a ≠ 0, b ≠ 0 admitted a = b = −1, where the Gaussian law degenerates to a point mass (audit AU-M1, R1). (Audit addition: at Σ = 0 the c = 0 bullet of Thm 1.8 is false, since U ≡ 0 and z = i give T_z = 1/4.)

**P3. Def 1.4 does not make (B, B̃) jointly Gaussian.** `paper.tex:L301-308`.
"B, B̃ standard BMs with Cov(B_t, B̃_t) = ct/√(ab)" does not say that (B, B̃) is a
two-dimensional BM, and ct/√(ab) is 0/0 when ab = 0. §2.4 (L819ff) and the proofs use the
intended meaning: (Re U, Im U) is a planar BM with covariance Σ.
**Proposed:** positive semidefiniteness of Σ (0 ≤ a, 0 ≤ b, c² ≤ ab) is a standing assumption of every theorem. SLE_Σ is driven by U : ℝ≥0 → Ω → ℂ with a.s. continuous paths, U₀ = 0,
independent increments, and U_t − U_s ~ N(0, (t−s)Σ) on ℂ ≅ ℝ² for s ≤ t. The
representation U = √a B + i√b B̃ (when ab > 0) becomes a lemma.

**P4. Which p Thm 1.8 refers to.** `paper.tex:L428-453`, footnote 1, and Lemma 2.14
(L963-967). Eq. (1.11) says "2π-periodic". Lemmas 2.13 and 2.14 say π-periodic, and the
uniqueness of p is not proved.
**Proposed:** Thm 1.8 reads "for **every** p that is admissible in the sense of Lemma 2.14
(continuous, ≥ 0, π-periodic, ∫₀^{2π} p = 1, C² and solving (2.24) off x + πℤ for some x,
D·p ∈ C¹(ℝ)), the four sign implications hold", together with the existence of such a p
(Lemma 2.13). Footnote 1 asserts exactly this generality. The graph will carry an explicit
step "every admissible p vanishes only on a Lebesgue-null set", which Lemma 3.3 needs and
which Lemma 2.14's hypotheses do not state (SOURCE_GAP). The weaker alternative "∃ p from
Lemma 2.13 such that …" is available if you prefer it.

Companion root (audit R3): Lemma 2.13's existence part, `∃ p, IsAdmissibleDensity a b c p` for a, b > 0 and c² ≤ ab, is frozen together with Thm 1.8 so that Thm 1.8 cannot be vacuous. π-periodicity (not 2π) is kept, because Lemma 2.14's proof uses it (−z has the same law as z).

**P5. The meaning of lim_{t→T_z−} dist(z, L_t).** `paper.tex:L1276-1286`.
L_t is increasing, so t ↦ dist(z, L_t) is non-increasing and the limit always exists,
including when T_z = ∞. L_t ∋ U₀ is nonempty, which avoids Mathlib's `infDist z ∅ = 0`.
**Proposed:** the carrier is `⨅ t < T_z, infDist z (L t)` (inf over real t with t < T_z).

**P6. Lemma A.1's normalization, and the sign constraint on α.** `paper.tex:L2318-2330`.
A.1 normalizes ∫₀^π p = 1 and samples X₀ ~ p·1_{[0,π]}, whereas Lemma 2.14 uses ∫₀^{2π} p = 1
(it is applied with p ↦ 2p). A.1 also states α, β : ℝ → [0,∞), but the drift µ changes sign
and β = √a sin ∓ √b cos takes both signs.
**Proposed:** α, β : ℝ → ℝ, and the application in Lemma 2.14 uses 2p (an explicit graph step).

**P7. Thm 1.10(b) uniformity.** `paper.tex:L508-509`. "Almost surely, for each t > 0" is
uniform in t (the proof uses monotonicity of L_t).
**Proposed:** freeze it as `∀ᵐ ω, ∀ t > 0, (interior {z | L_t disconnects z from ∞}).Nonempty`.

Audit note: by Def 1.9 the points of L_t themselves count as disconnected from ∞, so (b) does not by itself say that ℂ∖L_t is disconnected (the prose at L513 and L1950 suggests more). Downstream nodes must not use (b) that way.

**P8. Thm 1.8's c = 0 bullet vs. Lemmas 3.11/3.12.** "Hitting if a − b ≥ 8" is Lemma 3.11
(a − b > 8) plus Lemma 3.12 (a − b = 8), so the two are consistent.
**Proposed:** one frozen c = 0 theorem with three conclusions (thin / swallowing / hitting),
for a, b > 0 (see P2).

**P9. "SLE_Σ is in phase X" quantifies over probability spaces.**
**Proposed:** "for every probability space (Ω : Type, P) and every driving process U as in
P3 …". Ω is in universe 0 (Type). Statements are about a.s. events, and a.s. is read as
"the complement is P-null", so no measurability of the event is presupposed.

### Typos (graph notes only)

- T1 Lemma 2.6 proof `paper.tex:L732`: "f_t = f_{s,t} ∘ f_s|_{L_t}" should be "f_s|_{ℂ∖L_t}".
- T2 Lemma 3.4 `paper.tex:L1341`: "E(f⁰(X₀⁰))" should be "E(f⁰(X₀))".
- T3 Lemma 4.4 proof `paper.tex:L2138`: "ℜf₁(x) ≤ −C, ℜf₁(y) ≥ C" should be ℜf₂.
- T4 Fig. 8 caption `paper.tex:L1653`: "s = σ(s+t) − σ(s)" should be "− σ(t)".
- T5 Lemma 2.4 proof `paper.tex:L658-666`: "a.s." in a deterministic lemma. The step
  "f_t ∘ L homotopic to L in ℂ∖{0}, hence the region bounded by L misses L_t" is a sketch
  and will be a SOURCE_GAP step node.
- T7 §2.1.1 `paper.tex:L545`: "U : [0,∞) → ℝ" should be "→ ℂ".
- T6 Lemma 4.3 `paper.tex:L1991-2030`: [Law05, Prop 4.43] "extends to ℂ by replacing ℍ by
  ℂ". This is an external input whose extension is asserted, not proved (SOURCE_GAP, and
  part of E12).
