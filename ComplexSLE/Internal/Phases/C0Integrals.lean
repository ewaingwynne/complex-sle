/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.C0Sign
public import ComplexSLE.Frozen.Defs.IntegralI
public import ComplexSLE.Frozen.Defs.IntegralII

/-!
# The case `c = 0`: the integrals (I) and (II) and the sign split

Deterministic part of Lemma 3.11 (`lem-c0-phases`, paper.tex:L1824-1910), equation
`eqn-c0-integrals`: for `c = 0` we have `ν(u) = (2 - a/2 + b/2) cos 2u`, so
`integralI a b 0 p = (2 - a/2 + b/2) S` and `integralII a b 0 p = (4 - a/2 + b/2) S` with
`S = ∫₀^{2π} cos(2u) p(u) du`, and `S > 0` (`integral_cos_mul_pos`). Consequently the signs of (I)
and (II) are decided by `a - b` against `4` and `8`:

* `0 ≤ (I) ↔ a - b ≤ 4`, `(I) < 0 ↔ 4 < a - b`, `(I) = 0 ↔ a - b = 4`;
* `0 < (II) ↔ a - b < 8`, `(II) < 0 ↔ 8 < a - b`, `(II) = 0 ↔ a - b = 8`.

`c0_integral_signs` bundles exactly the case split consumed by `theorem_1_8_c_zero`.
-/

public section

open Set Filter Topology MeasureTheory intervalIntegral Function Real

namespace ComplexSLE.Internal

variable {a b : ℝ} {p : ℝ → ℝ}

/-- `eqn-c0-integrals`, the integral (I) for `c = 0`. -/
theorem integralI_c0_eq (a b : ℝ) (p : ℝ → ℝ) :
    integralI a b 0 p = (2 - a / 2 + b / 2) * ∫ u in (0)..(2 * π), cos (2 * u) * p u := by
  unfold integralI
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext u
  simp only [nu]
  ring

/-- `eqn-c0-integrals`, the integral (II) for `c = 0`. -/
theorem integralII_c0_eq (a b : ℝ) (p : ℝ → ℝ) :
    integralII a b 0 p = (4 - a / 2 + b / 2) * ∫ u in (0)..(2 * π), cos (2 * u) * p u := by
  unfold integralII
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext u
  simp only [nu]
  ring

/-- `(I) ≥ 0` iff `a - b ≤ 4` (`c = 0`, `a, b > 0`, `p` admissible). -/
theorem integralI_c0_nonneg_iff (ha : 0 < a) (hb : 0 < b) (hp : IsAdmissibleDensity a b 0 p) :
    0 ≤ integralI a b 0 p ↔ a - b ≤ 4 := by
  have hS := integral_cos_mul_pos ha hb hp
  rw [integralI_c0_eq, mul_nonneg_iff_of_pos_right hS]
  constructor <;> intro h <;> linarith

/-- `(I) < 0` iff `4 < a - b` (`c = 0`, `a, b > 0`, `p` admissible). -/
theorem integralI_c0_neg_iff (ha : 0 < a) (hb : 0 < b) (hp : IsAdmissibleDensity a b 0 p) :
    integralI a b 0 p < 0 ↔ 4 < a - b := by
  have := integralI_c0_nonneg_iff ha hb hp
  rw [← not_le, this, not_le]

/-- `(I) = 0` iff `a - b = 4` (`c = 0`, `a, b > 0`, `p` admissible). -/
theorem integralI_c0_eq_zero_iff (ha : 0 < a) (hb : 0 < b) (hp : IsAdmissibleDensity a b 0 p) :
    integralI a b 0 p = 0 ↔ a - b = 4 := by
  have hS := integral_cos_mul_pos ha hb hp
  rw [integralI_c0_eq, mul_eq_zero]
  constructor
  · rintro (h | h)
    · linarith
    · exact absurd h hS.ne'
  · intro h; left; linarith

/-- `0 < (II)` iff `a - b < 8` (`c = 0`, `a, b > 0`, `p` admissible). -/
theorem integralII_c0_pos_iff (ha : 0 < a) (hb : 0 < b) (hp : IsAdmissibleDensity a b 0 p) :
    0 < integralII a b 0 p ↔ a - b < 8 := by
  have hS := integral_cos_mul_pos ha hb hp
  rw [integralII_c0_eq, mul_pos_iff_of_pos_right hS]
  constructor <;> intro h <;> linarith

/-- `(II) < 0` iff `8 < a - b` (`c = 0`, `a, b > 0`, `p` admissible). -/
theorem integralII_c0_neg_iff (ha : 0 < a) (hb : 0 < b) (hp : IsAdmissibleDensity a b 0 p) :
    integralII a b 0 p < 0 ↔ 8 < a - b := by
  have hS := integral_cos_mul_pos ha hb hp
  rw [← not_le, integralII_c0_eq, mul_nonneg_iff_of_pos_right hS]
  constructor <;> intro h <;> linarith

/-- `(II) = 0` iff `a - b = 8` (`c = 0`, `a, b > 0`, `p` admissible). -/
theorem integralII_c0_eq_zero_iff (ha : 0 < a) (hb : 0 < b) (hp : IsAdmissibleDensity a b 0 p) :
    integralII a b 0 p = 0 ↔ a - b = 8 := by
  have hS := integral_cos_mul_pos ha hb hp
  rw [integralII_c0_eq, mul_eq_zero]
  constructor
  · rintro (h | h)
    · linarith
    · exact absurd h hS.ne'
  · intro h; left; linarith

/-- The sign split consumed by `theorem_1_8` and `theorem_1_8_c_zero`: for `c = 0`,
`a, b > 0` and `p` admissible,
* `a - b ≤ 4` gives `0 ≤ (I)` and `0 < (II)` (thin phase);
* `4 < a - b < 8` gives `(I) < 0` and `0 < (II)` (swallowing phase);
* `8 < a - b` gives `(I) < 0` and `(II) < 0` (hitting phase);
* `a - b = 8` gives `(I) < 0` and `(II) = 0` (the boundary case of `lem-c0-bdy`). -/
theorem c0_integral_signs (ha : 0 < a) (hb : 0 < b) (hp : IsAdmissibleDensity a b 0 p) :
    (a - b ≤ 4 → 0 ≤ integralI a b 0 p ∧ 0 < integralII a b 0 p) ∧
    (4 < a - b → a - b < 8 → integralI a b 0 p < 0 ∧ 0 < integralII a b 0 p) ∧
    (8 < a - b → integralI a b 0 p < 0 ∧ integralII a b 0 p < 0) ∧
    (a - b = 8 → integralI a b 0 p < 0 ∧ integralII a b 0 p = 0) := by
  have h1 := integralI_c0_nonneg_iff ha hb hp
  have h2 := integralI_c0_neg_iff ha hb hp
  have h3 := integralII_c0_pos_iff ha hb hp
  have h4 := integralII_c0_neg_iff ha hb hp
  have h5 := integralII_c0_eq_zero_iff ha hb hp
  refine ⟨fun h => ⟨h1.2 h, h3.2 (by linarith)⟩, fun h h' => ⟨h2.2 h, h3.2 h'⟩,
    fun h => ⟨h2.2 (by linarith), h4.2 h⟩, fun h => ⟨h2.2 (by linarith), h5.2 h⟩⟩

end ComplexSLE.Internal

end
