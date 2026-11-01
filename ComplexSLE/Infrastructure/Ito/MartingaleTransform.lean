/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.Adapted

/-!
# Martingale transforms: orthogonality of increments and an `L²` bound

Source-independent probability for the bounded core of Itô's formula
(`ComplexSLE.Infrastructure.Ito`); no external input is used.

* `AEBdd P f`: `f` is a.e. strongly measurable and almost surely bounded (closed under sums,
  products, ...; such functions are integrable).
* `integral_mul_sub_eq_zero`: for a martingale `G`, `u ≤ v` and `c` bounded-times-integrable and
  `ℱ u`-measurable, `E[c (G v - G u)] = 0`.
* `integral_sq_sub_eq`: `E[(G v - G u)²] = E[G v²] - E[G u²]` for a.s. bounded `G`.
* `transform G τ c N = ∑_{k<N} c_k (G_{τ_{k+1}} - G_{τ_k})`, the martingale transform of `G` by an
  adapted sequence; `integral_sq_transform_le`: `E[(transform)²] ≤ L² K²` if `|c_k| ≤ L` and
  `|G| ≤ K` almost surely, and `setIntegral_transform_eq_zero`: it integrates to `0` on every
  `B ∈ ℱ (τ 0)`.
-/

@[expose] public section

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Infrastructure.Ito

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}

theorem integral_mul_sub_eq_zero [IsProbabilityMeasure P] {G : ℝ≥0 → Ω → ℝ}
    (hG : Martingale G ℱ P) {u v : ℝ≥0} (huv : u ≤ v) {c : Ω → ℝ}
    (hc : StronglyMeasurable[ℱ u] c) (hint : Integrable (fun ω => c ω * (G v ω - G u ω)) P) :
    ∫ ω, c ω * (G v ω - G u ω) ∂P = 0 := by
  have hg : Integrable (fun ω => G v ω - G u ω) P := (hG.integrable v).sub (hG.integrable u)
  have h1 : P[fun ω => G v ω - G u ω | ℱ u] =ᵐ[P] 0 := by
    have h2 : P[fun ω => G v ω - G u ω | ℱ u] =ᵐ[P] P[G v | ℱ u] - P[G u | ℱ u] :=
      condExp_sub (hG.integrable v) (hG.integrable u) _
    have h3 : P[G u | ℱ u] = G u := condExp_of_stronglyMeasurable (ℱ.le u) (hG.stronglyMeasurable u)
        (hG.integrable u)
    filter_upwards [h2, hG.condExp_ae_eq huv] with ω h2 h4
    simp only [Pi.sub_apply, Pi.zero_apply] at h2 ⊢
    rw [h2, h4, h3]; ring
  have h5 : P[c * fun ω => G v ω - G u ω | ℱ u] =ᵐ[P] c * P[fun ω => G v ω - G u ω | ℱ u] :=
    condExp_mul_of_stronglyMeasurable_left hc hint hg
  calc ∫ ω, c ω * (G v ω - G u ω) ∂P = ∫ ω, (P[c * fun ω => G v ω - G u ω | ℱ u]) ω ∂P :=
        (integral_condExp (ℱ.le u)).symm
    _ = ∫ ω, (c * P[fun ω => G v ω - G u ω | ℱ u]) ω ∂P := integral_congr_ae h5
    _ = 0 := by
      rw [integral_congr_ae (g := fun _ => (0:ℝ))]
      · simp
      · filter_upwards [h1] with ω hω
        simp only [Pi.mul_apply]
        rw [hω]; simp


/-! ### Almost surely bounded random variables -/

/-- `f` is a.e. strongly measurable and almost surely bounded. -/
def AEBdd (P : Measure Ω) (f : Ω → ℝ) : Prop :=
  AEStronglyMeasurable f P ∧ ∃ b : ℝ, ∀ᵐ ω ∂P, |f ω| ≤ b

namespace AEBdd

variable {f g : Ω → ℝ}

theorem of_bound (hf : AEStronglyMeasurable f P) {b : ℝ} (h : ∀ᵐ ω ∂P, |f ω| ≤ b) :
    AEBdd P f := ⟨hf, b, h⟩

theorem integrable [IsFiniteMeasure P] (hf : AEBdd P f) : Integrable f P := by
  obtain ⟨hm, b, hb⟩ := hf
  exact Integrable.of_bound hm b (by simpa [Real.norm_eq_abs] using hb)

theorem const (c : ℝ) : AEBdd P (fun _ => c) :=
  ⟨aestronglyMeasurable_const, |c|, Filter.Eventually.of_forall fun _ => le_rfl⟩

theorem add (hf : AEBdd P f) (hg : AEBdd P g) : AEBdd P (fun ω => f ω + g ω) := by
  obtain ⟨hm, b, hb⟩ := hf
  obtain ⟨hm', b', hb'⟩ := hg
  refine ⟨hm.add hm', b + b', ?_⟩
  filter_upwards [hb, hb'] with ω h1 h2
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem neg (hf : AEBdd P f) : AEBdd P (fun ω => -f ω) := by
  obtain ⟨hm, b, hb⟩ := hf
  exact ⟨hm.neg, b, by filter_upwards [hb] with ω h; simpa using h⟩

theorem sub (hf : AEBdd P f) (hg : AEBdd P g) : AEBdd P (fun ω => f ω - g ω) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem mul (hf : AEBdd P f) (hg : AEBdd P g) : AEBdd P (fun ω => f ω * g ω) := by
  obtain ⟨hm, b, hb⟩ := hf
  obtain ⟨hm', b', hb'⟩ := hg
  refine ⟨hm.mul hm', b * b', ?_⟩
  filter_upwards [hb, hb'] with ω h1 h2
  rw [abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)

theorem const_mul (c : ℝ) (hf : AEBdd P f) : AEBdd P (fun ω => c * f ω) :=
  (const c).mul hf

theorem abs (hf : AEBdd P f) : AEBdd P (fun ω => |f ω|) := by
  obtain ⟨hm, b, hb⟩ := hf
  exact ⟨hm.norm, b, by filter_upwards [hb] with ω h; simpa using h⟩

theorem sq (hf : AEBdd P f) : AEBdd P (fun ω => f ω ^ 2) := by
  simpa [_root_.sq] using hf.mul hf

theorem finset_sum {ι : Type*} (s : Finset ι) {f : ι → Ω → ℝ} (h : ∀ i ∈ s, AEBdd P (f i)) :
    AEBdd P (fun ω => ∑ i ∈ s, f i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using AEBdd.const (P := P) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end AEBdd


/-! ### Orthogonality of martingale increments, `L²` bound for martingale transforms -/

theorem AEBdd.of_stronglyMeasurable {i : ℝ≥0} {f : Ω → ℝ} (hf : StronglyMeasurable[ℱ i] f)
    {b : ℝ} (h : ∀ᵐ ω ∂P, |f ω| ≤ b) : AEBdd P f :=
  AEBdd.of_bound (hf.mono (ℱ.le i)).aestronglyMeasurable h


theorem integral_sq_sub_eq [IsProbabilityMeasure P] {G : ℝ≥0 → Ω → ℝ}
    (hG : Martingale G ℱ P) {u v : ℝ≥0} (huv : u ≤ v) (hu : AEBdd P (G u)) (hv : AEBdd P (G v)) :
    ∫ ω, (G v ω - G u ω) ^ 2 ∂P = ∫ ω, G v ω ^ 2 ∂P - ∫ ω, G u ω ^ 2 ∂P := by
  have h0 : ∫ ω, G u ω * (G v ω - G u ω) ∂P = 0 :=
    integral_mul_sub_eq_zero hG huv (hG.stronglyMeasurable u) (hu.mul (hv.sub hu)).integrable
  have e : ∀ ω, (G v ω - G u ω) ^ 2 =
      (G v ω ^ 2 - G u ω ^ 2) - 2 * (G u ω * (G v ω - G u ω)) := fun ω => by ring
  simp only [e]
  rw [integral_sub (hv.sq.sub hu.sq).integrable ((hu.mul (hv.sub hu)).const_mul 2).integrable,
    integral_sub hv.sq.integrable hu.sq.integrable, integral_const_mul, h0]
  ring


/-- Orthogonality of a martingale increment to bounded `ℱ u`-measurable variables, on a set
`B ∈ ℱ u`. -/
theorem setIntegral_mul_sub_eq_zero [IsProbabilityMeasure P] {G : ℝ≥0 → Ω → ℝ}
    (hG : Martingale G ℱ P) {u v : ℝ≥0} (huv : u ≤ v) {c : Ω → ℝ}
    (hc : StronglyMeasurable[ℱ u] c) {L K : ℝ} (hcL : ∀ᵐ ω ∂P, |c ω| ≤ L)
    (hGu : ∀ᵐ ω ∂P, |G u ω| ≤ K) (hGv : ∀ᵐ ω ∂P, |G v ω| ≤ K)
    {B : Set Ω} (hB : MeasurableSet[ℱ u] B) :
    ∫ ω in B, c ω * (G v ω - G u ω) ∂P = 0 := by
  have hcb : AEBdd P c := AEBdd.of_stronglyMeasurable hc hcL
  have hGub : AEBdd P (G u) := AEBdd.of_stronglyMeasurable (hG.stronglyMeasurable u) hGu
  have hGvb : AEBdd P (G v) :=
    ⟨((hG.stronglyMeasurable v).mono (ℱ.le v)).aestronglyMeasurable, K, hGv⟩
  have hcB : AEBdd P (B.indicator c) := by
    refine ⟨(hc.mono (ℱ.le _)).aestronglyMeasurable.indicator (ℱ.le _ _ hB), ?_⟩
    obtain ⟨_, b, hb⟩ := hcb
    refine ⟨b, ?_⟩
    filter_upwards [hb] with ω h
    by_cases hω : ω ∈ B <;> simp [hω, h, (abs_nonneg _).trans h]
  have := integral_mul_sub_eq_zero hG huv (c := B.indicator c) (hc.indicator hB)
    (hcB.mul (hGvb.sub hGub)).integrable
  rw [← this, ← integral_indicator (ℱ.le _ _ hB)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  by_cases hω : ω ∈ B <;> simp [hω]

/-- The martingale transform `∑_{k<N} c_k (G_{τ_{k+1}} - G_{τ_k})`. -/
noncomputable def transform (G : ℝ≥0 → Ω → ℝ) (τ : ℕ → ℝ≥0) (c : ℕ → Ω → ℝ) (N : ℕ)
    (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range N, c k ω * (G (τ (k + 1)) ω - G (τ k) ω)

theorem transform_zero (G : ℝ≥0 → Ω → ℝ) (τ : ℕ → ℝ≥0) (c : ℕ → Ω → ℝ) :
    transform G τ c 0 = fun _ => 0 := by
  funext ω; simp [transform]

theorem transform_succ (G : ℝ≥0 → Ω → ℝ) (τ : ℕ → ℝ≥0) (c : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) :
    transform G τ c (N + 1) ω =
      transform G τ c N ω + c N ω * (G (τ (N + 1)) ω - G (τ N) ω) := by
  simp [transform, Finset.sum_range_succ]

theorem sum_transform_aux [IsProbabilityMeasure P] {G : ℝ≥0 → Ω → ℝ} (hG : Martingale G ℱ P)
    {τ : ℕ → ℝ≥0} (hτ : Monotone τ) {c : ℕ → Ω → ℝ}
    (hc : ∀ k, StronglyMeasurable[ℱ (τ k)] (c k)) {L K : ℝ}
    (hcL : ∀ k, ∀ᵐ ω ∂P, |c k ω| ≤ L) (hGK : ∀ k, ∀ᵐ ω ∂P, |G (τ k) ω| ≤ K) (N : ℕ) :
    StronglyMeasurable[ℱ (τ N)] (transform G τ c N) ∧ AEBdd P (transform G τ c N) ∧
      ∫ ω, transform G τ c N ω ^ 2 ∂P ≤
        L ^ 2 * (∫ ω, G (τ N) ω ^ 2 ∂P - ∫ ω, G (τ 0) ω ^ 2 ∂P) := by
  have hGb : ∀ k, AEBdd P (G (τ k)) := fun k =>
    AEBdd.of_stronglyMeasurable (hG.stronglyMeasurable (τ k)) (hGK k)
  have hcb : ∀ k, AEBdd P (c k) := fun k => AEBdd.of_stronglyMeasurable (hc k) (hcL k)
  induction N with
  | zero =>
    rw [transform_zero]
    refine ⟨stronglyMeasurable_const, AEBdd.const 0, ?_⟩
    simp
  | succ N ih =>
    obtain ⟨hSm, hSb, hSint⟩ := ih
    have hd : AEBdd P (fun ω => G (τ (N + 1)) ω - G (τ N) ω) := (hGb _).sub (hGb _)
    have hle : ℱ (τ N) ≤ ℱ (τ (N + 1)) := ℱ.mono (hτ (Nat.le_succ N))
    have hfun : transform G τ c (N + 1) = fun ω => transform G τ c N ω +
        c N ω * (G (τ (N + 1)) ω - G (τ N) ω) := funext (transform_succ G τ c N)
    refine ⟨?_, ?_, ?_⟩
    · rw [hfun]
      exact (hSm.mono hle).add (((hc N).mono hle).mul
        ((hG.stronglyMeasurable _).sub ((hG.stronglyMeasurable _).mono hle)))
    · rw [hfun]
      exact hSb.add ((hcb N).mul hd)
    · simp only [transform_succ]
      have hcross : ∫ ω, transform G τ c N ω *
          (c N ω * (G (τ (N + 1)) ω - G (τ N) ω)) ∂P = 0 := by
        have := integral_mul_sub_eq_zero hG (hτ (Nat.le_succ N))
          (c := fun ω => transform G τ c N ω * c N ω)
          (hSm.mul (hc N)) ((hSb.mul (hcb N)).mul hd).integrable
        simpa [mul_assoc] using this
      have hexp : ∀ ω, (transform G τ c N ω + c N ω * (G (τ (N + 1)) ω - G (τ N) ω)) ^ 2 =
          transform G τ c N ω ^ 2 + 2 * (transform G τ c N ω *
            (c N ω * (G (τ (N + 1)) ω - G (τ N) ω))) +
            (c N ω) ^ 2 * (G (τ (N + 1)) ω - G (τ N) ω) ^ 2 := fun ω => by ring
      have hA : AEBdd P (fun ω => transform G τ c N ω ^ 2) := hSb.sq
      have hB : AEBdd P (fun ω => transform G τ c N ω *
          (c N ω * (G (τ (N + 1)) ω - G (τ N) ω))) := hSb.mul ((hcb N).mul hd)
      have hC : AEBdd P (fun ω => (c N ω) ^ 2 * (G (τ (N + 1)) ω - G (τ N) ω) ^ 2) :=
        (hcb N).sq.mul hd.sq
      simp only [hexp]
      rw [integral_add (hA.add (hB.const_mul 2)).integrable hC.integrable,
        integral_add hA.integrable (hB.const_mul 2).integrable, integral_const_mul, hcross]
      have hint2 : ∫ ω, (c N ω) ^ 2 * (G (τ (N + 1)) ω - G (τ N) ω) ^ 2 ∂P ≤
          L ^ 2 * ∫ ω, (G (τ (N + 1)) ω - G (τ N) ω) ^ 2 ∂P := by
        rw [← integral_const_mul]
        refine integral_mono_ae hC.integrable (hd.sq.const_mul _).integrable ?_
        filter_upwards [hcL N] with ω h
        have h2 : c N ω ^ 2 ≤ L ^ 2 := by
          have := sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2
          simpa using this
        exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
      rw [integral_sq_sub_eq hG (hτ (Nat.le_succ N)) (hGb _) (hGb _)] at hint2
      nlinarith

/-- **`L²` bound for a martingale transform.** -/
theorem integral_sq_transform_le [IsProbabilityMeasure P] {G : ℝ≥0 → Ω → ℝ}
    (hG : Martingale G ℱ P) {τ : ℕ → ℝ≥0} (hτ : Monotone τ) {c : ℕ → Ω → ℝ}
    (hc : ∀ k, StronglyMeasurable[ℱ (τ k)] (c k)) {L K : ℝ}
    (hcL : ∀ k, ∀ᵐ ω ∂P, |c k ω| ≤ L) (hGK : ∀ k, ∀ᵐ ω ∂P, |G (τ k) ω| ≤ K) (N : ℕ) :
    ∫ ω, transform G τ c N ω ^ 2 ∂P ≤ L ^ 2 * K ^ 2 := by
  refine (sum_transform_aux hG hτ hc hcL hGK N).2.2.trans ?_
  have h1 : ∫ ω, G (τ N) ω ^ 2 ∂P ≤ K ^ 2 := by
    have hb := (AEBdd.of_stronglyMeasurable (hG.stronglyMeasurable (τ N)) (hGK N)).sq
    calc ∫ ω, G (τ N) ω ^ 2 ∂P ≤ ∫ ω, K ^ 2 ∂P := by
          refine integral_mono_ae hb.integrable (integrable_const _) ?_
          filter_upwards [hGK N] with ω h
          have := sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2
          simpa using this
      _ = K ^ 2 := by simp
  have h0 : 0 ≤ ∫ ω, G (τ 0) ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)

/-- The transform of a martingale by an adapted bounded sequence is a.s. bounded, strongly
measurable for `ℱ (τ N)`, and integrates to zero on every `B ∈ ℱ (τ 0)`. -/
theorem setIntegral_transform_eq_zero [IsProbabilityMeasure P] {G : ℝ≥0 → Ω → ℝ}
    (hG : Martingale G ℱ P) {τ : ℕ → ℝ≥0} (hτ : Monotone τ) {c : ℕ → Ω → ℝ}
    (hc : ∀ k, StronglyMeasurable[ℱ (τ k)] (c k)) {L K : ℝ}
    (hcL : ∀ k, ∀ᵐ ω ∂P, |c k ω| ≤ L) (hGK : ∀ k, ∀ᵐ ω ∂P, |G (τ k) ω| ≤ K) (N : ℕ)
    {B : Set Ω} (hB : MeasurableSet[ℱ (τ 0)] B) :
    ∫ ω in B, transform G τ c N ω ∂P = 0 := by
  have hGb : ∀ k, AEBdd P (G (τ k)) := fun k =>
    AEBdd.of_stronglyMeasurable (hG.stronglyMeasurable (τ k)) (hGK k)
  have hcb : ∀ k, AEBdd P (c k) := fun k => AEBdd.of_stronglyMeasurable (hc k) (hcL k)
  have hterm : ∀ k, ∫ ω in B, c k ω * (G (τ (k + 1)) ω - G (τ k) ω) ∂P = 0 := fun k =>
    setIntegral_mul_sub_eq_zero hG (hτ (Nat.le_succ k)) (hc k) (hcL k) (hGK k) (hGK (k + 1))
      (ℱ.mono (hτ (Nat.zero_le k)) _ hB)
  simp only [transform]
  rw [integral_finsetSum]
  · exact Finset.sum_eq_zero fun k _ => hterm k
  · intro k _
    exact ((hcb k).mul ((hGb _).sub (hGb _))).integrable.integrableOn

/-! ### Variables with vanishing mean on a set -/

/-- `f` is a.s. bounded and integrates to zero on `B`. -/
def NullOn (P : Measure Ω) (B : Set Ω) (f : Ω → ℝ) : Prop :=
  AEBdd P f ∧ ∫ ω in B, f ω ∂P = 0

namespace NullOn

variable {B : Set Ω} {f g : Ω → ℝ}

theorem zero : NullOn P B (fun _ => 0) := ⟨AEBdd.const 0, by simp⟩

theorem add [IsFiniteMeasure P] (hf : NullOn P B f) (hg : NullOn P B g) :
    NullOn P B (fun ω => f ω + g ω) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  rw [integral_add hf.1.integrable.integrableOn hg.1.integrable.integrableOn, hf.2, hg.2]
  simp

theorem sub [IsFiniteMeasure P] (hf : NullOn P B f) (hg : NullOn P B g) :
    NullOn P B (fun ω => f ω - g ω) := by
  refine ⟨hf.1.sub hg.1, ?_⟩
  rw [integral_sub hf.1.integrable.integrableOn hg.1.integrable.integrableOn, hf.2, hg.2]
  simp

theorem const_mul (c : ℝ) (hf : NullOn P B f) : NullOn P B (fun ω => c * f ω) := by
  refine ⟨hf.1.const_mul c, ?_⟩
  rw [integral_const_mul, hf.2]
  simp

theorem finset_sum [IsFiniteMeasure P] {ι : Type*} (s : Finset ι) {f : ι → Ω → ℝ}
    (h : ∀ i ∈ s, NullOn P B (f i)) : NullOn P B (fun ω => ∑ i ∈ s, f i ω) := by
  refine ⟨AEBdd.finset_sum s fun i hi => (h i hi).1, ?_⟩
  rw [integral_finsetSum s fun i hi => (h i hi).1.integrable.integrableOn]
  exact Finset.sum_eq_zero fun i hi => (h i hi).2

/-- A bounded `ℱ u`-measurable multiple of a bounded martingale increment has mean zero on
`B ∈ ℱ u`. -/
theorem of_martingale [IsProbabilityMeasure P] {G : ℝ≥0 → Ω → ℝ} (hG : Martingale G ℱ P)
    {u v : ℝ≥0} (huv : u ≤ v) {c : Ω → ℝ} (hc : StronglyMeasurable[ℱ u] c) {L K : ℝ}
    (hcL : ∀ᵐ ω ∂P, |c ω| ≤ L) (hGu : ∀ᵐ ω ∂P, |G u ω| ≤ K) (hGv : ∀ᵐ ω ∂P, |G v ω| ≤ K)
    (hB : MeasurableSet[ℱ u] B) : NullOn P B (fun ω => c ω * (G v ω - G u ω)) := by
  have hcb : AEBdd P c := AEBdd.of_stronglyMeasurable hc hcL
  have hGub : AEBdd P (G u) := AEBdd.of_stronglyMeasurable (hG.stronglyMeasurable u) hGu
  have hGvb : AEBdd P (G v) :=
    ⟨((hG.stronglyMeasurable v).mono (ℱ.le v)).aestronglyMeasurable, K, hGv⟩
  exact ⟨hcb.mul (hGvb.sub hGub), setIntegral_mul_sub_eq_zero hG huv hc hcL hGu hGv hB⟩

end NullOn

end ComplexSLE.Infrastructure.Ito

end
