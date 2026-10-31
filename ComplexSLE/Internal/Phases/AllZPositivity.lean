/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.C0Density
public import ComplexSLE.Internal.Stationary.Coefficients
public import Mathlib.Analysis.Complex.Arg
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Topology.Algebra.Module.Cardinality
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# An admissible density vanishes only on a countable set

Part 1 of Lemma 3.2 (`lem-all-z`, paper.tex:L1294-1325): the proof begins with "the density
`p 1_{[0,2π]}` of the law of `arg 𝐳` is non-zero on `[0, 2π]` except possibly on a discrete set";
Lemma 2.14 does not state this (ERRATA: "an admissible `p` vanishes only on a null set").

* `IsAdmissibleDensity.pos_of_differentiableAt`: for `a, b > 0` and `c² ≤ a b`, an admissible
  density is strictly positive at every point of differentiability.
* `IsAdmissibleDensity.pos_off_lattice`: in particular `p u > 0` for every `u` off the lattice
  `x + πℤ` of the definition.
* `IsAdmissibleDensity.countable_zeroSet`, `IsAdmissibleDensity.ae_pos`: the zero set of `p` is
  countable, hence Lebesgue-null.

Route. By `IsAdmissibleDensity.exists_hasDerivAt` (`(D p)' = J + µ p`), a zero `u₀` of `p` at which
`p` is differentiable is a minimum, so `J = 0`. Then `q = D p` solves the linear ODE
`q' = (µ/D) q` on every interval `(l, l + π)` on which `D > 0`; a zero of `q` in the interval forces
`q = 0` on it, and by `π`-periodicity and continuity `p ≡ 0`, contradicting `∫₀^{2π} p = 1`. If
`D(u₀) = 0` (only possible for `c² = ab`) the sign of `µ(u₀) ≠ 0` makes `q = D p ≥ 0` monotone next
to `u₀` with `q(u₀) = 0`, which produces a zero of `p` where `D > 0`.
-/

public section

open Set Filter Topology MeasureTheory intervalIntegral Function Real

namespace ComplexSLE.Internal

variable {a b c : ℝ}

/-! ### Linear ODE uniqueness on an interval -/

/-- A solution of `q' = φ q` with `φ` continuous on an open interval that vanishes at one point
vanishes on the whole interval. -/
theorem eq_zero_of_hasDerivAt_mul {φ q : ℝ → ℝ} {l r u₁ : ℝ}
    (hφ : ContinuousOn φ (Ioo l r))
    (hd : ∀ u ∈ Ioo l r, HasDerivAt q (φ u * q u) u) (hu₁ : u₁ ∈ Ioo l r) (h0 : q u₁ = 0) :
    ∀ u ∈ Ioo l r, q u = 0 := by
  intro u hu
  set m := min u u₁ with hm
  set M := max u u₁ with hM
  have hlm : l < m := lt_min hu.1 hu₁.1
  have hMr : M < r := max_lt hu.2 hu₁.2
  have hmM : m ≤ M := min_le_max
  set α := (l + m) / 2 with hα
  set β := (M + r) / 2 with hβ
  have hαm : α < m := by rw [hα]; linarith
  have hlα : l < α := by rw [hα]; linarith
  have hMβ : M < β := by rw [hβ]; linarith
  have hβr : β < r := by rw [hβ]; linarith
  have hsub : Icc α β ⊆ Ioo l r := fun t ht => ⟨lt_of_lt_of_le hlα ht.1, lt_of_le_of_lt ht.2 hβr⟩
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := α) (b := β)).exists_bound_of_continuousOn
    (hφ.mono hsub)
  set K' : NNReal := ⟨max K 0, le_max_right _ _⟩ with hK'
  have hlip : ∀ t ∈ Ioo α β, LipschitzOnWith K' (fun x : ℝ => φ t * x) univ := by
    intro t ht
    refine (LipschitzWith.of_dist_le_mul fun x y => ?_).lipschitzOnWith
    rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
    have h1 : ‖φ t‖ ≤ K := hK t (Ioo_subset_Icc_self ht)
    have h2 : |φ t| ≤ (K' : ℝ) := by
      rw [← Real.norm_eq_abs]
      exact h1.trans (le_max_left _ _)
    exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  have hqcont : ContinuousOn q (Icc α β) := fun t ht =>
    (hd t (hsub ht)).continuousAt.continuousWithinAt
  have hu₁' : u₁ ∈ Ioo α β := ⟨lt_of_lt_of_le hαm (min_le_right _ _),
    lt_of_le_of_lt (le_max_right _ _) hMβ⟩
  have hEq := ODE_solution_unique_of_mem_Icc (v := fun t x => φ t * x) (s := fun _ => univ)
    (K := K') (f := q) (g := fun _ => 0) (a := α) (b := β) (t₀ := u₁) hlip hu₁' hqcont
    (fun t ht => hd t (Ioo_subset_Ioo hlα.le hβr.le ht)) (fun _ _ => mem_univ _)
    continuousOn_const (fun t _ => by simpa using hasDerivAt_const t (0 : ℝ))
    (fun _ _ => mem_univ _) (by simpa using h0)
  have huαβ : u ∈ Icc α β := ⟨lt_of_lt_of_le hαm (min_le_left _ _) |>.le,
    (le_max_left _ _).trans hMβ.le⟩
  simpa using hEq huαβ

/-! ### The zeros of `D` in the critical case -/

/-- In the critical case `c² = ab` the zeros of `D` form a lattice `x₀ + πℤ`. -/
theorem exists_diffusionD_eq_zero_iff (ha : 0 < a) (hc : c ^ 2 = a * b) :
    ∃ x₀ : ℝ, ∀ u, diffusionD a b c u = 0 ↔ ∃ n : ℤ, (n : ℝ) * π = u - x₀ := by
  set z : ℂ := ⟨a, c⟩ with hz
  have hz0 : z ≠ 0 := by
    intro h
    have : z.re = 0 := by rw [h]; rfl
    simp [hz] at this
    linarith
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  refine ⟨z.arg, fun u => ?_⟩
  have hcos : cos z.arg = a / ‖z‖ := by rw [Complex.cos_arg hz0]
  have hsin : sin z.arg = c / ‖z‖ := by rw [Complex.sin_arg]
  have key : sin (u - z.arg) = (a * sin u - c * cos u) / ‖z‖ := by
    rw [sin_sub, hcos, hsin]
    field_simp
  have hsa : √a ^ 2 = a := Real.sq_sqrt ha.le
  have hsa0 : √a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have e : c / √a * √a = c := div_mul_cancel₀ c hsa0
  have h1 : diffusionD a b c u = 0 ↔ betaCrit a c u = 0 := by
    have := sq_betaCrit ha hc u
    constructor
    · intro h; rw [h] at this; simpa using this
    · intro h; rw [h] at this; linarith
  have h2 : betaCrit a c u = 0 ↔ a * sin u - c * cos u = 0 := by
    unfold betaCrit
    constructor
    · intro h
      linear_combination √a * h - sin u * hsa + cos u * e
    · intro h
      have : √a * (√a * sin u - c / √a * cos u) = 0 := by
        linear_combination h + sin u * hsa - cos u * e
      exact (mul_eq_zero.mp this).resolve_left hsa0
  rw [h1, h2, ← Real.sin_eq_zero_iff]
  rw [key, div_eq_zero_iff]
  simp [hnorm.ne']

/-- Every point where `D > 0` lies in an interval `(l, l + π)` on which `D > 0`. -/
theorem exists_Ioo_diffusionD_pos (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b) {u₁ : ℝ}
    (hu₁ : 0 < diffusionD a b c u₁) :
    ∃ l : ℝ, u₁ ∈ Ioo l (l + π) ∧ ∀ u ∈ Ioo l (l + π), 0 < diffusionD a b c u := by
  rcases hc.lt_or_eq with hlt | heq
  · exact ⟨u₁ - π / 2, ⟨by linarith [pi_pos], by linarith [pi_pos]⟩,
      fun u _ => diffusionD_pos ha hb hlt u⟩
  · obtain ⟨x₀, hx₀⟩ := exists_diffusionD_eq_zero_iff ha heq
    set n : ℤ := ⌊(u₁ - x₀) / π⌋ with hn
    have hn1 : (n : ℝ) ≤ (u₁ - x₀) / π := Int.floor_le _
    have hn2 : (u₁ - x₀) / π < n + 1 := Int.lt_floor_add_one _
    have hπ := pi_pos
    have hn1' : (n : ℝ) * π ≤ u₁ - x₀ := by rwa [le_div_iff₀ hπ] at hn1
    have hn2' : u₁ - x₀ < (n + 1) * π := by rwa [div_lt_iff₀ hπ] at hn2
    have hne : (n : ℝ) * π ≠ u₁ - x₀ := fun h =>
      hu₁.ne' ((hx₀ u₁).2 ⟨n, h⟩)
    refine ⟨x₀ + n * π, ⟨?_, ?_⟩, fun u hu => ?_⟩
    · have := lt_of_le_of_ne hn1' hne
      linarith
    · linarith
    · refine lt_of_le_of_ne (diffusionD_nonneg ha hb hc u) fun h0 => ?_
      obtain ⟨m, hm⟩ := (hx₀ u).1 h0.symm
      have h1 : (n : ℝ) * π < m * π := by linarith [hu.1]
      have h2 : (m : ℝ) * π < (n + 1) * π := by linarith [hu.2]
      have h1' : (n : ℝ) < m := lt_of_mul_lt_mul_right h1 hπ.le
      have h2' : (m : ℝ) < n + 1 := lt_of_mul_lt_mul_right h2 hπ.le
      have h1'' : n < m := by exact_mod_cast h1'
      have h2'' : m < n + 1 := by exact_mod_cast h2'
      omega

/-- If `J = 0`, then an admissible density that vanishes at a point where `D > 0` is zero. -/
theorem IsAdmissibleDensity.false_of_zero_of_hasDerivAt (ha : 0 < a) (hb : 0 < b)
    (hc : c ^ 2 ≤ a * b) {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p)
    (hJ : ∀ u, HasDerivAt (fun v => diffusionD a b c v * p v) (mu a b c u * p u) u) {u₁ : ℝ}
    (hD : 0 < diffusionD a b c u₁) (h0 : p u₁ = 0) : False := by
  obtain ⟨l, hl, hDpos⟩ := exists_Ioo_diffusionD_pos ha hb hc hD
  have hφ : ContinuousOn (fun u => mu a b c u / diffusionD a b c u) (Ioo l (l + π)) :=
    (continuous_mu a b c).continuousOn.div (continuous_diffusionD a b c).continuousOn
      fun u hu => (hDpos u hu).ne'
  have hd : ∀ u ∈ Ioo l (l + π), HasDerivAt (fun v => diffusionD a b c v * p v)
      ((mu a b c u / diffusionD a b c u) * (diffusionD a b c u * p u)) u := by
    intro u hu
    have := hJ u
    convert this using 1
    have := (hDpos u hu).ne'
    field_simp
  have hq0 : diffusionD a b c u₁ * p u₁ = 0 := by rw [h0, mul_zero]
  have hzero := eq_zero_of_hasDerivAt_mul hφ hd hl hq0
  have hpzero : ∀ u ∈ Ioo l (l + π), p u = 0 := fun u hu =>
    (mul_eq_zero.mp (hzero u hu)).resolve_left (hDpos u hu).ne'
  obtain ⟨hcont, -, hper, hint, -⟩ := hp
  -- `p = 0` off the lattice `l + πℤ`
  have hoff : ∀ u, (∀ n : ℤ, u ≠ l + n * π) → p u = 0 := by
    intro u hu
    set m : ℤ := ⌊(u - l) / π⌋ with hm
    have hπ := pi_pos
    have hm1 : (m : ℝ) ≤ (u - l) / π := Int.floor_le _
    have hm2 : (u - l) / π < m + 1 := Int.lt_floor_add_one _
    have hm1' : (m : ℝ) * π ≤ u - l := by rwa [le_div_iff₀ hπ] at hm1
    have hm2' : u - l < (m + 1) * π := by rwa [div_lt_iff₀ hπ] at hm2
    have hne : (m : ℝ) * π ≠ u - l := fun h => hu m (by linarith)
    have hmem : u - m * π ∈ Ioo l (l + π) := ⟨by
      have := lt_of_le_of_ne hm1' hne
      linarith, by linarith⟩
    rw [← hper.sub_int_mul_eq m]
    exact hpzero _ hmem
  have hdense : Dense {u : ℝ | ∀ n : ℤ, u ≠ l + n * π} := by
    have hc : (range fun n : ℤ => l + n * π).Countable := Set.countable_range _
    have := Set.Countable.dense_compl ℝ hc
    convert this using 1
    ext u
    simp [eq_comm]
  have hall : p = fun _ => 0 :=
    hcont.ext_on hdense continuous_const (fun u hu => hoff u hu)
  rw [hall] at hint
  simp at hint

/-- At a zero of `D` in the critical case, `µ ≠ 0`. -/
theorem mu_ne_zero_of_diffusionD_eq_zero (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a * b) {u : ℝ}
    (h0 : diffusionD a b c u = 0) : mu a b c u ≠ 0 := by
  have hβ : betaCrit a c u = 0 := by
    have := sq_betaCrit ha hc u
    rw [h0] at this
    simpa using this
  rw [mu_eq_of_betaCrit_eq_zero ha hb hc hβ]
  have hc0 : c ≠ 0 := by
    rintro rfl
    have := mul_pos ha hb
    rw [zero_pow two_ne_zero] at hc
    linarith
  have hab : a + b ≠ 0 := by positivity
  exact div_ne_zero (by intro h; apply hc0; linarith) hab

/-- A zero of `p` at a point of differentiability forces `J = 0`. -/
theorem IsAdmissibleDensity.J_eq_zero_of_zero {p : ℝ → ℝ} {J : ℝ} (hp : IsAdmissibleDensity a b c p)
    (hJ : ∀ u, HasDerivAt (fun v => diffusionD a b c v * p v) (J + mu a b c u * p u) u) {u₀ : ℝ}
    (hdiff : DifferentiableAt ℝ p u₀) (h0 : p u₀ = 0) : J = 0 := by
  have hmin : IsLocalMin p u₀ :=
    Filter.Eventually.of_forall fun x => by rw [h0]; exact hp.2.1 x
  have hder : HasDerivAt p 0 u₀ := by
    have := hdiff.hasDerivAt
    have h2 := hmin.hasDerivAt_eq_zero this
    rwa [h2] at this
  have hDd : HasDerivAt (diffusionD a b c) (deriv (diffusionD a b c) u₀) u₀ :=
    ((contDiff_diffusionD a b c).differentiable (by simp) u₀).hasDerivAt
  have h1 := hDd.mul hder
  have h2 := hJ u₀
  have := h1.unique h2
  rw [h0] at this
  simpa using this.symm

/-- **Positivity of an admissible density at points of differentiability.** For `a, b > 0` and
`c² ≤ a b`, an admissible density is strictly positive wherever it is differentiable. -/
theorem IsAdmissibleDensity.pos_of_differentiableAt (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) {u₀ : ℝ} (hdiff : DifferentiableAt ℝ p u₀) :
    0 < p u₀ := by
  by_contra hneg
  have hp0 : p u₀ = 0 := le_antisymm (not_lt.1 hneg) (hp.2.1 u₀)
  obtain ⟨J, hJ⟩ := IsAdmissibleDensity.exists_hasDerivAt hp
  have hJ0 : J = 0 := IsAdmissibleDensity.J_eq_zero_of_zero hp hJ hdiff hp0
  subst hJ0
  have hJ' : ∀ u, HasDerivAt (fun v => diffusionD a b c v * p v) (mu a b c u * p u) u := by
    intro u; simpa using hJ u
  rcases (diffusionD_nonneg ha hb hc u₀).lt_or_eq with hD | hD
  · exact IsAdmissibleDensity.false_of_zero_of_hasDerivAt ha hb hc hp hJ' hD hp0
  · -- `D u₀ = 0`: critical case
    have hcrit : c ^ 2 = a * b := by
      rcases hc.lt_or_eq with hlt | heq
      · exact absurd hD.symm (diffusionD_pos ha hb hlt u₀).ne'
      · exact heq
    obtain ⟨x₀, hx₀⟩ := exists_diffusionD_eq_zero_iff ha hcrit
    have hμ0 : mu a b c u₀ ≠ 0 := mu_ne_zero_of_diffusionD_eq_zero ha hb hcrit hD.symm
    obtain ⟨δ, hδ, hδμ⟩ : ∃ δ > 0, ∀ u, |u - u₀| < δ →
        (mu a b c u₀ < 0 → mu a b c u < 0) ∧ (0 < mu a b c u₀ → 0 < mu a b c u) := by
      have hcont := (continuous_mu a b c).continuousAt (x := u₀)
      rcases hμ0.lt_or_gt with hneg | hpos
      · obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 hcont (-mu a b c u₀) (by linarith)
        refine ⟨δ, hδ, fun u hu => ⟨fun _ => ?_, fun h' => absurd h' (by linarith)⟩⟩
        have := h (by simpa [Real.dist_eq] using hu)
        rw [Real.dist_eq] at this
        have := (abs_lt.1 this).2
        linarith
      · obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 hcont (mu a b c u₀) (by linarith)
        refine ⟨δ, hδ, fun u hu => ⟨fun h' => absurd h' (by linarith), fun _ => ?_⟩⟩
        have := h (by simpa [Real.dist_eq] using hu)
        rw [Real.dist_eq] at this
        have := (abs_lt.1 this).1
        linarith
    set δ' := min δ π / 2 with hδ'
    have hδ'pos : 0 < δ' := by have := pi_pos; positivity
    have hδ'lt : δ' < π := by
      have := min_le_right δ π
      have := pi_pos
      rw [hδ']; linarith
    have hδ'δ : δ' < δ := by
      have := min_le_left δ π
      rw [hδ']; linarith [lt_min hδ pi_pos]
    -- `D > 0` at `u₀ ± δ'`
    obtain ⟨n, hn⟩ := (hx₀ u₀).1 hD.symm
    have hDpos : ∀ s : ℝ, (s = δ' ∨ s = -δ') → 0 < diffusionD a b c (u₀ + s) := by
      intro s hs
      refine lt_of_le_of_ne (diffusionD_nonneg ha hb hc _) fun h0 => ?_
      obtain ⟨m, hm⟩ := (hx₀ _).1 h0.symm
      have hdiff' : ((m : ℝ) - n) * π = s := by linarith
      have hmn : ((m - n : ℤ) : ℝ) * π = s := by push_cast; exact hdiff'
      rcases hs with rfl | rfl
      · have h1 : (0 : ℝ) < ((m - n : ℤ) : ℝ) := by
          have := mul_pos_iff_of_pos_right pi_pos |>.1 (hmn ▸ hδ'pos)
          exact this
        have h2 : ((m - n : ℤ) : ℝ) < 1 := by
          have : ((m - n : ℤ) : ℝ) * π < 1 * π := by rw [hmn]; linarith
          exact lt_of_mul_lt_mul_right this pi_pos.le
        have h1' : (0 : ℤ) < m - n := by exact_mod_cast h1
        have h2' : m - n < (1 : ℤ) := by exact_mod_cast h2
        omega
      · have h1 : ((m - n : ℤ) : ℝ) < 0 := by
          have : ((m - n : ℤ) : ℝ) * π < 0 * π := by rw [hmn]; linarith
          exact lt_of_mul_lt_mul_right this pi_pos.le
        have h2 : (-1 : ℝ) < ((m - n : ℤ) : ℝ) := by
          have : (-1 : ℝ) * π < ((m - n : ℤ) : ℝ) * π := by rw [hmn]; linarith
          exact lt_of_mul_lt_mul_right this pi_pos.le
        have h1' : m - n < (0 : ℤ) := by exact_mod_cast h1
        have h2' : (-1 : ℤ) < m - n := by exact_mod_cast h2
        omega
    set q : ℝ → ℝ := fun v => diffusionD a b c v * p v with hq
    have hqu₀ : q u₀ = 0 := by simp [hq, hp0]
    have hqnn : ∀ v, 0 ≤ q v := fun v =>
      mul_nonneg (diffusionD_nonneg ha hb hc v) (hp.2.1 v)
    have hqcont : Continuous q := continuous_iff_continuousAt.2 fun v => (hJ' v).continuousAt
    have hqderiv : ∀ v, deriv q v = mu a b c v * p v := fun v => (hJ' v).deriv
    rcases hμ0.lt_or_gt with hneg | hpos
    · -- `µ < 0` to the right of `u₀`: `q` is antitone on `[u₀, u₀ + δ']`
      have hanti : AntitoneOn q (Icc u₀ (u₀ + δ')) := by
        refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hqcont.continuousOn
          (fun v _ => (hJ' v).differentiableAt.differentiableWithinAt) fun v hv => ?_
        rw [interior_Icc] at hv
        rw [hqderiv]
        have hμv : mu a b c v < 0 := (hδμ v (by
          rw [abs_lt]; constructor <;> linarith [hv.1, hv.2])).1 hneg
        exact mul_nonpos_of_nonpos_of_nonneg hμv.le (hp.2.1 v)
      have hle : q (u₀ + δ') ≤ q u₀ :=
        hanti ⟨le_refl _, by linarith⟩ ⟨by linarith, le_refl _⟩ (by linarith)
      have hq1 : q (u₀ + δ') = 0 := le_antisymm (hqu₀ ▸ hle) (hqnn _)
      have hD1 := hDpos δ' (Or.inl rfl)
      have : p (u₀ + δ') = 0 :=
        (mul_eq_zero.mp hq1).resolve_left hD1.ne'
      exact IsAdmissibleDensity.false_of_zero_of_hasDerivAt ha hb hc hp hJ' hD1 this
    · -- `µ > 0` to the left of `u₀`: `q` is monotone on `[u₀ - δ', u₀]`
      have hmono : MonotoneOn q (Icc (u₀ - δ') u₀) := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) hqcont.continuousOn
          (fun v _ => (hJ' v).differentiableAt.differentiableWithinAt) fun v hv => ?_
        rw [interior_Icc] at hv
        rw [hqderiv]
        have hμv : 0 < mu a b c v := (hδμ v (by
          rw [abs_lt]; constructor <;> linarith [hv.1, hv.2])).2 hpos
        exact mul_nonneg hμv.le (hp.2.1 v)
      have hle : q (u₀ - δ') ≤ q u₀ :=
        hmono ⟨le_refl _, by linarith⟩ ⟨by linarith, le_refl _⟩ (by linarith)
      have hq1 : q (u₀ - δ') = 0 := le_antisymm (hqu₀ ▸ hle) (hqnn _)
      have hD1 := hDpos (-δ') (Or.inr rfl)
      rw [← sub_eq_add_neg] at hD1
      have : p (u₀ - δ') = 0 :=
        (mul_eq_zero.mp hq1).resolve_left hD1.ne'
      exact IsAdmissibleDensity.false_of_zero_of_hasDerivAt ha hb hc hp hJ' hD1 this

/-- **Positivity off the lattice of the definition.** If `p` is admissible and `C²` off the lattice
`x + πℤ`, then `p u > 0` for every `u` off that lattice. -/
theorem IsAdmissibleDensity.pos_off_lattice (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) {x : ℝ}
    (hC2 : ContDiffOn ℝ 2 p {u | ∀ n : ℤ, u ≠ x + n * π}) {u : ℝ}
    (hu : ∀ n : ℤ, u ≠ x + n * π) : 0 < p u := by
  refine IsAdmissibleDensity.pos_of_differentiableAt ha hb hc hp ?_
  exact (hC2.differentiableOn (by norm_num)).differentiableAt
    ((isOpen_compl_lattice x).mem_nhds hu)

/-- The zero set of an admissible density is contained in a lattice `x + πℤ`, hence countable. -/
theorem IsAdmissibleDensity.exists_zeroSet_subset (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) :
    ∃ x : ℝ, {u | p u = 0} ⊆ range fun n : ℤ => x + n * π := by
  obtain ⟨-, -, -, -, x, hC2, -⟩ := id hp
  refine ⟨x, fun u hu => ?_⟩
  by_contra hmem
  have hu' : ∀ n : ℤ, u ≠ x + n * π := fun n hn => hmem ⟨n, hn.symm⟩
  have := IsAdmissibleDensity.pos_off_lattice ha hb hc hp hC2 hu'
  exact absurd (show p u = 0 from hu) this.ne'

theorem IsAdmissibleDensity.countable_zeroSet (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) : {u | p u = 0}.Countable := by
  obtain ⟨x, hx⟩ := IsAdmissibleDensity.exists_zeroSet_subset ha hb hc hp
  exact (Set.countable_range _).mono hx

/-- **Positivity almost everywhere.** An admissible density is positive Lebesgue-a.e. -/
theorem IsAdmissibleDensity.ae_pos (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 ≤ a * b)
    {p : ℝ → ℝ} (hp : IsAdmissibleDensity a b c p) : ∀ᵐ u ∂volume, 0 < p u := by
  have hnull : volume {u | p u = 0} = 0 :=
    (IsAdmissibleDensity.countable_zeroSet ha hb hc hp).measure_zero _
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with u hu
  exact lt_of_le_of_ne (hp.2.1 u) fun h => hu h.symm

end ComplexSLE.Internal

end
