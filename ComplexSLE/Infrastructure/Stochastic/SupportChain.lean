/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Gaussian.SupportBall
public import ComplexSLE.Infrastructure.Stochastic.IndepProductBound
public import ComplexSLE.Infrastructure.Stochastic.RationalOscillation

/-!
# Chaining for the support theorem of a planar Gaussian process

Source-independent probability. Let `U : ℝ≥0 → Ω → ℂ` be a process with measurable coordinates,
almost surely continuous paths, `U 0 = 0` almost surely, restarted paths independent of the past at
every deterministic time, and increments `U t - U s ∼ N (0, (t - s) S)` for a positive semidefinite
real `2 × 2` matrix `S` (`MeasurableDriver`).

Fix a grid of mesh `h` (rational), a target sequence `ψ`, and tolerances `ε`, `r`. A path `u` is
*good for `k` steps* (`ChainParam.Good`) if `u 0 = 0` and, at every grid time `j h` with `j < k`,
the increment path `f = u (· + j h) - u (j h)` satisfies `ChainParam.StepCond`:

* `f h` is within `√h` of `w_j - θ x_j`, where `x_j = u (j h) - ψ j` is the offset to the target,
  `w_j = ψ (j + 1) - ψ j` the prescribed drift and `θ = 4 √h / ε`;
* `f h` lies in the range of `S`;
* `‖f q‖ ≤ r` at all rational times `q ≤ h`.

Main results.

* `ChainParam.invariant`: on good paths, `x_j` lies in the range of `S` and `‖x_j‖ < ε / 4`.
* `ChainParam.chain_bound`: `P (good for n steps) ≥ (q₀ / 2) ^ n` (where `q₀` is the scale-invariant
  Gaussian ball lower bound and the oscillation event has probability at most `q₀ / 2`). The
  conditional probability of each step given the past is bounded below by Fubini
  (`mul_measure_le_of_indepFun`), applied to the path of the process frozen at the grid time and the
  restarted path.
* `ChainParam.good_close`: a continuous good path stays within `ε / 4 + r + b` of the target.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ComplexSLE.Infrastructure.Support

open ComplexSLE.Infrastructure.SupportGaussian

/-- Parameters of the chaining argument. -/
structure ChainParam where
  S : Matrix (Fin 2) (Fin 2) ℝ
  h : ℚ≥0
  ε : ℝ
  r : ℝ
  ψ : ℕ → ℂ

namespace ChainParam

variable (c : ChainParam)

/-- The mesh as a time. -/
def mesh : ℝ≥0 := (c.h : ℝ≥0)

/-- The square root of the mesh. -/
noncomputable def sq : ℝ := Real.sqrt (c.mesh : ℝ)

/-- The pull-back coefficient. -/
noncomputable def θ : ℝ := 4 * c.sq / c.ε

/-- The grid times `j h`. -/
def time (j : ℕ) : ℝ≥0 := (((j : ℚ≥0) * c.h : ℚ≥0) : ℝ≥0)

/-- The prescribed increments of the target. -/
def drift (j : ℕ) : ℂ := c.ψ (j + 1) - c.ψ j

/-- One step: the increment path `f` of the process after a grid time moves the offset `x` into
the ball of radius `ε / 4`, in the range of `S`, with small oscillation. -/
def StepCond (w x : ℂ) (f : ℝ≥0 → ℂ) : Prop :=
  ‖f c.mesh - (w - (c.θ : ℂ) * x)‖ < c.sq ∧ f c.mesh ∈ covRange c.S ∧
    ∀ q : ℚ≥0, (q : ℝ≥0) ≤ c.mesh → ‖f q‖ ≤ c.r

/-- A path is good for `k` steps. -/
def Good (k : ℕ) (u : ℝ≥0 → ℂ) : Prop :=
  u 0 = 0 ∧ ∀ j < k, c.StepCond (c.drift j) (u (c.time j) - c.ψ j)
    (fun s => u (s + c.time j) - u (c.time j))

theorem time_zero : c.time 0 = 0 := by simp [time]

theorem time_succ (j : ℕ) : c.time (j + 1) = c.mesh + c.time j := by
  simp only [time, mesh]
  push_cast
  ring

theorem good_succ (k : ℕ) (u : ℝ≥0 → ℂ) :
    c.Good (k + 1) u ↔ c.Good k u ∧ c.StepCond (c.drift k) (u (c.time k) - c.ψ k)
      (fun s => u (s + c.time k) - u (c.time k)) := by
  unfold Good
  rw [Nat.forall_lt_succ_right]
  tauto

theorem good_zero (u : ℝ≥0 → ℂ) : c.Good 0 u ↔ u 0 = 0 := by simp [Good]

theorem theta_mul (hε : 0 < c.ε) : c.θ * c.ε = 4 * c.sq := by
  unfold θ; field_simp

/-- **Invariant.** On good paths the offset to the target stays in the range of `S` and in the ball
of radius `ε / 4`. -/
theorem invariant (hε : 0 < c.ε) (hθ : c.θ ≤ 1) (hψ0 : c.ψ 0 = 0)
    (hdrift : ∀ j, c.drift j ∈ covRange c.S) {k : ℕ} {u : ℝ≥0 → ℂ}
    (hu : c.Good k u) : ∀ j ≤ k, (u (c.time j) - c.ψ j ∈ covRange c.S ∧
      ‖u (c.time j) - c.ψ j‖ < c.ε / 4) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp [time_zero, hu.1, hψ0, hε]
  | succ j ih =>
    intro hj
    obtain ⟨hR, hn⟩ := ih (by omega)
    obtain ⟨h1, h2, h3⟩ := hu.2 j (by omega)
    set x := u (c.time j) - c.ψ j with hx
    set Y := u (c.mesh + c.time j) - u (c.time j) with hY
    have hrel : u (c.time (j + 1)) - c.ψ (j + 1) = x + Y - c.drift j := by
      rw [time_succ, hx, hY, drift]; ring
    have h1' : ‖Y - (c.drift j - (c.θ : ℂ) * x)‖ < c.sq := by simpa [hY] using h1
    refine ⟨?_, ?_⟩
    · rw [hrel]
      refine Submodule.sub_mem _ (Submodule.add_mem _ hR ?_) (hdrift j)
      simpa [hY] using h2
    · rw [hrel]
      have e : x + Y - c.drift j = ((1 - c.θ : ℝ) : ℂ) * x + (Y - (c.drift j - (c.θ : ℂ) * x)) := by
        push_cast; ring
      rw [e]
      calc ‖((1 - c.θ : ℝ) : ℂ) * x + (Y - (c.drift j - (c.θ : ℂ) * x))‖
          ≤ ‖((1 - c.θ : ℝ) : ℂ) * x‖ + ‖Y - (c.drift j - (c.θ : ℂ) * x)‖ := norm_add_le _ _
        _ < (1 - c.θ) * (c.ε / 4) + c.sq := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
            have : (1 - c.θ) * ‖x‖ ≤ (1 - c.θ) * (c.ε / 4) :=
              mul_le_mul_of_nonneg_left hn.le (by linarith)
            linarith
        _ = c.ε / 4 := by
            have := c.theta_mul hε
            nlinarith

/-! ### Measurability -/

theorem measurable_shiftPath (t : ℝ≥0) :
    Measurable (fun u : ℝ≥0 → ℂ => fun s => u (s + t) - u t) :=
  measurable_pi_iff.2 fun _ => (measurable_pi_apply _).sub (measurable_pi_apply _)

/-- The set of pairs `(past path, increment path)` satisfying the step condition at grid time
`j`. -/
def stepSet (j : ℕ) : Set ((ℝ≥0 → ℂ) × (ℝ≥0 → ℂ)) :=
  {z | c.StepCond (c.drift j) (z.1 (c.time j) - c.ψ j) z.2}

theorem measurableSet_stepSet (j : ℕ) : MeasurableSet (c.stepSet j) := by
  have hf : ∀ s : ℝ≥0, Measurable fun z : (ℝ≥0 → ℂ) × (ℝ≥0 → ℂ) => z.2 s := fun s =>
    (measurable_pi_apply s).comp measurable_snd
  have hg : ∀ s : ℝ≥0, Measurable fun z : (ℝ≥0 → ℂ) × (ℝ≥0 → ℂ) => z.1 s := fun s =>
    (measurable_pi_apply s).comp measurable_fst
  have e : c.stepSet j = {z | ‖z.2 c.mesh - (c.drift j - (c.θ : ℂ) * (z.1 (c.time j) - c.ψ j))‖ <
        c.sq} ∩ ({z | z.2 c.mesh ∈ covRange c.S} ∩ ⋂ q : ℚ≥0,
      {z | (q : ℝ≥0) ≤ c.mesh → ‖z.2 q‖ ≤ c.r}) := by
    ext z
    simp [stepSet, StepCond]
  rw [e]
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.iInter fun q => ?_))
  · exact measurableSet_lt (((hf _).sub (measurable_const.sub
      (measurable_const.mul ((hg _).sub measurable_const)))).norm) measurable_const
  · exact (isClosed_covRange c.S).measurableSet.preimage (hf _)
  · by_cases hq : (q : ℝ≥0) ≤ c.mesh
    · simp only [hq, true_implies]
      exact measurableSet_le (hf _).norm measurable_const
    · simp [hq]

theorem measurableSet_good (k : ℕ) : MeasurableSet {u : ℝ≥0 → ℂ | c.Good k u} := by
  have e : {u : ℝ≥0 → ℂ | c.Good k u} = {u | u 0 = 0} ∩ ⋂ j : ℕ, ⋂ (_ : j < k),
      (fun u : ℝ≥0 → ℂ => (u, fun s => u (s + c.time j) - u (c.time j))) ⁻¹' (c.stepSet j) := by
    ext u
    simp [Good, stepSet]
  rw [e]
  refine MeasurableSet.inter ?_ (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_)
  · exact measurableSet_eq_fun (measurable_pi_apply 0) measurable_const
  · exact (measurable_id.prodMk (measurable_shiftPath _)) (c.measurableSet_stepSet j)

/-! ### Dependence on the path up to time `k h` only -/

theorem time_mono {j k : ℕ} (hjk : j ≤ k) : c.time j ≤ c.time k := by
  simp only [time]
  exact_mod_cast mul_le_mul_of_nonneg_right (by exact_mod_cast hjk) zero_le

theorem stepCond_congr {w x : ℂ} {f g : ℝ≥0 → ℂ} (h : ∀ s ≤ c.mesh, f s = g s) :
    c.StepCond w x f ↔ c.StepCond w x g := by
  unfold StepCond
  have h0 : f c.mesh = g c.mesh := h _ le_rfl
  have h1 : ∀ q : ℚ≥0, (q : ℝ≥0) ≤ c.mesh → f q = g q := fun q hq => h _ hq
  rw [h0]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun q => imp_congr_right fun hq => ?_))
  rw [h1 q hq]

theorem good_congr {k : ℕ} {u v : ℝ≥0 → ℂ} (h : ∀ s ≤ c.time k, u s = v s) :
    c.Good k u ↔ c.Good k v := by
  unfold Good
  have h0 : u 0 = v 0 := h 0 zero_le
  refine and_congr (by rw [h0]) (forall_congr' fun j => imp_congr_right fun hj => ?_)
  have hj1 : c.time (j + 1) ≤ c.time k := c.time_mono hj
  have hj0 : c.time j ≤ c.time k := c.time_mono (by omega)
  have e0 : u (c.time j) = v (c.time j) := h _ hj0
  rw [e0]
  refine c.stepCond_congr fun s hs => ?_
  have : s + c.time j ≤ c.time k := by
    calc s + c.time j ≤ c.mesh + c.time j := by gcongr
      _ = c.time (j + 1) := (c.time_succ j).symm
      _ ≤ c.time k := hj1
  simp only [h _ this]

end ChainParam

/-! ### The process -/

/-- A process with measurable coordinates, almost surely continuous with `U 0 = 0` almost surely,
whose restarted paths are independent of the past, and whose increments have the laws
`N (0, (t - s) S)`. -/
structure MeasurableDriver {Ω : Type*} [MeasurableSpace Ω] (S : Matrix (Fin 2) (Fin 2) ℝ)
    (U : ℝ≥0 → Ω → ℂ) (P : Measure Ω) : Prop where
  measurable : ∀ s, Measurable (U s)
  zero : ∀ᵐ ω ∂P, U 0 ω = 0
  cont : ∀ᵐ ω ∂P, Continuous fun t => U t ω
  indep : ∀ t : ℝ≥0, IndepFun (fun ω (s : ℝ≥0) => U (s + t) ω - U t ω)
    (fun ω (r : Set.Iic t) => U (r : ℝ≥0) ω) P
  law : ∀ s t : ℝ≥0, s ≤ t →
    P.map (fun ω => U t ω - U s ω) = ComplexSLE.complexGaussian (((t : ℝ) - s) • S)

namespace ChainParam

variable (c : ChainParam) {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {U : ℝ≥0 → Ω → ℂ}

/-- **One step, conditional probability.** -/
theorem condProb_ge [IsProbabilityMeasure P] (hU : MeasurableDriver c.S U P)
    (hS : c.S.PosSemidef) (hh : 0 < c.h) {q₀ : ℝ≥0∞}
    (hq₀ : ∀ t : ℝ, 0 < t → ∀ y ∈ covRange c.S, ‖y‖ ≤ 2 * Real.sqrt t →
      q₀ ≤ ComplexSLE.complexGaussian (t • c.S) (Metric.ball y (Real.sqrt t)))
    {N : ℝ≥0} (k : ℕ) (hk : c.time k + c.mesh ≤ N)
    (hosc : P (oscSet U N c.mesh c.r) ≤ q₀ / 2) {L : ℝ} (hL : c.sq * L ≤ 1)
    (hε : 0 < c.ε) (hdriftR : c.drift k ∈ covRange c.S) (hdriftL : ‖c.drift k‖ ≤ L * c.mesh)
    {x : ℂ} (hxR : x ∈ covRange c.S) (hxn : ‖x‖ < c.ε / 4) :
    q₀ / 2 ≤ P {ω | c.StepCond (c.drift k) x (fun s => U (s + c.time k) ω - U (c.time k) ω)} := by
  have hmesh : (0 : ℝ) < (c.mesh : ℝ) := by
    simp only [mesh]; exact_mod_cast (by exact_mod_cast hh : (0 : ℝ≥0) < (c.h : ℝ≥0))
  have hsq : 0 < c.sq := Real.sqrt_pos.2 hmesh
  have hsq2 : c.sq * c.sq = (c.mesh : ℝ) := Real.mul_self_sqrt hmesh.le
  set t := c.time k with ht
  set y : ℂ := c.drift k - (c.θ : ℂ) * x with hy
  set X : Ω → ℂ := fun ω => U (c.mesh + t) ω - U t ω with hX
  have hXm : Measurable X := (hU.measurable _).sub (hU.measurable _)
  have hlawX : P.map X = ComplexSLE.complexGaussian ((c.mesh : ℝ) • c.S) := by
    have := hU.law t (c.mesh + t) (by simp)
    rw [show ((c.mesh + t : ℝ≥0) : ℝ) - (t : ℝ) = (c.mesh : ℝ) by push_cast; ring] at this
    exact this
  have hyR : y ∈ covRange c.S := Submodule.sub_mem _ hdriftR (by
    have := (covRange c.S).smul_mem c.θ hxR
    simpa [Complex.real_smul] using this)
  have hyn : ‖y‖ ≤ 2 * Real.sqrt (c.mesh : ℝ) := by
    have h1 : ‖y‖ ≤ ‖c.drift k‖ + c.θ * ‖x‖ := by
      calc ‖y‖ ≤ ‖c.drift k‖ + ‖(c.θ : ℂ) * x‖ := norm_sub_le _ _
        _ = ‖c.drift k‖ + |c.θ| * ‖x‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ _ := by
          have : 0 ≤ c.θ := by unfold ChainParam.θ; positivity
          rw [abs_of_nonneg this]
    have h2 : c.θ * ‖x‖ ≤ c.sq := by
      have := c.theta_mul hε
      have h3 : c.θ * ‖x‖ ≤ c.θ * (c.ε / 4) :=
        mul_le_mul_of_nonneg_left hxn.le (by unfold ChainParam.θ; positivity)
      nlinarith
    have h4 : ‖c.drift k‖ ≤ c.sq := by
      calc ‖c.drift k‖ ≤ L * c.mesh := hdriftL
        _ = (c.sq * L) * c.sq := by rw [← hsq2]; ring
        _ ≤ 1 * c.sq := by gcongr
        _ = c.sq := one_mul _
    unfold ChainParam.sq at h4 h2
    linarith
  -- the three events
  have hB1 : q₀ ≤ P {ω | ‖X ω - y‖ < c.sq} := by
    have : {ω | ‖X ω - y‖ < c.sq} = X ⁻¹' Metric.ball y (Real.sqrt (c.mesh : ℝ)) := by
      ext ω; simp [Metric.mem_ball, dist_eq_norm, ChainParam.sq]
    rw [this, ← Measure.map_apply hXm Metric.isOpen_ball.measurableSet, hlawX]
    exact hq₀ _ hmesh y hyR hyn
  have hB2 : P {ω | X ω ∉ covRange c.S} = 0 := by
    have : {ω | X ω ∉ covRange c.S} = X ⁻¹' ((covRange c.S : Set ℂ)ᶜ) := by
      ext ω; simp
    rw [this, ← Measure.map_apply hXm (isClosed_covRange c.S).isOpen_compl.measurableSet, hlawX]
    exact complexGaussian_compl_covRange hS hmesh.le
  have hB3 : {ω | ¬ ∀ q : ℚ≥0, (q : ℝ≥0) ≤ c.mesh → ‖U (q + t) ω - U t ω‖ ≤ c.r} ⊆
      oscSet U N c.mesh c.r := by
    intro ω hω
    simp only [not_forall, not_le] at hω
    obtain ⟨q, hq, hlt⟩ := hω
    have ht' : t = (k : ℝ≥0) * (c.h : ℝ≥0) := by simp [ht, time]
    simp only [oscSet, mem_iUnion]
    refine ⟨q + (k : ℚ≥0) * c.h, (k : ℚ≥0) * c.h, ?_⟩
    push_cast
    rw [← ht']
    have hmesh' : c.mesh = (c.h : ℝ≥0) := rfl
    have hq' : (q : ℝ≥0) ≤ (c.h : ℝ≥0) := hq
    refine ⟨?_, ?_, ?_, ?_, hlt⟩
    · calc (q : ℝ≥0) + t ≤ c.mesh + t := by gcongr
        _ = c.time k + c.mesh := add_comm _ _
        _ ≤ N := hk
    · calc t ≤ c.time k + c.mesh := le_self_add
        _ ≤ N := hk
    · calc (q : ℝ≥0) + t ≤ c.mesh + t := by gcongr
        _ = t + c.mesh := add_comm _ _
    · rw [add_assoc]; exact le_self_add.trans le_add_self
  have hsub : {ω | ‖X ω - y‖ < c.sq} ⊆
      ({ω | c.StepCond (c.drift k) x (fun s => U (s + t) ω - U t ω)} ∪
        {ω | X ω ∉ covRange c.S}) ∪ oscSet U N c.mesh c.r := by
    intro ω hω
    by_cases h2 : X ω ∈ covRange c.S
    · by_cases h3 : ∀ q : ℚ≥0, (q : ℝ≥0) ≤ c.mesh → ‖U (q + t) ω - U t ω‖ ≤ c.r
      · exact Or.inl (Or.inl ⟨hω, h2, h3⟩)
      · exact Or.inr (hB3 h3)
    · exact Or.inl (Or.inr h2)
  have h1 : q₀ ≤ P {ω | c.StepCond (c.drift k) x (fun s => U (s + t) ω - U t ω)} + q₀ / 2 := by
    calc q₀ ≤ P {ω | ‖X ω - y‖ < c.sq} := hB1
      _ ≤ P (({ω | c.StepCond (c.drift k) x (fun s => U (s + t) ω - U t ω)} ∪
          {ω | X ω ∉ covRange c.S}) ∪ oscSet U N c.mesh c.r) := measure_mono hsub
      _ ≤ P ({ω | c.StepCond (c.drift k) x (fun s => U (s + t) ω - U t ω)} ∪
          {ω | X ω ∉ covRange c.S}) + P (oscSet U N c.mesh c.r) := measure_union_le _ _
      _ ≤ (P {ω | c.StepCond (c.drift k) x (fun s => U (s + t) ω - U t ω)} +
          P {ω | X ω ∉ covRange c.S}) + P (oscSet U N c.mesh c.r) := by
          gcongr; exact measure_union_le _ _
      _ ≤ P {ω | c.StepCond (c.drift k) x (fun s => U (s + t) ω - U t ω)} + q₀ / 2 := by
          rw [hB2, add_zero]; gcongr
  have hq₀top : q₀ ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top P _) hB1
  have hhalf : q₀ / 2 ≠ ∞ := ENNReal.div_ne_top hq₀top (by norm_num)
  refine ENNReal.le_of_add_le_add_right hhalf ?_
  rwa [ENNReal.add_halves]

/-- **One step of the chain.** -/
theorem step_bound [IsProbabilityMeasure P] (hU : MeasurableDriver c.S U P)
    (hS : c.S.PosSemidef) (hh : 0 < c.h) {q₀ : ℝ≥0∞}
    (hq₀ : ∀ t : ℝ, 0 < t → ∀ y ∈ covRange c.S, ‖y‖ ≤ 2 * Real.sqrt t →
      q₀ ≤ ComplexSLE.complexGaussian (t • c.S) (Metric.ball y (Real.sqrt t)))
    {N : ℝ≥0} (k : ℕ) (hk : c.time k + c.mesh ≤ N)
    (hosc : P (oscSet U N c.mesh c.r) ≤ q₀ / 2) {L : ℝ} (hL : c.sq * L ≤ 1)
    (hε : 0 < c.ε) (hθ : c.θ ≤ 1) (hψ0 : c.ψ 0 = 0) (hdriftR : ∀ j, c.drift j ∈ covRange c.S)
    (hdriftL : ∀ j, ‖c.drift j‖ ≤ L * c.mesh) :
    q₀ / 2 * P {ω | c.Good k (fun s => U s ω)} ≤ P {ω | c.Good (k + 1) (fun s => U s ω)} := by
  set t := c.time k with ht
  let Φ : (Set.Iic t → ℂ) → (ℝ≥0 → ℂ) := fun p s => p ⟨min s t, (min_le_right s t : min s t ≤ t)⟩
  have hΦ : Measurable Φ := measurable_pi_iff.2 fun s => measurable_pi_apply _
  have hind : IndepFun (fun ω s => U (min s t) ω) (fun ω s => U (s + t) ω - U t ω) P :=
    (hU.indep t).symm.comp hΦ measurable_id
  have hFr : Measurable fun ω s => U (min s t) ω :=
    measurable_pi_iff.2 fun s => hU.measurable _
  have hY : Measurable fun ω s => U (s + t) ω - U t ω :=
    measurable_pi_iff.2 fun s => (hU.measurable _).sub (hU.measurable _)
  have hq : ∀ a ∈ {u : ℝ≥0 → ℂ | c.Good k u}, q₀ / 2 ≤
      P ((fun ω s => U (s + t) ω - U t ω) ⁻¹' {b | (a, b) ∈ c.stepSet k}) := by
    intro a ha
    obtain ⟨hR, hn⟩ := c.invariant hε hθ hψ0 hdriftR ha k le_rfl
    have := c.condProb_ge hU hS hh hq₀ k hk hosc hL hε (hdriftR k) (hdriftL k) hR hn
    exact this
  have key := mul_measure_le_of_indepFun hFr hY hind (c.measurableSet_stepSet k)
    (c.measurableSet_good k) hq
  have e1 : (fun ω s => U (min s t) ω) ⁻¹' {u | c.Good k u} =
      {ω | c.Good k (fun s => U s ω)} := by
    ext ω
    change c.Good k (fun s => U (min s t) ω) ↔ c.Good k (fun s => U s ω)
    exact c.good_congr fun s hs => by show U (min s t) ω = U s ω; rw [min_eq_left hs]
  have e2 : {ω | (fun s => U (min s t) ω) ∈ {u | c.Good k u} ∧
      ((fun s => U (min s t) ω), (fun s => U (s + t) ω - U t ω)) ∈ c.stepSet k} =
      {ω | c.Good (k + 1) (fun s => U s ω)} := by
    ext ω
    change (c.Good k (fun s => U (min s t) ω) ∧ c.StepCond (c.drift k)
        (U (min t t) ω - c.ψ k) (fun s => U (s + t) ω - U t ω)) ↔ c.Good (k + 1) (fun s => U s ω)
    rw [c.good_succ, min_self]
    refine and_congr ?_ Iff.rfl
    exact c.good_congr fun s hs => by show U (min s t) ω = U s ω; rw [min_eq_left hs]
  rwa [e1, e2] at key

theorem time_eq (n : ℕ) : c.time n = (n : ℝ≥0) * c.mesh := by
  simp [time, mesh]

/-- **Good paths track the target.** -/
theorem good_close (hε : 0 < c.ε) (hθ : c.θ ≤ 1) (hψ0 : c.ψ 0 = 0)
    (hdriftR : ∀ j, c.drift j ∈ covRange c.S) (hh : 0 < c.h) {n : ℕ} {u : ℝ≥0 → ℂ}
    (hu : c.Good n u) (hcont : Continuous u) {φ : ℝ≥0 → ℂ} {b : ℝ} {T : ℝ≥0}
    (hTn : T < c.time n)
    (hφ : ∀ j < n, ∀ t, c.time j ≤ t → t ≤ c.time (j + 1) → ‖c.ψ j - φ t‖ ≤ b) :
    ∀ t ≤ T, ‖u t - φ t‖ < c.ε / 4 + c.r + b := by
  intro t ht
  have hmesh : (0 : ℝ≥0) < c.mesh := by
    simp only [mesh]; exact_mod_cast hh
  set j := ⌊t / c.mesh⌋₊ with hj
  have hjn : j < n := by
    rw [hj, Nat.floor_lt zero_le, div_lt_iff₀ hmesh]
    calc t ≤ T := ht
      _ < c.time n := hTn
      _ = (n : ℝ≥0) * c.mesh := c.time_eq n
  have hj1 : c.time j ≤ t := by
    rw [time_eq]
    have := Nat.floor_le (zero_le : 0 ≤ t / c.mesh)
    rwa [le_div_iff₀ hmesh] at this
  have hj2 : t ≤ c.time (j + 1) := by
    rw [time_eq]
    have := Nat.lt_floor_add_one (t / c.mesh)
    rw [div_lt_iff₀ hmesh] at this
    push_cast
    exact this.le
  have hs : t - c.time j ≤ c.mesh := by
    rw [tsub_le_iff_right]
    calc t ≤ c.time (j + 1) := hj2
      _ = c.mesh + c.time j := c.time_succ j
  have hts : t = (t - c.time j) + c.time j := (tsub_add_cancel_of_le hj1).symm
  obtain ⟨_, _, h3⟩ := hu.2 j hjn
  have hosc := le_of_forall_nnrat_le
    (f := fun s => ‖u (s + c.time j) - u (c.time j)‖)
    (by have := hcont; fun_prop) (h := c.mesh) (c := c.r) (fun q hq => h3 q hq) _ hs
  rw [← hts] at hosc
  obtain ⟨_, hinv⟩ := c.invariant hε hθ hψ0 hdriftR hu j hjn.le
  have hb := hφ j hjn t hj1 hj2
  calc ‖u t - φ t‖ = ‖(u t - u (c.time j)) + (u (c.time j) - c.ψ j) + (c.ψ j - φ t)‖ := by
        ring_nf
    _ ≤ ‖u t - u (c.time j)‖ + ‖u (c.time j) - c.ψ j‖ + ‖c.ψ j - φ t‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ < c.ε / 4 + c.r + b := by linarith

/-- **The chain.** The probability of being good for `n` steps is at least `(q₀ / 2) ^ n`. -/
theorem chain_bound [IsProbabilityMeasure P] (hU : MeasurableDriver c.S U P)
    (hS : c.S.PosSemidef) (hh : 0 < c.h) {q₀ : ℝ≥0∞}
    (hq₀ : ∀ t : ℝ, 0 < t → ∀ y ∈ covRange c.S, ‖y‖ ≤ 2 * Real.sqrt t →
      q₀ ≤ ComplexSLE.complexGaussian (t • c.S) (Metric.ball y (Real.sqrt t)))
    {N : ℝ≥0} (hosc : P (oscSet U N c.mesh c.r) ≤ q₀ / 2) {L : ℝ} (hL : c.sq * L ≤ 1)
    (hε : 0 < c.ε) (hθ : c.θ ≤ 1) (hψ0 : c.ψ 0 = 0) (hdriftR : ∀ j, c.drift j ∈ covRange c.S)
    (hdriftL : ∀ j, ‖c.drift j‖ ≤ L * c.mesh) (n : ℕ) (hn : c.time n ≤ N) :
    (q₀ / 2) ^ n ≤ P {ω | c.Good n (fun s => U s ω)} := by
  induction n with
  | zero =>
    have h0 : P {ω | c.Good 0 (fun s => U s ω)} = 1 := by
      have : {ω | c.Good 0 (fun s => U s ω)} = {ω | U 0 ω = 0} := by
        ext ω; exact c.good_zero (fun s => U s ω)
      rw [this]
      have := ae_iff.1 hU.zero
      rw [← prob_compl_eq_zero_iff (measurableSet_eq_fun (hU.measurable 0) measurable_const)]
      exact this
    rw [h0]; simp
  | succ n ih =>
    have hk : c.time n + c.mesh ≤ N := by
      rw [add_comm, ← c.time_succ]; exact hn
    have ih' := ih ((c.time_mono (Nat.le_succ n)).trans hn)
    calc (q₀ / 2) ^ (n + 1) = q₀ / 2 * (q₀ / 2) ^ n := pow_succ' _ _
      _ ≤ q₀ / 2 * P {ω | c.Good n (fun s => U s ω)} := by gcongr
      _ ≤ _ := c.step_bound hU hS hh hq₀ n hk hosc hL hε hθ hψ0 hdriftR hdriftL

end ChainParam

end ComplexSLE.Infrastructure.Support

end
