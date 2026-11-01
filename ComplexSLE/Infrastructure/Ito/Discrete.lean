/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Ito.Riemann
public import ComplexSLE.Infrastructure.Ito.Progressive
public import ComplexSLE.Infrastructure.Ito.Taylor
public import Mathlib.Probability.Martingale.Basic

/-!
# The discretized Itô expansion (pathwise algebra)

For `X = X₀ + M + ∫A` with `Mⁱ = Mp X A i`, `Nⁱʲ = Mⁱ Mʲ - ∫Qⁱʲ = Np X A Q i j`, and a `C²` function
`F` (with `gF F i = ∂ᵢF`, `HF F i j = ∂ᵢⱼF`), the increment of `F ∘ X` over a time step `[u, v]` is

`F(X_v) - F(X_u) = zTerm + wTerm + taylorRem`,

where `zTerm` is the martingale part (`∑ ∂ᵢF(X_u) ΔMⁱ + ½ ∑ ∂ᵢⱼF(X_u)(ΔNⁱʲ - Mʲ_u ΔMⁱ - Mⁱ_u ΔMʲ)`),
`wTerm` the drift part and `taylorRem` the second-order Taylor remainder (`step_decomposition`).
Summing over the uniform partition of `[s, t]` into `m + 1` pieces gives
`F(X_t) - F(X_s) = zSum + wSum + remSum` (`partition_decomposition`); `wSum` is the deterministic
`driftSum` of `Riemann.lean` along the paths (`wSum_eq_driftSum`).
-/

@[expose] public section

open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ComplexSLE.Infrastructure.Ito

section Defs

variable {Ω : Type*} {n : ℕ}

/-- The martingale part `Mⁱ_t = Xⁱ_t - Xⁱ_0 - ∫₀ᵗ Aⁱ_s ds` of a semimartingale given by its
drift `A`. -/
noncomputable def Mp (X A : ℝ≥0 → Ω → (Fin n → ℝ)) (i : Fin n) (t : ℝ≥0) (ω : Ω) : ℝ :=
  X t ω i - X 0 ω i - pathIntegral (fun s ω => A s ω i) t ω

/-- `Nⁱʲ_t = Mⁱ_t Mʲ_t - ∫₀ᵗ Qⁱʲ_s ds`. -/
noncomputable def Np (X A : ℝ≥0 → Ω → (Fin n → ℝ)) (Q : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Mp X A i t ω * Mp X A j t ω - pathIntegral (fun s ω => Q s ω i j) t ω

/-- The first partial derivative `∂ᵢF`. -/
noncomputable def gF (F : (Fin n → ℝ) → ℝ) (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ F x (Pi.single i 1)

/-- The second partial derivative `∂ᵢⱼF`. -/
noncomputable def HF (F : (Fin n → ℝ) → ℝ) (i j : Fin n) (x : Fin n → ℝ) : ℝ :=
  iteratedFDeriv ℝ 2 F x ![Pi.single i 1, Pi.single j 1]

/-- The drift integrand `∑ ∂ᵢF Aⁱ + ½ ∑ ∂ᵢⱼF Qⁱʲ` of Itô's formula. -/
noncomputable def itoDrift (F : (Fin n → ℝ) → ℝ) (X A : ℝ≥0 → Ω → (Fin n → ℝ))
    (Q : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i, gF F i (X s ω) * A s ω i + (1 / 2) * ∑ i, ∑ j, HF F i j (X s ω) * Q s ω i j

/-- The second-order Taylor remainder of `F` between `x` and `y`. -/
noncomputable def taylorRem (F : (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) : ℝ :=
  F y - F x - ∑ i, (y i - x i) * gF F i x -
    (1 / 2) * ∑ i, ∑ j, (y i - x i) * (y j - x j) * HF F i j x

theorem abs_taylorRem_le {F : (Fin n → ℝ) → ℝ} {B : ℝ} (hF : ContDiff ℝ 2 F)
    (hB : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ B) (x y : Fin n → ℝ) :
    |taylorRem F x y| ≤ (1 / 2) * modulus F ‖y - x‖ * ‖y - x‖ ^ 2 := by
  have := abs_taylor_remainder_le_coord hF hB x (y - x)
  simpa [taylorRem, gF, HF] using this

/-- The step identity: the increment of `F` splits into the martingale part, the drift part and
the Taylor remainder. -/
theorem step_identity (Fx Fy : ℝ) (g : Fin n → ℝ) (H : Fin n → Fin n → ℝ)
    (x y dM dD Mk : Fin n → ℝ) (dN dR : Fin n → Fin n → ℝ) (ρ : ℝ)
    (hxy : ∀ i, y i - x i = dM i + dD i)
    (hdN : ∀ i j, dN i j = Mk i * dM j + Mk j * dM i + dM i * dM j - dR i j)
    (hρ : ρ = Fy - Fx - ∑ i, (y i - x i) * g i -
      (1 / 2) * ∑ i, ∑ j, (y i - x i) * (y j - x j) * H i j) :
    Fy - Fx = (∑ i, g i * dM i +
        (1 / 2) * ∑ i, ∑ j, (H i j * dN i j - H i j * Mk j * dM i - H i j * Mk i * dM j)) +
      (∑ i, g i * dD i + (1 / 2) * ∑ i, ∑ j,
        H i j * (dR i j + dM i * dD j + dM j * dD i + dD i * dD j)) + ρ := by
  have e1 : ∑ i, (y i - x i) * g i = ∑ i, g i * dM i + ∑ i, g i * dD i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hxy i]; ring
  have e2 : ∑ i, ∑ j, (y i - x i) * (y j - x j) * H i j =
      ∑ i, ∑ j, (H i j * dN i j - H i j * Mk j * dM i - H i j * Mk i * dM j) +
        ∑ i, ∑ j, H i j * (dR i j + dM i * dD j + dM j * dD i + dD i * dD j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hxy i, hxy j, hdN i j]
    ring
  rw [hρ, e1, e2]
  ring

end Defs

/-! ### The one-step decomposition -/

section Step

variable {Ω : Type*} {n : ℕ} (F : (Fin n → ℝ) → ℝ) (X A : ℝ≥0 → Ω → (Fin n → ℝ))
  (Q : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)

/-- The martingale part of the one-step expansion between times `u` and `v`. -/
noncomputable def zTerm (u v : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i, gF F i (X u ω) * (Mp X A i v ω - Mp X A i u ω) +
    (1 / 2) * ∑ i, ∑ j,
      (HF F i j (X u ω) * (Np X A Q i j v ω - Np X A Q i j u ω) -
        HF F i j (X u ω) * Mp X A j u ω * (Mp X A i v ω - Mp X A i u ω) -
        HF F i j (X u ω) * Mp X A i u ω * (Mp X A j v ω - Mp X A j u ω))

/-- The drift part of the one-step expansion between times `u` and `v`. -/
noncomputable def wTerm (u v : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i, gF F i (X u ω) * (∫ x in (u : ℝ)..(v : ℝ), A x.toNNReal ω i) +
    (1 / 2) * ∑ i, ∑ j, HF F i j (X u ω) *
      ((∫ x in (u : ℝ)..(v : ℝ), Q x.toNNReal ω i j) +
        (Mp X A i v ω - Mp X A i u ω) * (∫ x in (u : ℝ)..(v : ℝ), A x.toNNReal ω j) +
        (Mp X A j v ω - Mp X A j u ω) * (∫ x in (u : ℝ)..(v : ℝ), A x.toNNReal ω i) +
        (∫ x in (u : ℝ)..(v : ℝ), A x.toNNReal ω i) * ∫ x in (u : ℝ)..(v : ℝ), A x.toNNReal ω j)

variable {F X A Q}

theorem step_decomposition {ω : Ω}
    (hA : ∀ i (u : ℝ≥0), IntervalIntegrable (fun x : ℝ => A x.toNNReal ω i) volume 0 u)
    (hQ : ∀ i j (u : ℝ≥0), IntervalIntegrable (fun x : ℝ => Q x.toNNReal ω i j) volume 0 u)
    (u v : ℝ≥0) :
    F (X v ω) - F (X u ω) =
      zTerm F X A Q u v ω + wTerm F X A Q u v ω + taylorRem F (X u ω) (X v ω) := by
  have hdA : ∀ i, pathIntegral (fun s ω => A s ω i) v ω - pathIntegral (fun s ω => A s ω i) u ω =
      ∫ x in (u : ℝ)..(v : ℝ), A x.toNNReal ω i := fun i => pathIntegral_sub_eq (hA i) u v
  have hdQ : ∀ i j, pathIntegral (fun s ω => Q s ω i j) v ω -
      pathIntegral (fun s ω => Q s ω i j) u ω = ∫ x in (u : ℝ)..(v : ℝ), Q x.toNNReal ω i j :=
    fun i j => pathIntegral_sub_eq (hQ i j) u v
  refine step_identity (F (X u ω)) (F (X v ω)) (fun i => gF F i (X u ω))
    (fun i j => HF F i j (X u ω)) (X u ω) (X v ω)
    (fun i => Mp X A i v ω - Mp X A i u ω)
    (fun i => ∫ x in (u : ℝ)..(v : ℝ), A x.toNNReal ω i) (fun i => Mp X A i u ω)
    (fun i j => Np X A Q i j v ω - Np X A Q i j u ω)
    (fun i j => ∫ x in (u : ℝ)..(v : ℝ), Q x.toNNReal ω i j) _ ?_ ?_ rfl
  · intro i
    simp only [Mp]
    rw [← hdA i]
    ring
  · intro i j
    simp only [Np, Mp]
    rw [← hdQ i j]
    ring

end Step

/-! ### The decomposition along a partition -/

section Partition

variable {Ω : Type*} {n : ℕ} (F : (Fin n → ℝ) → ℝ) (X A : ℝ≥0 → Ω → (Fin n → ℝ))
  (Q : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)

/-- The martingale part `Z` of the discretized expansion. -/
noncomputable def zSum (s t : ℝ≥0) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), zTerm F X A Q (pt s t m k) (pt s t m (k + 1)) ω

/-- The drift part `W'` of the discretized expansion. -/
noncomputable def wSum (s t : ℝ≥0) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), wTerm F X A Q (pt s t m k) (pt s t m (k + 1)) ω

/-- The sum of the second-order Taylor remainders. -/
noncomputable def remSum (s t : ℝ≥0) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), taylorRem F (X (pt s t m k) ω) (X (pt s t m (k + 1)) ω)

variable {F X A Q}

theorem partition_decomposition {ω : Ω}
    (hA : ∀ i (u : ℝ≥0), IntervalIntegrable (fun x : ℝ => A x.toNNReal ω i) volume 0 u)
    (hQ : ∀ i j (u : ℝ≥0), IntervalIntegrable (fun x : ℝ => Q x.toNNReal ω i j) volume 0 u)
    {s t : ℝ≥0} (m : ℕ) :
    F (X t ω) - F (X s ω) = zSum F X A Q s t m ω + wSum F X A Q s t m ω + remSum F X s t m ω := by
  have h1 : F (X t ω) - F (X s ω) = ∑ k ∈ Finset.range (m + 1),
      (F (X (pt s t m (k + 1)) ω) - F (X (pt s t m k) ω)) := by
    rw [Finset.sum_range_sub (fun k => F (X (pt s t m k) ω)), pt_last, pt_zero]
  rw [h1, zSum, wSum, remSum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => step_decomposition hA hQ _ _

theorem sum_range_sum_sum_comm {N : ℕ} (b : ℕ → Fin n → Fin n → ℝ) :
    ∑ k ∈ Finset.range N, ∑ i, ∑ j, b k i j = ∑ i, ∑ j, ∑ k ∈ Finset.range N, b k i j := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem wSum_eq_driftSum {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) (ω : Ω) :
    wSum F X A Q s t m ω = driftSum (s : ℝ) (t : ℝ) m
      (fun i u => gF F i (X u.toNNReal ω)) (fun i j u => HF F i j (X u.toNNReal ω))
      (fun i u => A u.toNNReal ω i) (fun i j u => Q u.toNNReal ω i j)
      (fun i u => Mp X A i u.toNNReal ω) := by
  unfold wSum driftSum
  have hterm : ∀ k ∈ Finset.range (m + 1), wTerm F X A Q (pt s t m k) (pt s t m (k + 1)) ω =
      ∑ i, gF F i (X (pt s t m k) ω) *
        pieceInt (fun u => A u.toNNReal ω i) (s : ℝ) (t : ℝ) m k +
      (1 / 2) * ∑ i, ∑ j, HF F i j (X (pt s t m k) ω) *
        (pieceInt (fun u => Q u.toNNReal ω i j) (s : ℝ) (t : ℝ) m k +
          (Mp X A i (pt s t m (k + 1)) ω - Mp X A i (pt s t m k) ω) *
            pieceInt (fun u => A u.toNNReal ω j) (s : ℝ) (t : ℝ) m k +
          (Mp X A j (pt s t m (k + 1)) ω - Mp X A j (pt s t m k) ω) *
            pieceInt (fun u => A u.toNNReal ω i) (s : ℝ) (t : ℝ) m k +
          pieceInt (fun u => A u.toNNReal ω i) (s : ℝ) (t : ℝ) m k *
            pieceInt (fun u => A u.toNNReal ω j) (s : ℝ) (t : ℝ) m k) := by
    intro k hk
    have hk' : k + 1 ≤ m + 1 := Nat.succ_le_succ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
    have hk'' : k ≤ m + 1 := (Nat.le_succ k).trans hk'
    simp only [wTerm, pieceInt, coe_pt hst m hk', coe_pt hst m hk'']
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_comm, sum_range_sum_sum_comm]
  rfl

end Partition

end ComplexSLE.Infrastructure.Ito

end
