/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.PeriodicGlue
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Topology.Order.LeftRightNhds

/-!
# Gluing the solution on a period into a `C¹` periodic function

Let `H` solve `H' = ρ - a H` on `(0, T)` with `H 0 = 0`, and `H → 0`, `a H → 0` at both ends of
the period. Then the `T`-periodic extension `K u = H (toIcoMod hT 0 u)` is `C¹` with
`K' = ρ - a K`, provided `a` and `ρ` are `T`-periodic, `ρ` is continuous with `ρ 0 = 0`
(so the derivative extends continuously through the lattice).
-/

public section

open Set Filter Topology Function

namespace ComplexSLE.Infrastructure

theorem exists_periodic_C1_of_bounded_solution {a ρ H : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (haper : Periodic a T) (hcontA : ContinuousOn a (Ioo 0 T)) (hρ : Continuous ρ)
    (hρper : Periodic ρ T) (hρ0 : ρ 0 = 0) (hH0 : H 0 = 0)
    (hHd : ∀ x ∈ Ioo 0 T, HasDerivAt H (ρ x - a x * H x) x)
    (hL1 : Tendsto H (𝓝[>] 0) (𝓝 0)) (hL2 : Tendsto (fun x => a x * H x) (𝓝[>] 0) (𝓝 0))
    (hR1 : Tendsto H (𝓝[<] T) (𝓝 0)) (hR2 : Tendsto (fun x => a x * H x) (𝓝[<] T) (𝓝 0)) :
    ∃ K : ℝ → ℝ, ContDiff ℝ 1 K ∧ Periodic K T ∧ K 0 = 0 ∧
      ∀ u, HasDerivAt K (ρ u - a u * K u) u := by
  set K : ℝ → ℝ := fun u => H (toIcoMod hT 0 u) with hK
  set K' : ℝ → ℝ := fun u => ρ u - a u * K u with hK'
  have hKper : Periodic K T := fun u => by simp only [hK, toIcoMod_add_right]
  have hPself : ∀ u ∈ Ioo 0 T, toIcoMod hT 0 u = u := fun u hu =>
    (toIcoMod_eq_self hT).2 ⟨hu.1.le, by simpa using hu.2⟩
  have hK0 : K 0 = 0 := by simp [hK, hH0]
  have hK'per : Periodic K' T := fun u => by simp only [hK', hρper u, haper u, hKper u]
  have hKR : ∀ u ∈ Ioo 0 T, K u = H u := fun u hu => by simp [hK, hPself u hu]
  have hKL : ∀ u ∈ Ioo (-T) 0, K u = H (u + T) := fun u hu => by
    rw [← hKper u]
    exact hKR _ ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hshift : Tendsto (fun u : ℝ => u + T) (𝓝[<] 0) (𝓝[<] T) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun u : ℝ => u + T) (𝓝 0) (𝓝 (0 + T)) :=
        (continuous_id.add continuous_const).tendsto 0
      rw [zero_add] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact show u + T < T by linarith [show u < 0 from hu]
  have hmemL : ∀ᶠ u in 𝓝[<] (0 : ℝ), u ∈ Ioo (-T) 0 := Ioo_mem_nhdsLT (by linarith)
  have hmemR : ∀ᶠ u in 𝓝[>] (0 : ℝ), u ∈ Ioo 0 T := Ioo_mem_nhdsGT hT
  -- one-sided limits of `K` and `K'` at `0`
  have hKr : Tendsto K (𝓝[>] 0) (𝓝 0) :=
    hL1.congr' (by filter_upwards [hmemR] with u hu using (hKR u hu).symm)
  have hKl : Tendsto K (𝓝[<] 0) (𝓝 0) := by
    refine (hR1.comp hshift).congr' ?_
    filter_upwards [hmemL] with u hu using (hKL u hu).symm
  have hρr : Tendsto ρ (𝓝[>] 0) (𝓝 0) := by
    simpa [hρ0] using (hρ.tendsto 0).mono_left nhdsWithin_le_nhds
  have hρl : Tendsto ρ (𝓝[<] 0) (𝓝 0) := by
    simpa [hρ0] using (hρ.tendsto 0).mono_left nhdsWithin_le_nhds
  have hK'r : Tendsto K' (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun u => ρ u - a u * H u) (𝓝[>] 0) (𝓝 (0 - 0)) := hρr.sub hL2
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [hmemR] with u hu
    simp only [hK', hKR u hu]
  have hK'l : Tendsto K' (𝓝[<] 0) (𝓝 0) := by
    have : Tendsto (fun u => ρ u - a (u + T) * H (u + T)) (𝓝[<] 0) (𝓝 (0 - 0)) :=
      hρl.sub (hR2.comp hshift)
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [hmemL] with u hu
    simp only [hK', hKL u hu, haper u]
  have hK'0 : K' 0 = 0 := by simp [hK', hK0, hρ0]
  have hcontK0 : ContinuousAt K 0 := by
    rw [continuousAt_iff_continuous_left'_right']
    exact ⟨by rw [ContinuousWithinAt, hK0]; exact hKl, by rw [ContinuousWithinAt, hK0]; exact hKr⟩
  have hcontK'0 : ContinuousAt K' 0 := by
    rw [continuousAt_iff_continuous_left'_right']
    exact ⟨by rw [ContinuousWithinAt, hK'0]; exact hK'l,
      by rw [ContinuousWithinAt, hK'0]; exact hK'r⟩
  -- derivative on `(0, T)` and on `(-T, 0)`
  have hKd_mid : ∀ v ∈ Ioo 0 T, HasDerivAt K (K' v) v := fun v hv => by
    have h2 : K' v = ρ v - a v * H v := by simp only [hK', hKR v hv]
    rw [h2]
    refine (hHd v hv).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hv.1 hv.2] with u hu using hKR u hu
  have hKd_left : ∀ u ∈ Ioo (-T) 0, HasDerivAt K (K' u) u := fun u hu => by
    have hw : u + T ∈ Ioo 0 T := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have h1 := (hHd (u + T) hw).comp_add_const u T
    have h2 : K' u = ρ (u + T) - a (u + T) * H (u + T) := by
      simp only [hK', hKL u hu, hρper u, haper u]
    rw [h2]
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with w hw using hKL w hw
  have hKd0 : HasDerivAt K (K' 0) 0 := by
    refine hasDerivAt_of_hasDerivAt_Ioo_Ioo (x := 0) (δ := T) hT hcontK0 ?_ ?_ hcontK'0
    · intro u hu
      exact hKd_mid u ⟨hu.1, by simpa using hu.2⟩
    · intro u hu
      exact hKd_left u ⟨by simpa using hu.1, hu.2⟩
  have hKd : ∀ u, HasDerivAt K (K' u) u := fun u =>
    Periodic.hasDerivAt_of_Ico (x := 0) hT hKper hK'per (fun v hv => by
      rcases eq_or_lt_of_le hv.1 with h0 | h0
      · rw [← h0]; exact hKd0
      · exact hKd_mid v ⟨h0, by simpa using hv.2⟩) u
  have hK'cont : Continuous K' := by
    refine Periodic.continuous_of_continuousAt_Ico (x := 0) hT hK'per fun v hv => ?_
    rcases eq_or_lt_of_le hv.1 with h0 | h0
    · rw [← h0]; exact hcontK'0
    · have hvI : v ∈ Ioo 0 T := ⟨h0, by simpa using hv.2⟩
      exact hρ.continuousAt.sub ((hcontA.continuousAt (Ioo_mem_nhds hvI.1 hvI.2)).mul
        (hKd v).continuousAt)
  refine ⟨K, ?_, hKper, hK0, hKd⟩
  rw [contDiff_one_iff_deriv]
  refine ⟨fun u => (hKd u).differentiableAt, ?_⟩
  have : deriv K = K' := funext fun u => (hKd u).deriv
  rw [this]
  exact hK'cont

end ComplexSLE.Infrastructure

end
