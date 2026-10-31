/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Infrastructure.Planar.CrossingLimit
public import ComplexSLE.Infrastructure.Planar.Chain

/-!
# Lemma 4.1: the hit point (chain argument)

A planar lemma used in the proof of Lemma 4.1 (paper.tex:L2159-2195).  Let `R` be a compact
connected set joining `0` to a point of real part `≥ 7 C + 1` inside the strip `|Im| < 1`, and let
`F` be continuous on the box `N = [2 C - 1, 7 C + 1] × [-1, 1]`, moving real parts to the left by
an amount in `[3 C, 6 C]` and imaginary parts into `[-M, M]`.  If `B` is a closed connected set in
the strip `|Re| < 1/2` reaching above `M + 2` and below `-(M + 2)`, then `F` maps some point of
`R ∩ N` into `B`.

The proof discretizes: `R` carries `ρ`-chains from `0` to the far point; the last passage of the
chain through `Re < 2 C - 1/2` and the next passage through `Re > 7 C + 1/2` cut out a chain
inside `N` whose `F`-image crosses from `Re ≤ -1/2` to `Re ≥ 1/2` at height `≤ M`; the chain
crossing lemma `exists_dist_le_of_chain_crossing` and a compactness limit finish.
-/

@[expose] public section

open Set Metric

namespace ComplexSLE.Internal

/-- A version of `ComplexSLE.Planar.exists_mem_image_of_chain_crossing` in which only chains of
mesh `ρ ≤ ρ₀` are required. -/
theorem exists_mem_image_of_chain_crossing_small {S : Set ℂ} (hS : IsCompact S) {F : ℂ → ℂ}
    (hF : ContinuousOn F S) {B : Set ℂ} (hB : IsClosed B) (hBc : IsPreconnected B)
    {ε h ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (hBre : ∀ w ∈ B, |w.re| < ε) {b₁ b₂ : ℂ} (hb₁ : b₁ ∈ B)
    (hb₂ : b₂ ∈ B) (hb₁h : h < b₁.im) (hb₂h : b₂.im < -h)
    (hchain : ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ (n : ℕ) (β : Fin (n + 1) → ℂ), (∀ k, β k ∈ S) ∧
      (∀ k : Fin n, dist (F (β k.castSucc)) (F (β k.succ)) < ρ) ∧
      (∀ k, |(F (β k)).im| + 2 * ρ ≤ h) ∧ (F (β 0)).re ≤ -ε ∧
      ε ≤ (F (β (Fin.last n))).re) :
    ∃ s ∈ S, F s ∈ B := by
  have hcross : ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ s ∈ S, ∃ w ∈ B, dist (F s) w ≤ ρ := by
    intro ρ hρ hρρ₀
    obtain ⟨n, β, hβS, hβd, hβim, hβ0, hβl⟩ := hchain ρ hρ hρρ₀
    obtain ⟨k, w, hwB, hk⟩ := ComplexSLE.Planar.exists_dist_le_of_chain_crossing hBc hBre hb₁ hb₂
      hb₁h hb₂h (fun k => F (β k)) hβd hβim hβ0 hβl
    exact ⟨β k, hβS k, w, hwB, hk⟩
  obtain ⟨s₀, hs₀S, -⟩ := hcross ρ₀ hρ₀ le_rfl
  have hcont : ContinuousOn (fun s => infDist (F s) B) S :=
    (continuous_infDist_pt B).comp_continuousOn hF
  obtain ⟨s, hsS, hmin⟩ := hS.exists_isMinOn ⟨s₀, hs₀S⟩ hcont
  refine ⟨s, hsS, ?_⟩
  have hBne : B.Nonempty := ⟨b₁, hb₁⟩
  rw [← hB.closure_eq, mem_closure_iff_infDist_zero hBne]
  by_contra hne
  have hpos : 0 < infDist (F s) B := lt_of_le_of_ne infDist_nonneg (Ne.symm hne)
  obtain ⟨s', hs'S, w, hwB, hw⟩ := hcross (min ρ₀ (infDist (F s) B / 2))
    (lt_min hρ₀ (by positivity)) (min_le_left _ _)
  have h1 : infDist (F s') B ≤ dist (F s') w := infDist_le_dist_of_mem hwB
  have h2 : infDist (F s) B ≤ infDist (F s') B := hmin hs'S
  have h3 := (hw.trans (min_le_right _ _))
  linarith

/-- Last exit and next entry of a real sequence with small steps. -/
theorem exists_exit_entry {n : ℕ} (g : ℕ → ℝ) {a b s : ℝ} (hab : a < b) (hs : s ≤ b - a)
    (h0 : g 0 < a) (hn : b < g n) (hstep : ∀ k < n, |g (k + 1) - g k| < s) :
    ∃ i j : ℕ, i + 1 < j ∧ j ≤ n ∧ g i < a ∧ b < g j ∧
      ∀ k, i < k → k < j → a ≤ g k ∧ g k ≤ b := by
  classical
  set i := Nat.findGreatest (fun k => g k < a) n with hi
  have hi_spec : g i < a := Nat.findGreatest_spec (P := fun k => g k < a) (Nat.zero_le n) h0
  have hin : i ≤ n := Nat.findGreatest_le n
  have hge : ∀ k, i < k → k ≤ n → a ≤ g k := fun k hk hkn =>
    not_lt.1 (Nat.findGreatest_is_greatest hk hkn)
  have hin' : i < n := by
    rcases hin.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [h] at hi_spec
      linarith
  have hex : ∃ k, i < k ∧ b < g k := ⟨n, hin', hn⟩
  set j := Nat.find hex with hj
  obtain ⟨hij, hjb⟩ := Nat.find_spec hex
  have hjn : j ≤ n := Nat.find_min' hex ⟨hin', hn⟩
  have hmid : ∀ k, i < k → k < j → a ≤ g k ∧ g k ≤ b := by
    intro k hik hkj
    refine ⟨hge k hik (by omega), ?_⟩
    have := Nat.find_min hex hkj
    push Not at this
    exact this hik
  refine ⟨i, j, ?_, hjn, hi_spec, hjb, hmid⟩
  by_contra hcon
  have hj1 : j = i + 1 := by omega
  have := hstep i hin'
  rw [← hj1] at this
  have h2 := (abs_lt.1 this).2
  have hjb' : b < g j := hjb
  linarith

/-- The box `N(C) = [2 C - 1, 7 C + 1] × [-1, 1]` of Lemma 4.4. -/
def hitBox (C : ℝ) : Set ℂ := {z | 2 * C - 1 ≤ z.re ∧ z.re ≤ 7 * C + 1 ∧ |z.im| ≤ 1}

theorem isClosed_hitBox (C : ℝ) : IsClosed (hitBox C) := by
  unfold hitBox
  simp only [Set.ofPred_and]
  refine (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le Complex.continuous_re continuous_const).inter ?_)
  exact isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const

/-- **The hit point.** -/
theorem exists_hit {R B : Set ℂ} {F : ℂ → ℂ} {C M : ℝ} (hC : 2 ≤ C)
    (hR : IsCompact R) (hRc : IsPreconnected R) (hR0 : (0 : ℂ) ∈ R) {q : ℂ} (hqR : q ∈ R)
    (hq : 7 * C + 1 ≤ q.re) (hRim : ∀ w ∈ R, |w.im| < 1)
    (hFc : ContinuousOn F (hitBox C))
    (hF : ∀ z ∈ hitBox C, z.re - 6 * C ≤ (F z).re ∧ (F z).re ≤ z.re - 3 * C ∧
      |(F z).im| ≤ M)
    (hB : IsClosed B) (hBc : IsPreconnected B) (hBre : ∀ w ∈ B, |w.re| < 1 / 2)
    {b₁ b₂ : ℂ} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (hb₁h : M + 2 < b₁.im)
    (hb₂h : b₂.im < -(M + 2)) :
    ∃ β ∈ R, β ∈ hitBox C ∧ F β ∈ B := by
  have hS : IsCompact (R ∩ hitBox C) := hR.inter_right (isClosed_hitBox C)
  have hFS : ContinuousOn F (R ∩ hitBox C) := hFc.mono inter_subset_right
  suffices hchain : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 2 → ∃ (n : ℕ) (β : Fin (n + 1) → ℂ),
      (∀ k, β k ∈ R ∩ hitBox C) ∧
      (∀ k : Fin n, dist (F (β k.castSucc)) (F (β k.succ)) < ρ) ∧
      (∀ k, |(F (β k)).im| + 2 * ρ ≤ M + 2) ∧ (F (β 0)).re ≤ -(1 / 2) ∧
      1 / 2 ≤ (F (β (Fin.last n))).re by
    obtain ⟨β, hβ, hFβ⟩ := exists_mem_image_of_chain_crossing_small (S := R ∩ hitBox C) hS hFS hB
      hBc (ε := 1 / 2) (h := M + 2) (ρ₀ := 1 / 2) (by norm_num) hBre hb₁ hb₂ hb₁h hb₂h hchain
    exact ⟨β, hβ.1, hβ.2, hFβ⟩
  intro ρ hρ hρ1
  have hunif := Metric.uniformContinuousOn_iff.1
    (hS.uniformContinuousOn_of_continuous hFS) ρ hρ
  obtain ⟨ρ', hρ', hunif⟩ := hunif
  set ρ'' : ℝ := min ρ' 1 with hρ''
  have hρ''pos : 0 < ρ'' := lt_min hρ' one_pos
  have hρ''1 : ρ'' ≤ 1 := min_le_right _ _
  have hρ''ρ' : ρ'' ≤ ρ' := min_le_left _ _
  obtain ⟨n, β, hβ0, hβl, hβR, hβd⟩ := ComplexSLE.Planar.exists_chain_of_isPreconnected hRc hR0 hqR
    hρ''pos
  -- ℕ-indexed version of the chain
  set β' : ℕ → ℂ := fun k => β ⟨min k n, Nat.lt_succ_of_le (min_le_right _ _)⟩ with hβ'
  have hβ'R : ∀ k, β' k ∈ R := fun k => hβR _
  have hβ'0 : β' 0 = 0 := by
    rw [← hβ0]
    simp only [hβ']
    congr 1
  have hβ'n : β' n = q := by
    rw [← hβl]
    simp only [hβ']
    congr 1
    exact Fin.ext (by simp)
  have hβ'd : ∀ k < n, dist (β' k) (β' (k + 1)) < ρ'' := by
    intro k hk
    have := hβd ⟨k, hk⟩
    convert this using 2
    · simp only [hβ']
      congr 1
      exact Fin.ext (by simp [min_eq_left hk.le])
    · simp only [hβ']
      congr 1
      exact Fin.ext (by simp [min_eq_left (Nat.succ_le_of_lt hk)])
  have hg : ∀ k < n, |(β' (k + 1)).re - (β' k).re| < ρ'' := by
    intro k hk
    have h1 := hβ'd k hk
    rw [dist_comm, dist_eq_norm] at h1
    have h2 := Complex.abs_re_le_norm (β' (k + 1) - β' k)
    rw [Complex.sub_re] at h2
    exact lt_of_le_of_lt h2 h1
  obtain ⟨i, j, hij, hjn, hia, hjb, hmid⟩ := exists_exit_entry (fun k => (β' k).re)
    (a := 2 * C - 1 / 2) (b := 7 * C + 1 / 2) (s := ρ'') (by linarith) (by linarith)
    (by simp only [hβ'0, Complex.zero_re]; linarith)
    (by simp only [hβ'n]; linarith) hg
  obtain ⟨m, hm⟩ : ∃ m, j = i + 1 + m + 1 := ⟨j - i - 2, by omega⟩
  have hγ : ∀ k : ℕ, k ≤ m → β' (i + 1 + k) ∈ R ∩ hitBox C ∧
      2 * C - 1 / 2 ≤ (β' (i + 1 + k)).re ∧ (β' (i + 1 + k)).re ≤ 7 * C + 1 / 2 := by
    intro k hk
    obtain ⟨h1, h2⟩ := hmid (i + 1 + k) (by omega) (by omega)
    refine ⟨⟨hβ'R _, ?_, ?_, ?_⟩, h1, h2⟩
    · change 2 * C - 1 ≤ _
      linarith
    · change _ ≤ 7 * C + 1
      linarith
    · exact (hRim _ (hβ'R _)).le
  refine ⟨m, fun k => β' (i + 1 + k), fun k => (hγ k (by omega)).1, ?_, ?_, ?_, ?_⟩
  · intro k
    simp only [Fin.val_castSucc, Fin.val_succ]
    have hk := k.2
    refine hunif _ (hγ k (by omega)).1 _ (hγ (k + 1) (by omega)).1 ?_
    have := hβ'd (i + 1 + k) (by omega)
    have e : i + 1 + ((k : ℕ) + 1) = i + 1 + (k : ℕ) + 1 := by omega
    rw [e]
    exact lt_of_lt_of_le this hρ''ρ'
  · intro k
    have := (hF _ (hγ k (by omega)).1.2).2.2
    linarith
  · simp only [Fin.val_zero, add_zero]
    have h1 := (hF _ (hγ 0 (by omega)).1.2).2.1
    have h2 := hg i (by omega)
    have h3 := (abs_lt.1 h2).2
    simp only [add_zero] at h1
    have h4 : (β' i).re < 2 * C - 1 / 2 := hia
    linarith
  · simp only [Fin.val_last]
    have h1 := (hF _ (hγ m le_rfl).1.2).1
    have h2 := hg (i + 1 + m) (by omega)
    have h3 := (abs_lt.1 h2).2
    have h4 : 7 * C + 1 / 2 < (β' (i + 1 + m + 1)).re := by rw [← hm]; exact hjb
    linarith

end ComplexSLE.Internal

end
