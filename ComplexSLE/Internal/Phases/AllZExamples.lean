/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import ComplexSLE.Internal.Phases.AllZEvents

/-!
# The event `{T_z < ∞}` is scale invariant and future dependent

The first example of events in the statement of Lemma 3.3 (paper.tex:L1304) is `{T_z < ∞}`. For
every continuous driver it satisfies the two algebraic hypotheses of Lemma 3.3 pathwise:

* `scaleInvariantEvents_absorbingTime_lt_top`: `T_{rz}(r u(·/r²)) = r² T_z(u)`
  (`absorbingTime_scale`);
* `futureDependentEvents_absorbingTime_lt_top`: `T_z(u) = s + T_{f_s z}(u(· + s) - u s)` for
  `z ∉ L_s` (`absorbingTime_eq_add_shift`).

(The measurability hypothesis `MeasurableEvents` of the example is not proved here.)
-/

public section

open scoped NNReal ENNReal

namespace ComplexSLE.Internal

theorem scaleInvariantEvents_absorbingTime_lt_top :
    ScaleInvariantEvents fun u z => absorbingTime u z < ⊤ := by
  intro u _ r hr z
  beta_reduce
  rw [absorbingTime_scale u z r hr]
  have hr2 : ((r ^ 2 : ℝ≥0) : ℝ≥0∞) ≠ 0 := by simpa using hr.ne'
  rw [ENNReal.mul_lt_top_iff]
  constructor
  · intro h
    exact Or.inl ⟨ENNReal.coe_lt_top, h⟩
  · rintro (⟨-, h⟩ | h | h)
    · exact h
    · exact absurd h hr2
    · simp [h]

theorem futureDependentEvents_absorbingTime_lt_top :
    FutureDependentEvents fun u z => absorbingTime u z < ⊤ := by
  intro u hu s z hz
  beta_reduce
  rw [absorbingTime_eq_add_shift hu s z hz]
  simp only [ENNReal.add_lt_top, ENNReal.coe_lt_top, true_and]

end ComplexSLE.Internal

end
