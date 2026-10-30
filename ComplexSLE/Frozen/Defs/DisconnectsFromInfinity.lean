/-
Loewner evolution driven by complex Brownian motion: a formalization of arXiv:2203.07313v4
(Gwynne–Pfeffer).
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Connected.Basic

/-!
# Disconnecting from infinity
-/

@[expose] public section


namespace ComplexSLE

/-- `S` disconnects `S'` from infinity: `S'` is disjoint from every unbounded connected
component of `ℂ \ S` (Def 1.9, paper.tex:L497-499). Points of `S` itself count as
disconnected, as the definition intends. -/
def DisconnectsFromInfinity (S S' : Set ℂ) : Prop :=
  ∀ x ∈ Sᶜ, ¬ Bornology.IsBounded (connectedComponentIn Sᶜ x) →
    Disjoint S' (connectedComponentIn Sᶜ x)

end ComplexSLE

end
