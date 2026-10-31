# M8 / T1 — Planar topology for §4: chain arguments, separation, crossing, pullback (prover brief, Sonnet)

Context: arXiv:2203.07313v4 §4 (source/arxiv-2203.07313v4/complex-sle-final.tex L1938-2224). The proof of Lemma 4.1 says
"by topological considerations" (L2194) and uses "L hits every left-right crossing" (event E_4, L2175). We replace these by
the elementary lemmas below (orchestrator blueprint: review/plans/M8.md §1). Everything here is deterministic planar
topology about subsets of ℂ, plus one Loewner growth lemma (part H). No EXTERNAL is allowed or needed.

Definition used (frozen, read-only): `ComplexSLE.DisconnectsFromInfinity S S'` (ComplexSLE/Frozen/Defs/DisconnectsFromInfinity.lean):
  ∀ x ∈ Sᶜ, ¬ Bornology.IsBounded (connectedComponentIn Sᶜ x) → Disjoint S' (connectedComponentIn Sᶜ x).

Ownership: new files `ComplexSLE/Infrastructure/Planar/*.lean` (parts A–G; namespace `ComplexSLE.Planar`) and
`ComplexSLE/Internal/Disconnect/Growth.lean` (part H; namespace `ComplexSLE.Internal`). Nothing else. Scratch only in
`.lake/probes/m8-t1/`. Another Sonnet works concurrently on `ComplexSLE/Internal/Disconnect/Lemma44*.lean`.

Deliverables (exact statements may be adjusted for convenience — e.g. List vs Fin-indexed chains, strict vs non-strict
inequalities — as long as they are at least as strong as described; report the final statements):

A. **Chains in preconnected sets.** In a (pseudo)metric space, if `s` is preconnected, `x y ∈ s`, `0 < ρ`, then there is a
   finite chain `β : Fin (n+1) → E` with `β 0 = x`, `β (Fin.last n) = y`, all `β k ∈ s`, consecutive distances `< ρ`.
   (Proof: the set of points of s reachable from x by ρ-chains in s is relatively clopen in s.)

B. **Chain argument.** For `β : Fin (n+1) → ℂ` define
   `chainArg β w := ∑ k : Fin n, Complex.arg ((w - β k.castSucc) / (w - β k.succ))`. Prove, for `ρ > 0` with all consecutive
   distances `< ρ`:
   - `ContinuousOn (chainArg β) {w | ∀ k, ρ < ‖w - β k‖}` (each ratio is `1 + (β_{k+1} - β_k)/(w - β_{k+1})`, at distance `< 1`
     from 1, hence in `Complex.slitPlane`; use `Complex.continuousAt_arg`);
   - `Complex.exp (chainArg β w * I) = r / ‖r‖` with `r = (w - β 0) / (w - β (Fin.last n))`, on that set (telescoping product
     of unit numbers);
   - `chainArg β w → 0` as `‖w‖ → ∞` (e.g. `Tendsto (chainArg β) (cocompact ℂ) (𝓝 0)`).

C. **Basic facts on `DisconnectsFromInfinity`.**
   - (mono) `K ⊆ K'` and `DisconnectsFromInfinity K W` ⇒ `DisconnectsFromInfinity K' W`.
   - (connected spread) `K` closed, `W` preconnected, `Disjoint W K`, `z ∈ W`, `DisconnectsFromInfinity K {z}` ⇒
     `DisconnectsFromInfinity K W`.
   - (open) `K` closed, `z ∉ K`, `DisconnectsFromInfinity K {z}` ⇒ `∃ r > 0, ball z r ⊆ Kᶜ ∧ DisconnectsFromInfinity K (ball z r)`.
   - (unique unbounded component) `K` compact (bounded closed): any two points of `Kᶜ` whose components in `Kᶜ` are both
     unbounded lie in the same component. (A large circle's exterior is connected and lies in `Kᶜ`.)
   - (image) `DisconnectsFromInfinity` is invariant under `conj` and under `z ↦ r * z` for `r > 0` real (homeomorphisms of ℂ
     preserving boundedness): `DisconnectsFromInfinity (f '' K) (f '' W) ↔ DisconnectsFromInfinity K W`. State for a general
     homeomorphism `f : ℂ ≃ₜ ℂ` that maps bounded sets to bounded sets and back.

D. **(P2) Separation by two connected sets.** Statement (x0 real, ε > 0):
   `A B : Set ℂ` compact and preconnected; `∀ w ∈ A, |w.im| < ε`; `Disjoint B (ball (x0 : ℂ) (3 * ε))`;
   `q p ∈ A ∩ B` with `q.re ≤ x0 - ε` and `x0 + ε ≤ p.re`; `z₁ ∈ ball (x0 + 2 * ε * I) ε`, `z₂ ∈ ball (x0 - 2 * ε * I) ε`.
   Conclusion: `DisconnectsFromInfinity (A ∪ B) {z₁} ∨ DisconnectsFromInfinity (A ∪ B) {z₂}`.
   Proof blueprint: suppose neither. Then z₁, z₂ ∉ A ∪ B (z₁ has Im > ε, and lies in the 3ε-ball). By C (unique
   unbounded component) they lie in one component of the open set (A ∪ B)ᶜ, so there is a path between them in it
   (open connected subsets of ℂ are path connected). The path has positive distance d from the compact set A ∪ B. By
   uniform continuity there is a chain from z₁ to z₂ along it with steps < ρ < d. Then Θ := chainArg is continuous on
   A ∪ B, with exp(iΘ) = r/|r| and r(w) = (w - z₁)/(w - z₂).
   - **On B.** B misses the closed segment [z₂, z₁], which lies in the 3ε-ball, so r(w) ∈ slitPlane. Hence
     D := arg ∘ r is continuous on B. Θ − D takes values in 2πℤ (from exp) and is continuous, so it is constant on the
     preconnected B. Call the constant 2πn; it holds at q and at p.
   - **Signs.** Write z₁ = x0 + 2εi + e₁ and z₂ = x0 − 2εi + e₂ with |eᵢ| < ε. Using Im((w−z₁)·conj(w−z₂)) =
     B₁A₂ − A₁B₂ in coordinates, one gets Im r(q) > 0 and Im r(p) < 0. So D(q) ∈ (0, π) and D(p) ∈ (−π, 0).
   - **On A.** Therefore Θ(p) < 2πn < Θ(q). By the IVT on the preconnected A (`IsPreconnected.intermediate_value`)
     some w ∈ A has Θ(w) = 2πn, so r(w) is a positive real λ. Solving w − z₁ = λ(w − z₂) gives
     Im w ∉ [Im z₂, Im z₁] ⊇ (−ε, ε), which contradicts |Im w| < ε.

E. **(CL) Chain crossing.** Statement: `B` compact, preconnected, `∀ w ∈ B, |w.re| < ε`; `b₁ b₂ ∈ B` with `h < b₁.im`,
   `b₂.im < -h`; `β : Fin (n+1) → ℂ` with consecutive distances `< ρ`, `∀ k, |(β k).im| + 2 * ρ ≤ h`, `(β 0).re ≤ -ε`,
   `ε ≤ (β (Fin.last n)).re`. Conclusion: `∃ k, ∃ w ∈ B, dist (β k) w ≤ ρ`.
   Proof blueprint: suppose every β_k is at distance > ρ from B. Then Φ := chainArg β is continuous on B and on the
   vertical rays R₁ = {b₁ + iτ : τ ≥ 0} and R₂ = {b₂ − iτ : τ ≥ 0}. Every point of these rays has |Im| ≥ h, so it is at
   distance ≥ 2ρ from every β_k. Let G(w) = (w − β_0)/(w − β_n), so exp(iΦ) = G/|G|.
   - **Values on B.** Within the strip |Re| < ε, the line through β_0 and β_n lies inside the closed segment
     [β_0, β_n], because Re β_0 ≤ −ε and Re β_n ≥ ε. So G(w) ∉ (0, ∞) for w ∈ B, hence Φ(B) ∩ 2πℤ = ∅. Since B is
     preconnected, Φ(B) ⊆ (2πm, 2π(m+1)) for one m.
   - **Values on the rays.** The rays miss the segment, which has |Im| ≤ h − 2ρ, so G ∈ slitPlane there. Φ − arg G is
     continuous with values in 2πℤ, hence constant on each ray. Both tend to 0 at ∞, so the constant is 0. Thus
     Φ(bᵢ) = arg G(bᵢ).
   - **Contradiction.** b₁ lies above the line and b₂ below it, since on the strip the line's Im is ≤ h − 2ρ < h. So
     Im G(b₁) and Im G(b₂) are nonzero with opposite signs, and arg G(b₁) and arg G(b₂) lie in (0, π) and (−π, 0) in
     some order. They cannot both lie in one interval (2πm, 2π(m+1)).

F. **Pullback of disconnection.** For `L R L' : Set ℂ` with `L` closed, `F : ↥Lᶜ → ℂ` continuous with `F z ∉ R` for all z,
   and the growth condition `∀ M, ∃ M', ∀ z : ↥Lᶜ, M' ≤ ‖(z : ℂ)‖ → M ≤ ‖F z‖`; `V ⊆ Lᶜ` with `F z ∉ L'` for z ∈ V;
   if `DisconnectsFromInfinity (R ∪ L') (F '' V)` (image of the subtype restriction), then
   `DisconnectsFromInfinity (L ∪ {z | ∃ h : z ∈ Lᶜ, F ⟨z, h⟩ ∈ L' \ R}) V`. (Proof: an unbounded component C of the
   complement of the left set is contained in Lᶜ. Its F-image is connected, avoids R ∪ L', is unbounded by growth,
   and contains F(z) for z ∈ C.) This matches the form of `ComplexSLE.concatenation_leftHull`
   (ComplexSLE/Frozen/Concatenation_LeftHull.lean), with F = centeredLoewnerMap U hU t, R = rightHull U hU t and
   L' = the shifted left hull.

G. A corollary of D and C combining the chain-crossing (E) with compactness: if `S ⊆ ℂ` is compact, `F : S → ℂ` is
   continuous, and for every `ρ > 0` there is a ρ-chain in `S` whose F-image satisfies E's hypotheses for `B`, then
   `∃ s ∈ S, F s ∈ B`. (Optional. Skip it if awkward; the orchestrator can do this step in the assembly.)

H. **Loewner growth** (file `ComplexSLE/Internal/Disconnect/Growth.lean`): for continuous `U` and `t`,
   `∀ M, ∃ M', ∀ z (h : z ∈ (leftHull U t)ᶜ), M' ≤ ‖z‖ → M ≤ ‖centeredLoewnerMap U hU t ⟨z, h⟩‖`.
   (Bootstrap along the ODE: while |γ − U| ≥ 1, |γ'| ≤ 2. See `centeredLoewnerMap_eq_of_closedSol` and
   `notMem_leftHull_iff_exists_closedSol` in ComplexSLE/Internal/Duality/Locality.lean, and the proof of
   `isBounded_leftHull'` in ComplexSLE/Internal/Hull/ConnectedNoExt.lean.)

Search Mathlib first (lean-search-discovery skill): `IsPreconnected.intermediate_value`, `IsOpen.isConnected_iff_isPathConnected`,
`Complex.continuousAt_arg`, `Complex.slitPlane`, `connectedComponentIn`, `IsPreconnected.subset_connectedComponentIn`,
`Metric.infDist`, `IsCompact.exists_infDist_eq_dist`, `CompactSpace.uniformContinuous_of_continuous`.

Checks: `lake build ComplexSLE.Infrastructure.Planar.<each>` and `ComplexSLE.Internal.Disconnect.Growth`; `tools/check.sh --quick`;
`#print axioms` (expect only propext, Classical.choice, Quot.sound). Budget ~4 hours; land what is proved, report the rest
precisely (D and E are the priority, then F, C, H, A/B as needed by them).

## Hard rules (repeat verbatim in every worker brief)


1. Never edit a file under `ComplexSLE/Frozen/`, `frozen-anchor-manifest.json`,
   `DEPGRAPH*.md`, `STATUS.md`, `ERRATA.md`, `lakefile.toml`, `lean-toolchain`
   or `lake-manifest.json`. If a frozen declaration looks wrong, stop and report.
2. No `sorry`, `admit`, `axiom`, `opaque` placeholders, `native_decide`,
   `implemented_by`, `@[extern]`, `unsafe`, or `set_option maxHeartbeats`
   (or any other heartbeat / recursion / debug override) anywhere in tracked files.
   Unfinished work stays out of `ComplexSLE/` or is reported as unfinished.
3. Never add a hypothesis to a source-facing statement to make a proof go through.
   A needed intermediate result is proved, not assumed.
4. Never import a frozen anchor that is in state `DRAFT_SORRY`, nor its provider
   module (see the manifest). Consume only sealed anchors, your own files, and
   `EXTERNAL` inputs through `ComplexSLE/External/` when your brief lists them.
5. Every Lean file is a `module`: copyright comment, `module`, imports
   (`public import` for anything statements need), module docstring,
   `public section` (`@[expose] public section` for source-facing definitions).
6. At most 1500 lines per file. Split larger files.
7. Do not run `lake clean`, delete anything under `.lake/`, or modify Mathlib.
8. Do not commit; the orchestrator commits. Do not touch files you were not given.
9. Scratch and probe files go outside `ComplexSLE/` (e.g. `.lake/probes/`) and are
   deleted after use.
10. Report exactly: files changed, approach, the exact commands run and their output,
    `#print axioms` for every new public theorem, and anything unproved or uncertain.
11. Do not spawn subagents, forks or parallel workers of your own (the orchestrator enforces a two-agent cap).

Handoff: files changed; exact statements; approach; commands and outputs; axioms; anything unproved.
