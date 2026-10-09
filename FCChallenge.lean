import Mathlib

/-!
# Challenge: the Formal Conjectures variants of the Hilbert–Smith conjecture

The two statements below are proposed as variants in
`FormalConjectures/HilbertProblems/5.lean` of
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(issue 6914). Their text, including the `namespace`, `open` and `variable` lines, is the text
proposed there; only the `@[category …, AMS …, formal_proof …]` attributes, which are defined in
Formal Conjectures, are omitted. They differ from `Hilbert5.hilbert_smith_conjecture` and
`Hilbert5.hilbert_smith_padic_formulation` of Formal Conjectures by:

* `[SecondCountableTopology X]`, and in the first one `[T2Space G] [SecondCountableTopology G]`;
* in the first one, the conclusion: a `C^∞` Lie group structure on `G` for its given topology
  (as in `Challenge.lean`), instead of `AdmitsLieGroupStructure G` (a continuous isomorphism onto
  a real-analytic Lie group).

This file imports only Mathlib and has proofs `sorry`. `FCSolution.lean` proves both statements.
-/

namespace Hilbert5

open scoped Manifold ContDiff Bundle

variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}

/-- The Hilbert–Smith conjecture for second-countable `X` and `G`, with a `C^∞` Lie group
structure on `G` for its given topology. -/
theorem hilbert_smith_conjecture.variants.second_countable_smooth {X : Type*}
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [ConnectedSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MulAction G X] [ContinuousSMul G X] [FaithfulSMul G X] :
    ∃ (d : ℕ) (_ : ChartedSpace (EuclideanSpace ℝ (Fin d)) G),
      LieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ G := by
  sorry

/-- The p-adic formulation for a second-countable manifold `X`: the p-adic integers `ℤ_[p]`
cannot act continuously and faithfully on `X`. -/
theorem hilbert_smith_padic_formulation.variants.second_countable {X : Type*}
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [ConnectedSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    (p : ℕ) [Fact p.Prime] [AddAction ℤ_[p] X] [ContinuousVAdd ℤ_[p] X] :
    ¬ FaithfulVAdd ℤ_[p] X := by
  sorry

end Hilbert5
