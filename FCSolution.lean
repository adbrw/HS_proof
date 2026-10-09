import Mathlib
import HSFormal.Universe

/-!
# Solution to `FCChallenge.lean`

The two statements are copied verbatim from `FCChallenge.lean` (the variants proposed in
`FormalConjectures/HilbertProblems/5.lean`) and proved by the universe-polymorphic theorems of
`HSFormal/Universe.lean`:

* `hilbert_smith_conjecture.variants.second_countable_smooth` by
  `HSFormal.Universe.hilbertSmith_univ`;
* `hilbert_smith_padic_formulation.variants.second_countable` by
  `HSFormal.Universe.padicExclusion_univ`.

`import Mathlib` is not needed by the proofs. It makes the imports of this file a superset of those
of `FCChallenge.lean`, which SafeVerify requires.
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
      LieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ G :=
  HSFormal.Universe.hilbertSmith_univ n X G

/-- The p-adic formulation for a second-countable manifold `X`: the p-adic integers `ℤ_[p]`
cannot act continuously and faithfully on `X`. -/
theorem hilbert_smith_padic_formulation.variants.second_countable {X : Type*}
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [ConnectedSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    (p : ℕ) [Fact p.Prime] [AddAction ℤ_[p] X] [ContinuousVAdd ℤ_[p] X] :
    ¬ FaithfulVAdd ℤ_[p] X :=
  HSFormal.Universe.padicExclusion_univ p n X

end Hilbert5
